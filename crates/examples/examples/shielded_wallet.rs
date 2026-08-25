//! A shielded-pool wallet syncing off an unreliable rpc.
//!
//! sealring owns the receive path: the pool publishes envelopes naming no recipient, so a
//! wallet finds its own only by trying its key against every one. chainfold owns the order.
//! The join is the `Source`: trial decryption is how this wallet decodes the wire format, so
//! the scan runs there, one batch per poll, and only the notes this key opens reach the fold.
//!
//! ```sh
//! cargo run --release -p examples --example shielded_wallet
//! ```

use chainfold::{
    BlockRef,
    Driver,
    DriverConfig,
    EngineConfig,
    Fold,
    FoldError,
    Position,
    Source,
    Tick,
};
use rand_chacha::{
    ChaCha20Rng,
    rand_core::SeedableRng,
};
use sealring::{
    Domain,
    Recipient,
    Scanner,
    SealedNote,
    X25519,
    seal,
};
use x25519_dalek::{
    PublicKey,
    StaticSecret,
};

/// Associated data every envelope in this pool binds. It names the pool alone, so an
/// envelope still opens at whatever position a reorg leaves it.
const POOL_AAD: &[u8] = b"examples.shielded-pool/v1";
/// Block the pool deployed at.
const FIRST_BLOCK: u64 = 1;
/// Blocks the pool publishes before the reorg.
const BLOCKS: u64 = 20;
/// Envelopes published per block, and how often one of them is this wallet's.
const NOTES_PER_BLOCK: u64 = 3;
/// Blocks per range query, the cap a node puts on `eth_getLogs`.
const WINDOW: u64 = 4;
/// Observed-block ring window.
const RING_CAPACITY: usize = 32;
/// Retained rollback points, and the blocks of cursor progress between them.
const CHECKPOINT_SLOTS: usize = 4;
const CHECKPOINT_INTERVAL: u64 = 2;
/// Blocks the reorg replaces, inside the rollback window above.
const REORG_DEPTH: usize = 3;

/// Envelope as it is published: canonical bytes, parsed once on the way into a block.
type Envelope = SealedNote<X25519, Vec<u8>>;

/// Note codec for this pool: a value in the smallest unit, little endian.
struct Payments;

impl Domain for Payments {
    // sealring discards the codec error at its boundary; the unit type carries it.
    type Error = ();
    type Note = u64;

    const DOMAIN_TAG: &'static str = "examples.shielded-wallet/v1";

    fn encode_note(note: &u64, out: &mut Vec<u8>) -> Result<(), ()> {
        out.extend_from_slice(&note.to_le_bytes());
        Ok(())
    }

    fn decode_note(bytes: &[u8]) -> Result<u64, ()> {
        Ok(u64::from_le_bytes(bytes.try_into().map_err(|_| ())?))
    }
}

/// One published block: an ancestry-committing hash and the envelopes it carries.
struct Block {
    number: u64,
    hash: [u8; 32],
    notes: Vec<Envelope>,
}

/// Scripted pool chain viewed through one wallet key.
///
/// Blocks carry envelopes for every recipient in the pool; `events_in` scans a whole poll
/// window in one batch and yields the values this key opens, at the position they were
/// published at.
struct Pool {
    first_block: u64,
    blocks: Vec<Block>,
    scanner: Scanner<X25519, Payments>,
    salt: u64,
    /// Envelopes trial-decrypted since the wallet opened, the cost of the receive path.
    scanned: usize,
}

impl Pool {
    /// Builds an empty pool whose first published block is numbered `first_block`.
    fn new(first_block: u64, recipient: Recipient<X25519>) -> Self {
        Self {
            first_block,
            blocks: Vec::new(),
            scanner: Scanner::new(recipient),
            salt: 0,
            scanned: 0,
        }
    }

    /// Publishes one block carrying `notes`, hashed from the tip and a fresh salt.
    fn push_block(&mut self, notes: Vec<Envelope>) {
        let pushed = u64::try_from(self.blocks.len()).expect("block count fits in u64");
        let number = self
            .first_block
            .checked_add(pushed)
            .expect("block number fits in u64");
        let parent = self.blocks.last().map_or([0u8; 32], |block| block.hash);
        let hash = block_hash(parent, number, self.salt);
        self.salt = self.salt.checked_add(1).expect("salt counter fits in u64");
        self.blocks.push(Block {
            number,
            hash,
            notes,
        });
    }

    /// Replaces the last `depth` blocks; every replacement hashes differently.
    fn reorg(&mut self, depth: usize, replacements: Vec<Vec<Envelope>>) {
        self.blocks
            .truncate(self.blocks.len().saturating_sub(depth));
        for notes in replacements {
            self.push_block(notes);
        }
    }

    /// Header for an exact block number if it is on the current chain.
    fn header(&self, number: u64) -> Option<BlockRef> {
        let offset = usize::try_from(number.checked_sub(self.first_block)?).ok()?;
        self.blocks.get(offset).map(|block| BlockRef {
            number: block.number,
            hash: block.hash,
        })
    }

    /// Every envelope on the current chain, oldest first.
    fn published(&self) -> impl Iterator<Item = &Envelope> {
        self.blocks.iter().flat_map(|block| block.notes.iter())
    }
}

impl Source for Pool {
    type Error = core::convert::Infallible;
    type Event = u64;

    fn head(&mut self) -> Result<u64, Self::Error> {
        Ok(self
            .blocks
            .last()
            .map_or(self.first_block.saturating_sub(1), |block| block.number))
    }

    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, Self::Error> {
        Ok(self.header(number))
    }

    fn events_in(
        &mut self,
        from: u64,
        to: u64,
        out: &mut Vec<(BlockRef, u32, u64)>,
    ) -> Result<(), Self::Error> {
        let Self {
            blocks,
            scanner,
            scanned,
            ..
        } = self;

        // one scan over the whole window: chunked decapsulation is what a scanner buys over
        // a per-envelope open, and the position lane keeps each hit's origin.
        let mut positions = Vec::new();
        let mut envelopes = Vec::new();
        for block in blocks.iter().filter(|b| (from..=to).contains(&b.number)) {
            let header = BlockRef {
                number: block.number,
                hash: block.hash,
            };
            for (index, envelope) in block.notes.iter().enumerate() {
                let log_index = u32::try_from(index).expect("log index fits in u32");
                positions.push((header, log_index));
                envelopes.push(envelope);
            }
        }
        *scanned += envelopes.len();

        out.extend(scanner.scan(envelopes, POOL_AAD).map(|(index, note)| {
            let (header, log_index) = positions[index];
            (
                header,
                log_index,
                note.expect("every envelope in this pool is well formed"),
            )
        }));
        Ok(())
    }

    fn window(&self) -> u64 {
        WINDOW
    }
}

/// Wallet balance over the notes this key opened.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct Balance {
    /// Value of every note folded so far.
    total: u128,
    /// Notes folded so far.
    notes: u64,
}

impl Balance {
    /// Adds one opened note.
    fn credit(&mut self, value: u64) -> Option<()> {
        self.total = self.total.checked_add(u128::from(value))?;
        self.notes = self.notes.checked_add(1)?;
        Some(())
    }
}

impl Fold for Balance {
    type Error = &'static str;
    type Event = u64;

    fn apply(
        &mut self,
        _pos: Position,
        event: &u64,
    ) -> Result<(), FoldError<Self::Error>> {
        self.credit(*event)
            .ok_or(FoldError::Halt("balance overflow"))
    }
}

/// Fixture block hash. Mixing only: what matters is that it commits to the parent, so a
/// replaced block changes the hash the engine compares.
fn block_hash(parent: [u8; 32], number: u64, salt: u64) -> [u8; 32] {
    let mut hash = [0u8; 32];
    let mut state = splitmix64(number ^ salt);
    for (lane, out) in parent.chunks_exact(8).zip(hash.chunks_exact_mut(8)) {
        let lane = u64::from_le_bytes(lane.try_into().expect("eight-byte lane"));
        state = splitmix64(state ^ lane);
        out.copy_from_slice(&state.to_le_bytes());
    }
    hash
}

/// One splitmix64 mixing step.
fn splitmix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

/// Seals one note of `value` to `pk`.
fn note(pk: &PublicKey, value: u64, rng: &mut ChaCha20Rng) -> Envelope {
    seal::<X25519, Payments>(pk, &value, POOL_AAD, rng).expect("the note seals")
}

/// Envelopes for one block: the slot at `mine` is sealed to the wallet, the rest to
/// strangers. Values carry `tag` so the reorg's notes are distinguishable.
fn block_notes(
    wallet: &PublicKey,
    strangers: &[PublicKey],
    mine: u64,
    tag: u64,
    rng: &mut ChaCha20Rng,
) -> Vec<Envelope> {
    (0..NOTES_PER_BLOCK)
        .map(|slot| {
            let value = tag + slot;
            match slot == mine {
                true => note(wallet, value, rng),
                false => {
                    let stranger = &strangers[(slot as usize) % strangers.len()];
                    note(stranger, value, rng)
                }
            }
        })
        .collect()
}

/// Publishes `blocks` blocks, one note per block addressed to the wallet.
fn extend(
    pool: &mut Pool,
    wallet: &PublicKey,
    strangers: &[PublicKey],
    blocks: u64,
    tag: u64,
    rng: &mut ChaCha20Rng,
) {
    for block in 0..blocks {
        let notes = block_notes(
            wallet,
            strangers,
            block % NOTES_PER_BLOCK,
            tag + block * 10,
            rng,
        );
        pool.push_block(notes);
    }
}

/// Ticks to the tip, reporting the recoveries the driver ran on the way.
fn sync(driver: &mut Driver<Balance, Pool>) {
    loop {
        match driver.tick() {
            Tick::Idle => return,
            Tick::Progressed(_) => {}
            Tick::RolledBack { to } => println!("  rolled back to {to:?}"),
            // the pool never fails a poll, and the reorg stays inside the checkpoint window
            other => panic!("the scripted pool cannot reach {other:?}"),
        }
    }
}

/// Balance a wallet that scanned the current canonical chain from genesis would hold.
///
/// Independent of the engine: a fresh scanner over every published envelope, in block order.
/// The fold has to agree whatever its reorg history was.
fn rescan(pool: &Pool, sk: &StaticSecret) -> Balance {
    let mut scanner = Scanner::<X25519, Payments>::new(Recipient::new(sk.clone()));
    let mut balance = Balance::default();
    for (_, note) in scanner.scan(pool.published(), POOL_AAD) {
        balance
            .credit(note.expect("every envelope in this pool is well formed"))
            .expect("the fixture's values do not overflow");
    }
    balance
}

fn main() {
    // fixed seed keeps the run reproducible
    let mut rng = ChaCha20Rng::seed_from_u64(7);

    let sk = StaticSecret::random_from_rng(&mut rng);
    let me = Recipient::<X25519>::new(sk.clone());
    let wallet = *me.public_key();
    let strangers: Vec<PublicKey> = (0..3)
        .map(|_| PublicKey::from(&StaticSecret::random_from_rng(&mut rng)))
        .collect();

    let mut pool = Pool::new(FIRST_BLOCK, me);
    extend(&mut pool, &wallet, &strangers, BLOCKS, 100, &mut rng);

    let mut driver = Driver::new(
        Balance::default(),
        pool,
        EngineConfig {
            ring_capacity: RING_CAPACITY,
            checkpoint_slots: CHECKPOINT_SLOTS,
        },
        DriverConfig {
            checkpoint_interval: Some(CHECKPOINT_INTERVAL),
            snapshot_interval: None,
            ..DriverConfig::from_block(FIRST_BLOCK)
        },
    )
    .expect("driver configuration is valid");

    sync(&mut driver);
    let synced = *driver.engine().fold();
    assert_eq!(synced, rescan(driver.source_mut(), &sk));
    println!(
        "caught up at {:?}: {} envelopes scanned, {} notes mine, balance {}",
        driver.engine().cursor(),
        driver.source_mut().scanned,
        synced.notes,
        synced.total,
    );

    // the last blocks are replaced by a branch paying this wallet different notes
    let replacements = (0..REORG_DEPTH)
        .map(|block| {
            block_notes(
                &wallet,
                &strangers,
                (block as u64) % NOTES_PER_BLOCK,
                9_000 + (block as u64) * 10,
                &mut rng,
            )
        })
        .collect();
    driver.source_mut().reorg(REORG_DEPTH, replacements);

    sync(&mut driver);
    let recovered = *driver.engine().fold();
    assert_eq!(recovered, rescan(driver.source_mut(), &sk));
    assert_ne!(recovered, synced);
    println!(
        "reorg absorbed: balance {} -> {}, {} envelopes scanned in total",
        synced.total,
        recovered.total,
        driver.source_mut().scanned,
    );
}
