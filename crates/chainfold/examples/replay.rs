//! End to end: fold a chain to the tip while a flusher persists trailing snapshots,
//! recover from a reorg, then restart from the durable cursor. Doubles as the manual
//! tick loop a non-tokio consumer writes.

use std::time::Duration;

use chainfold::{
    Driver,
    DriverConfig,
    Engine,
    EngineConfig,
    Position,
    Tick,
    harness,
    storage::{
        Flusher,
        RealVfs,
        SnapshotStore,
        StoreConfig,
    },
    test_util::{
        RecordingFold,
        ScriptedChain,
    },
};

/// Observed-block ring window.
const RING_CAPACITY: usize = 16;
/// Retained checkpoint slots.
const CHECKPOINT_SLOTS: usize = 4;
/// Blocks the scripted chain starts with.
const CHAIN_BLOCKS: u64 = 30;
/// Snapshot jobs the flusher admits before an offer blocks on the queue.
const QUEUE_DEPTH: usize = 4;

fn engine_config() -> EngineConfig {
    EngineConfig {
        ring_capacity: RING_CAPACITY,
        checkpoint_slots: CHECKPOINT_SLOTS,
    }
}

/// Builds a thirty-block chain with two events on every third block, delivered one
/// event-bearing block per poll so checkpoint_interval has room to take effect.
fn build_chain() -> ScriptedChain {
    let mut chain = ScriptedChain::new(1);
    for block in 1..=CHAIN_BLOCKS {
        if block % 3 == 0 {
            chain.push_block(&[block * 10, block * 10 + 1]);
        } else {
            chain.push_block(&[]);
        }
    }
    chain.set_window(1);
    chain
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let home = tempfile::tempdir().expect("temp directory is available");
    let store_config = StoreConfig {
        dir: home.path().to_path_buf(),
        retain: 1,
    };
    let (store, recovered) =
        SnapshotStore::open(store_config.clone(), RealVfs).expect("store opens cleanly");
    assert!(recovered.is_none(), "a fresh store recovers nothing");
    println!("opened a fresh store at {}", home.path().display());

    let chain = build_chain();
    let config = DriverConfig {
        checkpoint_interval: Some(5),
        snapshot_interval: Some(5),
        poll_interval: Duration::from_millis(10),
        ..DriverConfig::default()
    };
    let driver = Driver::with_sink(
        RecordingFold::default(),
        chain,
        Flusher::spawn(store, QUEUE_DEPTH),
        engine_config(),
        config,
    )
    .expect("driver configuration is valid");

    let mut handle = harness::spawn(driver);
    let status = handle.wait_caught_up().await;
    println!(
        "caught up: cursor {:?}, skips {}",
        status.cursor, status.skips
    );
    let durable = handle.wait_durable(Position::new(3, 0)).await;
    println!("durable cursor: {:?}", durable.durable_cursor);

    let mut driver = handle.shutdown().await;
    println!(
        "view length before reorg: {}",
        driver.engine().fold().applied.len()
    );

    // replace the last four blocks with five, so the post-reorg chain is taller
    let replacements: [&[u64]; 5] = [&[900, 901], &[], &[], &[910, 911], &[]];
    driver.source_mut().reorg(4, &replacements);

    // sans-runtime recovery loop: the same shape a consumer without tokio writes
    loop {
        match driver.tick() {
            Tick::RolledBack { to } => println!("recovery: rolled back to {to:?}"),
            Tick::Progressed(summary) => println!("recovery: progressed {summary:?}"),
            Tick::Idle => break,
            Tick::Resynced => println!("recovery: resynced from genesis"),
            Tick::SourceError => println!("recovery: source error, retrying"),
            Tick::DurabilityLost => println!("recovery: durability lost, folding on"),
            Tick::Terminal(status) => {
                println!("recovery: terminal at {status:?}");
                break;
            }
        }
    }

    let live_view = driver.engine().fold().applied.clone();
    println!("view length after recovery: {}", live_view.len());
    let post_reorg_chain = driver.source_mut().clone();
    let store = driver
        .into_sink()
        .join()
        .expect("the flusher drains its queue cleanly");
    println!("store durable cursor: {:?}", store.durable_cursor());

    let (_, recovered) = SnapshotStore::open(store_config, store.into_vfs())
        .expect("store reopens cleanly");
    let recovered = recovered.expect("the offered snapshot is durable");
    let engine =
        Engine::<RecordingFold>::decode_snapshot(&recovered.snapshot, engine_config())
            .expect("snapshot decodes cleanly");
    let mut resumed = Driver::resume(
        engine,
        post_reorg_chain,
        RecordingFold::default(),
        DriverConfig::default(),
    )
    .expect("resume configuration is valid");
    while !matches!(resumed.tick(), Tick::Idle) {}
    assert_eq!(resumed.engine().fold().applied, live_view);
    println!(
        "restart from the durable cursor converged, {} entries",
        live_view.len()
    );
}
