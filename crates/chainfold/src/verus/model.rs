//! Spec model of the chain, the fold and the engine (plan section 3). Reference with
//! signatures and the theorem that uses each item: cookbook section 15.

use vstd::prelude::*;

use crate::{
    error::{
        EngineStatus,
        FoldError,
    },
    position::{
        BlockRef,
        Position,
    },
};

verus! {

/// Canonical header per height at one instant (plan `View`, renamed so it does not
/// shadow vstd's `View` trait).
pub type ChainView = Map<u64, BlockRef>;

/// Ancestor at height `m` that block hash `h` commits to (A1).
pub uninterp spec fn anc(h: [u8; 32], m: u64) -> BlockRef;

/// Logs block hash `h` commits to, as source type `S` decodes them into `E` (A1).
pub uninterp spec fn logs<S: ?Sized, E>(h: [u8; 32]) -> Seq<(u32, E)>;

/// Every block of `v` sits at its own height and commits to the others below it.
pub open spec fn chain(v: ChainView) -> bool {
    &&& forall|n: u64| #[trigger] v.contains_key(n) ==> v[n].number == n
    &&& forall|n: u64, m: u64|
        #![trigger v[n], v[m]]
        v.contains_key(n) && v.contains_key(m) && m <= n ==> v[m] == anc(v[n].hash, m)
}

pub open spec fn logs_ascending<E>(l: Seq<(u32, E)>) -> bool {
    forall|i: int, j: int| #![trigger l[i], l[j]] 0 <= i < j < l.len() ==> l[i].0 < l[j].0
}

/// A1 for one view a source of type `S` presents: `chain` plus strictly ascending logs.
pub open spec fn a1<S: ?Sized, E>(v: ChainView) -> bool {
    &&& chain(v)
    &&& forall|n: u64| v.contains_key(n) ==> logs_ascending(#[trigger] logs::<S, E>(v[n].hash))
}

/// `Source::header_at` answer in view `v`.
pub open spec fn header(v: ChainView, n: u64) -> Option<BlockRef> {
    if v.contains_key(n) {
        Some(v[n])
    } else {
        None
    }
}

/// Entries of one height in the `Source::events_in` shape, log order.
pub open spec fn block_entries<S: ?Sized, E>(v: ChainView, n: u64) -> Seq<(BlockRef, u32, E)> {
    if v.contains_key(n) {
        let b = v[n];
        logs::<S, E>(b.hash).map_values(|x: (u32, E)| (b, x.0, x.1))
    } else {
        seq![]
    }
}

/// Entries of heights `lo..=hi` of `v`, ascending by height.
pub open spec fn range_entries<S: ?Sized, E>(v: ChainView, lo: int, hi: int) -> Seq<
    (BlockRef, u32, E),
>
    decreases hi - lo + 1,
{
    if hi < lo || hi < 0 || hi > u64::MAX {
        seq![]
    } else {
        range_entries::<S, E>(v, lo, hi - 1) + block_entries::<S, E>(v, hi as u64)
    }
}

/// Position just below block `n`; None (below every position) for block 0.
pub open spec fn before(n: u64) -> Option<Position> {
    if n == 0 {
        None
    } else {
        Some(Position { block: (n - 1) as u64, log_index: u64::MAX })
    }
}

/// Logs of `v`'s blocks with `a < pos <= c`, ascending (T6c, T7).
pub open spec fn canon<S: ?Sized, E>(v: ChainView, a: Option<Position>, c: Option<Position>) -> Seq<
    (Position, E),
> {
    match c {
        None => seq![],
        Some(c) => {
            let lo = match a {
                None => 0int,
                Some(a) => a.block as int,
            };
            range_entries::<S, E>(v, lo, c.block as int).map_values(
                |x: (BlockRef, u32, E)| (Position { block: x.0.number, log_index: x.1 as u64 }, x.2),
            ).filter(|x: (Position, E)| opt_lt(a, Some(x.0)) && le(x.0, c))
        },
    }
}

/// `ring[i]` is the ancestor that every later entry commits to (T4c, T7).
pub open spec fn ring_chain(r: Seq<BlockRef>) -> bool {
    forall|i: int, j: int|
        #![trigger r[i], r[j]]
        0 <= i < j < r.len() ==> r[i] == anc(r[j].hash, r[i].number)
}

/// Every ring entry is `v`'s block at its height (T7).
pub open spec fn ring_in(r: Seq<BlockRef>, v: ChainView) -> bool {
    forall|i: int|
        0 <= i < r.len() ==> v.contains_key(#[trigger] r[i].number) && v[r[i].number] == r[i]
}

pub open spec fn ring_ascending(r: Seq<BlockRef>) -> bool {
    forall|i: int, j: int| #![trigger r[i], r[j]] 0 <= i < j < r.len() ==> r[i].number < r[j].number
}

/// The ring holds an entry numbered `n`.
pub open spec fn observes(r: Seq<BlockRef>, n: u64) -> bool {
    exists|i: int| 0 <= i < r.len() && #[trigger] r[i].number == n
}

/// Position order: block, then log index (T1).
pub open spec fn lt(a: Position, b: Position) -> bool {
    a.block < b.block || (a.block == b.block && a.log_index < b.log_index)
}

pub open spec fn le(a: Position, b: Position) -> bool {
    lt(a, b) || a == b
}

/// `lt` lifted to cursors, with None below every position.
pub open spec fn opt_lt(a: Option<Position>, b: Option<Position>) -> bool {
    match (a, b) {
        (None, Some(_)) => true,
        (Some(a), Some(b)) => lt(a, b),
        _ => false,
    }
}

pub open spec fn opt_le(a: Option<Position>, b: Option<Position>) -> bool {
    opt_lt(a, b) || a == b
}

/// Three-way `lt`; the derived `Ord` is trusted to equal it (tcb.rs).
pub open spec fn pos_cmp(a: Position, b: Position) -> core::cmp::Ordering {
    if lt(a, b) {
        core::cmp::Ordering::Less
    } else if a == b {
        core::cmp::Ordering::Equal
    } else {
        core::cmp::Ordering::Greater
    }
}

/// T1: `lt` is irreflexive.
pub proof fn lemma_lt_irreflexive(a: Position)
    ensures
        !lt(a, a),
{
}

/// T1: `lt` is transitive.
pub proof fn lemma_lt_transitive(a: Position, b: Position, c: Position)
    requires
        lt(a, b),
        lt(b, c),
    ensures
        lt(a, c),
{
}

/// T1: exactly one of `lt(a, b)`, `a == b`, `lt(b, a)`.
pub proof fn lemma_lt_trichotomous(a: Position, b: Position)
    ensures
        lt(a, b) || a == b || lt(b, a),
        !(lt(a, b) && lt(b, a)),
        a == b ==> !lt(a, b),
{
}

/// T1 lifted: `opt_lt` is a strict total order too.
pub proof fn lemma_opt_lt_order(a: Option<Position>, b: Option<Position>, c: Option<Position>)
    ensures
        !opt_lt(a, a),
        opt_lt(a, b) && opt_lt(b, c) ==> opt_lt(a, c),
        opt_lt(a, b) || a == b || opt_lt(b, a),
        !(opt_lt(a, b) && opt_lt(b, a)),
{
}

/// Positions strictly `lt`-ascending (T2, T3c).
pub open spec fn lt_sorted<E>(s: Seq<(Position, E)>) -> bool {
    forall|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() ==> lt(s[i].0, s[j].0)
}

/// Entries strictly after cursor `c` (T3b dedup).
pub open spec fn newer<E>(c: Option<Position>, s: Seq<(Position, E)>) -> Seq<(Position, E)> {
    s.filter(|x: (Position, E)| opt_lt(c, Some(x.0)))
}

/// Abstract state view of a fold (A3). `int` stands in for the fold's state space, which
/// is countable; Clone, Halt, and `fold_mut` edits preserve it.
pub uninterp spec fn fview<F: ?Sized>(f: &F) -> int;

/// Transition of fold type `F` (A3); `Fold::apply` refines it.
pub uninterp spec fn step<F: ?Sized, E, Er>(v: int, pos: Position, e: E) -> (
    int,
    Result<(), FoldError<Er>>,
);

/// One step of `run`: a stopped state absorbs, Ok/Skip continue, Halt keeps the
/// pre-state and stops, Poison keeps the post-state and stops.
pub open spec fn fold_step<F: ?Sized, E, Er>(s: (int, bool), x: (Position, E)) -> (int, bool) {
    if s.1 {
        s
    } else {
        let (w, r) = step::<F, E, Er>(s.0, x.0, x.1);
        match r {
            Ok(()) => (w, false),
            Err(FoldError::Skip(_)) => (w, false),
            Err(FoldError::Halt(_)) => (s.0, true),
            Err(FoldError::Poison(_)) => (w, true),
        }
    }
}

/// Left fold of `step` over `log` from state `s`: (view, stopped).
pub open spec fn run<F: ?Sized, E, Er>(s: (int, bool), log: Seq<(Position, E)>) -> (int, bool)
    decreases log.len(),
{
    if log.len() == 0 {
        s
    } else {
        fold_step::<F, E, Er>(run::<F, E, Er>(s, log.drop_last()), log.last())
    }
}

/// Plan `fold(f, log)`: the view after folding `log` into `v` (T3f, T5d, T6c, T7).
pub open spec fn fold<F: ?Sized, E, Er>(v: int, log: Seq<(Position, E)>) -> int {
    run::<F, E, Er>((v, false), log).0
}

pub proof fn lemma_run_push<F: ?Sized, E, Er>(
    s: (int, bool),
    log: Seq<(Position, E)>,
    x: (Position, E),
)
    ensures
        run::<F, E, Er>(s, log.push(x)) == fold_step::<F, E, Er>(run::<F, E, Er>(s, log), x),
{
    assert(log.push(x).drop_last() =~= log);
}

pub proof fn lemma_run_concat<F: ?Sized, E, Er>(
    s: (int, bool),
    a: Seq<(Position, E)>,
    b: Seq<(Position, E)>,
)
    ensures
        run::<F, E, Er>(s, a + b) == run::<F, E, Er>(run::<F, E, Er>(s, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_run_concat::<F, E, Er>(s, a, b.drop_last());
    }
}

/// The view source `S` presents at one instant (A1, A2).
pub uninterp spec fn sview<S: ?Sized>(s: &S) -> ChainView;

/// Points of the offers sink `K` has taken since its last `reset` (A4).
pub uninterp spec fn sink_offered<K: ?Sized>(k: &K) -> Set<Position>;

pub struct SlotView {
    pub fold: int,
    pub cursor: Option<Position>,
}

/// A slot is live iff its cursor is None or its block is still in the ring.
pub open spec fn live(s: SlotView, ring: Seq<BlockRef>) -> bool {
    match s.cursor {
        None => true,
        Some(c) => observes(ring, c.block),
    }
}

/// Plan `EngineView`; `slots` has one entry per slot (K), oldest stored first, None
/// where nothing is stored.
pub struct EngineView {
    pub fold: int,
    pub cursor: Option<Position>,
    pub ring: Seq<BlockRef>,
    pub slots: Seq<Option<SlotView>>,
    pub status: EngineStatus,
    pub last_verified: Option<BlockRef>,
    pub skips: u64,
    pub resets: u64,
}

impl EngineView {
    /// The view-level clauses of plan `wf(Engine)`; `Engine::wf` adds the ring and
    /// slot representation.
    pub open spec fn wf(self) -> bool {
        &&& ring_ascending(self.ring)
        &&& match self.cursor {
            Some(c) => self.ring.len() > 0 && self.ring.last().number == c.block,
            None => self.ring.len() == 0,
        }
        &&& forall|i: int, j: int|
            #![trigger self.slots[i], self.slots[j]]
            0 <= i < j < self.slots.len() && self.slots[i] is Some && self.slots[j] is Some
                ==> opt_le(self.slots[i].unwrap().cursor, self.slots[j].unwrap().cursor)
        &&& forall|i: int|
            0 <= i < self.slots.len() && #[trigger] self.slots[i] is Some ==> opt_le(
                self.slots[i].unwrap().cursor,
                self.cursor,
            )
    }

    pub open spec fn live_at(self, k: int) -> bool {
        &&& 0 <= k < self.slots.len()
        &&& self.slots[k] is Some
        &&& live(self.slots[k].unwrap(), self.ring)
    }

    /// Index of the oldest live slot at or after `k`.
    pub open spec fn oldest_live_from(self, k: int) -> Option<int>
        decreases self.slots.len() - k,
    {
        if k < 0 || k >= self.slots.len() {
            None
        } else if self.live_at(k) {
            Some(k)
        } else {
            self.oldest_live_from(k + 1)
        }
    }

    /// `Engine::durable_point` (T6a).
    pub open spec fn durable_point(self) -> Option<Position> {
        match self.oldest_live_from(0) {
            Some(k) => self.slots[k].unwrap().cursor,
            None => None,
        }
    }

    /// Plan wf clause "a live slot's ring entry is unchanged since the slot was stored",
    /// over ghost `anchors`: the ring entry of each slot's cursor block when it was stored.
    pub open spec fn anchored(self, anchors: Seq<Option<BlockRef>>) -> bool {
        &&& anchors.len() == self.slots.len()
        &&& forall|k: int|
            #![trigger self.slots[k]]
            self.live_at(k) && self.slots[k].unwrap().cursor is Some ==> {
                &&& anchors[k] is Some
                &&& anchors[k].unwrap().number == self.slots[k].unwrap().cursor.unwrap().block
                &&& self.ring.contains(anchors[k].unwrap())
            }
    }
}

/// `Batch` lanes; `Batch::boundary` is a public field and is read directly.
pub struct BatchView<E> {
    pub blocks: Seq<u64>,
    pub hashes: Seq<[u8; 32]>,
    pub ends: Seq<usize>,
    pub log_indices: Seq<u32>,
    pub events: Seq<E>,
}

impl<E> BatchView<E> {
    /// Layout every `Batch` method keeps: parallel lanes, monotone span ends.
    pub open spec fn wf(self) -> bool {
        &&& self.hashes.len() == self.blocks.len()
        &&& self.ends.len() == self.blocks.len()
        &&& self.log_indices.len() == self.events.len()
        &&& forall|i: int, j: int|
            #![trigger self.ends[i], self.ends[j]]
            0 <= i < j < self.ends.len() ==> self.ends[i] <= self.ends[j]
        &&& if self.ends.len() == 0 {
            self.events.len() == 0
        } else {
            self.ends.last() == self.events.len()
        }
    }

    /// First event index of span `i`.
    pub open spec fn start(self, i: int) -> int {
        if i <= 0 {
            0
        } else {
            self.ends[i - 1] as int
        }
    }

    pub open spec fn block(self, i: int) -> BlockRef {
        BlockRef { number: self.blocks[i], hash: self.hashes[i] }
    }

    /// T2: what `validate` accepts.
    pub open spec fn shaped(self) -> bool {
        &&& forall|i: int, j: int|
            #![trigger self.blocks[i], self.blocks[j]]
            0 <= i < j < self.blocks.len() ==> self.blocks[i] < self.blocks[j]
        &&& forall|i: int| 0 <= i < self.ends.len() ==> self.start(i) < #[trigger] self.ends[i]
        &&& forall|i: int, j: int, k: int|
            #![trigger self.ends[i], self.log_indices[j], self.log_indices[k]]
            0 <= i < self.ends.len() && self.start(i) <= j < k < self.ends[i]
                ==> self.log_indices[j] < self.log_indices[k]
    }

    /// Events of span `i` with their positions.
    pub open spec fn span_events(self, i: int) -> Seq<(Position, E)> {
        let start = self.start(i);
        if self.ends[i] < start {
            seq![]
        } else {
            Seq::new(
                (self.ends[i] - start) as nat,
                |k: int|
                    (
                        Position {
                            block: self.blocks[i],
                            log_index: self.log_indices[start + k] as u64,
                        },
                        self.events[start + k],
                    ),
            )
        }
    }

    /// Events of spans `0..n`, flattened.
    pub open spec fn flat_upto(self, n: int) -> Seq<(Position, E)>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            self.flat_upto(n - 1) + self.span_events(n - 1)
        }
    }

    /// Plan `positions(b)`, with the events: every event of the batch in lane order.
    pub open spec fn flat(self) -> Seq<(Position, E)> {
        self.flat_upto(self.ends.len() as int)
    }
}

/// `BlockRing::push` (T4a): append `b`, evicting the oldest entry when `r` holds `w`.
pub open spec fn ring_push(r: Seq<BlockRef>, w: int, b: BlockRef) -> Seq<BlockRef> {
    if r.len() < w {
        r.push(b)
    } else {
        r.drop_first().push(b)
    }
}

/// `k` is the length of `r`'s prefix numbered at or below `n`; with `ring_ascending(r)`
/// it is unique (T4a `truncate_above`/`iter_at_or_below`, T5c `ring|<=t.block`).
pub open spec fn prefix_at_or_below(r: Seq<BlockRef>, n: u64, k: int) -> bool {
    &&& 0 <= k <= r.len()
    &&& forall|i: int| 0 <= i < k ==> #[trigger] r[i].number <= n
    &&& forall|i: int| k <= i < r.len() ==> #[trigger] r[i].number > n
}

/// View `v` holds block `b` at its height (T4c: a probe confirms a ring entry).
pub open spec fn confirms(v: ChainView, b: BlockRef) -> bool {
    header(v, b.number) == Some(b)
}

/// `v` holds every height below each height it holds, as a chain from genesis does
/// (T4c hypothesis; `chain` alone does not force it).
pub open spec fn down_closed(v: ChainView) -> bool {
    forall|n: u64, m: u64| #[trigger] v.contains_key(n) && m <= n ==> #[trigger] v.contains_key(m)
}

/// `k` is the longest prefix of `r` that `v` confirms entry by entry (T4c optimality).
pub open spec fn confirmed_prefix(r: Seq<BlockRef>, v: ChainView, k: int) -> bool {
    &&& 0 <= k <= r.len()
    &&& forall|i: int| 0 <= i < k ==> confirms(v, #[trigger] r[i])
    &&& k < r.len() ==> !confirms(v, r[k])
}

/// The views that answered each call on source `S` so far, oldest first; every `Source`
/// call appends `sview` of its post-state (A2 bookkeeping, T4c).
pub uninterp spec fn sview_log<S: ?Sized>(s: &S) -> Seq<ChainView>;

} // verus!
