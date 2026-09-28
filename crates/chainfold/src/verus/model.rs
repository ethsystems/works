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

/// `Batch` lanes and boundary. `Batch` has private fields, so Verus treats it as opaque
/// outside `batch.rs`, and even its public `boundary` is read through the view.
pub struct BatchView<E> {
    pub boundary: Option<BlockRef>,
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
/// it is unique (T4a `truncate_above`/`len_at_or_below`, T5c `ring|<=t.block`).
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

/// Entries of log `l` at or below cursor `c`: the prefix a checkpoint at `c` folded (T5d).
/// Drops from the end while the last entry is after `c`.
pub open spec fn upto<E>(l: Seq<(Position, E)>, c: Option<Position>) -> Seq<(Position, E)>
    decreases l.len(),
{
    if l.len() == 0 || opt_le(Some(l.last().0), c) {
        l
    } else {
        upto::<E>(l.drop_last(), c)
    }
}

/// `upto` is a prefix, and on a sorted log it splits at `c`.
pub proof fn lemma_upto<E>(l: Seq<(Position, E)>, c: Option<Position>)
    ensures
        upto::<E>(l, c).len() <= l.len(),
        upto::<E>(l, c) == l.subrange(0, upto::<E>(l, c).len() as int),
        lt_sorted(l) ==> forall|i: int|
            0 <= i < upto::<E>(l, c).len() ==> opt_le(Some(#[trigger] l[i].0), c),
        forall|i: int| upto::<E>(l, c).len() <= i < l.len() ==> opt_lt(c, Some(#[trigger] l[i].0)),
    decreases l.len(),
{
    if l.len() == 0 {
        assert(l.subrange(0, 0) =~= l);
    } else if opt_le(Some(l.last().0), c) {
        assert(l.subrange(0, l.len() as int) =~= l);
        if lt_sorted(l) {
            assert forall|i: int| 0 <= i < l.len() implies opt_le(Some(#[trigger] l[i].0), c) by {
                if i < l.len() - 1 {
                    assert(lt(l[i].0, l[l.len() - 1].0));
                    lemma_opt_lt_order(Some(l[i].0), Some(l.last().0), c);
                }
            }
        }
    } else {
        let d = l.drop_last();
        lemma_upto::<E>(d, c);
        let u = upto::<E>(d, c);
        assert(u == d.subrange(0, u.len() as int));
        assert(l.subrange(0, u.len() as int) =~= d.subrange(0, u.len() as int));
        if lt_sorted(l) {
            assert(lt_sorted(d)) by {
                assert forall|i: int, j: int| 0 <= i < j < d.len() implies lt(
                    #[trigger] d[i].0,
                    #[trigger] d[j].0,
                ) by {
                    assert(d[i] == l[i] && d[j] == l[j]);
                }
            }
            assert forall|i: int| 0 <= i < u.len() implies opt_le(Some(#[trigger] l[i].0), c) by {
                assert(d[i] == l[i]);
            }
        }
        assert forall|i: int| u.len() <= i < l.len() implies opt_lt(c, Some(#[trigger] l[i].0)) by {
            if i < d.len() {
                assert(d[i] == l[i]);
            }
            lemma_opt_lt_order(c, Some(l[i].0), None);
        }
    }
}

/// Truncating at `t` then at `c <= t` is truncating at `c` (rollback keeps older slots).
pub proof fn lemma_upto_upto<E>(l: Seq<(Position, E)>, c: Option<Position>, t: Option<Position>)
    requires
        opt_le(c, t),
    ensures
        upto::<E>(upto::<E>(l, t), c) == upto::<E>(l, c),
    decreases l.len(),
{
    if l.len() > 0 && !opt_le(Some(l.last().0), t) {
        lemma_opt_lt_order(c, t, Some(l.last().0));
        lemma_opt_lt_order(Some(l.last().0), t, c);
        lemma_upto_upto::<E>(l.drop_last(), c, t);
    }
}

/// Appending entries after `c` leaves `upto(_, c)` alone (P5: apply keeps slot folds).
pub proof fn lemma_upto_append<E>(l: Seq<(Position, E)>, m: Seq<(Position, E)>, c: Option<Position>)
    requires
        forall|i: int| 0 <= i < m.len() ==> opt_lt(c, Some(#[trigger] m[i].0)),
    ensures
        upto::<E>(l + m, c) == upto::<E>(l, c),
    decreases m.len(),
{
    if m.len() == 0 {
        assert(l + m =~= l);
    } else {
        let x = m.last();
        assert(opt_lt(c, Some(m[m.len() - 1].0)));
        lemma_opt_lt_order(c, Some(x.0), None);
        assert((l + m).drop_last() =~= l + m.drop_last());
        assert forall|i: int| 0 <= i < m.drop_last().len() implies opt_lt(
            c,
            Some(#[trigger] m.drop_last()[i].0),
        ) by {
            assert(m.drop_last()[i] == m[i]);
        }
        lemma_upto_append::<E>(l, m.drop_last(), c);
    }
}

/// Slot `s` can serve a rollback to block `a` (T5b).
pub open spec fn qualifies(s: SlotView, a: u64) -> bool {
    match s.cursor {
        Some(c) => c.block <= a,
        None => true,
    }
}

/// Live stored slots, counted over the first `n` logical indices.
pub open spec fn live_count(slots: Seq<Option<SlotView>>, ring: Seq<BlockRef>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        live_count(slots, ring, n - 1) + if slots[n - 1] is Some && live(slots[n - 1].unwrap(), ring) {
            1int
        } else {
            0int
        }
    }
}

/// The engine a snapshot of `(fold, cursor, ring)` decodes to with `slots` empty slots:
/// `Engine::decode_snapshot`'s `restored` shape (T6c).
pub open spec fn snapshot_view(fold: int, cursor: Option<Position>, ring: Seq<BlockRef>, slots: nat) -> EngineView {
    EngineView {
        fold,
        cursor,
        ring,
        slots: Seq::new(slots, |_i: int| None::<SlotView>),
        status: EngineStatus::Active,
        last_verified: None,
        skips: 0,
        resets: 0,
    }
}

impl EngineView {
    /// Plan T5d `Inv`, over ghost `init` (the fold view at the last rewind) and `log` (the
    /// entries `F::apply` ran on since, in call order). While Active the log is at or
    /// below the cursor and has not stopped; each stored slot folded `upto(log, cursor)`.
    pub open spec fn inv<F: ?Sized, E, Er>(self, init: int, log: Seq<(Position, E)>) -> bool {
        &&& lt_sorted(log)
        &&& run::<F, E, Er>((init, false), log).0 == self.fold
        &&& self.status is Active ==> {
            &&& !run::<F, E, Er>((init, false), log).1
            &&& forall|i: int| 0 <= i < log.len() ==> opt_le(Some(#[trigger] log[i].0), self.cursor)
        }
        &&& forall|k: int|
            0 <= k < self.slots.len() && #[trigger] self.slots[k] is Some ==> run::<F, E, Er>(
                (init, false),
                upto::<E>(log, self.slots[k].unwrap().cursor),
            ) == (self.slots[k].unwrap().fold, false)
    }

    /// T5b: slot `k` is the one `rollback_at_or_below(a)` restores: live and qualifying,
    /// and the newest stored such slot.
    pub open spec fn rollback_target(self, a: u64, k: int) -> bool {
        &&& self.live_at(k)
        &&& qualifies(self.slots[k].unwrap(), a)
        &&& forall|j: int|
            k < j < self.slots.len() ==> !(#[trigger] self.live_at(j) && qualifies(
                self.slots[j].unwrap(),
                a,
            ))
    }
}

impl EngineView {
    /// `anchors` after a checkpoint stores the current cursor: the new newest slot is
    /// anchored at the ring tip (the cursor block), the oldest entry drops.
    pub open spec fn stored_anchors(self, anchors: Seq<Option<BlockRef>>) -> Seq<Option<BlockRef>> {
        if self.status is Active && self.slots.len() > 0 {
            anchors.drop_first().push(
                match self.cursor {
                    Some(_) => Some(self.ring.last()),
                    None => None,
                },
            )
        } else {
            anchors
        }
    }

    /// `oldest_live_from(from)` finds the first live slot at or after `from`.
    pub proof fn lemma_oldest_live(self, from: int, k: int)
        requires
            0 <= from <= k,
            self.live_at(k),
            forall|j: int| from <= j < k ==> !#[trigger] self.live_at(j),
        ensures
            self.oldest_live_from(from) == Some(k),
        decreases k - from,
    {
        if from < k {
            self.lemma_oldest_live(from + 1, k);
        }
    }

    /// With no live slot at or after `from`, `oldest_live_from(from)` is None.
    pub proof fn lemma_no_live(self, from: int)
        requires
            0 <= from,
            forall|j: int| from <= j < self.slots.len() ==> !#[trigger] self.live_at(j),
        ensures
            self.oldest_live_from(from) is None,
        decreases self.slots.len() - from,
    {
        if from < self.slots.len() {
            self.lemma_no_live(from + 1);
        }
    }
}

impl EngineView {
    /// The oldest live slot, the one `durable_point` reads.
    pub open spec fn durable_slot(self) -> SlotView {
        self.slots[self.oldest_live_from(0).unwrap()].unwrap()
    }

    /// T6c: what `encode_durable_snapshot` writes, as the engine it decodes to: the
    /// oldest live slot's fold and cursor, and the ring prefix of length `k` at or below
    /// the cursor block (`len_at_or_below`'s ensures give `k`).
    pub open spec fn durable_snapshot(self, k: int, slots: nat) -> EngineView {
        snapshot_view(self.durable_slot().fold, self.durable_slot().cursor, self.ring.subrange(0, k), slots)
    }
}

/// `oldest_live_from(j)` is the least live index at or after `j`.
pub proof fn lemma_oldest_live_from(v: EngineView, j: int)
    requires
        0 <= j,
    ensures
        match v.oldest_live_from(j) {
            Some(k) => j <= k < v.slots.len() && v.live_at(k) && forall|i: int|
                j <= i < k ==> !#[trigger] v.live_at(i),
            None => forall|i: int| j <= i ==> !#[trigger] v.live_at(i),
        },
    decreases v.slots.len() - j,
{
    if j < v.slots.len() && !v.live_at(j) {
        lemma_oldest_live_from(v, j + 1);
    }
}

/// T6a: the durable point never passes the cursor.
pub proof fn lemma_durable_point_le_cursor(v: EngineView)
    requires
        v.wf(),
    ensures
        opt_le(v.durable_point(), v.cursor),
{
    lemma_oldest_live_from(v, 0);
    if let Some(k) = v.oldest_live_from(0) {
        assert(v.slots[k] is Some);
    }
}

/// T6c, encode side: the durable snapshot of a `wf` engine is `wf`, its cursor is the
/// durable point, and its ring is a prefix of the engine's (so it fits the window).
pub proof fn lemma_durable_snapshot(v: EngineView, k: int, slots: nat)
    requires
        v.wf(),
        v.durable_point() is Some,
        prefix_at_or_below(v.ring, v.durable_point().unwrap().block, k),
    ensures
        v.durable_snapshot(k, slots).cursor == v.durable_point(),
        v.durable_snapshot(k, slots).wf(),
        v.durable_snapshot(k, slots).ring.len() <= v.ring.len(),
{
    lemma_oldest_live_from(v, 0);
    let s = v.durable_slot();
    let d = s.cursor.unwrap();
    let snap = v.durable_snapshot(k, slots);
    // Live with a cursor: the cursor block is in the ring, so the prefix ends on it.
    assert(observes(v.ring, d.block));
    let w = choose|i: int| 0 <= i < v.ring.len() && #[trigger] v.ring[i].number == d.block;
    assert(w < k) by {
        if w >= k {
            assert(v.ring[w].number > d.block);
        }
    }
    assert(k - 1 <= w) by {
        if k - 1 > w {
            assert(v.ring[w].number < v.ring[k - 1].number);
        }
    }
    assert(snap.ring.last() == v.ring[k - 1]);
    assert(ring_ascending(snap.ring));
}

/// T6c, encode side, `Inv`: the durable snapshot satisfies `Inv` from the same `init`
/// over `upto(log, d)`, the log prefix its slot folded (clause 4 at the oldest live slot).
pub proof fn lemma_durable_snapshot_inv<F: ?Sized, E, Er>(
    v: EngineView,
    k: int,
    slots: nat,
    init: int,
    log: Seq<(Position, E)>,
)
    requires
        v.inv::<F, E, Er>(init, log),
        v.oldest_live_from(0) is Some,
    ensures
        v.durable_snapshot(k, slots).cursor == v.durable_point(),
        v.durable_snapshot(k, slots).inv::<F, E, Er>(init, upto::<E>(log, v.durable_point())),
{
    lemma_oldest_live_from(v, 0);
    let j = v.oldest_live_from(0).unwrap();
    assert(v.slots[j] is Some);
    let c = v.durable_point();
    let u = upto::<E>(log, c);
    lemma_upto::<E>(log, c);
    assert forall|a: int, b: int| 0 <= a < b < u.len() implies lt(#[trigger] u[a].0, #[trigger] u[b].0) by {
        assert(u[a] == log[a] && u[b] == log[b]);
    }
    assert forall|i: int| 0 <= i < u.len() implies opt_le(Some(#[trigger] u[i].0), c) by {
        assert(u[i] == log[i]);
    }
}

} // verus!
