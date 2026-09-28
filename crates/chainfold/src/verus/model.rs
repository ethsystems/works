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

impl<E> BatchView<E> {
    /// Span `i` as source entries `(block, log_index, event)`, in lane order (P8).
    pub open spec fn span_triples(self, i: int) -> Seq<(BlockRef, u32, E)> {
        let start = self.start(i);
        if self.ends[i] < start {
            seq![]
        } else {
            Seq::new(
                (self.ends[i] - start) as nat,
                |k: int| (self.block(i), self.log_indices[start + k], self.events[start + k]),
            )
        }
    }

    /// Entries of spans `0..n`, flattened.
    pub open spec fn triples_upto(self, n: int) -> Seq<(BlockRef, u32, E)>
        decreases n,
    {
        if n <= 0 {
            seq![]
        } else {
            self.triples_upto(n - 1) + self.span_triples(n - 1)
        }
    }

    /// Every entry of the batch in lane order, as the source delivered it.
    pub open spec fn triples(self) -> Seq<(BlockRef, u32, E)> {
        self.triples_upto(self.ends.len() as int)
    }
}


// P5: engine apply (T3).

/// Prefix of `s` through its first stopping step: the entries `F::apply` runs on (T3b).
pub open spec fn applied<F: ?Sized, E, Er>(v: int, s: Seq<(Position, E)>) -> Seq<(Position, E)>
    decreases s.len(),
{
    if s.len() == 0 || !run::<F, E, Er>((v, false), s.drop_last()).1 {
        s
    } else {
        applied::<F, E, Er>(v, s.drop_last())
    }
}

/// Header of every span of `b`, oldest first.
pub open spec fn span_refs<E>(b: BatchView<E>) -> Seq<BlockRef> {
    Seq::new(b.blocks.len(), |i: int| b.block(i))
}

/// `r` after pushing each of `bs` in order into a ring of capacity `w`.
pub open spec fn ring_ext(r: Seq<BlockRef>, w: int, bs: Seq<BlockRef>) -> Seq<BlockRef>
    decreases bs.len(),
{
    if bs.len() == 0 {
        r
    } else {
        ring_push(ring_ext(r, w, bs.drop_last()), w, bs.last())
    }
}

/// `k` spans of `b` are at or below the block of cursor `c` (none for a None cursor).
pub open spec fn split_at_tip<E>(b: BatchView<E>, c: Option<Position>, k: int) -> bool {
    match c {
        None => k == 0,
        Some(p) => prefix_at_or_below(span_refs(b), p.block, k),
    }
}

/// A span at or below the cursor block carries a hash the ring disagrees with.
pub open spec fn forked<E>(v: EngineView, b: BatchView<E>) -> bool {
    &&& v.cursor is Some
    &&& exists|i: int, j: int|
        #![trigger b.blocks[i], v.ring[j]]
        0 <= i < b.blocks.len() && 0 <= j < v.ring.len() && b.blocks[i] <= v.cursor.unwrap().block
            && v.ring[j].number == b.blocks[i] && v.ring[j].hash != b.hashes[i]
}

/// `apply_batch` runs the fold on `b` (every check before the first `F::apply` passes).
pub open spec fn accepted<E>(v: EngineView, b: BatchView<E>) -> bool {
    &&& v.status is Active
    &&& b.shaped()
    &&& v.cursor is Some ==> b.boundary == Some(v.ring.last())
    &&& !forked(v, b)
}

/// T3b: the entries `apply_batch` runs `F::apply` on, in call order.
pub open spec fn calls<F: ?Sized, E, Er>(v: EngineView, b: BatchView<E>) -> Seq<(Position, E)> {
    if accepted(v, b) {
        applied::<F, E, Er>(v.fold, newer(v.cursor, b.flat()))
    } else {
        Seq::empty()
    }
}

pub open spec fn stopped<F: ?Sized, E, Er>(v: EngineView, b: BatchView<E>) -> bool {
    run::<F, E, Er>((v.fold, false), calls::<F, E, Er>(v, b)).1
}

/// The calls that consumed their position: all of them, or all but the stopping one.
pub open spec fn ok_calls<F: ?Sized, E, Er>(v: EngineView, b: BatchView<E>) -> Seq<(Position, E)> {
    if stopped::<F, E, Er>(v, b) {
        calls::<F, E, Er>(v, b).drop_last()
    } else {
        calls::<F, E, Er>(v, b)
    }
}

pub open spec fn cursor_after<E>(c: Option<Position>, ok: Seq<(Position, E)>) -> Option<Position> {
    if ok.len() == 0 {
        c
    } else {
        Some(ok.last().0)
    }
}

pub proof fn lemma_run_stopped<F: ?Sized, E, Er>(w: int, y: Seq<(Position, E)>)
    ensures
        run::<F, E, Er>((w, true), y) == (w, true),
    decreases y.len(),
{
    if y.len() > 0 {
        lemma_run_stopped::<F, E, Er>(w, y.drop_last());
    }
}

/// A stopped run stays stopped.
pub proof fn lemma_run_absorb<F: ?Sized, E, Er>(
    s: (int, bool),
    x: Seq<(Position, E)>,
    y: Seq<(Position, E)>,
)
    requires
        run::<F, E, Er>(s, x).1,
    ensures
        run::<F, E, Er>(s, x + y) == run::<F, E, Er>(s, x),
{
    lemma_run_concat::<F, E, Er>(s, x, y);
    lemma_run_stopped::<F, E, Er>(run::<F, E, Er>(s, x).0, y);
}

pub proof fn lemma_applied_prefix<F: ?Sized, E, Er>(v: int, s: Seq<(Position, E)>)
    ensures
        applied::<F, E, Er>(v, s).len() <= s.len(),
        applied::<F, E, Er>(v, s) == s.subrange(0, applied::<F, E, Er>(v, s).len() as int),
        !run::<F, E, Er>((v, false), applied::<F, E, Er>(v, s)).1 ==> applied::<F, E, Er>(v, s) == s,
    decreases s.len(),
{
    if s.len() > 0 && run::<F, E, Er>((v, false), s.drop_last()).1 {
        lemma_applied_prefix::<F, E, Er>(v, s.drop_last());
    } else {
        assert(s == s.subrange(0, s.len() as int));
    }
}

pub proof fn lemma_applied_all<F: ?Sized, E, Er>(v: int, s: Seq<(Position, E)>)
    requires
        !run::<F, E, Er>((v, false), s).1,
    ensures
        applied::<F, E, Er>(v, s) == s,
{
    if s.len() > 0 && run::<F, E, Er>((v, false), s.drop_last()).1 {
        assert(s.drop_last() + seq![s.last()] =~= s);
        lemma_run_absorb::<F, E, Er>((v, false), s.drop_last(), seq![s.last()]);
    }
}

/// A prefix `G` that did not stop is applied whole.
pub proof fn lemma_applied_concat<F: ?Sized, E, Er>(
    v: int,
    g: Seq<(Position, E)>,
    p: Seq<(Position, E)>,
)
    requires
        !run::<F, E, Er>((v, false), g).1,
    ensures
        applied::<F, E, Er>(v, g + p) == g + applied::<F, E, Er>(run::<F, E, Er>((v, false), g).0, p),
    decreases p.len(),
{
    let w = run::<F, E, Er>((v, false), g).0;
    if p.len() == 0 {
        assert(g + p =~= g);
        lemma_applied_all::<F, E, Er>(v, g);
        assert(g + applied::<F, E, Er>(w, p) =~= g);
    } else {
        assert((g + p).drop_last() =~= g + p.drop_last());
        lemma_run_concat::<F, E, Er>((v, false), g, p.drop_last());
        if run::<F, E, Er>((w, false), p.drop_last()).1 {
            lemma_applied_concat::<F, E, Er>(v, g, p.drop_last());
        }
    }
}

/// Entries after the stop are never applied.
pub proof fn lemma_applied_extend<F: ?Sized, E, Er>(
    v: int,
    p: Seq<(Position, E)>,
    r: Seq<(Position, E)>,
)
    requires
        run::<F, E, Er>((v, false), applied::<F, E, Er>(v, p)).1,
    ensures
        applied::<F, E, Er>(v, p + r) == applied::<F, E, Er>(v, p),
    decreases r.len(),
{
    if r.len() == 0 {
        assert(p + r =~= p);
    } else {
        lemma_applied_extend::<F, E, Er>(v, p, r.drop_last());
        lemma_applied_prefix::<F, E, Er>(v, p);
        let a = applied::<F, E, Er>(v, p);
        let q = p + r.drop_last();
        assert((p + r).drop_last() =~= q);
        assert(q =~= a + q.subrange(a.len() as int, q.len() as int));
        lemma_run_absorb::<F, E, Er>((v, false), a, q.subrange(a.len() as int, q.len() as int));
    }
}

/// The first stopping entry of `p` is at `m`.
pub proof fn lemma_applied_stop<F: ?Sized, E, Er>(v: int, p: Seq<(Position, E)>, m: int)
    requires
        0 <= m < p.len(),
        !run::<F, E, Er>((v, false), p.subrange(0, m)).1,
        run::<F, E, Er>((v, false), p.subrange(0, m + 1)).1,
    ensures
        applied::<F, E, Er>(v, p) == p.subrange(0, m + 1),
{
    let x = p.subrange(0, m + 1);
    assert(x.drop_last() =~= p.subrange(0, m));
    lemma_applied_extend::<F, E, Er>(v, x, p.subrange(m + 1, p.len() as int));
    assert(x + p.subrange(m + 1, p.len() as int) =~= p);
}

/// On a sorted log, the entries after `c` are a suffix, in order.
pub proof fn lemma_newer_sorted<E>(c: Option<Position>, s: Seq<(Position, E)>)
    requires
        lt_sorted(s),
    ensures
        newer(c, s).len() <= s.len(),
        newer(c, s) == s.subrange(s.len() - newer(c, s).len(), s.len() as int),
        forall|k: int| 0 <= k < s.len() - newer(c, s).len() ==> !opt_lt(c, Some(#[trigger] s[k].0)),
        forall|k: int| s.len() - newer(c, s).len() <= k < s.len() ==> opt_lt(c, Some(#[trigger] s[k].0)),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        assert(lt_sorted(t)) by {
            assert forall|i: int, j: int| 0 <= i < j < t.len() implies lt(t[i].0, t[j].0) by {
                assert(t[i] == s[i] && t[j] == s[j]);
            }
        }
        lemma_newer_sorted(c, t);
        let x = s.last();
        if !opt_lt(c, Some(x.0)) {
            assert forall|k: int| 0 <= k < t.len() implies !opt_lt(c, Some(#[trigger] t[k].0)) by {
                assert(lt(s[k].0, s[s.len() - 1].0));
                if opt_lt(c, Some(t[k].0)) {
                    lemma_opt_lt_order(c, Some(t[k].0), Some(x.0));
                }
            }
            assert(newer(c, t).len() == 0);
            assert(newer(c, s) == newer(c, t));
            assert(newer(c, s) =~= s.subrange(s.len() as int, s.len() as int));
        } else {
            assert(newer(c, s) == newer(c, t).push(x));
            assert(newer(c, s) =~= s.subrange(s.len() - newer(c, s).len(), s.len() as int));
        }
        assert forall|k: int| 0 <= k < s.len() - newer(c, s).len() implies !opt_lt(c, Some(#[trigger] s[k].0)) by {
            if k < t.len() {
                assert(s[k] == t[k]);
            }
        }
        assert forall|k: int| s.len() - newer(c, s).len() <= k < s.len() implies opt_lt(c, Some(#[trigger] s[k].0)) by {
            if k < t.len() {
                assert(s[k] == t[k]);
            }
        }
    }
}

/// `newer` of a sequence split at `d`: nothing before `d` is newer, everything after is.
pub proof fn lemma_newer_split<E>(c: Option<Position>, s: Seq<(Position, E)>, d: int)
    requires
        0 <= d <= s.len(),
        forall|k: int| 0 <= k < d ==> !opt_lt(c, Some(#[trigger] s[k].0)),
        forall|k: int| d <= k < s.len() ==> opt_lt(c, Some(#[trigger] s[k].0)),
    ensures
        newer(c, s) == s.subrange(d, s.len() as int),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let e = if d == s.len() { d - 1 } else { d };
        assert forall|k: int| 0 <= k < e implies !opt_lt(c, Some(#[trigger] t[k].0)) by {
            assert(t[k] == s[k]);
        }
        assert forall|k: int| e <= k < t.len() implies opt_lt(c, Some(#[trigger] t[k].0)) by {
            assert(t[k] == s[k]);
        }
        lemma_newer_split(c, t, e);
        assert(newer(c, s) =~= s.subrange(d, s.len() as int));
    } else {
        assert(newer(c, s) =~= s.subrange(d, s.len() as int));
    }
}

pub proof fn lemma_newer_add<E>(c: Option<Position>, a: Seq<(Position, E)>, b: Seq<(Position, E)>)
    ensures
        newer(c, a + b) == newer(c, a) + newer(c, b),
    decreases b.len(),
{
    reveal(Seq::filter);
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(newer(c, a) + newer(c, b) =~= newer(c, a));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_newer_add(c, a, b.drop_last());
        if opt_lt(c, Some(b.last().0)) {
            assert(newer(c, a + b) =~= newer(c, a) + newer(c, b));
        } else {
            assert(newer(c, a + b) =~= newer(c, a) + newer(c, b));
        }
    }
}

/// `flat_upto(m)` is a prefix of `flat_upto(n)`.
pub proof fn lemma_flat_prefix<E>(b: BatchView<E>, m: int, n: int)
    requires
        0 <= m <= n,
    ensures
        b.flat_upto(m).len() <= b.flat_upto(n).len(),
        b.flat_upto(n).subrange(0, b.flat_upto(m).len() as int) == b.flat_upto(m),
    decreases n,
{
    if n > m {
        lemma_flat_prefix(b, m, n - 1);
        assert(b.flat_upto(n) == b.flat_upto(n - 1) + b.span_events(n - 1));
        assert(b.flat_upto(n).subrange(0, b.flat_upto(m).len() as int) =~= b.flat_upto(n - 1).subrange(
            0,
            b.flat_upto(m).len() as int,
        ));
    } else {
        assert(b.flat_upto(n).subrange(0, b.flat_upto(m).len() as int) =~= b.flat_upto(m));
    }
}

/// Every entry of `ring_ext(r, w, bs)` comes from `r` or `bs`.
pub proof fn lemma_ring_ext_from(r: Seq<BlockRef>, w: int, bs: Seq<BlockRef>)
    requires
        0 < w,
    ensures
        forall|j: int|
            0 <= j < ring_ext(r, w, bs).len() ==> r.contains(#[trigger] ring_ext(r, w, bs)[j])
                || bs.contains(ring_ext(r, w, bs)[j]),
    decreases bs.len(),
{
    if bs.len() > 0 {
        let t = bs.drop_last();
        lemma_ring_ext_from(r, w, t);
        let pre = ring_ext(r, w, t);
        assert(ring_ext(r, w, bs) == ring_push(pre, w, bs.last()));
        assert forall|j: int| 0 <= j < ring_ext(r, w, bs).len() implies r.contains(
            #[trigger] ring_ext(r, w, bs)[j],
        ) || bs.contains(ring_ext(r, w, bs)[j]) by {
            let x = ring_ext(r, w, bs)[j];
            if j == ring_ext(r, w, bs).len() - 1 {
                assert(x == bs[bs.len() - 1]);
            } else {
                if pre.len() < w {
                    assert(x == pre[j]);
                    assert(r.contains(x) || t.contains(x));
                } else {
                    assert(x == pre.drop_first()[j]);
                    assert(x == pre[j + 1]);
                    assert(r.contains(x) || t.contains(x));
                }
                if bs.drop_last().contains(x) {
                    let u = choose|u: int| 0 <= u < t.len() && t[u] == x;
                    assert(bs[u] == x);
                }
            }
        }
    }
}

/// `ring_ext` over `bs.push(x)`.
pub proof fn lemma_ring_ext_push(r: Seq<BlockRef>, w: int, bs: Seq<BlockRef>, x: BlockRef)
    ensures
        ring_ext(r, w, bs.push(x)) == ring_push(ring_ext(r, w, bs), w, x),
{
    assert(bs.push(x).drop_last() =~= bs);
}

/// `split_at_tip` names one count.
pub proof fn lemma_split_unique<E>(b: BatchView<E>, c: Option<Position>, i: int, j: int)
    requires
        split_at_tip(b, c, i),
        split_at_tip(b, c, j),
    ensures
        i == j,
{
    if c is Some {
        let r = span_refs(b);
        if i < j {
            assert(r[i].number <= c.unwrap().block);
        } else if j < i {
            assert(r[j].number <= c.unwrap().block);
        }
    }
}

/// Count of the leading blocks at or below `n`; on ascending blocks, a partition point.
pub open spec fn count_le(bl: Seq<u64>, n: u64) -> int
    decreases bl.len(),
{
    if bl.len() == 0 || bl.last() <= n {
        bl.len() as int
    } else {
        count_le(bl.drop_last(), n)
    }
}

pub proof fn lemma_count_le(bl: Seq<u64>, n: u64)
    requires
        forall|i: int, j: int| #![trigger bl[i], bl[j]] 0 <= i < j < bl.len() ==> bl[i] < bl[j],
    ensures
        0 <= count_le(bl, n) <= bl.len(),
        forall|k: int| 0 <= k < count_le(bl, n) ==> #[trigger] bl[k] <= n,
        forall|k: int| count_le(bl, n) <= k < bl.len() ==> #[trigger] bl[k] > n,
    decreases bl.len(),
{
    if bl.len() > 0 {
        let t = bl.drop_last();
        if bl.last() <= n {
            assert forall|k: int| 0 <= k < bl.len() implies #[trigger] bl[k] <= n by {
                if k < bl.len() - 1 {
                    assert(bl[k] < bl[bl.len() - 1]);
                }
            }
        } else {
            assert forall|i: int, j: int| #![trigger t[i], t[j]] 0 <= i < j < t.len() implies t[i] < t[j] by {
                assert(t[i] == bl[i] && t[j] == bl[j]);
            }
            lemma_count_le(t, n);
            assert forall|k: int| 0 <= k < count_le(bl, n) implies #[trigger] bl[k] <= n by {
                assert(t[k] == bl[k]);
            }
            assert forall|k: int| count_le(bl, n) <= k < bl.len() implies #[trigger] bl[k] > n by {
                if k < t.len() {
                    assert(t[k] == bl[k]);
                }
            }
        }
    }
}

/// `last_verified` after the boundary check: the boundary once it has passed.
pub open spec fn checked_freshness<E>(v: EngineView, b: BatchView<E>) -> Option<BlockRef> {
    if v.status is Active && b.shaped() && v.cursor is Some && b.boundary == Some(v.ring.last()) {
        b.boundary
    } else {
        v.last_verified
    }
}

/// T3e ring: the ring gains exactly the blocks of the spans above the old cursor block
/// and at or below the new one; freshness is the newest gained block, or the checked
/// boundary when none was gained.
pub open spec fn ring_after<E>(v: EngineView, post: EngineView, b: BatchView<E>, w: int) -> bool {
    exists|i0: int, i1: int|
        #![trigger split_at_tip(b, v.cursor, i0), split_at_tip(b, post.cursor, i1)]
        {
            &&& i0 <= i1
            &&& split_at_tip(b, v.cursor, i0)
            &&& split_at_tip(b, post.cursor, i1)
            &&& post.ring == ring_ext(v.ring, w, span_refs(b).subrange(i0, i1))
            &&& post.last_verified == if i0 < i1 {
                Some(post.ring.last())
            } else {
                checked_freshness(v, b)
            }
        }
}

/// T3d: when no position of `b` is after the cursor, applying `b` calls the fold zero
/// times; with `lemma_split_unique`, `apply_batch` then keeps fold, cursor and ring.
pub proof fn lemma_idempotent<F: ?Sized, E, Er>(v: EngineView, b: BatchView<E>)
    requires
        newer(v.cursor, b.flat()).len() == 0,
    ensures
        calls::<F, E, Er>(v, b).len() == 0,
        ok_calls::<F, E, Er>(v, b).len() == 0,
        fold::<F, E, Er>(v.fold, calls::<F, E, Er>(v, b)) == v.fold,
        cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b)) == v.cursor,
{
    lemma_applied_prefix::<F, E, Er>(v.fold, newer(v.cursor, b.flat()));
}


// P8c: driver end-to-end (T7).

/// View `v` holds every height in `[lo, hi]` (T7; weaker than `down_closed`).
pub open spec fn holds(v: ChainView, lo: u64, hi: u64) -> bool {
    forall|n: u64| lo <= n <= hi ==> #[trigger] v.contains_key(n)
}

/// No entry of `v`'s block `p.block` lies after `p`: the cursor ends its block.
pub open spec fn complete<S: ?Sized, E>(v: ChainView, p: Position) -> bool {
    forall|i: int|
        0 <= i < block_entries::<S, E>(v, p.block).len() ==> (#[trigger] block_entries::<S, E>(
            v,
            p.block,
        )[i]).1 as u64 <= p.log_index
}

/// A source entry with its position.
pub open spec fn tpos<E>(x: (BlockRef, u32, E)) -> (Position, E) {
    (Position { block: x.0.number, log_index: x.1 as u64 }, x.2)
}

/// Source entries strictly ascending by position.
pub open spec fn ksorted<E>(s: Seq<(BlockRef, u32, E)>) -> bool {
    forall|i: int, j: int| #![trigger s[i], s[j]] 0 <= i < j < s.len() ==> lt(tpos(s[i]).0, tpos(s[j]).0)
}

/// `range_entries` with positions.
pub open spec fn pentries<S: ?Sized, E>(v: ChainView, lo: int, hi: int) -> Seq<(Position, E)> {
    range_entries::<S, E>(v, lo, hi).map_values(|x: (BlockRef, u32, E)| tpos(x))
}

/// `canon`'s lowest height and filter.
pub open spec fn alo(a: Option<Position>) -> int {
    match a {
        None => 0,
        Some(a) => a.block as int,
    }
}

pub open spec fn within<E>(a: Option<Position>, c: Position) -> spec_fn((Position, E)) -> bool {
    |x: (Position, E)| opt_lt(a, Some(x.0)) && le(x.0, c)
}

pub proof fn lemma_canon_def<S: ?Sized, E>(v: ChainView, a: Option<Position>, c: Position)
    ensures
        canon::<S, E>(v, a, Some(c)) == pentries::<S, E>(v, alo(a), c.block as int).filter(within::<E>(a, c)),
{
    let m = range_entries::<S, E>(v, alo(a), c.block as int).map_values(
        |x: (BlockRef, u32, E)| (Position { block: x.0.number, log_index: x.1 as u64 }, x.2),
    );
    assert(m =~= pentries::<S, E>(v, alo(a), c.block as int));
    assert(within::<E>(a, c) =~= (|x: (Position, E)| opt_lt(a, Some(x.0)) && le(x.0, c)));
}

pub proof fn lemma_filter_ext<A>(s: Seq<A>, p: spec_fn(A) -> bool, q: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i]) == q(s[i]),
    ensures
        s.filter(p) == s.filter(q),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        assert forall|i: int| 0 <= i < s.drop_last().len() implies p(#[trigger] s.drop_last()[i]) == q(
            s.drop_last()[i],
        ) by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_filter_ext(s.drop_last(), p, q);
        assert(p(s[s.len() - 1]) == q(s[s.len() - 1]));
    }
}

pub proof fn lemma_filter_all<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i]),
    ensures
        s.filter(p) == s,
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        assert forall|i: int| 0 <= i < s.drop_last().len() implies p(#[trigger] s.drop_last()[i]) by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_filter_all(s.drop_last(), p);
        assert(p(s[s.len() - 1]));
        assert(s.drop_last().push(s.last()) =~= s);
    }
}

pub proof fn lemma_filter_none<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> !p(#[trigger] s[i]),
    ensures
        s.filter(p) == Seq::<A>::empty(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        assert forall|i: int| 0 <= i < s.drop_last().len() implies !p(#[trigger] s.drop_last()[i]) by {
            assert(s.drop_last()[i] == s[i]);
        }
        lemma_filter_none(s.drop_last(), p);
        assert(!p(s[s.len() - 1]));
    } else {
        assert(s =~= Seq::<A>::empty());
    }
}

/// `range_entries` splits at any height in range.
pub proof fn lemma_re_split<S: ?Sized, E>(v: ChainView, lo: int, mid: int, hi: int)
    requires
        0 <= lo,
        lo - 1 <= mid <= hi <= u64::MAX,
    ensures
        range_entries::<S, E>(v, lo, hi) == range_entries::<S, E>(v, lo, mid) + range_entries::<S, E>(
            v,
            mid + 1,
            hi,
        ),
    decreases hi - mid,
{
    if hi == mid {
        assert(range_entries::<S, E>(v, lo, hi) + range_entries::<S, E>(v, mid + 1, hi) =~= range_entries::<
            S,
            E,
        >(v, lo, hi));
    } else {
        lemma_re_split::<S, E>(v, lo, mid, hi - 1);
        assert(range_entries::<S, E>(v, lo, hi) =~= range_entries::<S, E>(v, lo, mid) + range_entries::<
            S,
            E,
        >(v, mid + 1, hi));
    }
}

pub proof fn lemma_pe_split<S: ?Sized, E>(v: ChainView, lo: int, mid: int, hi: int)
    requires
        0 <= lo,
        lo - 1 <= mid <= hi <= u64::MAX,
    ensures
        pentries::<S, E>(v, lo, hi) == pentries::<S, E>(v, lo, mid) + pentries::<S, E>(v, mid + 1, hi),
{
    lemma_re_split::<S, E>(v, lo, mid, hi);
    assert(pentries::<S, E>(v, lo, hi) =~= pentries::<S, E>(v, lo, mid) + pentries::<S, E>(v, mid + 1, hi));
}

/// Every entry of `range_entries(v, lo, hi)` is `v`'s block at a height in `[lo, hi]`.
pub proof fn lemma_re_facts<S: ?Sized, E>(v: ChainView, lo: int, hi: int)
    requires
        chain(v),
    ensures
        forall|i: int|
            0 <= i < range_entries::<S, E>(v, lo, hi).len() ==> {
                let x = #[trigger] range_entries::<S, E>(v, lo, hi)[i];
                &&& lo <= x.0.number <= hi
                &&& v.contains_key(x.0.number)
                &&& v[x.0.number] == x.0
            },
    decreases hi - lo + 1,
{
    if !(hi < lo || hi < 0 || hi > u64::MAX) {
        lemma_re_facts::<S, E>(v, lo, hi - 1);
        let (r0, b) = (range_entries::<S, E>(v, lo, hi - 1), block_entries::<S, E>(v, hi as u64));
        assert forall|i: int| 0 <= i < range_entries::<S, E>(v, lo, hi).len() implies {
            let x = #[trigger] range_entries::<S, E>(v, lo, hi)[i];
            &&& lo <= x.0.number <= hi
            &&& v.contains_key(x.0.number)
            &&& v[x.0.number] == x.0
        } by {
            if i >= r0.len() {
                assert(range_entries::<S, E>(v, lo, hi)[i] == b[i - r0.len()]);
                assert(v.contains_key(hi as u64));
            } else {
                assert(range_entries::<S, E>(v, lo, hi)[i] == r0[i]);
            }
        }
    }
}

/// Entries of block `p.block` in a range sit at or below a `complete` point `p`.
pub proof fn lemma_re_complete<S: ?Sized, E>(v: ChainView, lo: int, hi: int, p: Position)
    requires
        chain(v),
        complete::<S, E>(v, p),
    ensures
        forall|i: int|
            0 <= i < range_entries::<S, E>(v, lo, hi).len() && (#[trigger] range_entries::<S, E>(
                v,
                lo,
                hi,
            )[i]).0.number == p.block ==> range_entries::<S, E>(v, lo, hi)[i].1 as u64 <= p.log_index,
    decreases hi - lo + 1,
{
    if !(hi < lo || hi < 0 || hi > u64::MAX) {
        lemma_re_complete::<S, E>(v, lo, hi - 1, p);
        let (r0, b) = (range_entries::<S, E>(v, lo, hi - 1), block_entries::<S, E>(v, hi as u64));
        assert forall|i: int|
            0 <= i < range_entries::<S, E>(v, lo, hi).len() && (#[trigger] range_entries::<S, E>(
                v,
                lo,
                hi,
            )[i]).0.number == p.block implies range_entries::<S, E>(v, lo, hi)[i].1 as u64
            <= p.log_index by {
            if i >= r0.len() {
                assert(range_entries::<S, E>(v, lo, hi)[i] == b[i - r0.len()]);
                assert(v.contains_key(hi as u64));
                assert(b[i - r0.len()] == block_entries::<S, E>(v, p.block)[i - r0.len()]);
            } else {
                assert(range_entries::<S, E>(v, lo, hi)[i] == r0[i]);
            }
        }
    }
}


/// Views that agree on `[lo, hi]` give the same entries there.
pub proof fn lemma_re_agree<S: ?Sized, E>(v: ChainView, u: ChainView, lo: int, hi: int)
    requires
        forall|n: u64| lo <= n <= hi ==> #[trigger] header(v, n) == header(u, n),
    ensures
        range_entries::<S, E>(v, lo, hi) == range_entries::<S, E>(u, lo, hi),
    decreases hi - lo + 1,
{
    if !(hi < lo || hi < 0 || hi > u64::MAX) {
        lemma_re_agree::<S, E>(v, u, lo, hi - 1);
        assert(header(v, hi as u64) == header(u, hi as u64));
        assert(block_entries::<S, E>(v, hi as u64) == block_entries::<S, E>(u, hi as u64));
    }
}

/// Under A1 the entries of a range are strictly ascending by position.
pub proof fn lemma_re_sorted<S: ?Sized, E>(v: ChainView, lo: int, hi: int)
    requires
        a1::<S, E>(v),
    ensures
        ksorted(range_entries::<S, E>(v, lo, hi)),
    decreases hi - lo + 1,
{
    if !(hi < lo || hi < 0 || hi > u64::MAX) {
        lemma_re_sorted::<S, E>(v, lo, hi - 1);
        lemma_re_facts::<S, E>(v, lo, hi - 1);
        let (r0, b) = (range_entries::<S, E>(v, lo, hi - 1), block_entries::<S, E>(v, hi as u64));
        let r = range_entries::<S, E>(v, lo, hi);
        assert(r == r0 + b);
        if v.contains_key(hi as u64) {
            let l = logs::<S, E>(v[hi as u64].hash);
            assert(logs_ascending(l));
            assert(v[hi as u64].number == hi);
        }
        assert forall|i: int, j: int| 0 <= i < j < r.len() implies lt(tpos(#[trigger] r[i]).0, tpos(#[trigger] r[j]).0) by {
            if j < r0.len() {
                assert(r[i] == r0[i] && r[j] == r0[j]);
            } else if i < r0.len() {
                assert(r[i] == r0[i] && r[j] == b[j - r0.len()]);
            } else {
                let l = logs::<S, E>(v[hi as u64].hash);
                assert(r[i] == b[i - r0.len()] && r[j] == b[j - r0.len()]);
                assert(l[i - r0.len()].0 < l[j - r0.len()].0);
            }
        }
    }
}

/// Two strictly sorted sequences with the same elements are equal.
pub proof fn lemma_sorted_unique<E>(s: Seq<(BlockRef, u32, E)>, t: Seq<(BlockRef, u32, E)>)
    requires
        ksorted(s),
        ksorted(t),
        s.to_multiset() == t.to_multiset(),
    ensures
        s == t,
    decreases s.len(),
{
    broadcast use {vstd::seq_lib::to_multiset_len, vstd::seq_lib::to_multiset_contains, vstd::seq_lib::to_multiset_remove};
    vstd::seq_lib::to_multiset_len(s);
    vstd::seq_lib::to_multiset_len(t);
    assert(s.len() == t.len());
    if s.len() > 0 {
        vstd::seq_lib::to_multiset_contains(s, s[0]);
        vstd::seq_lib::to_multiset_contains(t, s[0]);
        vstd::seq_lib::to_multiset_contains(s, t[0]);
        vstd::seq_lib::to_multiset_contains(t, t[0]);
        assert(s.contains(s[0]));
        assert(t.contains(t[0]));
        assert(t.contains(s[0]));
        assert(s.contains(t[0]));
        vstd::seq_lib::to_multiset_remove(s, 0);
        vstd::seq_lib::to_multiset_remove(t, 0);
        let j = choose|j: int| 0 <= j < t.len() && t[j] == s[0];
        let i = choose|i: int| 0 <= i < s.len() && s[i] == t[0];
        if i > 0 {
            assert(lt(tpos(s[0]).0, tpos(s[i]).0));
            if j > 0 {
                assert(lt(tpos(t[0]).0, tpos(t[j]).0));
            }
            assert(false);
        }
        assert(s[0] == t[0]);
        assert(s.remove(0) =~= s.drop_first());
        assert(t.remove(0) =~= t.drop_first());
        assert(s.drop_first().to_multiset() == t.drop_first().to_multiset());
        assert(ksorted(s.drop_first())) by {
            assert forall|a: int, b: int| 0 <= a < b < s.drop_first().len() implies lt(
                tpos(#[trigger] s.drop_first()[a]).0,
                tpos(#[trigger] s.drop_first()[b]).0,
            ) by {
                assert(s.drop_first()[a] == s[a + 1] && s.drop_first()[b] == s[b + 1]);
            }
        }
        assert(ksorted(t.drop_first())) by {
            assert forall|a: int, b: int| 0 <= a < b < t.drop_first().len() implies lt(
                tpos(#[trigger] t.drop_first()[a]).0,
                tpos(#[trigger] t.drop_first()[b]).0,
            ) by {
                assert(t.drop_first()[a] == t[a + 1] && t.drop_first()[b] == t[b + 1]);
            }
        }
        lemma_sorted_unique(s.drop_first(), t.drop_first());
        assert(s =~= t) by {
            assert forall|k: int| 0 <= k < s.len() implies s[k] == t[k] by {
                if k > 0 {
                    assert(s[k] == s.drop_first()[k - 1] && t[k] == t.drop_first()[k - 1]);
                }
            }
        }
    } else {
        assert(s =~= t);
    }
}

/// Positioned entries of a range are `lt_sorted` under A1.
pub proof fn lemma_pe_sorted<S: ?Sized, E>(v: ChainView, lo: int, hi: int)
    requires
        a1::<S, E>(v),
    ensures
        lt_sorted(pentries::<S, E>(v, lo, hi)),
{
    lemma_re_sorted::<S, E>(v, lo, hi);
    let (r, p) = (range_entries::<S, E>(v, lo, hi), pentries::<S, E>(v, lo, hi));
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies lt((#[trigger] p[i]).0, (#[trigger] p[j]).0) by {
        assert(p[i] == tpos(r[i]) && p[j] == tpos(r[j]));
        assert(lt(tpos(r[i]).0, tpos(r[j]).0));
    }
}

/// Chains that agree at `c` and both hold `[start, c]` agree on all of it.
pub proof fn lemma_view_agree(h: ChainView, v: ChainView, start: u64, c: u64)
    requires
        chain(h),
        chain(v),
        holds(h, start, c),
        holds(v, start, c),
        h[c] == v[c],
    ensures
        forall|n: u64| start <= n <= c ==> #[trigger] header(h, n) == header(v, n),
{
    assert forall|n: u64| start <= n <= c implies #[trigger] header(h, n) == header(v, n) by {
        assert(h.contains_key(n) && h.contains_key(c) && v.contains_key(n) && v.contains_key(c));
        assert(h[n] == anc(h[c].hash, n));
        assert(v[n] == anc(v[c].hash, n));
    }
}

/// `canon` from `before(start)` reads only heights `start..`.
pub proof fn lemma_canon_agree<S: ?Sized, E>(v: ChainView, u: ChainView, start: u64, c: Option<Position>)
    requires
        chain(v),
        chain(u),
        c matches Some(p) ==> forall|n: u64| start <= n <= p.block ==> #[trigger] header(v, n) == header(u, n),
    ensures
        canon::<S, E>(v, before(start), c) == canon::<S, E>(u, before(start), c),
{
    if let Some(p) = c {
        let a = before(start);
        lemma_canon_def::<S, E>(v, a, p);
        lemma_canon_def::<S, E>(u, a, p);
        let hi = p.block as int;
        if start == 0 {
            lemma_re_agree::<S, E>(v, u, 0, hi);
        } else if hi >= start - 1 {
            let lo = start - 1;
            lemma_pe_split::<S, E>(v, lo, lo, hi);
            lemma_pe_split::<S, E>(u, lo, lo, hi);
            lemma_re_agree::<S, E>(v, u, lo + 1, hi);
            let w = within::<E>(a, p);
            Seq::filter_distributes_over_add(pentries::<S, E>(v, lo, lo), pentries::<S, E>(v, lo + 1, hi), w);
            Seq::filter_distributes_over_add(pentries::<S, E>(u, lo, lo), pentries::<S, E>(u, lo + 1, hi), w);
            lemma_re_facts::<S, E>(v, lo, lo);
            lemma_re_facts::<S, E>(u, lo, lo);
            assert forall|i: int| 0 <= i < pentries::<S, E>(v, lo, lo).len() implies !w(#[trigger] pentries::<S, E>(v, lo, lo)[i]) by {
                assert(pentries::<S, E>(v, lo, lo)[i] == tpos(range_entries::<S, E>(v, lo, lo)[i]));
            }
            assert forall|i: int| 0 <= i < pentries::<S, E>(u, lo, lo).len() implies !w(#[trigger] pentries::<S, E>(u, lo, lo)[i]) by {
                assert(pentries::<S, E>(u, lo, lo)[i] == tpos(range_entries::<S, E>(u, lo, lo)[i]));
            }
            lemma_filter_none(pentries::<S, E>(v, lo, lo), w);
            lemma_filter_none(pentries::<S, E>(u, lo, lo), w);
        }
    }
}

pub open spec fn and_le<E>(p: spec_fn((Position, E)) -> bool, t: Option<Position>) -> spec_fn((Position, E)) -> bool {
    |x: (Position, E)| p(x) && opt_le(Some(x.0), t)
}

/// On a sorted log `upto` is a filter.
pub proof fn lemma_upto_filter<E>(s: Seq<(Position, E)>, p: spec_fn((Position, E)) -> bool, t: Option<Position>)
    requires
        lt_sorted(s),
    ensures
        upto(s.filter(p), t) == s.filter(and_le(p, t)),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let (s0, x) = (s.drop_last(), s.last());
        assert(lt_sorted(s0)) by {
            assert forall|i: int, j: int| 0 <= i < j < s0.len() implies lt((#[trigger] s0[i]).0, (#[trigger] s0[j]).0) by {
                assert(s0[i] == s[i] && s0[j] == s[j]);
            }
        }
        lemma_upto_filter(s0, p, t);
        let q = and_le(p, t);
        if p(x) {
            assert(s.filter(p) == s0.filter(p).push(x));
            assert(s.filter(p).drop_last() =~= s0.filter(p));
            if opt_le(Some(x.0), t) {
                assert forall|i: int| 0 <= i < s0.len() implies p(#[trigger] s0[i]) == q(s0[i]) by {
                    assert(s0[i] == s[i]);
                    assert(lt(s[i].0, s[s.len() - 1].0));
                    assert(opt_lt(Some(s0[i].0), Some(x.0)));
                    lemma_opt_lt_order(Some(s0[i].0), Some(x.0), t);
                }
                lemma_filter_ext(s0, p, q);
            }
        }
    }
}

/// `upto` of `canon` at a lower point is `canon` there.
pub proof fn lemma_canon_upto<S: ?Sized, E>(v: ChainView, a: Option<Position>, c: Position, t: Option<Position>)
    requires
        a1::<S, E>(v),
        opt_le(t, Some(c)),
        t matches Some(q) ==> alo(a) <= q.block + 1,
    ensures
        upto(canon::<S, E>(v, a, Some(c)), t) == canon::<S, E>(v, a, t),
{
    lemma_canon_def::<S, E>(v, a, c);
    let (lo, hi) = (alo(a), c.block as int);
    let s = pentries::<S, E>(v, lo, hi);
    let w = within::<E>(a, c);
    lemma_pe_sorted::<S, E>(v, lo, hi);
    lemma_upto_filter(s, w, t);
    lemma_re_facts::<S, E>(v, lo, hi);
    match t {
        None => {
            lemma_filter_none(s, and_le(w, t));
        },
        Some(q) => {
            lemma_canon_def::<S, E>(v, a, q);
            let m = q.block as int;
            assert(m <= hi);
            lemma_pe_split::<S, E>(v, lo, m, hi);
            let (s1, s2) = (pentries::<S, E>(v, lo, m), pentries::<S, E>(v, m + 1, hi));
            Seq::filter_distributes_over_add(s1, s2, and_le(w, t));
            lemma_re_facts::<S, E>(v, lo, m);
            lemma_re_facts::<S, E>(v, m + 1, hi);
            assert forall|i: int| 0 <= i < s2.len() implies !and_le(w, t)(#[trigger] s2[i]) by {
                assert(s2[i] == tpos(range_entries::<S, E>(v, m + 1, hi)[i]));
            }
            lemma_filter_none(s2, and_le(w, t));
            assert forall|i: int| 0 <= i < s1.len() implies and_le(w, t)(#[trigger] s1[i]) == within::<E>(a, q)(s1[i]) by {
                assert(s1[i] == tpos(range_entries::<S, E>(v, lo, m)[i]));
                if le(s1[i].0, q) {
                    lemma_opt_lt_order(Some(s1[i].0), t, Some(c));
                }
            }
            lemma_filter_ext(s1, and_le(w, t), within::<E>(a, q));
            assert(s1.filter(and_le(w, t)) + Seq::empty() =~= s1.filter(and_le(w, t)));
        },
    }
}


/// T7 apply step: extending a complete cursor `co` (or the anchor) to a complete `cn`
/// appends the positioned entries of the heights between.
pub proof fn lemma_canon_extend<S: ?Sized, E>(
    v: ChainView,
    a: Option<Position>,
    lb: int,
    co: Option<Position>,
    cn: Position,
)
    requires
        a1::<S, E>(v),
        alo(a) - 1 <= lb < cn.block,
        a matches Some(q) ==> q.block <= lb,
        co matches Some(p) ==> p.block == lb && complete::<S, E>(v, p),
        co is None ==> (a is None && lb == -1) || (a matches Some(q) && q.log_index == u64::MAX && lb
            == q.block),
        complete::<S, E>(v, cn),
    ensures
        canon::<S, E>(v, a, Some(cn)) == canon::<S, E>(v, a, co) + pentries::<S, E>(v, lb + 1, cn.block as int),
{
    lemma_canon_def::<S, E>(v, a, cn);
    let (lo, hi) = (alo(a), cn.block as int);
    let wn = within::<E>(a, cn);
    lemma_pe_split::<S, E>(v, lo, lb, hi);
    let (s1, s2) = (pentries::<S, E>(v, lo, lb), pentries::<S, E>(v, lb + 1, hi));
    Seq::filter_distributes_over_add(s1, s2, wn);
    assert(s2.filter(wn) == s2) by {
        lemma_re_facts::<S, E>(v, lb + 1, hi);
        lemma_re_complete::<S, E>(v, lb + 1, hi, cn);
        assert forall|i: int| 0 <= i < s2.len() implies wn(#[trigger] s2[i]) by {
            assert(s2[i] == tpos(range_entries::<S, E>(v, lb + 1, hi)[i]));
        }
        lemma_filter_all(s2, wn);
    }
    assert(s1.filter(wn) == canon::<S, E>(v, a, co)) by {
        lemma_re_facts::<S, E>(v, lo, lb);
        match co {
            None => {
                if a is None {
                    assert(s1.len() == 0);
                }
                assert forall|i: int| 0 <= i < s1.len() implies !wn(#[trigger] s1[i]) by {
                    assert(s1[i] == tpos(range_entries::<S, E>(v, lo, lb)[i]));
                }
                lemma_filter_none(s1, wn);
            },
            Some(p) => {
                lemma_canon_def::<S, E>(v, a, p);
                lemma_re_complete::<S, E>(v, lo, lb, p);
                assert forall|i: int| 0 <= i < s1.len() implies wn(#[trigger] s1[i]) == within::<E>(a, p)(s1[i]) by {
                    assert(s1[i] == tpos(range_entries::<S, E>(v, lo, lb)[i]));
                }
                lemma_filter_ext(s1, wn, within::<E>(a, p));
            },
        }
    }
    if co is None {
        assert(Seq::<(Position, E)>::empty() + s2 =~= s2);
    }
}


/// The last entry of a non-empty range ends its block, and nothing lies above its block.
pub proof fn lemma_last_complete<S: ?Sized, E>(v: ChainView, lo: int, hi: int)
    requires
        a1::<S, E>(v),
        0 <= lo,
        range_entries::<S, E>(v, lo, hi).len() > 0,
    ensures
        ({
            let r = range_entries::<S, E>(v, lo, hi);
            let x = tpos(r.last()).0;
            &&& complete::<S, E>(v, x)
            &&& lo <= x.block <= hi
            &&& r == range_entries::<S, E>(v, lo, x.block as int)
        }),
    decreases hi - lo,
{
    let (r0, b) = (range_entries::<S, E>(v, lo, hi - 1), block_entries::<S, E>(v, hi as u64));
    let r = range_entries::<S, E>(v, lo, hi);
    assert(r == r0 + b);
    if b.len() > 0 {
        assert(v.contains_key(hi as u64));
        assert(v[hi as u64].number == hi);
        let l = logs::<S, E>(v[hi as u64].hash);
        assert(logs_ascending(l));
        assert(r.last() == b.last());
        assert forall|i: int| 0 <= i < b.len() implies (#[trigger] b[i]).1 as u64 <= b.last().1 as u64 by {
            if i < b.len() - 1 {
                assert(l[i].0 < l[b.len() - 1].0);
            }
        }
    } else {
        assert(r =~= r0);
        lemma_last_complete::<S, E>(v, lo, hi - 1);
    }
}

/// A ring inside a chain view, ascending, is a hash chain.
pub proof fn lemma_ring_chain_in(r: Seq<BlockRef>, v: ChainView)
    requires
        ring_in(r, v),
        chain(v),
        ring_ascending(r),
    ensures
        ring_chain(r),
{
    assert forall|i: int, j: int| 0 <= i < j < r.len() implies r[i] == anc(#[trigger] r[j].hash, (#[trigger] r[i]).number) by {
        assert(v.contains_key(r[i].number) && v.contains_key(r[j].number));
        assert(r[i].number < r[j].number);
        assert(v[r[i].number] == anc(v[r[j].number].hash, r[i].number));
    }
}

/// A ring inside `h`, at heights where `h` and `v` agree, is inside `v`.
pub proof fn lemma_ring_move(r: Seq<BlockRef>, h: ChainView, v: ChainView, lo: u64, hi: u64)
    requires
        ring_in(r, h),
        forall|i: int| 0 <= i < r.len() ==> lo <= #[trigger] r[i].number <= hi,
        forall|n: u64| lo <= n <= hi ==> #[trigger] header(h, n) == header(v, n),
    ensures
        ring_in(r, v),
{
    assert forall|i: int| 0 <= i < r.len() implies v.contains_key(#[trigger] r[i].number) && v[r[i].number] == r[i] by {
        assert(header(h, r[i].number) == header(v, r[i].number));
    }
}


/// Every entry after `c` is newer.
pub proof fn lemma_newer_all<E>(c: Option<Position>, s: Seq<(Position, E)>)
    requires
        forall|i: int| 0 <= i < s.len() ==> opt_lt(c, Some((#[trigger] s[i]).0)),
    ensures
        newer(c, s) == s,
{
    let p = |x: (Position, E)| opt_lt(c, Some(x.0));
    lemma_filter_all(s, p);
}


/// Every newer entry is after `c`.
pub proof fn lemma_newer_after<E>(c: Option<Position>, s: Seq<(Position, E)>)
    ensures
        forall|i: int| 0 <= i < newer(c, s).len() ==> opt_lt(c, Some((#[trigger] newer(c, s)[i]).0)),
{
    let p = |x: (Position, E)| opt_lt(c, Some(x.0));
    assert forall|i: int| 0 <= i < newer(c, s).len() implies opt_lt(c, Some((#[trigger] newer(c, s)[i]).0)) by {
        s.lemma_filter_pred(p, i);
    }
}

/// Apply never moves the cursor back (T6b floor through apply).
pub proof fn lemma_cursor_advances<F: ?Sized, E, Er>(v: EngineView, b: BatchView<E>)
    ensures
        opt_le(v.cursor, cursor_after(v.cursor, ok_calls::<F, E, Er>(v, b))),
{
    let nw = newer(v.cursor, b.flat());
    let cl = calls::<F, E, Er>(v, b);
    let ok = ok_calls::<F, E, Er>(v, b);
    if ok.len() > 0 {
        lemma_newer_after(v.cursor, b.flat());
        lemma_applied_prefix::<F, E, Er>(v.fold, nw);
        assert(accepted(v, b));
        assert(ok.last() == cl[ok.len() - 1]);
        assert(cl[ok.len() - 1] == nw[ok.len() - 1]);
    }
}

} // verus!
