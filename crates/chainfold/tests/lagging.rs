use chainfold::{
    BlockRef,
    Driver,
    DriverConfig,
    EngineConfig,
    Position,
    Source,
    Tick,
    test_util::{
        PollFailure,
        RecordingFold,
        ScriptedChain,
    },
};

/// Answers `head` from one node and every other read from another.
struct TwoNodes {
    head: ScriptedChain,
    reads: ScriptedChain,
}

impl Source for TwoNodes {
    type Event = u64;
    type Error = PollFailure;

    fn head(&mut self) -> Result<BlockRef, PollFailure> {
        self.head.head()
    }

    fn header_at(&mut self, number: u64) -> Result<Option<BlockRef>, PollFailure> {
        self.reads.header_at(number)
    }

    fn events_in(
        &mut self,
        from: u64,
        to: u64,
        out: &mut Vec<(BlockRef, u32, u64)>,
    ) -> Result<(), PollFailure> {
        self.reads.events_in(from, to, out)
    }
}

/// A driver folded to the tip of a `len`-block chain with one event at each of `events`.
fn folded(len: u64, events: &[u64]) -> Driver<RecordingFold, TwoNodes> {
    let mut chain = ScriptedChain::new(1);
    for n in 1..=len {
        let event = [n];
        chain.push_block(if events.contains(&n) { &event } else { &[] });
    }
    let source = TwoNodes {
        head: chain.clone(),
        reads: chain,
    };
    let config = EngineConfig {
        ring_capacity: 64,
        checkpoint_slots: 4,
    };
    let mut driver = Driver::new(
        RecordingFold::default(),
        source,
        config,
        DriverConfig::from_block(1),
    )
    .unwrap();
    while driver.tick() != Tick::Idle {}
    driver
}

fn applied(driver: &Driver<RecordingFold, TwoNodes>) -> Vec<u64> {
    driver
        .engine()
        .fold()
        .applied
        .iter()
        .map(|(_, event)| *event)
        .collect()
}

#[test]
fn a_shorter_fork_with_no_ring_entry_at_its_head_is_found() {
    // given a driver folded to the events at blocks 10 and 20
    let mut driver = folded(20, &[10, 20]);
    // when both nodes move to a fork from block 9 that ends at 15, with an event at 12
    let fork: [&[u64]; 6] = [&[], &[], &[12], &[], &[], &[]];
    let source = driver.source_mut();
    source.head.reorg(11, &fork);
    source.reads.reorg(11, &fork);
    let ticks: Vec<Tick> = (0..3).map(|_| driver.tick()).collect();
    // then the orphaned ring entry at 10 sends the driver into recovery, and it folds the
    // fork's event instead of waiting on the head
    assert_eq!(ticks[0], Tick::Resynced);
    assert_eq!(ticks[2], Tick::Idle);
    assert_eq!(applied(&driver), vec![12]);
}

#[test]
fn a_node_with_no_header_under_its_own_head_is_lagging_not_forked() {
    // given a driver folded to the events at blocks 10, 20 and 30
    let mut driver = folded(30, &[10, 20, 30]);
    // when the head comes from a node at 25 and every other read from a node at 5, both
    // on the same chain
    let source = driver.source_mut();
    source.head.reorg(5, &[]);
    source.reads.reorg(25, &[]);
    let tick = driver.tick();
    // then the missing header at 20 proves no fork, and nothing is thrown away
    assert_eq!(tick, Tick::Idle);
    assert_eq!(driver.engine().cursor(), Some(Position::new(30, 0)));
    assert_eq!(applied(&driver), vec![10, 20, 30]);
}
