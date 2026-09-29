#[cfg(verus_keep_ghost)]
use {
    crate::verus::model::{
        fview,
        step,
    },
    vstd::prelude::*,
};

use crate::{
    error::FoldError,
    position::Position,
};

/// Consumer state machine folding events at strictly increasing positions.
///
/// A `Clone` fold must clone its full observable state: checkpoints are clones, and
/// rollback resumes from them.
// `apply` is a deterministic function of the state view, position and event, and a
// Halt leaves the view unchanged. Implementations are trusted to meet this spec.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Fold {
    /// Event the fold consumes.
    type Event;
    /// Failure the fold classifies as skip, halt, or poison.
    type Error;

    /// Folds one event into the state at a strictly increasing position.
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        ensures
            (fview::<Self>(final(self)), r)
                == step::<Self, Self::Event, Self::Error>(fview::<Self>(old(self)), pos, *event),
            r matches Err(FoldError::Halt(_)) ==> fview::<Self>(final(self)) == fview::<Self>(old(self)),
    ))]
    fn apply(
        &mut self,
        pos: Position,
        event: &Self::Event,
    ) -> Result<(), FoldError<Self::Error>>;
}
