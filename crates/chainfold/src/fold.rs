use crate::{
    error::FoldError,
    position::Position,
};

/// Consumer state machine folding events at strictly increasing positions.
pub trait Fold {
    /// Event the fold consumes.
    type Event;
    /// Failure the fold classifies as skip, halt, or poison.
    type Error;

    /// Folds one event into the state at a strictly increasing position.
    fn apply(
        &mut self,
        pos: Position,
        event: &Self::Event,
    ) -> Result<(), FoldError<Self::Error>>;
}
