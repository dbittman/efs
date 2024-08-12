//! Errors related to device manipulation.

use derive_more::derive::{Display, Error};

/// Enumeration of possible errors encountered with device's manipulation.
#[allow(clippy::module_name_repetitions)]
#[derive(Debug, PartialEq, Eq, Display, Error)]
#[display("Device Error: {_variant}")]
pub enum DevError {
    /// `OutOfBounds(structure, value, (lower_bound, upper_bound))`: the given `struct` has a `value`  not between the given
    /// bounds.
    #[display("Out of Bounds: the {_0} has a value {_1} not between the lower bound {} and the upper bound {}", _2.0, _2.1)]
    OutOfBounds(&'static str, i128, (i128, i128)),

    /// An error returned when an operation could not be completed because an “end of file” was reached prematurely.
    ///
    /// This typically means that an operation could only succeed if it read a particular number of bytes but only a smaller number
    /// of bytes could be read.
    #[display("Unexpected End of File: an operation could not be completed because an \"end of file\" was reached prematurely")]
    UnexpectedEof,

    /// An error returned when an operation could not be completed because a call to [`write`](crate::io::Write::write) returned
    /// `Ok(0)`.
    #[display("Write Zero: An error returned when an operation could not be completed because a call to write returned Ok(0)")]
    WriteZero,
}
