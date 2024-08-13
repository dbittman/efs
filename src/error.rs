//! Interface for `efs` possible errors

use derive_more::derive::{Display, Error, From};

use crate::dev::error::DevError;
use crate::fs::error::FsError;
use crate::path::PathError;

/// Enumeration of possible sources of error
#[allow(clippy::error_impl_error)]
#[derive(Debug, Display, Error, From)]
#[display("Error: {_variant}")]
pub enum Error<E: core::error::Error> {
    /// Device error
    Device(DevError),

    /// Filesystem error
    Fs(FsError<E>),

    /// Path error
    Path(PathError),

    /// Standard I/O error
    #[cfg(feature = "std")]
    #[display("I/O Error: {_0}")]
    IO(std::io::Error),
}
