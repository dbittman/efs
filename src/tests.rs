//! Utilities for tests in the whole crate.

use std::fs::File;
use std::io::copy;
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering};

use spin::Lazy;
use tempfile::tempfile;

use crate::error::Error;

/// Stores the next unique device id returned by [`new_device_id`].
static DEVICE_ID: Lazy<AtomicU32> = Lazy::new(AtomicU32::default);

/// Returns a new unique device ID (useful for tests).
pub fn new_device_id() -> u32 {
    DEVICE_ID.fetch_add(1, Ordering::Relaxed)
}

/// Copies the file at the given path and returns a temporary file with the same content.
pub fn copy_file<P: AsRef<Path>>(path: P) -> Result<File, Error<!>> {
    let mut real_file = File::open(path).map_err(Error::IO)?;
    let mut temp_file = tempfile().map_err(Error::IO)?;
    copy(&mut real_file, &mut temp_file).map_err(Error::IO)?;
    Ok(temp_file)
}
