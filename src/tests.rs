//! Utilities for tests in the whole crate.

use std::fs::File;
use std::io::copy;
use std::path::Path;
use std::string::ToString;
use std::sync::atomic::{AtomicU32, Ordering};
use std::{print, println};

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
///
/// # Errors
///
/// Returns a [`Error::IO`] error if the given file could not be opened or copied to a temporary file.
pub fn copy_file<P: AsRef<Path> + ToString>(path: P) -> Result<File, Error<!>> {
    let mut real_file = File::open(path)?;
    let mut temp_file = tempfile()?;
    copy(&mut real_file, &mut temp_file)?;
    Ok(temp_file)
}

/// Trait that every tested function implement.
pub trait Testable {
    /// Run the function with a pretty printing.
    fn run(&self);
}

impl<T: Fn()> Testable for T {
    #[inline]
    fn run(&self) {
        print!("{:.<90}", core::any::type_name::<T>());
        self();
        println!("[ok]");
    }
}

/// Custom runner for tests.
pub fn runner(tests: &[&dyn Testable]) {
    println!("Running {} tests", tests.len());

    for test in tests {
        test.run();
    }
}
