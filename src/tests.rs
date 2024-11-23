//! Utilities for tests in the whole crate.

use alloc::string::String;
use std::format;
use std::fs::File;
use std::io::copy;
use std::process::Command;
use std::sync::atomic::{AtomicU32, Ordering};

use spin::Lazy;

use crate::error::Error;

/// Stores the next unique device id returned by [`new_device_id`].
static DEVICE_ID: Lazy<AtomicU32> = Lazy::new(AtomicU32::default);

/// Returns a new unique device ID (useful for tests).
pub fn new_device_id() -> u32 {
    DEVICE_ID.fetch_add(1, Ordering::Relaxed)
}

/// Stores the next unique file id returned by [`new_file_id`].
static FILE_ID: Lazy<AtomicU32> = Lazy::new(AtomicU32::default);

/// Returns a new unique file ID (useful for tests).
pub fn new_file_id() -> u32 {
    FILE_ID.fetch_add(1, Ordering::Relaxed)
}

/// Copies the file at the given path and returns a temporary file with the same content.
///
/// # Errors
///
/// Returns a [`Error::IO`] error if the given file could not be opened or copied to a temporary file.
pub fn copy_file(path: &str) -> Result<String, Error<!>> {
    let mut real_file = File::open(path)?;
    let temp_file_name = format!("{path}_{}", new_file_id());
    let mut temp_file = File::create(&temp_file_name)?;
    copy(&mut real_file, &mut temp_file)?;
    Ok(temp_file_name)
}

/// Enumeration of possible post-checks.
#[derive(Debug, PartialEq, Eq)]
pub enum PostCheck {
    /// Runs a post-check for the ext family.
    ///
    /// Precisely, this will run `e2fsck -fvn <file>`.
    Ext,

    /// Runs no post-check.
    None,
}

impl PostCheck {
    pub fn run(self, file_path: &str) -> Result<(), Error<std::io::Error>> {
        match self {
            Self::Ext => {
                let output = Command::new("e2fsck").arg("-f").arg("-v").arg("-n").arg(file_path).output()?;

                if output.status.success() {
                    Ok(())
                } else {
                    Err(Error::IO(
                        String::from_utf8(output.stdout).expect("Could not convert e2fsck stderr to a valid UTF-8 string"),
                    ))
                }
            },
            Self::None => Ok(()),
        }
    }
}

/// Produces a new function that will be tested from a function whose arguments depend on the type of the test.
macro_rules! generate_fs_test {
    ($func_name:ident, $input_file:tt) => {
        generate_fs_test!($func_name, $input_file, crate::tests::PostCheck::None);
    };
    ($func_name:ident, $input_file:tt, $post_check:expr) => {
        #[test]
        fn $func_name() {
            let file_name = crate::tests::copy_file($input_file).unwrap();
            let file = std::fs::OpenOptions::new().read(true).write(true).open(&file_name).unwrap();
            super::$func_name(file);
            match $post_check.run(&file_name) {
                Ok(()) => {
                    std::fs::remove_file(&file_name).unwrap();
                },
                Err(err) => {
                    std::fs::remove_file(&file_name).unwrap();
                    panic!("Post Check Error: {err}");
                },
            }
        }
    };
}

pub(crate) use generate_fs_test;
