//! Extended fs.
//!
//! An OS and architecture independent implementation of some Unix filesystems in Rust.

#![no_std]
#![allow(
    clippy::absolute_paths,
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::else_if_without_else,
    clippy::exhaustive_enums,
    clippy::exhaustive_structs,
    clippy::expect_used,
    clippy::implicit_return,
    clippy::integer_division,
    clippy::missing_trait_methods,
    clippy::mod_module_files,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::pattern_type_mismatch,
    clippy::pub_with_shorthand,
    clippy::question_mark_used,
    clippy::separated_literal_suffix,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::todo,
    clippy::unreachable,
    clippy::use_debug,
    clippy::unwrap_in_result,
    clippy::wildcard_in_or_patterns
)]
#![cfg_attr(
    test,
    allow(
        clippy::assertions_on_result_states,
        clippy::collection_is_never_read,
        clippy::enum_glob_use,
        clippy::indexing_slicing,
        clippy::non_ascii_literal,
        clippy::too_many_lines,
        clippy::undocumented_unsafe_blocks,
        clippy::unwrap_used,
        clippy::wildcard_imports
    )
)]
#![feature(const_mut_refs)]
#![feature(error_in_core)]
#![feature(exact_size_is_empty)]
#![feature(let_chains)]
#![feature(step_trait)]

extern crate alloc;
extern crate core;
#[cfg(any(feature = "std", test))]
extern crate std;

pub mod dev;
pub mod error;
pub mod file;
pub mod fs;
pub mod io;
pub mod path;
pub mod permissions;
pub mod types;
