//! Safer wrappers for nul-terminated C strings.

#![cfg_attr(not(test), no_std)]
#![cfg_attr(all(doc, has_doc_auto_cfg), feature(doc_auto_cfg))]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod array;
mod cursor;
mod ffi;
mod macros;
mod thin;
mod utils;

pub use crate::{array::*, cursor::*, thin::*};

/// An error indicating that no nul byte was present or that a byte slice contains interior nul
/// bytes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NulError(());
