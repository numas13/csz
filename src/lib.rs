//! Safer wrappers for nul-terminated C strings.

#![cfg_attr(not(test), no_std)]
#![deny(unsafe_op_in_unsafe_fn)]

#[cfg(feature = "alloc")]
extern crate alloc;

mod array;
mod boxed;
mod cursor;
mod ext_cstr;
mod ffi;
mod macros;
mod thin;
mod utils;

pub use crate::{array::*, boxed::*, cursor::*, ext_cstr::*, thin::*};

/// An error indicating that no nul byte was present or that a byte slice contains interior nul
/// bytes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NulError(());
