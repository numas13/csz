#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(all(doc, docsrs), feature(doc_cfg))]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(missing_docs)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(test)]
extern crate std;

mod array;
mod boxed;
mod cursor;
mod ext_cstr;
mod ffi;
mod macros;
mod slice;
mod thin;
mod utils;

pub use crate::{array::*, boxed::*, cursor::*, ext_cstr::*, slice::*, thin::*};

/// An error indicating that no nul byte was present or that a byte slice contains interior nul
/// bytes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct NulError(());
