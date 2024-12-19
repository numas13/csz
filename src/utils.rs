use core::ffi::c_int;

use crate::ffi;

pub fn memchr(needle: u8, bytes: &[u8]) -> Option<usize> {
    let ptr = bytes.as_ptr().cast();
    match unsafe { ffi::memchr(ptr, needle as c_int, bytes.len()) } {
        p if p.is_null() => None,
        p => Some(unsafe { p.offset_from(ptr) as usize }),
    }
}
