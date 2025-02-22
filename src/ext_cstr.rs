use core::{cmp::Ordering, ffi::CStr};

use crate::CStrThin;

/// Extends [CStr] with extra methods.
pub trait CStrExt {
    /// Compares two C strings ignoring case.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::{cmp::Ordering, ffi::CStr};
    /// use csz::CStrExt;
    ///
    /// let s1 = CStr::from_bytes_with_nul(b"Hello\0").unwrap();
    /// let s2 = CStr::from_bytes_with_nul(b"HELLO\0").unwrap();
    /// assert_eq!(s1.cmp_ignore_case(s2), Ordering::Equal);
    /// ```
    fn cmp_ignore_case(&self, other: &CStr) -> Ordering;

    /// Checks that two C strings are an case-insensitive match.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ffi::CStr;
    /// use csz::CStrExt;
    ///
    /// let s1 = CStr::from_bytes_with_nul(b"foobar\0").unwrap();
    /// let s2 = CStr::from_bytes_with_nul(b"fooBAR\0").unwrap();
    /// assert!(s1.eq_ignore_case(&s2));
    /// ```
    fn eq_ignore_case(&self, other: &CStr) -> bool {
        self.cmp_ignore_case(other).is_eq()
    }
}

impl CStrExt for CStr {
    fn cmp_ignore_case(&self, other: &CStr) -> Ordering {
        <&CStrThin>::from(self).cmp_ignore_case(other.into())
    }
}
