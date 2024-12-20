use core::{
    cmp::Ordering,
    ffi::{c_char, CStr},
    fmt::{self, Write},
    marker::PhantomData,
    ptr, slice,
};

#[cfg(feature = "alloc")]
use alloc::ffi::CString;

use crate::{ffi, macros::const_assert_size_eq, utils::memchr, NulError};

/// Representaion of a borrowed C string.
///
/// # Examples
///
/// Use [cstr](crate::cstr) macro to create a `CStrThin` from a string literal:
///
/// ```
/// use csz::{CStrThin, cstr};
///
/// let s1 = CStrThin::from_bytes_until_nul(b"hello\0").unwrap();
/// let s2 = cstr!("hello");
/// assert_eq!(s1, s2);
/// ```
///
/// `CStrThin` can be used to pass C strings to FFI:
///
/// ```no_run
/// use csz::{CStrThin, cstr};
///
/// extern "C" {
///     fn func_c(s: Option<&CStrThin>); // same as *const c_char
/// }
///
/// unsafe {
///     func_c(Some(cstr!("hello C")));
/// }
/// ```
///
/// `CStrThin` can be used to receive C strings from FFI:
///
/// ```no_run
/// use csz::{CStrThin, cstr};
///
/// extern "C" fn func(s: Option<&CStrThin>) { // same as *const c_char
///     match s {
///         Some(s) => println!("s is {s:?}"),
///         None => println!("s is null :("),
///     }
/// }
/// ```
#[repr(transparent)]
pub struct CStrThin(c_char);

const_assert_size_eq!(c_char, u8);
const_assert_size_eq!(*const c_char, &CStrThin);
const_assert_size_eq!(*const c_char, Option<&CStrThin>);

impl CStrThin {
    /// Creates a `CStrThin` reference from a raw C string pointer.
    ///
    /// # Safety
    ///
    /// The pointer must be non-null and point to a valid C string with nul terminator.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use core::ffi::c_char;
    /// use csz::{CStrThin, cstr};
    ///
    /// extern "C" {
    ///     fn func_c() -> *const c_char;
    /// }
    ///
    /// let s = unsafe { CStrThin::from_ptr(func_c()) };
    /// assert_eq!(s.to_str().unwrap(), "hello");
    /// ```
    pub const unsafe fn from_ptr<'a>(ptr: *const c_char) -> &'a CStrThin {
        unsafe { &*(ptr as *const CStrThin) }
    }

    /// Returns the inner pointer to this C string.
    ///
    /// The returned pointer will be valid for as long as `self` is, and points to a contiguous
    /// region of memory terminated with a nul byte to represent the end of the string.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use core::ffi::c_char;
    /// use csz::cstr;
    ///
    /// extern "C" {
    ///     fn func_c(s: *const c_char);
    /// }
    ///
    /// unsafe {
    ///     func_c(cstr!("hello").as_ptr());
    /// }
    /// ```
    pub const fn as_ptr(&self) -> *const c_char {
        ptr::addr_of!(self.0)
    }

    /// Returns `true` if this C string has a length of 0.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let s = CStrThin::from_bytes_until_nul(b"\0").unwrap();
    /// assert!(s.is_empty());
    ///
    /// let s = CStrThin::from_bytes_until_nul(b"123\0").unwrap();
    /// assert!(!s.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }

    /// Calculate the length of a C string, excluding the nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"123456\0";
    /// let s = CStrThin::from_bytes_until_nul(bytes).unwrap();
    /// assert_eq!(bytes.len(), 7);
    /// assert_eq!(s.count_bytes(), 6);
    /// ```
    pub fn count_bytes(&self) -> usize {
        unsafe { ffi::strlen(self.as_ptr()) }
    }

    /// Iterates over the bytes in this C string, **without** the nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let bytes = cstr!("hello").bytes();
    /// assert!(bytes.eq(*b"hello"));
    /// ```
    pub fn bytes(&self) -> Bytes {
        Bytes::new(self)
    }

    /// Iterates over the bytes in this C string, **with** the nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let bytes = cstr!("hello").bytes_with_nul();
    /// assert!(bytes.eq(*b"hello\0"));
    /// ```
    pub fn bytes_with_nul(&self) -> BytesWithNul {
        BytesWithNul::new(self)
    }

    /// Converts this C string to a byte slice **without** nul terminator.
    ///
    /// This method will calculate the length of this C string to create a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"123456\0";
    /// let s = CStrThin::from_bytes_until_nul(bytes).unwrap();
    /// assert_eq!(s.to_bytes(), b"123456");
    /// ```
    pub fn to_bytes(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr().cast(), self.count_bytes()) }
    }

    /// Converts this C string to a byte slice **with** nul terminator.
    ///
    /// This method will calculate the length of this C string to create a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"123456\0";
    /// let s = CStrThin::from_bytes_until_nul(bytes).unwrap();
    /// assert_eq!(s.to_bytes_with_nul(), b"123456\0");
    /// ```
    pub fn to_bytes_with_nul(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr().cast(), self.count_bytes() + 1) }
    }

    /// Unsafely creates a `CStrThin` reference from a byte slice.
    ///
    /// # Safety
    ///
    /// The provided slice must contain at least one nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"foo\0bar\0";
    /// let s = unsafe { CStrThin::from_bytes_until_nul_unchecked(bytes) };
    /// assert_eq!(s.to_bytes(), b"foo");
    /// ```
    pub const unsafe fn from_bytes_until_nul_unchecked(bytes: &[u8]) -> &CStrThin {
        unsafe { Self::from_ptr(bytes.as_ptr().cast()) }
    }

    /// Creates a C string reference from a byte slice with at least one nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"hello\0 world\0";
    /// let s = CStrThin::from_bytes_until_nul(bytes).unwrap();
    /// assert_eq!(s.to_bytes(), b"hello");
    /// ```
    ///
    /// Creating a `CStrThin` without a trailing nul terminator is an error:
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"hello world";
    /// assert!(CStrThin::from_bytes_until_nul(bytes).is_err());
    /// ```
    pub fn from_bytes_until_nul(bytes: &[u8]) -> Result<&CStrThin, NulError> {
        memchr(0, bytes)
            .map(|_| unsafe { Self::from_bytes_until_nul_unchecked(bytes) })
            .ok_or(NulError(()))
    }

    /// Creates a C string reference from a byte slice with exactly one nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"hello world\0";
    /// let s = CStrThin::from_bytes_with_nul(bytes).unwrap();
    /// assert_eq!(s.to_bytes(), b"hello world");
    /// ```
    ///
    /// Creating a `CStrThin` without a trailing nul terminator is an error:
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"hello world";
    /// assert!(CStrThin::from_bytes_with_nul(bytes).is_err());
    /// ```
    ///
    /// Creating a `CStrThin` with an interior nul byte is an error:
    ///
    /// ```
    /// # use csz::CStrThin;
    /// let bytes = b"hello\0 world\0";
    /// assert!(CStrThin::from_bytes_with_nul(bytes).is_err());
    /// ```
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&CStrThin, NulError> {
        match memchr(b'\0', bytes) {
            Some(index) if index + 1 == bytes.len() => {
                Ok(unsafe { Self::from_bytes_until_nul_unchecked(bytes) })
            }
            _ => Err(NulError(())),
        }
    }

    /// Yields a <code>&[str]</code> slice if the `CStrThin` contains valid UTF-8.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let s = cstr!("foobar");
    /// assert_eq!(s.to_str(), Ok("foobar"));
    /// ```
    pub fn to_str(&self) -> Result<&str, core::str::Utf8Error> {
        core::str::from_utf8(self.to_bytes())
    }

    #[cfg(not(has_strcasecmp))]
    fn cmp_ignore_case_impl(&self, other: &Self) -> Ordering {
        let a = self.bytes_with_nul().map(|c| c.to_ascii_lowercase());
        let b = other.bytes_with_nul().map(|c| c.to_ascii_lowercase());
        core::iter::zip(a, b)
            .find_map(|(a, b)| match a.cmp(&b) {
                Ordering::Equal => None,
                x => Some(x),
            })
            .unwrap_or(Ordering::Equal)
    }

    #[cfg(has_strcasecmp)]
    fn cmp_ignore_case_impl(&self, other: &Self) -> Ordering {
        match unsafe { ffi::strcasecmp(self.as_ptr(), other.as_ptr()) } {
            x if x > 0 => Ordering::Greater,
            x if x < 0 => Ordering::Less,
            _ => Ordering::Equal,
        }
    }

    /// Compares two C strings ignoring case.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::cmp::Ordering;
    /// use csz::cstr;
    ///
    /// let s1 = cstr!("Hello");
    /// let s2 = cstr!("HELLO");
    /// assert_eq!(s1.cmp_ignore_case(s2), Ordering::Equal);
    /// ```
    pub fn cmp_ignore_case(&self, other: &Self) -> Ordering {
        self.cmp_ignore_case_impl(other)
    }

    /// Checks that two C strings are an case-insensitive match.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let s1 = cstr!("foobar");
    /// let s2 = cstr!("fooBAR");
    /// assert!(s1.eq_ignore_case(&s2));
    /// ```
    pub fn eq_ignore_case(&self, other: &Self) -> bool {
        self.cmp_ignore_case(other).is_eq()
    }

    /// Returns the byte index of the first character of this C string that matches the pattern.
    ///
    /// Returns [None] if the pattern doesn’t match.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let s = cstr!("C string is a sequence of nonzero bytes \
    /// followed by a byte with value zero");
    ///
    /// assert_eq!(s.find(cstr!("sequence")), Some(14));
    /// assert_eq!(s.find(cstr!("nonzero")), Some(26));
    /// assert_eq!(s.find(cstr!("value")), Some(64));
    /// ```
    pub fn find(&self, pat: &Self) -> Option<usize> {
        // TODO: add Pattern trait
        match unsafe { ffi::strstr(self.as_ptr(), pat.as_ptr()) } {
            p if p.is_null() => None,
            p => Some(unsafe { p.offset_from(self.as_ptr()) as usize }),
        }
    }

    /// Returns `true` if the given pattern matches a sub-string in this C string.
    ///
    /// Returns `false` if it does not.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let bananas = cstr!("bananas");
    ///
    /// assert!(bananas.contains(cstr!("nana")));
    /// assert!(!bananas.contains(cstr!("apples")));
    /// ```
    pub fn contains(&self, pat: &Self) -> bool {
        self.find(pat).is_some()
    }

    /// Returns `true` if the given pattern matches a prefix of this C string.
    ///
    /// Returns `false` if it does not.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::cstr;
    ///
    /// let bananas = cstr!("bananas");
    ///
    /// assert!(bananas.starts_with(cstr!("bana")));
    /// assert!(!bananas.starts_with(cstr!("nana")));
    /// ```
    pub fn starts_with(&self, pat: &Self) -> bool {
        matches!(self.find(pat), Some(0))
    }
}

impl Default for &CStrThin {
    fn default() -> Self {
        unsafe { CStrThin::from_ptr(b"\0".as_ptr().cast()) }
    }
}

impl PartialEq for CStrThin {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for CStrThin {}

impl PartialOrd for CStrThin {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for CStrThin {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        match unsafe { ffi::strcmp(self.as_ptr(), other.as_ptr()) } {
            x if x > 0 => Ordering::Greater,
            x if x < 0 => Ordering::Less,
            _ => Ordering::Equal,
        }
    }
}

impl From<&CStr> for &CStrThin {
    fn from(value: &CStr) -> Self {
        unsafe { CStrThin::from_ptr(value.as_ptr()) }
    }
}

impl From<&CStrThin> for &CStr {
    fn from(value: &CStrThin) -> Self {
        unsafe { CStr::from_ptr(value.as_ptr()) }
    }
}

#[cfg(feature = "alloc")]
impl From<&CString> for &CStrThin {
    fn from(value: &CString) -> Self {
        unsafe { CStrThin::from_ptr(value.as_ptr()) }
    }
}

#[cfg(feature = "alloc")]
impl From<&'_ CStrThin> for CString {
    fn from(value: &CStrThin) -> Self {
        unsafe { CString::from_vec_unchecked(value.to_bytes_with_nul().to_vec()) }
    }
}

impl AsRef<[u8]> for &CStrThin {
    fn as_ref(&self) -> &[u8] {
        self.to_bytes()
    }
}

impl fmt::Display for CStrThin {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        for byte in self.bytes() {
            char::from(byte).fmt(fmt)?;
        }
        Ok(())
    }
}

impl fmt::Debug for CStrThin {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.write_char('"')?;
        for byte in self.bytes() {
            fmt::Display::fmt(&char::from(byte).escape_debug(), fmt)?;
        }
        fmt.write_char('"')
    }
}

/// An iterator over the bytes of a [CStrThin], without the nul terminator.
///
/// This struct is created by the [bytes](CStrThin::bytes) method on [CStrThin].
/// See its documentation for more.
pub struct Bytes<'a> {
    ptr: *const c_char,
    phantom: PhantomData<&'a CStrThin>,
}

impl Bytes<'_> {
    const fn new(s: &CStrThin) -> Self {
        Self {
            ptr: s.as_ptr(),
            phantom: PhantomData,
        }
    }
}

impl Iterator for Bytes<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match unsafe { self.ptr.read() } {
            0 => None,
            c => {
                self.ptr = unsafe { self.ptr.add(1) };
                Some(c as u8)
            }
        }
    }
}

/// An iterator over the bytes of a [CStrThin], with the nul terminator.
///
/// This struct is created by the [bytes_with_nul](CStrThin::bytes_with_nul) method on [CStrThin].
/// See its documentation for more.
pub struct BytesWithNul<'a> {
    ptr: *const c_char,
    phantom: PhantomData<&'a CStrThin>,
}

impl BytesWithNul<'_> {
    const fn new(s: &CStrThin) -> Self {
        Self {
            ptr: s.as_ptr(),
            phantom: PhantomData,
        }
    }
}

impl Iterator for BytesWithNul<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ptr.is_null() {
            return None;
        }
        match unsafe { self.ptr.read() } {
            0 => {
                self.ptr = ptr::null();
                Some(b'\0')
            }
            c => {
                self.ptr = unsafe { self.ptr.add(1) };
                Some(c as u8)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::cstr;

    #[test]
    fn to_bytes() {
        let s = unsafe { CStrThin::from_bytes_until_nul_unchecked(b"123abc\0") };
        assert_eq!(s.to_bytes(), b"123abc");
        assert_eq!(s.to_bytes_with_nul(), b"123abc\0");
    }

    #[test]
    fn display() {
        let s1 = format!("{}", cstr!("foo\x1b123"));
        let s2 = format!("{}", "foo\x1b123");
        assert_eq!(s1, s2);
    }

    #[test]
    fn debug() {
        let s1 = format!("{:?}", cstr!("foo\x1b123"));
        let s2 = format!("{:?}", "foo\x1b123");
        assert_eq!(s1, s2);
    }
}
