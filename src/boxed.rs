use core::{
    cmp::Ordering,
    ffi::c_char,
    fmt, mem,
    ops::Deref,
    ptr::{self, NonNull},
};

use crate::{ffi, macros::const_assert_size_eq, utils::memchr, CStr, NulError};

/// An owned C string allocated using `malloc`.
///
/// # Examples
///
/// ```
/// use csz::{CStrBox, cstr};
///
/// extern "C" {
///     fn puts(s: Option<&CStrBox>); // same as *const c_char
/// }
///
/// let mut s = CStrBox::from(cstr!("string"));
/// s.push_c_str(cstr!(" in heap"));
/// assert_eq!(s.as_c_str(), cstr!("string in heap"));
/// unsafe {
///     puts(Some(&s));
/// }
/// ```
#[repr(transparent)]
pub struct CStrBox {
    ptr: NonNull<c_char>,
}

const_assert_size_eq!(*const c_char, CStrBox);
const_assert_size_eq!(*const c_char, Option<CStrBox>);

impl CStrBox {
    /// Creates a new `CStrBox`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// let s = CStrBox::new();
    /// ```
    pub fn new() -> CStrBox {
        unsafe {
            let ptr = ffi::malloc(1) as *mut c_char;
            *ptr = 0;
            Self {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    /// Consumes the `CStrBox`, returning a wrapped raw pointer.
    ///
    /// The pointer will be non-null.
    ///
    /// The pointer must be freed with `free` function from libc.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// extern "C" {
    ///     fn free(s: *mut u8);
    /// }
    /// let s = CStrBox::try_from("foobar").unwrap();
    /// unsafe {
    ///     let ptr = CStrBox::into_raw(s);
    ///     free(ptr.cast());
    /// }
    /// ```
    pub fn into_raw(b: CStrBox) -> *mut c_char {
        let ptr = b.ptr.as_ptr();
        mem::forget(b);
        ptr
    }

    /// Constructs a `CStrBox` from a raw pointer.
    ///
    /// # Safety
    ///
    /// The pointer must be allocated with `malloc/calloc` funcstions from libc or
    /// [CStrBox::into_raw] method.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// extern "C" {
    ///     fn malloc(size: usize) -> *mut u8;
    /// }
    ///
    /// unsafe {
    ///     let bytes = b"hello\0";
    ///     let ptr = malloc(bytes.len()) as *mut u8;
    ///     for (i, &c) in bytes.iter().enumerate() {
    ///         ptr.add(i).write(c);
    ///     }
    ///     let s = CStrBox::from_raw(ptr.cast());
    /// }
    /// ```
    pub const unsafe fn from_raw(ptr: *mut c_char) -> Self {
        Self {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    /// Creates a `CStrBox` from a byte slice.
    ///
    /// # Safety
    ///
    /// The byte slice must not contain nul bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// let s = unsafe { CStrBox::from_bytes_unchecked(b"foobar") };
    /// assert_eq!(s.to_bytes(), b"foobar");
    /// ```
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        unsafe {
            let ptr = ffi::malloc(bytes.len() + 1).cast::<c_char>();
            assert!(!ptr.is_null());
            ptr::copy_nonoverlapping(bytes.as_ptr().cast(), ptr, bytes.len());
            *ptr.add(bytes.len()) = 0;
            Self::from_raw(ptr)
        }
    }

    /// Creates a `CStrBox` from a byte slice.
    ///
    /// # Safety
    ///
    /// The byte slice must ends with a nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// let s = unsafe { CStrBox::from_bytes_with_nul_unchecked(b"foobar\0") };
    /// assert_eq!(s.to_bytes(), b"foobar");
    /// ```
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> Self {
        unsafe {
            let ptr = ffi::malloc(bytes.len()).cast::<c_char>();
            assert!(!ptr.is_null());
            ptr::copy_nonoverlapping(bytes.as_ptr().cast(), ptr, bytes.len());
            Self::from_raw(ptr)
        }
    }

    /// Returns a C string reference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// let s = CStrBox::try_from("hello").unwrap();
    /// assert_eq!(s.as_c_str().to_bytes(), b"hello");
    /// ```
    pub const fn as_c_str(&self) -> &CStr {
        unsafe { CStr::from_ptr(self.ptr.as_ptr()) }
    }

    /// Allocate space and copy a byte slice to the end of this string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrBox;
    /// let mut s = CStrBox::new();
    /// s.push_bytes(b"foo");
    /// s.push_bytes(b"123");
    /// assert_eq!(s.to_bytes(), b"foo123");
    /// ```
    ///
    /// Pushing a byte slice with nul bytes is an error:
    ///
    /// ```
    /// # use csz::CStrBox;
    /// let mut s = CStrBox::new();
    /// assert!(s.push_bytes(b"hello\0world").is_err());
    /// ```
    pub fn push_bytes<T: AsRef<[u8]>>(&mut self, bytes: T) -> Result<(), NulError> {
        let bytes = bytes.as_ref();
        match memchr(b'\0', bytes) {
            Some(_) => Err(NulError(())),
            None => {
                let len = self.count_bytes();
                let new_len = len + bytes.len() + 1;
                unsafe {
                    let ptr = ffi::realloc(self.ptr.as_ptr().cast(), new_len).cast::<c_char>();
                    assert!(!ptr.is_null());
                    ptr::copy_nonoverlapping(bytes.as_ptr().cast(), ptr.add(len), bytes.len());
                    *ptr.add(new_len) = 0;
                    self.ptr = NonNull::new_unchecked(ptr);
                }
                Ok(())
            }
        }
    }

    /// Allocate space and copy a string slice to the end of this string.
    ///
    /// See documentation for [CStrBox::push_bytes].
    pub fn push_str(&mut self, s: &str) -> Result<(), NulError> {
        self.push_bytes(s.as_bytes())
    }

    /// Allocate space and copy a C string to the end of this string.
    ///
    /// See documentation for [CStrBox::push_bytes].
    pub fn push_c_str(&mut self, s: &CStr) -> Result<(), NulError> {
        self.push_bytes(s.to_bytes())
    }
}

impl Default for CStrBox {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for CStrBox {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        unsafe { CStr::from_ptr(self.ptr.as_ptr()) }
    }
}

impl From<&CStr> for CStrBox {
    fn from(value: &CStr) -> Self {
        unsafe { Self::from_bytes_unchecked(value.to_bytes_with_nul()) }
    }
}

impl TryFrom<&str> for CStrBox {
    type Error = NulError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match memchr(b'\0', value.as_bytes()) {
            Some(_) => Err(NulError(())),
            None => Ok(unsafe { Self::from_bytes_unchecked(value.as_bytes()) }),
        }
    }
}

impl Drop for CStrBox {
    fn drop(&mut self) {
        unsafe {
            ffi::free(self.ptr.as_ptr().cast());
        }
    }
}

impl fmt::Display for CStrBox {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_c_str(), fmt)
    }
}

impl fmt::Debug for CStrBox {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_c_str(), fmt)
    }
}

impl Eq for CStrBox {}

impl PartialEq for CStrBox {
    fn eq(&self, other: &Self) -> bool {
        self.as_c_str().eq(other.as_c_str())
    }
}

impl PartialEq<CStr> for CStrBox {
    fn eq(&self, other: &CStr) -> bool {
        self.as_c_str().eq(other)
    }
}

impl PartialEq<CStrBox> for CStr {
    fn eq(&self, other: &CStrBox) -> bool {
        self.eq(other.as_c_str())
    }
}

impl PartialOrd for CStrBox {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<CStr> for CStrBox {
    fn partial_cmp(&self, other: &CStr) -> Option<Ordering> {
        Some(self.as_c_str().cmp(other))
    }
}

impl PartialOrd<CStrBox> for CStr {
    fn partial_cmp(&self, other: &CStrBox) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

impl Ord for CStrBox {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_c_str().cmp(other.as_c_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::cstr;

    #[test]
    fn from_cstr() {
        let s = cstr!("foobar");
        let b = CStrBox::from(s);
        assert_eq!(&*b, s);
    }

    #[test]
    fn from_str() {
        let s = "abc123";
        let b = CStrBox::try_from(s).unwrap();
        assert_eq!(b.to_str(), Ok(s));
    }

    #[test]
    fn display() {
        let s = CStrBox::try_from("hello").unwrap();
        let s = format!("{s}");
        assert_eq!(s, "hello");
    }

    #[test]
    fn debug() {
        let s = CStrBox::try_from("hello").unwrap();
        let s = format!("{s:?}");
        assert_eq!(s, "\"hello\"");
    }

    #[test]
    fn cmp() {
        let s1 = CStrBox::try_from("foobar").unwrap();
        let s2 = CStrBox::try_from("foobar").unwrap();
        let s3 = CStr::from_bytes_with_nul(b"foobar\0").unwrap();

        assert!(s1 == s2);
        assert!(s1 == *s3);
        assert!(s2 == s1);
        assert!(!(s1 < s2));
        assert!(!(s1 < *s3));
        assert!(!(s2 < s1));
    }
}
