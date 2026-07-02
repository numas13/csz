use core::{
    borrow::Borrow,
    cmp::Ordering,
    ffi::{c_char, CStr},
    fmt,
    hash::{Hash, Hasher},
    mem,
    ops::Deref,
    ptr::{self, NonNull},
};

#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;

use crate::{ffi, macros::const_assert_size_eq, utils::memchr, CStrArray, CStrThin, NulError};

/// An owned C string allocated using C `malloc`.
///
/// # Examples
///
/// ```
/// use csz::{CStringThin, cstr};
///
/// // same as *const c_char
/// unsafe extern "C" fn take_ownership(s: Option<CStringThin>) {}
///
/// let mut s = CStringThin::from(cstr!("string"));
/// s.push_c_str(cstr!(" in heap"));
/// assert_eq!(s.as_c_str(), cstr!("string in heap"));
/// unsafe {
///     take_ownership(Some(s));
/// }
/// ```
#[repr(transparent)]
pub struct CStringThin {
    ptr: NonNull<c_char>,
}

const_assert_size_eq!(*const c_char, CStringThin);
const_assert_size_eq!(*const c_char, Option<CStringThin>);

impl CStringThin {
    /// Creates a new `CStringThin`.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStringThin;
    ///
    /// let s = CStringThin::new();
    /// assert_eq!(s.to_bytes(), b"");
    /// ```
    pub fn new() -> CStringThin {
        unsafe {
            let ptr = ffi::malloc(1) as *mut c_char;
            *ptr = 0;
            Self {
                ptr: NonNull::new_unchecked(ptr),
            }
        }
    }

    /// Consumes the `CStringThin`, returning a wrapped raw pointer.
    ///
    /// The pointer will be non-null.
    ///
    /// The pointer must be freed with `free` function from libc.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStringThin;
    ///
    /// extern "C" {
    ///     fn free(s: *mut u8);
    /// }
    /// let s = CStringThin::try_from("foobar").unwrap();
    /// unsafe {
    ///     let ptr = CStringThin::into_raw(s);
    ///     free(ptr.cast());
    /// }
    /// ```
    pub fn into_raw(b: CStringThin) -> *mut c_char {
        let ptr = b.ptr.as_ptr();
        mem::forget(b);
        ptr
    }

    /// Constructs a `CStringThin` from a raw pointer.
    ///
    /// # Safety
    ///
    /// The pointer must be allocated with `malloc/calloc` functions from libc or
    /// [CStringThin::into_raw] method.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStringThin;
    ///
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
    ///     let s = CStringThin::from_raw(ptr.cast());
    /// }
    /// ```
    pub const unsafe fn from_raw(ptr: *mut c_char) -> Self {
        Self {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }

    /// Creates a `CStringThin` from a byte slice.
    ///
    /// # Safety
    ///
    /// The byte slice must not contain nul bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStringThin;
    ///
    /// let s = unsafe { CStringThin::from_bytes_unchecked(b"foobar") };
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

    /// Creates a `CStringThin` from a byte slice.
    ///
    /// # Safety
    ///
    /// The byte slice must ends with a nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStringThin;
    ///
    /// let s = unsafe { CStringThin::from_bytes_with_nul_unchecked(b"foobar\0") };
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
    /// use csz::CStringThin;
    ///
    /// let s = CStringThin::try_from("hello").unwrap();
    /// assert_eq!(s.as_c_str().to_bytes(), b"hello");
    /// ```
    pub const fn as_c_str(&self) -> &CStrThin {
        unsafe { CStrThin::from_ptr(self.ptr.as_ptr()) }
    }

    /// Allocate space and copy a byte slice to the end of this string.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStringThin;
    ///
    /// let mut s = CStringThin::new();
    /// s.push_bytes(b"foo");
    /// s.push_bytes(b"123");
    /// assert_eq!(s.to_bytes(), b"foo123");
    /// ```
    ///
    /// Pushing a byte slice with nul bytes is an error:
    ///
    /// ```
    /// use csz::CStringThin;
    ///
    /// let mut s = CStringThin::new();
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
                    *ptr.add(new_len - 1) = 0;
                    self.ptr = NonNull::new_unchecked(ptr);
                }
                Ok(())
            }
        }
    }

    /// Allocate space and copy a string slice to the end of this string.
    ///
    /// See documentation for [CStringThin::push_bytes].
    pub fn push_str(&mut self, s: &str) -> Result<(), NulError> {
        self.push_bytes(s.as_bytes())
    }

    /// Allocate space and copy a C string to the end of this string.
    ///
    /// See documentation for [CStringThin::push_bytes].
    pub fn push_c_str(&mut self, s: &CStrThin) -> Result<(), NulError> {
        self.push_bytes(s.to_bytes())
    }
}

impl Default for CStringThin {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for CStringThin {
    type Target = CStrThin;

    fn deref(&self) -> &Self::Target {
        unsafe { CStrThin::from_ptr(self.ptr.as_ptr()) }
    }
}

impl AsRef<CStrThin> for CStringThin {
    fn as_ref(&self) -> &CStrThin {
        self
    }
}

impl From<&CStrThin> for CStringThin {
    fn from(value: &CStrThin) -> Self {
        unsafe { Self::from_bytes_with_nul_unchecked(value.to_bytes_with_nul()) }
    }
}

impl From<&CStr> for CStringThin {
    fn from(value: &CStr) -> Self {
        unsafe { Self::from_bytes_with_nul_unchecked(value.to_bytes_with_nul()) }
    }
}

impl TryFrom<&str> for CStringThin {
    type Error = NulError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match memchr(b'\0', value.as_bytes()) {
            Some(_) => Err(NulError(())),
            None => Ok(unsafe { Self::from_bytes_unchecked(value.as_bytes()) }),
        }
    }
}

impl Drop for CStringThin {
    fn drop(&mut self) {
        unsafe {
            ffi::free(self.ptr.as_ptr().cast());
        }
    }
}

impl fmt::Display for CStringThin {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_c_str(), fmt)
    }
}

impl fmt::Debug for CStringThin {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_c_str(), fmt)
    }
}

impl Eq for CStringThin {}

impl PartialEq for CStringThin {
    fn eq(&self, other: &Self) -> bool {
        self.as_c_str().eq(other.as_c_str())
    }
}

impl PartialEq<CStrThin> for CStringThin {
    fn eq(&self, other: &CStrThin) -> bool {
        self.as_c_str().eq(other)
    }
}

impl PartialEq<CStringThin> for CStrThin {
    fn eq(&self, other: &CStringThin) -> bool {
        self.eq(other.as_c_str())
    }
}

impl<const N: usize> From<&'_ CStrArray<N>> for CStringThin {
    fn from(value: &CStrArray<N>) -> Self {
        CStringThin::from(value.as_thin())
    }
}

impl PartialEq<CStr> for CStringThin {
    fn eq(&self, other: &CStr) -> bool {
        self.as_c_str().eq(<&CStrThin>::from(other))
    }
}

impl PartialEq<CStringThin> for CStr {
    fn eq(&self, other: &CStringThin) -> bool {
        <&CStrThin>::from(self).eq(other)
    }
}

impl PartialOrd for CStringThin {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<CStrThin> for CStringThin {
    fn partial_cmp(&self, other: &CStrThin) -> Option<Ordering> {
        Some(self.as_c_str().cmp(other))
    }
}

impl PartialOrd<CStringThin> for CStrThin {
    fn partial_cmp(&self, other: &CStringThin) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<CStr> for CStringThin {
    fn partial_cmp(&self, other: &CStr) -> Option<Ordering> {
        Some(self.as_c_str().cmp(<&CStrThin>::from(other)))
    }
}

impl PartialOrd<CStringThin> for CStr {
    fn partial_cmp(&self, other: &CStringThin) -> Option<Ordering> {
        Some(<&CStrThin>::from(self).cmp(other.as_c_str()))
    }
}

impl Ord for CStringThin {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_c_str().cmp(other.as_c_str())
    }
}

impl Borrow<CStrThin> for CStringThin {
    fn borrow(&self) -> &CStrThin {
        self.as_c_str()
    }
}

impl Hash for CStringThin {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes().for_each(|i| i.hash(state));
    }
}

#[cfg(feature = "alloc")]
impl ToOwned for CStrThin {
    type Owned = CStringThin;

    fn to_owned(&self) -> Self::Owned {
        self.into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::format;

    use crate::cstr;

    #[test]
    fn from_cstr() {
        let s = cstr!("foobar");
        let b = CStringThin::from(s);
        assert_eq!(&*b, s);
    }

    #[test]
    fn from_str() {
        let s = "abc123";
        let b = CStringThin::try_from(s).unwrap();
        assert_eq!(b.to_str(), Ok(s));
    }

    #[test]
    fn display() {
        let s = CStringThin::try_from("hello").unwrap();
        let s = format!("{s}");
        assert_eq!(s, "hello");
    }

    #[test]
    fn debug() {
        let s = CStringThin::try_from("hello").unwrap();
        let s = format!("{s:?}");
        assert_eq!(s, "\"hello\"");
    }

    #[test]
    fn cmp() {
        let s1 = CStringThin::try_from("foobar").unwrap();
        let s2 = CStringThin::try_from("foobar").unwrap();
        let s3 = CStrThin::from_bytes_with_nul(b"foobar\0").unwrap();

        assert!(s1 == s2);
        assert!(s1 == *s3);
        assert!(s2 == s1);
        assert!(s1 >= s2);
        assert!(s1 >= *s3);
        assert!(s2 >= s1);
    }

    #[test]
    fn borrow() {
        let b = CStringThin::try_from("123abc").unwrap();
        let s: &CStrThin = b.borrow();
        assert_eq!(s.to_bytes(), b"123abc");
    }

    #[test]
    fn hash() {
        fn hash<T: Hash>(t: &T) -> u64 {
            use std::collections::hash_map::DefaultHasher;
            let mut s = DefaultHasher::new();
            t.hash(&mut s);
            s.finish()
        }

        let s1 = CStringThin::try_from("foobar").unwrap();
        let s2 = CStrThin::from_bytes_with_nul(b"foobar\0").unwrap();

        assert_eq!(hash(&s1), hash(&s2));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn to_owned() {
        let s = cstr!("hello");
        let _: crate::CStringThin = s.to_owned();
    }
}
