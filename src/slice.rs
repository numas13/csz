use core::{
    borrow::Borrow,
    cmp::Ordering,
    ffi::{c_char, CStr},
    fmt,
    hash::{Hash, Hasher},
    mem,
    ops::Deref,
    ptr,
};

use crate::{macros::const_assert_size_eq, utils::memchr, CStrThin, Cursor, NulError};

/// Representation of a borrowed C string in a byte slice.
///
/// # Examples
///
/// ```
/// use csz::CStrSlice;
///
/// let mut buf = [0; 64];
/// let mut s = CStrSlice::new_in(&mut buf);
/// let mut c = s.cursor();
/// c.write_str("hello").unwrap();
/// c.write_str(" world").unwrap();
/// c.finish();
/// assert_eq!(s.to_bytes_with_nul(), b"hello world\0");
/// s.clear();
/// assert_eq!(s.to_bytes_with_nul(), b"\0");
/// ```
#[repr(transparent)]
pub struct CStrSlice {
    bytes: [u8],
}

const_assert_size_eq!(c_char, u8);
const_assert_size_eq!(&[c_char], &CStrSlice);

impl CStrSlice {
    /// Creates a mutable reference to `CStrSlice` from a byte slice and clears it.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut bytes = [0; 32];
    /// bytes[..4].copy_from_slice(b"abc\0");
    /// let s = CStrSlice::new_in(&mut bytes);
    /// assert!(s.is_empty());
    /// assert_eq!(s.capacity(), 32);
    /// ```
    pub fn new_in(bytes: &mut [u8]) -> &mut CStrSlice {
        let s = unsafe { Self::from_bytes_unchecked_mut(bytes) };
        s.clear();
        s
    }

    /// Creates a reference to `CStrSlice` from a byte slice.
    ///
    /// # Safety
    ///
    /// The given slice must contain at least one nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut bytes = [0; 16];
    /// bytes[..4].copy_from_slice(b"abc\0");
    /// let s = unsafe { CStrSlice::from_bytes_unchecked(&bytes) };
    /// assert_eq!(s.to_bytes(), b"abc");
    /// assert_eq!(s.capacity(), 16);
    /// ```
    pub const unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &CStrSlice {
        unsafe { mem::transmute(bytes) }
    }

    /// Same as [CStrSlice::from_bytes_unchecked] but with a mutable reference.
    ///
    /// # Safety
    ///
    /// See [CStrSlice::from_bytes_unchecked].
    pub unsafe fn from_bytes_unchecked_mut(bytes: &mut [u8]) -> &mut CStrSlice {
        unsafe { mem::transmute(bytes) }
    }

    /// Creates a reference to `CStrSlice` from a byte slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut bytes = [0; 128];
    /// bytes[..7].copy_from_slice(b"foobar\0");
    /// let s = CStrSlice::from_bytes(&bytes).unwrap();
    /// assert_eq!(s.to_bytes(), b"foobar");
    /// assert_eq!(s.capacity(), 128);
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<&CStrSlice, NulError> {
        match memchr(b'\0', bytes) {
            Some(_) => Ok(unsafe { Self::from_bytes_unchecked(bytes) }),
            None => Err(NulError(())),
        }
    }

    /// Same as [CStrSlice::from_bytes] but with a mutable reference.
    pub fn from_bytes_mut(bytes: &mut [u8]) -> Result<&mut CStrSlice, NulError> {
        match memchr(b'\0', bytes) {
            Some(_) => Ok(unsafe { Self::from_bytes_unchecked_mut(bytes) }),
            None => Err(NulError(())),
        }
    }

    /// Creates a `CStrSlice` string reference from a byte slice with exactly one nul terminator.
    ///
    /// See [CStrThin::from_bytes_with_nul] for examples.
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<&CStrSlice, NulError> {
        CStrThin::from_bytes_with_nul(bytes)?;
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Same as [CStrSlice::from_bytes_with_nul] but with a mutable reference.
    pub fn from_bytes_with_nul_mut(bytes: &mut [u8]) -> Result<&mut CStrSlice, NulError> {
        CStrThin::from_bytes_with_nul(bytes)?;
        Ok(unsafe { Self::from_bytes_unchecked_mut(bytes) })
    }

    /// Creates a `CStrSlice` reference from a byte slice with at least one nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let bytes = b"hello\0 world\0";
    /// let s = CStrSlice::from_bytes_until_nul(bytes).unwrap();
    /// assert_eq!(s.to_bytes(), b"hello");
    /// ```
    ///
    /// Creating without a trailing nul terminator is an error:
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let bytes = b"hello world";
    /// assert!(CStrSlice::from_bytes_until_nul(bytes).is_err());
    /// ```
    pub fn from_bytes_until_nul(bytes: &[u8]) -> Result<&CStrSlice, NulError> {
        CStrThin::from_bytes_until_nul(bytes)?;
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Same as [CStrSlice::from_bytes_until_nul] but with a mutable reference.
    pub fn from_bytes_until_nul_mut(bytes: &mut [u8]) -> Result<&mut CStrSlice, NulError> {
        CStrThin::from_bytes_until_nul(bytes)?;
        Ok(unsafe { Self::from_bytes_unchecked_mut(bytes) })
    }

    /// Truncates this C string, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrArray;
    ///
    /// let mut s = CStrArray::<64>::new();
    /// s.cursor().write_bytes(b"foo").unwrap();
    /// assert_eq!(s.to_bytes(), b"foo");
    /// s.clear();
    /// assert!(s.is_empty());
    /// ```
    pub fn clear(&mut self) {
        if self.capacity() > 0 {
            self.bytes[0] = 0;
        }
    }

    /// Returns this string's capacity, in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut buf = [0; 128];
    /// let s = CStrSlice::new_in(&mut buf);
    /// assert_eq!(s.capacity(), 128);
    /// ```
    pub const fn capacity(&self) -> usize {
        self.bytes.len()
    }

    /// Returns the mutable inner pointer to this C string.
    ///
    /// The returned pointer will be valid for as long as `self` is, and points to a contiguous
    /// region of memory terminated with a nul byte to represent the end of the string.
    pub fn as_mut_ptr(&mut self) -> *mut c_char {
        self.bytes.as_mut_ptr().cast()
    }

    /// Returns a C string reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::{CStrArray, cstr};
    ///
    /// let mut s = CStrArray::<32>::try_from("hello").unwrap();
    /// assert_eq!(s.as_thin(), cstr!("hello"));
    /// ```
    pub const fn as_thin(&self) -> &CStrThin {
        let ptr = if self.capacity() > 0 {
            self.bytes.as_ptr().cast()
        } else {
            [0].as_ptr()
        };
        unsafe { CStrThin::from_ptr(ptr) }
    }

    /// Write a byte slice at position `offset` within this C string.
    ///
    /// Returns an offset after written bytes.
    ///
    /// # Safety
    ///
    /// * `offset + bytes.len()` needs to be less than or equal to `capacity`.
    /// * If a nul terminator was overwritten by this method a call to any other method of this C
    ///   string is UB. The nul terminator needs to be written by this method before any call to
    ///   other methods.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut buf = [0; 32];
    /// let mut s = CStrSlice::new_in(&mut buf);
    /// s.cursor().write_str("foo").unwrap();
    /// let mut n = s.count_bytes();
    /// unsafe {
    ///     n = s.write_bytes_unchecked(n, b"bar");
    ///     // other methods must not be called because
    ///     // the string do not ends with a nul terminator
    ///     n = s.write_bytes_unchecked(n, b"123");
    ///     // write a nul byte
    ///     n = s.write_bytes_unchecked(n, b"\0");
    ///     // safe to call other methods
    /// }
    /// assert_eq!(s.to_bytes_with_nul(), b"foobar123\0");
    /// ```
    pub unsafe fn write_bytes_unchecked(&mut self, offset: usize, bytes: &[u8]) -> usize {
        let src = bytes.as_ptr();
        let len = bytes.len();
        let dst = self.as_mut_ptr().cast::<u8>();
        unsafe {
            ptr::copy_nonoverlapping(src, dst.add(offset), len);
        }
        offset + len
    }

    /// Creates a [Cursor] that will overwrite this string's content.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut buf = [0; 64];
    /// let mut s = CStrSlice::new_in(&mut buf);
    /// s.cursor().write_bytes(b"banana").unwrap();
    /// assert_eq!(s.to_bytes(), b"banana");
    /// ```
    pub fn cursor(&mut self) -> Cursor<'_> {
        self.clear();
        Cursor::new(&mut self.bytes, 0)
    }

    /// Creates a [Cursor] that will append to the end of this C string.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut buf = [0; 64];
    /// let mut s = CStrSlice::new_in(&mut buf);
    /// s.cursor().write_bytes(b"foo").unwrap();
    /// s.append().write_bytes(b"bar").unwrap();
    /// assert_eq!(s.to_bytes(), b"foobar");
    /// ```
    pub fn append(&mut self) -> Cursor<'_> {
        let offset = self.count_bytes();
        Cursor::new(&mut self.bytes, offset)
    }

    /// Returns the inner slice.
    pub const fn inner_slice(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the mutable inner slice.
    ///
    /// # Safety
    ///
    /// The array must contain a nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrSlice;
    ///
    /// let mut buf = [0; 32];
    /// let mut s = CStrSlice::new_in(&mut buf);
    /// unsafe {
    ///     let inner = s.inner_slice_mut();
    ///     let test = b"inner buffer";
    ///     inner[..test.len()].copy_from_slice(test);
    /// }
    /// assert_eq!(s.to_bytes(), b"inner buffer");
    /// ```
    pub unsafe fn inner_slice_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}

impl Deref for CStrSlice {
    type Target = CStrThin;

    fn deref(&self) -> &Self::Target {
        self.as_thin()
    }
}

impl AsRef<CStrThin> for CStrSlice {
    fn as_ref(&self) -> &CStrThin {
        self.as_thin()
    }
}

impl Eq for CStrSlice {}

impl PartialEq for CStrSlice {
    fn eq(&self, other: &Self) -> bool {
        self.as_thin().eq(other.as_thin())
    }
}

impl PartialEq<CStrThin> for CStrSlice {
    fn eq(&self, other: &CStrThin) -> bool {
        self.as_thin().eq(other)
    }
}

impl PartialEq<CStr> for CStrSlice {
    fn eq(&self, other: &CStr) -> bool {
        self.as_thin().eq(<&CStrThin>::from(other))
    }
}

impl PartialOrd for CStrSlice {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<CStrThin> for CStrSlice {
    fn partial_cmp(&self, other: &CStrThin) -> Option<Ordering> {
        Some(self.as_thin().cmp(other))
    }
}

impl PartialOrd<CStr> for CStrSlice {
    fn partial_cmp(&self, other: &CStr) -> Option<Ordering> {
        Some(self.as_thin().cmp(<&CStrThin>::from(other)))
    }
}

impl Ord for CStrSlice {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_thin().cmp(other)
    }
}

impl fmt::Display for CStrSlice {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_thin(), fmt)
    }
}

impl fmt::Debug for CStrSlice {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_thin(), fmt)
    }
}

impl Borrow<CStrThin> for CStrSlice {
    fn borrow(&self) -> &CStrThin {
        self.as_thin()
    }
}

impl Hash for CStrSlice {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes().for_each(|i| i.hash(state));
    }
}
