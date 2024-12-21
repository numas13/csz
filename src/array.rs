use core::{
    borrow::Borrow,
    cmp::Ordering,
    ffi::{c_char, CStr},
    fmt,
    hash::{Hash, Hasher},
    mem::MaybeUninit,
    ops::Deref,
    ptr,
};

use crate::{
    macros::const_assert_size_eq, utils::memchr, CStrBox, CStrThin, Cursor, CursorError, NulError,
};

/// An owned C string with a fixed-size capacity.
///
/// # Examples
///
/// ```
/// use csz::CStrArray;
///
/// let mut s = CStrArray::<64>::new();
/// let mut c = s.cursor();
/// c.write_str("hello").unwrap();
/// c.write_str(" world").unwrap();
/// c.finish();
/// assert_eq!(s.to_bytes_with_nul(), b"hello world\0");
/// s.clear();
/// assert_eq!(s.to_bytes_with_nul(), b"\0");
/// ```
#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct CStrArray<const N: usize> {
    bytes: [c_char; N],
}

const_assert_size_eq!([c_char; 64], CStrArray<64>);

impl<const N: usize> CStrArray<N> {
    /// Creates a new empty `CStrArray`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let s = CStrArray::<64>::new();
    /// ```
    pub fn new() -> CStrArray<N> {
        let mut bytes = MaybeUninit::<Self>::uninit();
        if N > 0 {
            unsafe {
                (*bytes.as_mut_ptr()).bytes[0] = 0;
            }
        }
        unsafe { bytes.assume_init() }
    }

    /// Truncates this C string, removing all contents.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let mut s = CStrArray::<64>::new();
    /// s.cursor().write_bytes(b"foo").unwrap();
    /// assert_eq!(s.to_bytes(), b"foo");
    /// s.clear();
    /// assert!(s.is_empty());
    /// ```
    pub fn clear(&mut self) {
        if N > 0 {
            self.bytes[0] = 0;
        }
    }

    /// Returns this string's capacity, in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let s = CStrArray::<128>::new();
    /// assert_eq!(s.capacity(), 128);
    /// ```
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Creates a mutable reference to `CStrArray` from a byte array and clears it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let mut bytes = [0; 32];
    /// bytes[..4].copy_from_slice(b"abc\0");
    /// let s = CStrArray::new_in(&mut bytes);
    /// assert!(s.is_empty());
    /// assert_eq!(s.capacity(), 32);
    /// ```
    pub fn new_in(bytes: &mut [u8; N]) -> &mut CStrArray<N> {
        if N > 0 {
            bytes[0] = 0;
        }
        unsafe { Self::from_array_unchecked(bytes) }
    }

    /// Creates a mutable reference to `CStrArray` from a byte array.
    ///
    /// # Safety
    ///
    /// The given array must contain at least one nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let mut bytes = [0; 16];
    /// bytes[..4].copy_from_slice(b"abc\0");
    /// let s = unsafe { CStrArray::from_array_unchecked(&mut bytes) };
    /// assert_eq!(s.to_bytes(), b"abc");
    /// assert_eq!(s.capacity(), 16);
    /// ```
    pub unsafe fn from_array_unchecked(bytes: &mut [u8; N]) -> &mut CStrArray<N> {
        unsafe { &mut *(bytes as *mut [u8; N] as *mut Self) }
    }

    /// Creates a mutable reference to `CStrArray` from a byte array.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let mut bytes = [0; 128];
    /// bytes[..7].copy_from_slice(b"foobar\0");
    /// let s = CStrArray::from_array(&mut bytes).unwrap();
    /// assert_eq!(s.to_bytes(), b"foobar");
    /// assert_eq!(s.capacity(), 128);
    /// ```
    pub fn from_array(bytes: &mut [u8; N]) -> Result<&mut CStrArray<N>, NulError> {
        match memchr(b'\0', bytes) {
            Some(_) => Ok(unsafe { &mut *(bytes as *mut [u8; N] as *mut Self) }),
            None => Err(NulError(())),
        }
    }

    /// Creates a new fixed-size C string from a byte slice.
    ///
    /// # Safety
    ///
    /// See documentation for [Cursor::write_bytes_unchecked].
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Result<CStrArray<N>, CursorError> {
        let mut s = Self::new();
        unsafe {
            s.cursor().write_bytes_unchecked(bytes)?;
        }
        Ok(s)
    }

    /// Creates a new fixed-size C string from a byte slice.
    ///
    /// See documentation for [Cursor::write_bytes].
    pub fn from_bytes(bytes: &[u8]) -> Result<CStrArray<N>, CursorError> {
        let mut s = Self::new();
        s.cursor().write_bytes(bytes)?;
        Ok(s)
    }

    /// Returns the mutable inner pointer to this C string.
    ///
    /// The returned pointer will be valid for as long as `self` is, and points to a contiguous
    /// region of memory terminated with a nul byte to represent the end of the string.
    pub fn as_mut_ptr(&mut self) -> *mut c_char {
        self.bytes.as_mut_ptr()
    }

    /// Returns a C string reference.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::{CStrArray, cstr};
    ///
    /// let mut s = CStrArray::<32>::try_from("hello").unwrap();
    /// assert_eq!(s.as_c_str(), cstr!("hello"));
    /// ```
    pub const fn as_c_str(&self) -> &CStrThin {
        let ptr = if N > 0 {
            self.bytes.as_ptr()
        } else {
            [0].as_ptr()
        };
        unsafe { CStrThin::from_ptr(ptr) }
    }

    /// Returns the inner array as a mutable reference.
    ///
    /// # Safety
    ///
    /// The array must contain a nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let mut s = CStrArray::<32>::try_from("inner buffer").unwrap();
    /// assert!(unsafe { s.inner_mut() }.starts_with(b"inner buffer\0"));
    /// ```
    pub unsafe fn inner_mut(&mut self) -> &mut [u8; N] {
        unsafe { &mut *ptr::addr_of_mut!(self.bytes).cast() }
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
    /// # use csz::CStrArray;
    /// let mut s = CStrArray::<32>::try_from("foo").unwrap();
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
    /// # use csz::CStrArray;
    /// let mut s = CStrArray::<64>::try_from("foobar").unwrap();
    /// s.cursor().write_bytes(b"banana").unwrap();
    /// assert_eq!(s.to_bytes(), b"banana");
    /// ```
    pub fn cursor(&mut self) -> Cursor {
        self.clear();
        Cursor::new(unsafe { self.inner_mut() }, 0)
    }

    /// Creates a [Cursor] that will append to the end of this C string.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::CStrArray;
    /// let mut s = CStrArray::<64>::try_from("foo").unwrap();
    /// s.append().write_bytes(b"bar").unwrap();
    /// assert_eq!(s.to_bytes(), b"foobar");
    /// ```
    pub fn append(&mut self) -> Cursor {
        let offset = self.count_bytes();
        Cursor::new(unsafe { self.inner_mut() }, offset)
    }
}

impl<const N: usize> Default for CStrArray<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deref for CStrArray<N> {
    type Target = CStrThin;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

impl<const N: usize> TryFrom<&CStrThin> for CStrArray<N> {
    type Error = CursorError;

    fn try_from(value: &CStrThin) -> Result<Self, Self::Error> {
        let mut s = Self::new();
        s.cursor().write_c_str(value)?;
        Ok(s)
    }
}

impl<const N: usize> TryFrom<&CStr> for CStrArray<N> {
    type Error = CursorError;

    fn try_from(value: &CStr) -> Result<Self, Self::Error> {
        Self::try_from(<&CStrThin>::from(value))
    }
}

impl<const N: usize> TryFrom<&str> for CStrArray<N> {
    type Error = NulError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let mut s = Self::new();
        s.cursor()
            .write_bytes(value.as_bytes())
            .map_err(|_| NulError(()))?;
        Ok(s)
    }
}

impl<const N: usize> From<&'_ CStrArray<N>> for CStrBox {
    fn from(value: &CStrArray<N>) -> Self {
        CStrBox::from(value.as_c_str())
    }
}

impl<const N: usize> Eq for CStrArray<N> {}

impl<const N: usize> PartialEq for CStrArray<N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_c_str().eq(other.as_c_str())
    }
}

impl<const N: usize> PartialEq<CStrThin> for CStrArray<N> {
    fn eq(&self, other: &CStrThin) -> bool {
        self.as_c_str().eq(other)
    }
}

impl<const N: usize> PartialEq<CStr> for CStrArray<N> {
    fn eq(&self, other: &CStr) -> bool {
        self.as_c_str().eq(<&CStrThin>::from(other))
    }
}

impl<const N: usize> PartialOrd for CStrArray<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.as_c_str().cmp(other.as_c_str()))
    }
}

impl<const N: usize> PartialOrd<CStrThin> for CStrArray<N> {
    fn partial_cmp(&self, other: &CStrThin) -> Option<Ordering> {
        Some(self.as_c_str().cmp(other))
    }
}

impl<const N: usize> PartialOrd<CStr> for CStrArray<N> {
    fn partial_cmp(&self, other: &CStr) -> Option<Ordering> {
        Some(self.as_c_str().cmp(<&CStrThin>::from(other)))
    }
}

impl<const N: usize> Ord for CStrArray<N> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_c_str().cmp(other)
    }
}

impl<const N: usize> fmt::Display for CStrArray<N> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_c_str(), fmt)
    }
}

impl<const N: usize> fmt::Debug for CStrArray<N> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_c_str(), fmt)
    }
}

impl<const N: usize> Borrow<CStrThin> for CStrArray<N> {
    fn borrow(&self) -> &CStrThin {
        self.as_c_str()
    }
}

impl<const N: usize> Hash for CStrArray<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes().for_each(|i| i.hash(state));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_capacity() {
        let mut s = CStrArray::<0>::new();
        s.clear();
        assert!(s.is_empty());
        assert!(!s.as_mut_ptr().is_null());
        assert_eq!(s.to_bytes(), b"");
        assert_eq!(s.to_bytes_with_nul(), b"\0");
        assert!(s.append().write_bytes(b"1").is_err());
    }

    #[test]
    fn borrow() {
        let a = CStrArray::<64>::try_from("test").unwrap();
        let s: &CStrThin = a.borrow();
        assert_eq!(s.to_bytes(), b"test");
    }
}
