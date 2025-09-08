use core::{
    borrow::Borrow,
    cmp::Ordering,
    ffi::{c_char, CStr},
    fmt,
    hash::{Hash, Hasher},
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
};

use crate::{
    macros::const_assert_size_eq, utils::memchr, CStrBox, CStrSlice, CStrThin, CursorError,
    NulError,
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
    bytes: [u8; N],
}

const_assert_size_eq!(c_char, u8);
const_assert_size_eq!([c_char; 64], CStrArray<64>);

impl<const N: usize> CStrArray<N> {
    /// Creates a new empty `CStrArray`.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrArray;
    ///
    /// let s = CStrArray::<64>::new();
    /// assert_eq!(s.to_bytes(), b"")
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

    /// Creates a mutable reference to `CStrArray` from a `c_char` array and clears it.
    ///
    /// # Examples
    ///
    /// ```
    /// use core::ffi::c_char;
    /// use csz::CStrArray;
    ///
    /// let mut array = [0; 32];
    /// for (i, c) in b"abc\0".iter().enumerate() {
    ///     array[i] = *c as c_char;
    /// }
    /// let s = CStrArray::new_in_array(&mut array);
    /// assert!(s.is_empty());
    /// assert_eq!(s.capacity(), 32);
    /// ```
    pub fn new_in_array(array: &mut [c_char; N]) -> &mut CStrArray<N> {
        Self::new_in(unsafe { &mut *(array as *mut _ as *mut [u8; N]) })
    }

    /// Creates a mutable reference to `CStrArray` from a byte array and clears it.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::CStrArray;
    ///
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
    /// use csz::CStrArray;
    ///
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
    /// use csz::CStrArray;
    ///
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
    /// See documentation for [crate::Cursor::write_bytes_unchecked].
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Result<CStrArray<N>, CursorError> {
        let mut s = Self::new();
        unsafe {
            s.cursor().write_bytes_unchecked(bytes)?;
        }
        Ok(s)
    }

    /// Creates a new fixed-size C string from a byte slice.
    ///
    /// See documentation for [crate::Cursor::write_bytes].
    pub fn from_bytes(bytes: &[u8]) -> Result<CStrArray<N>, CursorError> {
        let mut s = Self::new();
        s.cursor().write_bytes(bytes)?;
        Ok(s)
    }

    /// Returns a C string slice containing the entire C string array.
    pub fn as_slice(&self) -> &CStrSlice {
        unsafe { CStrSlice::from_bytes_unchecked(&self.bytes[..]) }
    }

    /// Returns a mutable C string slice containing the entire C string array.
    pub fn as_slice_mut(&mut self) -> &mut CStrSlice {
        unsafe { CStrSlice::from_bytes_unchecked_mut(&mut self.bytes[..]) }
    }
}

impl<const N: usize> Default for CStrArray<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Deref for CStrArray<N> {
    type Target = CStrSlice;

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<const N: usize> DerefMut for CStrArray<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_slice_mut()
    }
}

impl<const N: usize> AsRef<CStrThin> for CStrArray<N> {
    fn as_ref(&self) -> &CStrThin {
        self.as_thin()
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
        CStrBox::from(value.as_thin())
    }
}

impl<const N: usize> Eq for CStrArray<N> {}

impl<const N: usize> PartialEq for CStrArray<N> {
    fn eq(&self, other: &Self) -> bool {
        self.as_thin().eq(other.as_thin())
    }
}

impl<const N: usize> PartialEq<CStrThin> for CStrArray<N> {
    fn eq(&self, other: &CStrThin) -> bool {
        self.as_thin().eq(other)
    }
}

impl<const N: usize> PartialEq<CStr> for CStrArray<N> {
    fn eq(&self, other: &CStr) -> bool {
        self.as_thin().eq(<&CStrThin>::from(other))
    }
}

impl<const N: usize> PartialOrd for CStrArray<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> PartialOrd<CStrThin> for CStrArray<N> {
    fn partial_cmp(&self, other: &CStrThin) -> Option<Ordering> {
        Some(self.as_thin().cmp(other))
    }
}

impl<const N: usize> PartialOrd<CStr> for CStrArray<N> {
    fn partial_cmp(&self, other: &CStr) -> Option<Ordering> {
        Some(self.as_thin().cmp(<&CStrThin>::from(other)))
    }
}

impl<const N: usize> Ord for CStrArray<N> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_thin().cmp(other)
    }
}

impl<const N: usize> fmt::Display for CStrArray<N> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_thin(), fmt)
    }
}

impl<const N: usize> fmt::Debug for CStrArray<N> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_thin(), fmt)
    }
}

impl<const N: usize> Borrow<CStrThin> for CStrArray<N> {
    fn borrow(&self) -> &CStrThin {
        self.as_thin()
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
