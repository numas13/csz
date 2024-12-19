use core::{fmt, ptr};

use crate::{utils::memchr, CStr};

/// An error indicating problems with a write into a cursor.
///
/// This error is created by the [Cursor] methods. See its documentation for more.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CursorError {
    /// An error indicating that no nul byte was present or that a byte slice contains interior nul
    /// bytes.
    NulError,
    /// An inner buffer does not have enough free space.
    OverflowError,
}

/// A cursor for writing strings with a nul byte at the end.
///
/// # Examples
///
/// ```
/// use csz::Cursor;
///
/// let mut buffer = [b' '; 123];
/// let mut cur = Cursor::new(&mut buffer, 0);
/// cur.write_str("half").unwrap();
/// cur.write_bytes(b"-life").unwrap();
/// cur.finish();
/// assert!(buffer.starts_with(b"half-life\0"))
/// ```
pub struct Cursor<'a> {
    buffer: &'a mut [u8],
    offset: usize,
    dirty: bool,
}

impl<'a> Cursor<'a> {
    /// Creates a new `Cursor`.
    pub fn new(buffer: &'a mut [u8], offset: usize) -> Cursor<'a> {
        Self {
            buffer,
            offset,
            dirty: false,
        }
    }

    /// Creates a new `Cursor` that will append to the end of C string.
    pub fn append(buffer: &'a mut [u8]) -> Result<Cursor<'a>, CursorError> {
        match memchr(b'\0', buffer) {
            Some(offset) => Ok(Self::new(buffer, offset)),
            None => Err(CursorError::NulError),
        }
    }

    /// Returns this cursor's capacity, in bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [0; 128];
    /// let cur = Cursor::new(&mut bytes, 0);
    /// assert_eq!(cur.capacity(), 128);
    /// ```
    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    /// Write a nul byte at the end this cursor.
    pub fn finish(self) {}

    /// Writes a byte slice into this cursor.
    ///
    /// # Safety
    ///
    /// The byte slice must not contain a nul byte.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::{CStrArray, Cursor};
    ///
    /// let mut bytes = [b'x'; 64];
    /// bytes[..6].copy_from_slice(b"hello\0");
    /// let mut cur = Cursor::append(&mut bytes).unwrap();
    /// unsafe {
    ///     cur.write_bytes_unchecked(b" abc").unwrap();
    ///     cur.write_bytes_unchecked(b" 123").unwrap();
    /// }
    /// cur.finish();
    /// assert!(bytes.starts_with(b"hello abc 123\0xxx"));
    /// ```
    pub unsafe fn write_bytes_unchecked(&mut self, bytes: &[u8]) -> Result<(), CursorError> {
        if self.offset + bytes.len() + 1 < self.capacity() {
            let src = bytes.as_ptr();
            let dst = self.buffer.as_mut_ptr().cast::<u8>();
            unsafe {
                ptr::copy_nonoverlapping(src, dst.add(self.offset), bytes.len());
            }
            self.offset += bytes.len();
            self.dirty = true;
            Ok(())
        } else {
            Err(CursorError::OverflowError)
        }
    }

    /// Writes a byte slice into this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [b'x'; 32];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// cur.write_bytes(b"foo").unwrap();
    /// cur.write_bytes(b"bar").unwrap();
    /// cur.finish();
    /// assert!(bytes.starts_with(b"foobar\0xxx"));
    /// ```
    ///
    /// Writing a byte slice with an interior nul byte is an error:
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [0; 32];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// assert!(cur.write_bytes(b"foo\0bar").is_err());
    /// ```
    ///
    /// This method returns an error if the inner buffer does not have capacity to hold
    /// a byte slice:
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [b'x'; 8];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// assert!(cur.write_bytes(b"1234").is_ok());
    /// assert!(cur.write_bytes(b"5678").is_err());
    /// cur.finish();
    /// assert_eq!(bytes.as_slice(), b"1234\0xxx");
    /// ```
    pub fn write_bytes<T: AsRef<[u8]>>(&mut self, bytes: T) -> Result<(), CursorError> {
        let bytes = bytes.as_ref();
        if bytes.contains(&0) {
            return Err(CursorError::NulError);
        }
        unsafe { self.write_bytes_unchecked(bytes) }
    }

    /// Writes a byte slice up to the first nul byte into this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [b'x'; 32];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// cur.write_bytes_until_nul(b"foo\0baz\0").unwrap();
    /// cur.write_bytes_until_nul(b"bar\0baz\0").unwrap();
    /// cur.finish();
    /// assert!(bytes.starts_with(b"foobar\0xxx"));
    /// ```
    ///
    /// Writing a byte slice without a nul byte in a byte slice is an error:
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [0; 32];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// assert!(cur.write_bytes_until_nul(b"hello").is_err());
    /// ```
    ///
    /// This method returns an error if the inner buffer does not have enough capacity to hold
    /// a byte slice:
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [b'x'; 8];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// assert!(cur.write_bytes_until_nul(b"1234\0foobar").is_ok());
    /// assert!(cur.write_bytes_until_nul(b"5678\0").is_err());
    /// cur.finish();
    /// assert_eq!(bytes, *b"1234\0xxx");
    /// ```
    pub fn write_bytes_until_nul<T: AsRef<[u8]>>(&mut self, bytes: T) -> Result<(), CursorError> {
        let bytes = bytes.as_ref();
        match memchr(b'\0', bytes) {
            Some(nul_pos) => unsafe { self.write_bytes_unchecked(&bytes[..nul_pos]) },
            None => Err(CursorError::NulError),
        }
    }

    /// Writes a given C string into this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// use csz::{Cursor, cstr};
    ///
    /// let mut bytes = [b'x'; 8];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// cur.write_c_str(cstr!("hello")).unwrap();
    /// cur.finish();
    /// assert_eq!(bytes, *b"hello\0xx");
    /// ```
    pub fn write_c_str(&mut self, s: &CStr) -> Result<(), CursorError> {
        unsafe { self.write_bytes_unchecked(s.to_bytes()) }
    }

    /// Writes a given string slice into this cursor.
    ///
    /// # Examples
    ///
    /// ```
    /// # use csz::Cursor;
    /// let mut bytes = [b'x'; 8];
    /// let mut cur = Cursor::new(&mut bytes, 0);
    /// cur.write_str("hello").unwrap();
    /// cur.finish();
    /// assert_eq!(bytes, *b"hello\0xx");
    /// ```
    pub fn write_str(&mut self, s: &str) -> Result<(), CursorError> {
        self.write_bytes(s.as_bytes())
    }
}

impl Drop for Cursor<'_> {
    fn drop(&mut self) {
        if self.dirty {
            // write nul terminator
            self.buffer[self.offset] = 0;
        }
    }
}

impl fmt::Write for Cursor<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.write_str(s).map_err(|_| fmt::Error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use core::fmt::Write;

    #[test]
    fn format() {
        let mut buffer = [0; 128];
        let mut cur = Cursor::new(&mut buffer, 0);
        write!(&mut cur, "foobar").ok();
        write!(&mut cur, " 123456").ok();
        cur.finish();
        assert!(buffer.starts_with(b"foobar 123456"));
    }
}
