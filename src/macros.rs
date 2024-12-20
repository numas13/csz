macro_rules! const_assert {
    ($x:expr $(,)?) => {
        const _: [(); 0 / {
            const X: bool = $x;
            X as usize
        }] = [];
    };
}
pub(super) use const_assert;

macro_rules! const_assert_eq {
    ($lhs:expr, $rhs:expr $(,)?) => {
        $crate::macros::const_assert!($lhs == $rhs);
    };
}
pub(super) use const_assert_eq;

macro_rules! const_assert_size_eq {
    ($lhs:ty, $rhs:ty $(,)?) => {
        $crate::macros::const_assert_eq! {
            core::mem::size_of::<$lhs>(),
            core::mem::size_of::<$rhs>(),
        }
    };
}
pub(super) use const_assert_size_eq;

/// Creates a [CStrThin](crate::CStrThin) from a string literal.
///
/// # Examples
///
/// ```
/// use csz::{CStrThin, cstr};
///
/// let s1 = CStrThin::from_bytes_until_nul(b"hello\0").unwrap();
/// let s2 = cstr!("hello");
/// assert_eq!(s1, s2);
/// ```
#[macro_export]
macro_rules! cstr {
    ($s:literal) => {
        unsafe { $crate::CStrThin::from_bytes_until_nul_unchecked(concat!($s, "\0").as_bytes()) }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::CStrThin;

    const_assert!(true);
    const_assert_eq!(1, 1);
    const_assert_size_eq!(u8, u8);

    const _: &CStrThin = cstr!("abcd");
}
