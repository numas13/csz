use core::{cmp::Ordering, ffi::CStr};

use crate::CStrThin;

pub trait CStrExt {
    fn cmp_ignore_case(&self, other: &CStr) -> Ordering;

    fn eq_ignore_case(&self, other: &CStr) -> bool {
        self.cmp_ignore_case(other).is_eq()
    }
}

impl CStrExt for CStr {
    fn cmp_ignore_case(&self, other: &CStr) -> Ordering {
        <&CStrThin>::from(self).cmp_ignore_case(other.into())
    }
}
