#[cfg(not(feature = "libc"))]
mod imp {
    use core::ffi::{c_char, c_int, c_void};

    #[allow(non_camel_case_types)]
    type size_t = usize;

    extern "C" {
        pub fn strlen(c: *const c_char) -> size_t;
        pub fn strstr(s: *const c_char, n: *const c_char) -> *mut c_char;
        pub fn strcmp(s1: *const c_char, s2: *const c_char) -> c_int;
        pub fn memchr(s: *const c_void, c: c_int, n: size_t) -> *mut c_void;
        pub fn malloc(size: size_t) -> *mut c_void;
        pub fn free(ptr: *mut c_void);
        pub fn realloc(ptr: *mut c_void, size: size_t) -> *mut c_void;

        #[cfg(unix)]
        pub fn strcasecmp(s1: *const c_char, s2: *const c_char) -> c_int;

        #[cfg(windows)]
        pub fn stricmp(s1: *const c_char, s2: *const c_char) -> c_int;

    }

    #[cfg(windows)]
    pub use stricmp as strcasecmp;
}

#[cfg(feature = "libc")]
mod imp {
    pub use libc::{free, malloc, memchr, realloc, strcmp, strlen, strstr};

    #[cfg(unix)]
    pub use libc::strcasecmp;

    #[cfg(windows)]
    pub use libc::stricmp as strcasecmp;
}

pub use imp::*;
