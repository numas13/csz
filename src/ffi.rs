#[cfg(miri)]
mod imp {
    use core::{
        ffi::{c_char, c_int, c_void},
        ptr,
    };

    #[allow(non_camel_case_types)]
    type size_t = usize;

    pub unsafe extern "C" fn memchr(s: *const c_void, c: c_int, n: size_t) -> *mut c_void {
        let s = s.cast::<u8>();
        let c = c as u8;
        for i in 0..n {
            let p = s.wrapping_add(i);
            if unsafe { *p == c } {
                return p as *mut c_void;
            }
        }
        ptr::null_mut()
    }

    pub unsafe extern "C" fn strlen(s: *const c_char) -> size_t {
        unsafe {
            let mut p = s;
            while *p != 0 as c_char {
                p = p.wrapping_add(1);
            }
            p.offset_from(s) as size_t
        }
    }

    pub unsafe extern "C" fn strcmp(s1: *const c_char, s2: *const c_char) -> c_int {
        let mut i = 0;
        loop {
            let c1 = unsafe { *s1.wrapping_add(i) };
            let c2 = unsafe { *s2.wrapping_add(i) };
            if c1 != c2 || c1 == 0 || c2 == 0 {
                return c1 as c_int - c2 as c_int;
            }
            i += 1;
        }
    }

    pub unsafe extern "C" fn strcasecmp(s1: *const c_char, s2: *const c_char) -> c_int {
        let mut i = 0;
        loop {
            let c1 = unsafe { *s1.wrapping_add(i) } as u8;
            let c2 = unsafe { *s2.wrapping_add(i) } as u8;
            let c1 = c1.to_ascii_lowercase() as c_char;
            let c2 = c2.to_ascii_lowercase() as c_char;
            if c1 != c2 || c1 == 0 || c2 == 0 {
                return c1 as c_int - c2 as c_int;
            }
            i += 1;
        }
    }

    pub unsafe extern "C" fn strstr(mut s: *const c_char, n: *const c_char) -> *mut c_char {
        loop {
            for j in 0.. {
                let c2 = unsafe { *n.wrapping_add(j) };
                if c2 == 0 {
                    return s as *mut c_char;
                }
                let c1 = unsafe { *s.wrapping_add(j) };
                if c1 == 0 {
                    return ptr::null_mut();
                }
                if c1 != c2 {
                    break;
                }
            }
            s = s.wrapping_add(1);
        }
    }

    // pub unsafe extern "C" fn malloc(size: size_t) -> *mut c_void {
    //     todo!()
    // }
    //
    // pub unsafe extern "C" fn free(ptr: *mut c_void) {
    //     todo!()
    // }
    //
    // pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: size_t) -> *mut c_void {
    //     todo!()
    // }
}

#[cfg(all(not(miri), not(feature = "libc")))]
mod imp {
    use core::ffi::{c_char, c_int, c_void};

    #[allow(non_camel_case_types)]
    type size_t = usize;

    #[cfg_attr(all(not(windows), feature = "link_libc"), link(name = "c"))]
    extern "C" {
        pub fn strlen(c: *const c_char) -> size_t;
        pub fn strstr(s: *const c_char, n: *const c_char) -> *mut c_char;
        pub fn strcmp(s1: *const c_char, s2: *const c_char) -> c_int;
        pub fn memchr(s: *const c_void, c: c_int, n: size_t) -> *mut c_void;
        pub fn malloc(size: size_t) -> *mut c_void;
        pub fn free(ptr: *mut c_void);
        pub fn realloc(ptr: *mut c_void, size: size_t) -> *mut c_void;

        #[cfg(not(windows))]
        pub fn strcasecmp(s1: *const c_char, s2: *const c_char) -> c_int;

        #[cfg(windows)]
        #[link_name = "_stricmp"]
        pub fn strcasecmp(s1: *const c_char, s2: *const c_char) -> c_int;
    }
}

#[cfg(all(not(miri), feature = "libc"))]
mod imp {
    pub use libc::{free, malloc, memchr, realloc, strcmp, strlen, strstr};

    #[cfg(not(windows))]
    pub use libc::strcasecmp;

    #[cfg(windows)]
    pub use libc::stricmp as strcasecmp;
}

pub use imp::*;
