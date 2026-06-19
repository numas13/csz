# csz

Safe wrappers for nul-terminated C strings.

# Usage

Add the following line to your `Cargo.toml`:

```toml
[dependencies]
csz = "0.1"
```

`csz::CStrThin` has API similar to `std::ffi::CStr`.

```rust
use std::ffi::CStr;
use csz::CStrThin;

let s_std = CStr::from_bytes_until_nul(b"hello\0").unwrap();
let s_thin = CStrThin::from_bytes_until_nul(b"hello\0").unwrap();
assert_eq!(s_std.to_bytes_with_nul(), s_thin.to_bytes_with_nul());
```

`CStrThin` is a thin pointer and can be used as a replacement for `*const c_char`.

```rust
use std::{mem::size_of, ffi::c_char};
use csz::{CStrThin, cstr};

// C code for this function:
// void work(const char *s) { ... }
unsafe extern "C" fn work(s: Option<&CStrThin>) {}

assert_eq!(size_of::<&CStrThin>(), size_of::<*const c_char>());
assert_eq!(size_of::<Option<&CStrThin>>(), size_of::<*const c_char>());

let data = cstr!("Hello, world!");
unsafe { work(Some(data)) }
```

# Feature flags

* `link_libc` (*enabled by default*): links to the C standard library. Disable this feature if
  you want to manually define [C functions used by this crate](#portability).
* `libc`: use [libc](https://crates.io/crates/libc) crate for
  [C functions used by this crate](#portability).
* `alloc`: enables functionality dependent on the alloc library.

# Rust version

This version of crate requires Rust `1.68` or later.

# Portability

This crate uses C functions from the C standard library:

* `memchr`
* `strlen`
* `strstr`
* `strcmp`
* `strcasecmp` (`stricmp` on windows)
* `malloc`
* `free`
* `realloc`

# License

The crate is distributed under the terms of the MIT license.

See [LICENSE](https://github.com/numas13/csz/blob/main/LICENSE) for details.
