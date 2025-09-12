# Safer wrappers for nul-terminated C strings.

This crate uses C functions from the C standard library:

* `memchr`
* `strlen`
* `strstr`
* `strcmp`
* `strcasecmp` (`stricmp` on windows)
* `malloc`
* `free`
* `realloc`

# Features

* `link_libc` (*enabled by default*) - links to the C standard library. Disable the feature if
  you want to manually implement C functions.
* `libc` - use [libc](https://crates.io/crates/libc) crate.
* `alloc` - enables linking to the alloc crate.

# Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
csz = "0.1"
```

# Rust version support

The minimum supported Rust toolchain version is currently Rust 1.64.
