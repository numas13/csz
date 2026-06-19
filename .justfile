# set global cargo args
check_args := "--quiet"
tests_args := "--all-features"

# extract Rust version from Cargo.toml
msrv := `grep -m1 rust-version Cargo.toml | sed 's/^rust-version\s*=\s*"\([0-9]\+.[0-9]\+\).*"$/\1/'`

all: check test

check: check-fmt clippy check-stable check-msrv

check-fmt:
    cargo fmt --check

clippy:
    cargo clippy {{check_args}}

check-stable:
    cargo +stable check {{check_args}}
    cargo +stable check {{check_args}} --all-features
    cargo +stable check {{check_args}} --no-default-features

check-msrv:
    cargo +{{msrv}} check {{check_args}}
    cargo +{{msrv}} check {{check_args}} --all-features
    cargo +{{msrv}} check {{check_args}} --no-default-features

test:
    cargo test {{tests_args}}
