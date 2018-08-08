This crate provides extensions for [`slice`](https://doc.rust-lang.org/stable/std/primitive.slice.html)s.

[![Build Status](https://travis-ci.org/alkis/superslice-rs.svg?branch=master)](https://travis-ci.org/alkis/superslice-rs)
[![Latest Version](https://img.shields.io/crates/v/superslice.svg)](https://crates.io/crates/superslice)

Licensed under APACHE-2.

### Documentation

https://docs.rs/superslice

### Installation

This crate works with Cargo and is on
[crates.io](https://crates.io/crates/ordslice). Add it to your `Cargo.toml`:

```toml
[dependencies]
superslice = "1"
```

and augment `slice`s by using its `Ext` trait:

```rust
extern crate superslice;

use superslice::*;
```

Now you can enjoy high performance of common algorithms on slices:

- `lower_bound`
- `upper_bound`
- `equal_range`

### Why isn't this part of the standard library?

Worry not, work is on the way:

- [X] Make `binary_search` as fast as ~~`fast_binary_search`~~:  https://github.com/rust-lang/rust/pull/45333
- [ ] Add `lower_bound`, `upper_bound`, `equal_range` to std: https://github.com/rust-lang/rfcs/issues/2184
