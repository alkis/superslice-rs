This crate provides extensions for ordered [`slice`](https://doc.rust-lang.org/stable/std/primitive.slice.html)s.

[![Build Status](https://travis-ci.org/alkis/ordslice-rs.svg?branch=master)](https://travis-ci.org/alkis/ordslice-rs)
[![Latest Version](https://img.shields.io/crates/v/ordslice.svg)](https://crates.io/crates/ordslice)

Licensed under APACHE-2.

### Documentation

https://docs.rs/ordslice

### Installation

This crate works with Cargo and is on
[crates.io](https://crates.io/crates/ordslice). Add it to your `Cargo.toml`:

```toml
[dependencies]
ordslice = "1"
```

and augment `slice`s by using its `Ext` trait:

```rust
extern crate ordslice;

use ordslice::Ext;
```

Now you can enjoy super fast `lower_bound`, `upper_bound`, and `equal_range`.

### Why isn't this part of the standard library?

Worry not, work is on the way:

- [X] Make `binary_search` as fast as ~~`fast_binary_search`~~:  https://github.com/rust-lang/rust/pull/45333
- [ ] Add `lower_bound`, `upper_bound`, `equal_range` to std: https://github.com/rust-lang/rfcs/issues/2184
