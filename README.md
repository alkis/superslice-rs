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

Now you can enjoy super fast `lower_bound`, `upper_bound`, `equal_range`, and
`fast_binary_search`.

`fast_binary_search` is much faster than `binary_search`:

```diff,ignore
 name        std ns/iter  fast ns/iter  diff ns/iter   diff %  speedup
+l1::dups    31           10                     -21  -67.74%   x 3.10
+l1::unique  35           10                     -25  -71.43%   x 3.50
+l2::dups    54           19                     -35  -64.81%   x 2.84
+l2::unique  59           19                     -40  -67.80%   x 3.11
+l3::dups    131          81                     -50  -38.17%   x 1.62
+l3::unique  135          80                     -55  -40.74%   x 1.69
```

### Why isn't this part of the standard library?

Worry not, work is on the way:

- [ ] Make `binary_search` as fast as `fast_binary_search`:  https://github.com/rust-lang/rust/pull/45333
- [ ] Add `lower_bound`, `upper_bound`, `equal_range` to std: https://github.com/rust-lang/rfcs/issues/2184
