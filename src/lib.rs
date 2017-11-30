// Copyright 2017 Alkis Evlogimenos
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This crate provides extensions for ordered [`slice`]s.
//! 
//! # Examples
//! 
//! ```
//! use ordslice::Ext;
//! 
//! let b = [1, 3];
//! 
//! assert_eq!(b.lower_bound(&1), 0);
//! 
//! assert_eq!(b.upper_bound(&1), 1);
//! 
//! assert_eq!(b.equal_range(&3), 1..2);
//! ```
//! 
//! [`slice`]: https://doc.rust-lang.org/stable/std/primitive.slice.html
use std::cmp::Ordering::{self, Less, Greater};

/// Extends [`slice`] with fast operations on ordered slices.
/// 
/// [`slice`]: https://doc.rust-lang.org/stable/std/primitive.slice.html
pub trait Ext {
    type Item;

    /// Returns the index `i` pointing to the first element in the ordered slice
    /// that is _not less_ than `x`.
    /// 
    /// The slice MUST be ordered by the order defined by its elements.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let a = [10, 11, 13, 13, 15];
    /// assert_eq!(a.lower_bound(&9), 0);
    /// assert_eq!(a.lower_bound(&10), 0);
    /// assert_eq!(a.lower_bound(&11), 1);
    /// assert_eq!(a.lower_bound(&12), 2);
    /// assert_eq!(a.lower_bound(&13), 2);
    /// assert_eq!(a.lower_bound(&14), 4);
    /// assert_eq!(a.lower_bound(&15), 4);
    /// assert_eq!(a.lower_bound(&16), 5);
    /// ```
    fn lower_bound(&self, x: &Self::Item) -> usize
    where
        Self::Item: Ord;

    /// Returns the index `i` pointing to the first element in the ordered slice
    /// for which `f(self[i]) != Less`.
    /// 
    /// The slice MUST be ordered by the order defined by the comparator
    /// function. The comparator function should take an element and return
    /// `Ordering` that is consistent with the ordering of the slice.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [1, 2, 3, 6, 9, 9];
    /// assert_eq!(b.lower_bound(&3), b.lower_bound_by(|x| x.cmp(&3)));
    /// ```
    fn lower_bound_by<'a, F>(&'a self, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> Ordering;

    /// Returns the index `i` pointing to the first element in the ordered slice
    /// for which `f(self[i]) >= k`.
    /// 
    /// The slice MUST be ordered by the order defined by the keys of its
    /// elements.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [1, 2, 3, 6, 9, 9];
    /// assert_eq!(b.lower_bound(&3), b.lower_bound_by_key(&6, |x| x * 2));
    /// ```
    fn lower_bound_by_key<'a, K, F>(&'a self, k: &K, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;

    /// Returns the index `i` pointing to the first element in the ordered slice
    /// that is _greater_ than `x`.
    /// 
    /// The slice MUST be ordered by the order defined by its elements.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let a = [10, 11, 13, 13, 15];
    /// assert_eq!(a.upper_bound(&9), 0);
    /// assert_eq!(a.upper_bound(&10), 1);
    /// assert_eq!(a.upper_bound(&11), 2);
    /// assert_eq!(a.upper_bound(&12), 2);
    /// assert_eq!(a.upper_bound(&13), 4);
    /// assert_eq!(a.upper_bound(&14), 4);
    /// assert_eq!(a.upper_bound(&15), 5);
    /// assert_eq!(a.upper_bound(&16), 5);
    /// ```
    fn upper_bound(&self, x: &Self::Item) -> usize
    where
        Self::Item: Ord;

    /// Returns the index `i` pointing to the first element in the ordered slice
    /// for which `f(self[i]) == Greater`.
    /// 
    /// The slice MUST be ordered by the order defined by the comparator
    /// function. The comparator function should take an element and return
    /// `Ordering` that is consistent with the ordering of the slice.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [1, 2, 3, 6, 9, 9];
    /// assert_eq!(b.upper_bound(&3), b.upper_bound_by(|x| x.cmp(&3)));
    /// ```
    fn upper_bound_by<'a, F>(&'a self, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> Ordering;

    /// Returns the index `i` pointing to the first element in the ordered slice
    /// for which `f(self[i]) > k`.
    /// 
    /// The slice MUST be ordered by the order defined by the keys of its
    /// elements.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [1, 2, 3, 6, 9, 9];
    /// assert_eq!(b.lower_bound(&3), b.lower_bound_by_key(&6, |x| x * 2));
    fn upper_bound_by_key<'a, K, F>(&'a self, k: &K, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;

    /// Returns the [`Range`] `a..b` such that all elements in `self[a..b]` are
    /// _equal_ to `x`.
    /// 
    /// The slice MUST be ordered by the order defined by its elements.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [10, 11, 13, 13, 15];
    /// for i in 9..17 {
    ///     assert_eq!(b.equal_range(&i), (b.lower_bound(&i)..b.upper_bound(&i)));
    /// }
    /// ```
    /// [`Range`]: https://doc.rust-lang.org/stable/std/ops/struct.Range.html
    fn equal_range(&self, x: &Self::Item) -> std::ops::Range<usize>
    where
        Self::Item: Ord;
    
    /// Returns the [`Range`] `a..b` such that for all elements `e` in `self[a..b]` 
    /// `f(e) == Equal`.
    ///
    /// The slice MUST be ordered by the order defined by the comparator
    /// function. The comparator function should take an element and return
    /// `Ordering` that is consistent with the ordering of the slice.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [10, 11, 13, 13, 15];
    /// for i in 9..17 {
    ///     assert_eq!(b.equal_range(&i), b.equal_range_by(|x| x.cmp(&i)));
    /// }
    /// ```
    /// [`Range`]: https://doc.rust-lang.org/stable/std/ops/struct.Range.html
    fn equal_range_by<'a, F>(&'a self, f: F) -> std::ops::Range<usize>
    where
        F: FnMut(&'a Self::Item) -> Ordering;
    
    /// Returns the [`Range`] `a..b` such that for all elements `e` in `self[a..b]` 
    /// `f(e) == k`.
    ///
    /// The slice MUST be ordered by the order defined by the keys of its
    /// elements.
    /// 
    /// # Example:
    /// 
    /// ```
    /// # use ordslice::Ext;
    /// let b = [10, 11, 13, 13, 15];
    /// for i in 9..17 {
    ///     let i2 = i * 2;
    ///     assert_eq!(b.equal_range(&i), b.equal_range_by_key(&i2, |x| x * 2));
    /// }
    /// ```
    /// [`Range`]: https://doc.rust-lang.org/stable/std/ops/struct.Range.html
    fn equal_range_by_key<'a, K, F>(&'a self, k: &K, f: F) -> std::ops::Range<usize>
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;
}

impl<T> Ext for [T] {
    type Item = T;

    fn lower_bound(&self, x: &Self::Item) -> usize
    where
        T: Ord,
    {
        self.lower_bound_by(|y| y.cmp(x))
    }
    fn lower_bound_by<'a, F>(&'a self, mut f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> Ordering,
    {
        let s = self;
        let mut size = s.len();
        if size == 0 {
            return 0;
        }
        let mut base = 0usize;
        while size > 1 {
            let half = size / 2;
            let mid = base + half;
            let cmp = f(unsafe { s.get_unchecked(mid) });
            base = if cmp == Less { mid } else { base };
            size -= half;
        }
        let cmp = f(unsafe { s.get_unchecked(base) });
        base + (cmp == Less) as usize
    }
    fn lower_bound_by_key<'a, K, F>(&'a self, k: &K, mut f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord,
    {
        self.lower_bound_by(|e| f(e).cmp(k))
    }

    fn upper_bound(&self, x: &Self::Item) -> usize
    where
        T: Ord,
    {
        self.upper_bound_by(|y| y.cmp(x))
    }

    fn upper_bound_by<'a, F>(&'a self, mut f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> Ordering,
    {
        let s = self;
        let mut size = s.len();
        if size == 0 {
            return 0;
        }
        let mut base = 0usize;
        while size > 1 {
            let half = size / 2;
            let mid = base + half;
            let cmp = f(unsafe { s.get_unchecked(mid) });
            base = if cmp == Greater { base } else { mid };
            size -= half;
        }
        let cmp = f(unsafe { s.get_unchecked(base) });
        base + (cmp != Greater) as usize
    }
    fn upper_bound_by_key<'a, K, F>(&'a self, k: &K, mut f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord,
    {
        self.upper_bound_by(|e| f(e).cmp(k))
    }

    fn equal_range(&self, x: &Self::Item) -> std::ops::Range<usize>
    where
        T: Ord,
    {
        self.equal_range_by(|y| y.cmp(x))
    }
    fn equal_range_by<'a, F>(&'a self, mut f: F) -> std::ops::Range<usize>
    where
        F: FnMut(&'a Self::Item) -> Ordering,
    {
        let s = self;
        let mut size = s.len();
        if size == 0 {
            return 0..0;
        }
        let mut base = (0usize, 0usize);
        while size > 1 {
            let half = size / 2;
            let mid = (base.0 + half, base.1 + half);
            let cmp = (
                f(unsafe { s.get_unchecked(mid.0) }),
                f(unsafe { s.get_unchecked(mid.1) }),
            );
            base = (
                if cmp.0 == Less { mid.0 } else { base.0 },
                if cmp.1 == Greater { base.1 } else { mid.1 },
            );
            size -= half;
        }
        let cmp = (
            f(unsafe { s.get_unchecked(base.0) }),
            f(unsafe { s.get_unchecked(base.1) }),
        );
        (base.0 + (cmp.0 == Less) as usize..base.1 + (cmp.1 != Greater) as usize)
    }

    fn equal_range_by_key<'a, K, F>(&'a self, k: &K, mut f: F) -> std::ops::Range<usize>
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord,
    {
        self.equal_range_by(|e| f(e).cmp(k))
    }
}

#[cfg(test)]
mod tests {
    use super::Ext;

    #[test]
    fn lower_bound() {
        let b: [u32; 0] = [];
        assert_eq!(b.lower_bound(&0), 0);
        let b = [1, 3, 3, 5];
        assert_eq!(b.lower_bound(&0), 0);
        assert_eq!(b.lower_bound(&1), 0);
        assert_eq!(b.lower_bound(&2), 1);
        assert_eq!(b.lower_bound(&3), 1);
        assert_eq!(b.lower_bound(&4), 3);
        assert_eq!(b.lower_bound(&5), 3);
        assert_eq!(b.lower_bound(&6), 4);
    }

    #[test]
    fn upper_bound() {
        let b: [u32; 0] = [];
        assert_eq!(b.upper_bound(&0), 0);
        let b = [1, 3, 3, 5];
        assert_eq!(b.upper_bound(&0), 0);
        assert_eq!(b.upper_bound(&1), 1);
        assert_eq!(b.upper_bound(&2), 1);
        assert_eq!(b.upper_bound(&3), 3);
        assert_eq!(b.upper_bound(&4), 3);
        assert_eq!(b.upper_bound(&5), 4);
        assert_eq!(b.upper_bound(&6), 4);
    }

    #[test]
    fn equal_range() {
        let b: [u32; 0] = [];
        assert_eq!(b.equal_range(&0), 0..0);
        let b = [1, 3, 3, 5];
        assert_eq!(b.equal_range(&0), 0..0);
        assert_eq!(b.equal_range(&1), 0..1);
        assert_eq!(b.equal_range(&2), 1..1);
        assert_eq!(b.equal_range(&3), 1..3);
        assert_eq!(b.equal_range(&4), 3..3);
        assert_eq!(b.equal_range(&5), 3..4);
        assert_eq!(b.equal_range(&6), 4..4);
    }
}
