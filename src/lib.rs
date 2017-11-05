use std::cmp::Ordering::{self, Less, Equal, Greater};

pub trait Ext {
    type Item;

    fn fast_binary_search(&self, x: &Self::Item) -> Result<usize, usize>
    where
        Self::Item: Ord;
    fn fast_binary_search_by<'a, F>(&'a self, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Self::Item) -> Ordering;
    fn fast_binary_search_by_key<'a, K, F>(&'a self, k: &K, f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;

    fn lower_bound(&self, x: &Self::Item) -> usize
    where
        Self::Item: Ord;
    fn lower_bound_by<'a, F>(&'a self, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> Ordering;
    fn lower_bound_by_key<'a, K, F>(&'a self, k: &K, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;

    fn upper_bound(&self, x: &Self::Item) -> usize
    where
        Self::Item: Ord;
    fn upper_bound_by<'a, F>(&'a self, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> Ordering;
    fn upper_bound_by_key<'a, K, F>(&'a self, k: &K, f: F) -> usize
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;

    fn equal_range(&self, x: &Self::Item) -> std::ops::Range<usize>
    where
        Self::Item: Ord;
    fn equal_range_by<'a, F>(&'a self, f: F) -> std::ops::Range<usize>
    where
        F: FnMut(&'a Self::Item) -> Ordering;
    fn equal_range_by_key<'a, K, F>(&'a self, k: &K, f: F) -> std::ops::Range<usize>
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord;
}

impl<T> Ext for [T] {
    type Item = T;

    fn fast_binary_search(&self, x: &Self::Item) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.fast_binary_search_by(|y| y.cmp(x))
    }
    fn fast_binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Self::Item) -> Ordering,
    {
        let s = self;
        let mut size = s.len();
        if size == 0 {
            return Err(0);
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
        if cmp == Equal {
            Ok(base)
        } else {
            Err(base + (cmp == Less) as usize)
        }
    }
    fn fast_binary_search_by_key<'a, K, F>(&'a self, k: &K, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a Self::Item) -> K,
        K: Ord,
    {
        self.fast_binary_search_by(|e| f(e).cmp(k))
    }

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
        (self.lower_bound_by(&mut f)..self.upper_bound_by(&mut f))
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
    fn binary_search() {
        let b: [u32; 0] = [];
        assert_eq!(b.fast_binary_search(&0), Err(0));
    }

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
        assert_eq!(b.equal_range(&0), (0..0));
        let b = [1, 3, 3, 5];
        assert_eq!(b.equal_range(&0), (0..0));
        assert_eq!(b.equal_range(&1), (0..1));
        assert_eq!(b.equal_range(&2), (1..1));
        assert_eq!(b.equal_range(&3), (1..3));
        assert_eq!(b.equal_range(&4), (3..3));
        assert_eq!(b.equal_range(&5), (3..4));
        assert_eq!(b.equal_range(&6), (4..4));
    }
}
