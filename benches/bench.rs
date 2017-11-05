#![feature(test)]

extern crate ordslice;
extern crate rand;
extern crate test;

use rand::distributions::Range;
use rand::distributions::IndependentSample;
use ordslice::Ext;
use test::Bencher;

enum Cache {
    L1,
    L2,
    L3,
}

enum Config {
    Unique,
    Dups,
}

impl Cache {
    pub fn size(&self) -> usize {
        match *self {
            Cache::L1 => 1000, // 8kb
            Cache::L2 => 10_000, // 80kb
            Cache::L3 => 1_000_000, // 8Mb
        }
    }
}

macro_rules! for_each_config {
    () => (
        #[bench]
        fn unique(b: &mut Bencher) {
            run(b, Config::Unique);
        }
        #[bench]
        fn dups(b: &mut Bencher) {
            run(b, Config::Dups);
        }
    )
}

macro_rules! for_each_cache {
    () => (
        mod l1 {
            pub use super::*;
            fn run(b: &mut Bencher, config: Config) {
                super::run(b, Cache::L1, config)
            }

            for_each_config!();
        }
        mod l2 {
            pub use super::*;
            fn run(b: &mut Bencher, config: Config) {
                super::run(b, Cache::L2, config)
            }

            for_each_config!();
        }
        mod l3 {
            pub use super::*;
            fn run(b: &mut Bencher, config: Config) {
                super::run(b, Cache::L3, config)
            }

            for_each_config!();
        }
    )
}

fn generate_inputs(cache: Cache, config: Config) -> (Vec<usize>, Vec<usize>) {
    let size = cache.size();
    let between = Range::new(0, size * 16);
    let mut rng = rand::thread_rng();
    let mut values = Vec::with_capacity(size);
    for _ in 0..size {
        let sample = between.ind_sample(&mut rng);
        let sample = match config {
            Config::Dups => sample / 16 * 16,
            Config::Unique => sample,
        };
        values.push(sample);
    }
    values.sort();
    let mut lookups = Vec::with_capacity(size);
    for _ in 0..size {
        lookups.push(between.ind_sample(&mut rng));
    }
    (values, lookups)
}

mod binary_search {
    pub use super::*;
    fn run(b: &mut Bencher, cache: Cache, config: Config) {
        let (values, lookups) = generate_inputs(cache, config);
        let mut iter = lookups.iter();
        b.iter(|| {
            let k = match iter.next() {
                Some(k) => k,
                None => {
                    iter = lookups.iter();
                    iter.next().unwrap()
                }
            };
            values.fast_binary_search(&k).is_ok()
        })
    }

    for_each_cache!();
}

mod lower_bound {
    pub use super::*;
    fn run(b: &mut Bencher, cache: Cache, config: Config) {
        let (values, lookups) = generate_inputs(cache, config);
        let mut iter = lookups.iter();
        b.iter(|| {
            let k = match iter.next() {
                Some(k) => k,
                None => {
                    iter = lookups.iter();
                    iter.next().unwrap()
                }
            };
            values.lower_bound(&k)
        })
    }

    for_each_cache!();
}


mod upper_bound {
    pub use super::*;
    fn run(b: &mut Bencher, cache: Cache, config: Config) {
        let (values, lookups) = generate_inputs(cache, config);
        let mut iter = lookups.iter();
        b.iter(|| {
            let k = match iter.next() {
                Some(k) => k,
                None => {
                    iter = lookups.iter();
                    iter.next().unwrap()
                }
            };
            values.upper_bound(&k)
        })
    }

    for_each_cache!();
}


mod equal_range {
    pub use super::*;
    fn run(b: &mut Bencher, cache: Cache, config: Config) {
        let (values, lookups) = generate_inputs(cache, config);
        let mut iter = lookups.iter();
        b.iter(|| {
            let k = match iter.next() {
                Some(k) => k,
                None => {
                    iter = lookups.iter();
                    iter.next().unwrap()
                }
            };
            values.equal_range(&k)
        })
    }

    for_each_cache!();
}
