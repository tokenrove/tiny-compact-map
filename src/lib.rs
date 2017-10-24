//! Compact map of up to 64 elements.

#![warn(
    missing_copy_implementations,
    missing_docs,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces,
    variant_size_differences,
)]

#![feature(allocator_api)]
#![feature(unique)]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

use std::heap::{Alloc, Heap};
use std::{fmt, mem, ptr, u64};

/// Compact map of up to 64 elements, where the keys are small integers
/// and the values are `T`.
pub struct TinyCompactMap<T> {
    bitmap: u64,
    elts: Option<ptr::Unique<T>>,
}
/// Type of keys in a `TinyCompactMap`, which are always small
/// integers.
pub type Key = u8;

impl<T> fmt::Debug for TinyCompactMap<T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TinyCompactMap {{ bitmap: {:b}, elts: ", self.bitmap)?;
        {
            let mut list = f.debug_list();
            if let Some(p) = self.elts {
                list.entries((0..self.bitmap.count_ones())
                             .map(|i| unsafe { p.as_ptr().offset(1+i as isize) }));
            }
            list.finish()?;
        }
        write!(f, "}}")
    }
}

impl<T> TinyCompactMap<T> {
    /// Creates an empty map.
    pub fn new() -> Self {
        TinyCompactMap { bitmap: 0, elts: None }
    }

    fn index_of(&self, key: Key) -> Option<isize> {
        assert!(key < 64);
        if 0 == self.bitmap & 1<<key { return None }
        Some((self.bitmap & ((1<<key)-1)).count_ones() as isize)
    }

    /// Gets a mutable reference to the value associated with `key`.
    pub fn get_mut(&self, key: Key) -> Option<&mut T> {
        unsafe {
            self.index_of(key).and_then(|idx| self.elts.and_then({
                |p| p.as_ptr().offset(idx).as_mut()
            }))
        }
    }

    /// Gets a reference to the value associated with `key`.
    pub fn get(&self, key: Key) -> Option<&T> {
        unsafe {
            self.index_of(key).and_then(|idx| self.elts.and_then({
                |p| p.as_ptr().offset(idx).as_ref()
            }))
        }
    }

    /// Associates `value` with `key`, returning the old value if one
    /// existed.
    ///
    /// Panics on memory allocation failure.
    pub fn insert(&mut self, key: Key, value: T) -> Option<T> {
        assert!(key < 64);
        if let Some(slot) = self.get_mut(key) {
            return Some(mem::replace(slot, value))
        }
        let count = self.bitmap.count_ones() as usize;
        let new = unsafe {
            if let Some(p) = self.elts {
                Heap.realloc_array(p, count, 1+count).unwrap()
            } else {
                assert_eq!(0, self.bitmap);
                Heap.alloc_array(1+count).unwrap()
            }
        };
        self.elts = Some(new);
        self.bitmap |= 1<<key;
        let idx = (self.bitmap & ((1<<key) - 1)).count_ones() as isize;
        unsafe {
            ptr::copy(new.as_ptr().offset(idx),
                      new.as_ptr().offset(1+idx),
                      count - idx as usize);
            ptr::write(new.as_ptr().offset(idx), value)
        };
        None
    }

    /// Creates an iterator over this map.
    pub fn iter(&self) -> Iter<T> {
        Iter {
            map: self,
            front: 0,
            back: 0,
        }
    }
}

impl<T> Drop for TinyCompactMap<T> {
    fn drop(&mut self) {
        if let Some(p) = self.elts {
            let count = self.bitmap.count_ones() as usize;
            unsafe {
                for i in 0..count {
                    ptr::drop_in_place(p.as_ptr().offset(i as isize));
                }
                Heap.dealloc_array(p, count).unwrap();
            }
        }
    }
}

/// Iterator over a tiny compact map.
pub struct Iter<'a, T: 'a> {
    map: &'a TinyCompactMap<T>,
    front: Key,
    back: Key,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (Key, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.front + self.back >= 64 { return None }
        let masked = self.map.bitmap & !((1<<self.front)-1);
        if masked == 0 { return None }
        let next = masked.trailing_zeros() as u8;
        self.front = 1 + next;
        self.map.get(next).map(|v| (next, v))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front + self.back >= 64 { return None }
        let masked = self.map.bitmap & (u64::MAX>>self.back);
        if masked == 0 { return None }
        let lz = masked.leading_zeros() as u8;
        self.back = 1 + lz;
        let next = 63 - lz;
        self.map.get(next).map(|v| (next, v))
    }
}

#[cfg(test)]
mod test {
    use super::{TinyCompactMap, Key};
    use quickcheck::TestResult;
    use std::collections::BTreeMap;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Debug)]
    struct ExplicitDrop<'a>(&'a AtomicUsize);

    impl<'a> Drop for ExplicitDrop<'a> {
        fn drop(&mut self) { self.0.fetch_add(1, Ordering::Relaxed); }
    }

    #[test]
    fn explicit_drop_test() {
        let canary = AtomicUsize::new(0);
        {
            let mut t = TinyCompactMap::new();
            assert!(t.insert(42, ExplicitDrop(&canary)).is_none());
        }
        assert_eq!(1, canary.load(Ordering::Relaxed));
    }

    #[test]
    fn full_occupancy() {
        let mut m = TinyCompactMap::new();
        for i in 0..64 { m.insert(i,i); }
        assert!(m.iter().all(|(k,&v)| k == v));
    }

    #[test]
    fn reverse_iterator_full_occupancy() {
        let mut m = TinyCompactMap::new();
        let mut v = (0..64).collect::<Vec<_>>();
        for &i in v.iter() { m.insert(i,i); }
        v.reverse();
        assert_eq!(v, m.iter().rev().map(|(_k,&v)| v).collect::<Vec<_>>());
    }

    #[test]
    fn reverse_iterator() {
        let mut m = TinyCompactMap::new();
        let mut u = vec![(1,42),(10,23),(45,17)];
        for &(k,v) in u.iter() { m.insert(k,v); }
        u.reverse();
        assert_eq!(u, m.iter().rev().map(|(k,&v)| (k,v)).collect::<Vec<_>>());
    }


    quickcheck! {
        fn insert_and_query(v: Vec<(Key,u64)>) -> TestResult {
            let v = v.iter().cloned().filter(|&(i,_f)| i <= 63).collect::<Vec<(Key,u64)>>();
            let mut cv = TinyCompactMap::new();
            let mut tree = BTreeMap::new();
            for &(i,f) in v.iter() {
                assert_eq!(tree.insert(i, f), cv.insert(i, f));
            }
            for &(i,_) in v.iter() {
                assert_eq!(tree.get(&i), cv.get(i));
            }
            TestResult::passed()
        }

        fn double_insert_gives_orig(v: Vec<(Key,u64)>) -> TestResult {
            let v = v.iter().cloned().filter(|&(i,_f)| i <= 63).collect::<Vec<(Key,u64)>>();
            let mut cv = TinyCompactMap::new();
            let mut tree = BTreeMap::new();
            for &(i,f) in v.iter() {
                assert_eq!(tree.insert(i, f), cv.insert(i, f));
            }
            for &(i,f) in v.iter() {
                assert_eq!(tree.insert(i, f), cv.insert(i, f));
            }
            TestResult::passed()
        }

        fn insert_and_query_iter(v: Vec<(Key,u64)>) -> bool {
            let v = v.iter().cloned().filter(|&(i,_f)| i <= 63).collect::<Vec<(Key,u64)>>();
            let mut cv = TinyCompactMap::new();
            let mut tree = BTreeMap::new();
            for &(i,f) in v.iter() {
                assert_eq!(tree.insert(i, f), cv.insert(i, f));
            }
            cv.iter().zip(tree.iter()).all(|(a,(&bk,bv))| a == (bk,bv))
        }

        fn many_droppables(n: usize) -> bool {
            let canary = AtomicUsize::new(0);
            let n = ::std::cmp::min(n, 64);
            {
                let mut t = TinyCompactMap::new();
                for i in 0..n { t.insert(i as u8, ExplicitDrop(&canary)); }
            }
            n == canary.load(Ordering::Relaxed)
        }
    }
}
