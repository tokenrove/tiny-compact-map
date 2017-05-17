//! Compact map of up to 64 elements.

#![warn(
    missing_copy_implementations,
    missing_docs,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces,
    variant_size_differences,
)]

#![feature(alloc, heap_api)]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

extern crate alloc;

use alloc::heap;
use std::{fmt, mem, ptr};

/// Compact map of up to 64 elements, where the keys are small integers
/// and the values are `T`.
pub struct TinyCompactMap<T> {
    bitmap: u64,
    elts: *mut T,
}

impl<T> fmt::Debug for TinyCompactMap<T>
    where T: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TinyCompactMap {{ bitmap: {:b}, elts: ", self.bitmap)?;
        f.debug_list()
            .entries((0..self.bitmap.count_ones())
                     .map(|i| unsafe { self.elts.offset(1+i as isize) }))
            .finish()?;
        write!(f, "}}")
    }
}

impl<T> TinyCompactMap<T> {
    /// Creates an empty map.
    pub fn new() -> Self {
        TinyCompactMap { bitmap: 0, elts: ptr::null_mut() }
    }

    fn index_of(&self, key: u8) -> Option<isize> {
        assert!(key < 64);
        if 0 == self.bitmap & 1<<key { return None }
        Some((self.bitmap & ((1<<key)-1)).count_ones() as isize)
    }

    /// Gets a mutable reference to the value associated with `key`.
    pub fn get_mut(&self, key: u8) -> Option<&mut T> {
        unsafe { self.index_of(key).and_then(|idx| self.elts.offset(idx).as_mut()) }
    }

    /// Gets a reference to the value associated with `key`.
    pub fn get(&self, key: u8) -> Option<&T> {
        unsafe { self.index_of(key).and_then(|idx| self.elts.offset(idx).as_ref()) }
    }

    /// Associates `value` with `key`, returning the old value if one
    /// existed.
    pub fn insert(&mut self, key: u8, value: T) -> Option<T> {
        assert!(key < 64);
        let t_size = mem::size_of::<T>();
        if let Some(slot) = self.get_mut(key) {
            return Some(mem::replace(slot, value))
        }
        let count = self.bitmap.count_ones() as usize;
        let old_size = t_size * count;
        let new_size = old_size + t_size;
        let new = unsafe {
            if self.bitmap == 0 {
                assert!(self.elts.is_null());
                heap::allocate(new_size, mem::align_of::<T>())
            } else {
                heap::reallocate(self.elts as *mut u8, old_size, new_size, mem::align_of::<T>())
            }
        };
        assert!(!new.is_null());
        self.elts = new as *mut T;
        self.bitmap |= 1<<key;
        let idx = (self.bitmap & ((1<<key) - 1)).count_ones() as isize;
        unsafe {
            ptr::copy(self.elts.offset(idx),
                      self.elts.offset(1+idx),
                      count - idx as usize);
            ptr::write(self.elts.offset(idx), value)
        };
        None
    }
}

impl<T> Drop for TinyCompactMap<T> {
    fn drop(&mut self) {
        if self.bitmap == 0 { return }
        let count = self.bitmap.count_ones() as usize;
        unsafe {
            let size = count * mem::size_of::<T>();
            for i in 0..count { ptr::drop_in_place(self.elts.offset(i as isize)); }
            heap::deallocate(self.elts as *mut u8, size, mem::align_of::<T>());
        }
    }
}

#[cfg(test)]
mod test {
    use super::TinyCompactMap;
    use quickcheck::TestResult;
    use std::collections::BTreeMap;

    #[derive(PartialEq,Debug)]
    struct ExplicitDrop<'a>(&'a mut bool);

    impl<'a> Drop for ExplicitDrop<'a> {
        fn drop(&mut self) { *self.0 = true; }
    }

    #[test]
    fn explicit_drop_test() {
        let mut canary = false;
        {
            let mut t = TinyCompactMap::new();
            assert_eq!(None, t.insert(42, ExplicitDrop(&mut canary)));
        }
        assert!(canary);
    }

    quickcheck! {
        fn insert_and_query(v: Vec<(u8,u64)>) -> TestResult {
            let v = v.iter().cloned().filter(|&(i,_f)| i <= 63).collect::<Vec<(u8,u64)>>();
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

        fn double_insert_gives_orig(v: Vec<(u8,u64)>) -> TestResult {
            let v = v.iter().cloned().filter(|&(i,_f)| i <= 63).collect::<Vec<(u8,u64)>>();
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
    }
}
