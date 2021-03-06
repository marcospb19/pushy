//! A pushable array type with fixed capacity.

#![allow(rustdoc::all)]
#![warn(unsafe_op_in_unsafe_fn)]
#![allow(clippy::missing_safety_doc)]
#![cfg_attr(not(any(std, test)), no_std)]

use core::{
    fmt::Debug,
    hash::Hash,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr,
};
#[cfg(std)]
use std::vec::Vec;

#[macro_export]
macro_rules! arr {
    () => (
        $crate::PushArray::new()
    );
    ($($x:expr),+ $(,)?) => (
        $crate::PushArray::from([$($x),+])
    );
    ($elem:expr; $n:expr) => (
        $crate::PushArray::from_elem($elem, $n)
    );
}

/// A pushable array with fixed capacity.
///
/// Stack-allocated drop-in replacement for `Vec`, panic on `.push()` if capacity is
/// exhausted, see `.push_checked()` if you want a checked alternative.
///
/// # Examples
///
/// ```
/// use pushy::PushArray;
///
/// let mut array: PushArray<i32, 5> = PushArray::new();
/// array.push(1);
/// array.push(2);
/// array.push(3);
///
/// assert_eq!(array.len(), 3);
/// assert_eq!(array[0], 1);
///
/// assert_eq!(array.pop(), Some(3));
/// assert_eq!(array.len(), 2);
///
/// array[0] = 7;
/// assert_eq!(array, [7, 2]);
/// ```
pub struct PushArray<T, const CAP: usize> {
    buf: [MaybeUninit<T>; CAP],
    len: usize,
}

impl<T, const CAP: usize> PushArray<T, CAP> {
    /// Create an empty [`PushArray`] with the given capacity.
    /// ```
    /// # use pushy::PushArray;
    /// let mut arr: PushArray<u8, 5> = PushArray::new();
    ///
    /// assert!(arr.is_empty());
    /// assert_eq!(arr.len(), 0);
    /// assert_eq!(arr, []);
    /// ```
    pub const fn new() -> Self {
        // Safety: safe because target type is [MaybeUninit<T>; CAP], it does not drop nor requires initialization
        let buf = unsafe { MaybeUninit::uninit().assume_init() };
        Self { buf, len: 0 }
    }

    pub fn append(&mut self, other: &mut Self) {
        unsafe {
            self.append_elements(other.buf.as_slice() as *const [MaybeUninit<T>] as *const [T]);
            other.set_len(0);
        }
    }

    #[cfg(no_std)]
    pub fn append_vec(&mut self, other: &mut std::vec::Vec<T>) {
        unsafe {
            self.append_elements(other.as_slice() as *const [T]);
            other.set_len(0);
        }
    }

    // For the macro arr![elem; N]
    #[allow(dead_code)] // Only used in macro
    fn from_elem(elem: T, n: usize) -> Self
    where
        T: Clone,
    {
        let mut new = Self::new();
        for _ in 0..n.saturating_sub(1) {
            new.push(elem.clone());
        }
        new.push(elem);
        new
    }

    pub fn dedup(&mut self) {
        todo!();
    }

    pub fn dedup_by(&mut self) {
        todo!();
    }

    pub fn dedup_by_key(&mut self) {
        todo!();
    }

    pub fn drain(&mut self) {
        todo!();
    }

    pub fn drain_filter(&mut self) {
        todo!();
    }

    unsafe fn append_elements(&mut self, other: *const [T]) {
        let count = unsafe { (*other).len() };
        assert!(self.len + count <= self.buf.len(), "no capacity for append");
        unsafe {
            ptr::copy_nonoverlapping(other as *const T, self.as_mut_ptr().add(self.len), count)
        };
        self.len += count;
    }

    /// Pushes an element to the back of the [`PushArray`] without
    /// checking the boundaries of the array first.
    ///
    /// # Safety
    ///
    /// Caller must ensure that there is enough capacity.
    pub unsafe fn push_unchecked(&mut self, value: T) {
        let ptr = self.buf.as_mut_ptr();
        unsafe {
            ptr.add(self.len).write(MaybeUninit::new(value));
        }
        self.len += 1;
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        assert!(new_len <= self.capacity());

        self.len = new_len;
    }

    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Push an element to the end of this array after making sure
    /// that the array has enough space to hold it.
    ///
    /// ```
    /// # use pushy::PushArray;
    /// let mut arr: PushArray<u32, 2> = PushArray::new();
    ///
    /// assert!(arr.push_checked(5).is_some());
    /// assert!(arr.push_checked(20).is_some());
    ///
    /// // Not enough capacity!
    /// assert!(arr.push_checked(9).is_none());
    /// ```
    pub fn push_checked(&mut self, value: T) -> Option<()> {
        unsafe { (self.len < CAP).then(|| self.push_unchecked(value)) }
    }

    /// Push an element to the back of this [`PushArray`].
    ///
    /// # Panics
    ///
    /// Panics if the capacity of this array is overrun.
    pub fn push(&mut self, value: T) {
        self.push_checked(value).expect("overflow in PushArray!")
    }

    /// Push all elements of the given array at the end of the [`PushArray`].
    pub fn push_array<const M: usize>(&mut self, array: [T; M]) -> Option<()> {
        if self.len + M > CAP {
            return None;
        }

        unsafe {
            // Safety: we've just checked that there is enough capacity to
            // push these elements into our array.
            (self.as_mut_ptr().add(self.len) as *mut [T; M]).write(array);
        }

        self.len += M;

        Some(())
    }

    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len());

        let value = unsafe { self.as_mut_ptr().add(index).read() };

        for i in index..self.len - 1 {
            unsafe {
                let ptr = self.as_mut_ptr().add(i);
                ptr.write(ptr.add(1).read());
            }
        }
        self.len -= 1;

        value
    }

    pub fn swap_remove(&mut self, index: usize) -> T {
        #[cold]
        #[inline(never)]
        fn assert_failed(index: usize, len: usize) -> ! {
            panic!("swap_remove index (is {index}) should be < len (is {len})");
        }

        let len = self.len();
        if index >= len {
            assert_failed(index, len);
        }
        unsafe {
            // We replace self[index] with the last element. Note that if the
            // bounds check above succeeds there must be a last element (which
            // can be self[index] itself).
            let value = ptr::read(self.as_ptr().add(index));
            let base_ptr = self.as_mut_ptr();
            ptr::copy(base_ptr.add(len - 1), base_ptr.add(index), 1);
            self.set_len(len - 1);
            value
        }
    }

    /// Removes the last element from a array and returns it, or [`None`] if it
    /// is empty.
    ///
    /// If you'd like to pop the first element, consider using
    /// [`VecDeque::pop_front`] instead.
    ///
    /// [`VecDeque::pop_front`]: crate::collections::VecDeque::pop_front
    ///
    /// # Examples
    ///
    /// ```
    /// let mut vec = vec![1, 2, 3];
    /// assert_eq!(vec.pop(), Some(3));
    /// assert_eq!(vec, [1, 2]);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                self.len -= 1;
                Some(ptr::read(self.as_ptr().add(self.len())))
            }
        }
    }

    /// Gets a pointer to the first element of the array.
    pub fn as_ptr(&self) -> *const T {
        &self.buf as *const [MaybeUninit<T>] as *const T
    }

    /// Gets a mutable pointer to the first element of the array.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        &mut self.buf as *mut [MaybeUninit<T>] as *mut T
    }

    /// Reference to inner slice.
    pub fn as_slice(&self) -> &[T] {
        self.deref()
    }

    /// Mutable reference to inner slice.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.deref_mut()
    }

    /// Clear the [`PushArray`]. Dropping it's elements.
    ///
    /// ```
    /// # use pushy::PushArray;
    /// let mut bytes: PushArray<u8, 5> = PushArray::new();
    /// bytes.push_str("Hello").unwrap();
    ///
    /// assert_eq!(
    ///     bytes.as_str().unwrap(),
    ///     "Hello"
    /// );
    ///
    /// // Logically clear this array
    /// bytes.clear();
    ///
    /// assert_eq!(
    ///     bytes.as_str().unwrap(),
    ///     ""
    /// );
    /// ```
    pub fn clear(&mut self) {
        unsafe {
            core::ptr::drop_in_place(self.as_mut_slice());
        }
        self.len = 0;
    }
}

impl<T: Copy, const CAP: usize> PushArray<T, CAP> {
    /// Copy the elements from the given slice into the end of the [`PushArray`].
    ///
    // ```
    // # use pushy::PushArray;
    // let mut bytes: PushArray<u8, 5> = PushArray::new();
    // bytes.extend_from_slice(b"Hello").unwrap();
    //
    // assert_eq!(bytes.as_str(), Some("Hello"));
    // ```
    pub fn extend_from_slice(&mut self, slice: &[T]) -> Option<()> {
        if self.len + slice.len() > CAP {
            return None;
        }

        // Safety: we've just checked that there is enough storage
        //         to hold the new elements.
        //
        //         We also know these elements are trivially copiable since they implement Copy.
        unsafe {
            core::ptr::copy_nonoverlapping(
                slice.as_ptr(),
                self.as_mut_ptr().add(self.len),
                slice.len(),
            );
        }

        self.len += slice.len();
        Some(())
    }
}

impl<const CAP: usize> PushArray<u8, CAP> {
    /// Returns the bytes of this [`PushArray`] as a `&str` if they're valid UTF-8.
    /// ```
    /// # use pushy::PushArray;
    /// let mut bytes: PushArray<u8, 11> = PushArray::new();
    /// bytes.push_str("Hello").unwrap();
    /// assert_eq!(bytes.as_str(), Some("Hello"));
    ///
    /// bytes.push_str(" World").unwrap();
    /// assert_eq!(bytes.as_str(), Some("Hello World"));
    /// ```
    #[doc(hidden)]
    pub fn as_str(&self) -> Option<&str> {
        core::str::from_utf8(self).ok()
    }

    /// PLACEHOLDER TEXT
    ///
    /// # Safety
    ///
    /// Caller must ensure array is made of valid utf-8
    #[doc(hidden)]
    pub unsafe fn as_str_unchecked(&self) -> &str {
        unsafe { core::str::from_utf8_unchecked(self) }
    }

    /// Push a UTF-8 string to the back of this [`PushArray`].
    ///
    /// ```
    /// # use pushy::PushArray;
    /// let mut bytes: PushArray<u8, 11> = PushArray::new();
    ///
    /// assert_eq!(bytes.as_str(), Some(""));
    /// bytes.push_str("Hello").unwrap();
    /// assert_eq!(bytes.as_str(), Some("Hello"));
    /// ```
    pub fn push_str(&mut self, value: &str) -> Option<()> {
        let bytes = value.as_bytes();

        self.extend_from_slice(bytes)
    }
}

impl<T, const CAP: usize, const LEN: usize> From<[T; LEN]> for PushArray<T, CAP> {
    fn from(other: [T; LEN]) -> Self {
        other.into_iter().collect()
    }
}

impl<T: Clone, const CAP: usize> Clone for PushArray<T, CAP> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T: Hash, const CAP: usize> Hash for PushArray<T, CAP> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
        self.len.hash(state);
    }
}

impl<T, const CAP: usize> AsRef<[T]> for PushArray<T, CAP> {
    fn as_ref(&self) -> &[T] {
        self.deref()
    }
}

impl<T: PartialEq, const CAP: usize, U> PartialEq<U> for PushArray<T, CAP>
where
    U: AsRef<[T]>,
{
    fn eq(&self, other: &U) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T: Eq, const CAP: usize> Eq for PushArray<T, CAP> {}

impl<T: PartialOrd, const CAP: usize> PartialOrd for PushArray<T, CAP> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.as_slice().partial_cmp(other)
    }
}

impl<T: Ord, const CAP: usize> Ord for PushArray<T, CAP> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_slice().cmp(other)
    }
}

impl<T: Debug, const CAP: usize> Debug for PushArray<T, CAP> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PushArray")
            .field("initialized", self)
            .finish()
    }
}

impl<T, const CAP: usize> Drop for PushArray<T, CAP> {
    fn drop(&mut self) {
        self.clear()
    }
}

impl<T, const CAP: usize> Deref for PushArray<T, CAP> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len) }
    }
}

impl<T, const CAP: usize> DerefMut for PushArray<T, CAP> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }
}

impl<T, const CAP: usize> FromIterator<T> for PushArray<T, CAP> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut arr = Self::new();

        for item in iter {
            arr.push(item);
        }

        arr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pop_str() {
        let mut arr: PushArray<&str, 2> = PushArray::new();
        arr.push("Over");
        arr.push("There");
        assert_eq!(arr.len(), 2);

        let popped = arr.pop().unwrap();
        assert_eq!(arr.len(), 1);

        arr.push("Here");

        assert_eq!(arr.as_slice(), &["Over", "Here"]);
        assert_eq!(popped, "There");
    }

    #[test]
    fn test_partial_eq() {
        let mut arr1: PushArray<u64, 2> = PushArray::new();
        arr1.push(5);
        arr1.push(10);

        let mut arr2: PushArray<u64, 2> = PushArray::new();
        arr2.push(5);
        arr2.push(10);

        assert_eq!(arr1, arr2);
    }

    #[test]
    fn test_into_iter() {
        let mut arr: PushArray<u64, 2> = PushArray::new();
        arr.push(5);
        arr.push(10);

        let sum: u64 = arr.into_iter().sum();
        assert_eq!(sum, 15);
    }

    #[test]
    fn test_deref_to_slice() {
        let mut arr: PushArray<u8, 5> = PushArray::new();
        arr.push_str("World").unwrap();

        let slice: &[u8] = &*arr;

        assert_eq!(slice, arr.as_slice());
    }

    #[test]
    fn test_extend_from_slice_fails_when_not_enough_capacity() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        let zeroes = [0, 0, 0, 0];

        assert!(arr.extend_from_slice(&zeroes).is_none());
    }

    #[test]
    fn test_push_array_fails_when_not_enough_capacity() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        let zeroes = [0, 0, 0, 0];

        assert!(arr.push_array(zeroes).is_none());
    }

    #[test]
    fn test_push_checked() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        assert!(arr.push_checked(10).is_some());
        assert!(arr.push_checked(20).is_some());
        assert!(arr.push_checked(30).is_some());

        // Not enough capacity!
        assert!(arr.push_checked(50).is_none());
        assert!(arr.push_checked(60).is_none());
    }

    #[test]
    fn test_length() {
        let mut bytes: PushArray<u8, 9> = PushArray::new();
        assert_eq!(bytes.len(), 0);
        assert!(bytes.is_empty());

        bytes.push(b'H');
        assert_eq!(bytes.len(), 1);
        assert_eq!(bytes.is_empty(), false);

        bytes.push_str("ey ").unwrap();
        assert_eq!(bytes.len(), 4);
        assert_eq!(bytes.is_empty(), false);

        let hello = [b'H', b'e', b'l', b'l', b'o'];
        bytes.push_array(hello).unwrap();
        assert_eq!(bytes.len(), 9);

        bytes.clear();
        assert_eq!(bytes.len(), 0);
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_push_array() {
        let mut bytes: PushArray<u8, 10> = PushArray::new();
        let hello = [b'H', b'e', b'l', b'l', b'o'];
        bytes.extend_from_slice(&hello).unwrap();
        assert_eq!(bytes.as_str(), Some("Hello"));

        bytes.push_array(hello).unwrap();
        assert_eq!(bytes.as_str(), Some("HelloHello"));
    }

    #[test]
    fn test_as_str_and_push_str() {
        let mut bytes: PushArray<u8, 11> = PushArray::new();
        bytes.push_str("Hello").unwrap();
        assert_eq!(bytes.as_str(), Some("Hello"));

        bytes.push(b' ');
        assert_eq!(bytes.as_str(), Some("Hello "));

        bytes.push_str("World").unwrap();
        assert_eq!(bytes.as_str(), Some("Hello World"));
    }

    #[test]
    fn test_extend_from_slice() {
        let mut arr: PushArray<_, 10usize> = PushArray::new();
        let byte_slice = b"rogue-like";

        arr.extend_from_slice(byte_slice).unwrap();

        assert_eq!(arr.as_slice(), byte_slice)
    }

    #[test]
    fn test_get() {
        let mut arr: PushArray<u8, 10> = PushArray::new();
        arr.push_str("Hey").unwrap();

        assert_eq!(arr.get(0), Some(&b'H'));
        assert_eq!(arr.get(1), Some(&b'e'));
        assert_eq!(arr.get(2), Some(&b'y'));
        assert_eq!(arr.get(3), None);
    }

    #[test]
    fn test_get_mut() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        arr.push_str("Hey").unwrap();

        assert_eq!(arr.as_str().unwrap(), "Hey");

        let t = arr.get_mut(1).unwrap();
        *t = b'a';

        assert_eq!(arr.as_str().unwrap(), "Hay");
    }

    #[test]
    fn test_index_impl() {
        let mut arr: PushArray<u8, 3> = PushArray::new();

        arr.push_str("Hey").unwrap();

        assert_eq!(arr[0], b'H');
        assert_eq!(arr[1], b'e');
        assert_eq!(arr[2], b'y');
    }

    #[test]
    #[should_panic]
    fn test_index_panics_when_out_of_bounds() {
        let mut arr: PushArray<u8, 3> = PushArray::new();

        arr.push_str("Hey").unwrap();

        assert_eq!(arr[0], b'H');
        assert_eq!(arr[1], b'e');
        assert_eq!(arr[2], b'y');
        arr[3]; // uh-oh
    }

    #[test]
    #[should_panic]
    fn test_panics_when_overflows() {
        let mut numbers: PushArray<u32, 1> = PushArray::new();
        numbers.push(2); // ok
        numbers.push(3); // uh-oh!
    }

    #[test]
    fn test_initialized_i32() {
        let mut numbers: PushArray<u32, 50> = PushArray::new();
        for number in [2, 5, 7, 2, 3, 4] {
            numbers.push(number);
        }

        assert_eq!(&numbers, &[2, 5, 7, 2, 3, 4]);
        assert_eq!(&numbers[..], &[2, 5, 7, 2, 3, 4]);
        assert_eq!(numbers.as_ref(), &[2, 5, 7, 2, 3, 4]);
        assert_eq!(numbers.as_slice(), &[2, 5, 7, 2, 3, 4]);
    }

    #[test]
    fn test_initialized_str() {
        let mut words: PushArray<&str, 50> = PushArray::new();
        for word in ["hey", "there", "friend"] {
            words.push(word);
        }

        assert_eq!(words, &["hey", "there", "friend"]);

        words.push("miss ya");
        assert_eq!(words, &["hey", "there", "friend", "miss ya"]);
    }

    #[test]
    fn test_initiliazed_when_uninitialized() {
        let numbers: PushArray<u8, 20> = PushArray::new();
        assert_eq!(numbers, &[])
    }

    #[test]
    fn test_collect_iterator() {
        let array = [1, 2, 3, 4];
        let numbers: PushArray<u8, 20> = array.iter().copied().collect();

        assert_eq!(numbers.as_slice(), array.as_slice());
    }

    #[test]
    #[should_panic]
    fn test_collect_iterator_capacity_error() {
        let array = [1, 2, 3, 4];
        let numbers: PushArray<u8, 3> = array.iter().copied().collect();

        assert_eq!(numbers.as_ref(), array.as_slice());
    }

    #[test]
    fn test_collect_iterator_empty_without_capacity_dont_panic() {
        let array = [];
        let numbers: PushArray<u8, 0> = array.iter().copied().collect();

        assert_eq!(numbers.as_slice(), array.as_slice());
    }

    #[test]
    fn test_macros() {
        let pushy: PushArray<i32, 100> = arr![];
        assert_eq!(pushy, []);

        let pushy: PushArray<_, 4> = arr![1, 2, 3, 4];

        assert_eq!(pushy.len(), 4);
        assert_eq!(pushy.capacity(), 4);

        assert_eq!(pushy, [1, 2, 3, 4]);

        let pushy: PushArray<_, 4> = arr![1; 4];
        assert_eq!(pushy, [1, 1, 1, 1]);
    }

    #[test]
    fn test_from_array() {
        let array = [1, 2, 3, 4];

        let array: PushArray<u16, 6> = PushArray::from(array);

        // let numbers: PushArray<u8, 0> = array.iter().copied().collect();
        assert_eq!(array.len(), 4);
        assert_eq!(array.capacity(), 6);

        assert_eq!(array, [1, 2, 3, 4]);
    }

    #[test]
    fn test_sort() {
        let mut arr: PushArray<i32, 1024> = [5, 3, 2, 1, 4].into();
        arr.sort();
        assert_eq!(&arr, &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_remove() {
        let mut arr: PushArray<i32, 1024> = [4, 5, 1, 8, 2, 3, 6, 7].into();

        assert_eq!(&arr, &[4, 5, 1, 8, 2, 3, 6, 7]);
        assert_eq!(arr.remove(2), 1);
        assert_eq!(&arr, &[4, 5, 8, 2, 3, 6, 7]);
        assert_eq!(arr.remove(3), 2);
        assert_eq!(&arr, &[4, 5, 8, 3, 6, 7]);
        assert_eq!(arr.remove(3), 3);
        assert_eq!(&arr, &[4, 5, 8, 6, 7]);
        assert_eq!(arr.remove(0), 4);
        assert_eq!(&arr, &[5, 8, 6, 7]);
        assert_eq!(arr.remove(0), 5);
        assert_eq!(&arr, &[8, 6, 7]);
        assert_eq!(arr.remove(1), 6);
        assert_eq!(&arr, &[8, 7]);
        assert_eq!(arr.remove(1), 7);
        assert_eq!(&arr, &[8]);
        assert_eq!(arr.remove(0), 8);
        assert_eq!(&arr, &[]);
    }

    #[test]
    fn test_swap_remove() {
        let mut arr: PushArray<i32, 1024> = [4, 5, 1, 8, 2, 3, 6, 7].into();

        assert_eq!(&arr, &[4, 5, 1, 8, 2, 3, 6, 7]);
        assert_eq!(arr.swap_remove(2), 1);
        assert_eq!(&arr, &[4, 5, 7, 8, 2, 3, 6]);
        assert_eq!(arr.swap_remove(4), 2);
        assert_eq!(&arr, &[4, 5, 7, 8, 6, 3]);
        assert_eq!(arr.swap_remove(5), 3);
        assert_eq!(&arr, &[4, 5, 7, 8, 6]);
        assert_eq!(arr.swap_remove(0), 4);
        assert_eq!(&arr, &[6, 5, 7, 8]);
        assert_eq!(arr.swap_remove(1), 5);
        assert_eq!(&arr, &[6, 8, 7]);
        assert_eq!(arr.swap_remove(0), 6);
        assert_eq!(&arr, &[7, 8]);
        assert_eq!(arr.swap_remove(0), 7);
        assert_eq!(&arr, &[8]);
        assert_eq!(arr.swap_remove(0), 8);
        assert_eq!(&arr, &[]);
    }

    #[test]
    #[should_panic]
    fn test_remove_panics() {
        let mut arr: PushArray<i32, 1024> = arr![0; 1024];
        arr.remove(1024);
    }
}

#[cfg(all(test, feature = "std"))]
mod tests_with_std {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn test_drop() {
        let arc = Arc::new(0);

        {
            let mut arr: PushArray<_, 3> = PushArray::new();
            for _ in 0..3 {
                arr.push(arc.clone());
                assert_eq!(Arc::strong_count(&arc), 1 + arr.len());
            }
            // There should now be 4 references to the
            // element of the Arc
            assert_eq!(Arc::strong_count(&arc), 4);
        }

        // The PushArray must've been dropped
        //
        // Therefore the reference count of the Arc
        // should now be 1.
        assert_eq!(Arc::strong_count(&arc), 1);
    }

    #[test]
    fn test_clear() {
        let arc = Arc::new(0);

        let mut arr: PushArray<_, 4> = PushArray::new();
        for _ in 0..4 {
            arr.push(arc.clone());
        }

        let popped = arr.pop().unwrap();

        arr.clear();

        assert_eq!(Arc::strong_count(&arc), 2);
        assert_eq!(arr.len(), 0);
        assert_eq!(*popped, 0);
    }

    #[test]
    fn test_pop_drop() {
        let arc = Arc::new(0);
        let mut arr: PushArray<_, 1> = PushArray::new();

        arr.push(arc.clone());
        assert_eq!(Arc::strong_count(&arc), 2);

        arr.pop().unwrap();
        assert_eq!(Arc::strong_count(&arc), 1);
    }
}
