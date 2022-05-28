//! A pushable array type with fixed capacity.

// no_std except for testing
#![cfg_attr(not(test), no_std)]

mod trait_impls;

use core::{mem::MaybeUninit, ptr::addr_of_mut};

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
    #[inline]
    const fn array_of_uninit() -> [MaybeUninit<T>; CAP] {
        // Safety: safe since this is an array of `MaybeUninit`s and they don't require initialization
        unsafe { MaybeUninit::uninit().assume_init() }
    }

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
        let buf = Self::array_of_uninit();

        Self { buf, len: 0 }
    }

    /// Pushes an element to the back of the [`PushArray`] without
    /// checking the boundaries of the array first.
    ///
    /// # Safety
    ///
    /// The programmer must ensure this function does not push data after the end of the buffer, which would cause undefined behavior.
    pub unsafe fn push_unchecked(&mut self, value: T) {
        let ptr = self.buf.as_mut_ptr();
        addr_of_mut!(*ptr)
            .add(self.len)
            .write(MaybeUninit::new(value));

        self.len += 1;
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
    ///
    /// ```
    /// # use pushy::PushArray;
    /// let mut bytes: PushArray<u8, 2> = PushArray::new();
    /// bytes.push(b'H');
    /// bytes.push(b'i');
    ///
    /// assert_eq!(bytes.as_str().unwrap(), "Hi");
    /// ```
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

    /// Removes the last element from the `PushArray`.
    pub fn pop(&mut self) -> Option<T> {
        self.len = self.len.checked_sub(1)?;

        let mut popped = MaybeUninit::uninit();
        unsafe {
            let ptr = self.as_ptr().add(self.len) as *const T;
            popped.write(ptr.read());
            // Safety: we've just written to `popped`, therefore we
            //         can assume it's uninitialized
            Some(popped.assume_init())
        }
    }

    /// Gets a pointer to the first element of the array.
    ///
    /// # Safety
    ///
    /// * There is no guarantee that the first element pointed to is initialized.
    ///
    /// * There is no guarantee that the first element exists (if the capacity allocated was zero).
    pub unsafe fn as_ptr(&self) -> *const T {
        &self.buf as *const [MaybeUninit<T>] as *const T
    }

    /// Gets a mutable pointer to the first element of the array.
    ///
    /// # Safety
    ///
    /// * There is no guarantee that the first element pointed to is initialized.
    ///
    /// * There is no guarantee that the first element exists (if the capacity allocated was zero).
    pub unsafe fn as_mut_ptr(&mut self) -> *mut T {
        &mut self.buf as *mut [MaybeUninit<T>] as *mut T
    }

    /// Extracts a slice containing the entire array.
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Extracts a mutable slice containing the entire array.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    /// Clear the [`PushArray`]. All initialized elements will be dropped.
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
    pub fn as_str(&self) -> Option<&str> {
        core::str::from_utf8(self).ok()
    }

    pub unsafe fn as_str_unchecked(&self) -> &str {
        core::str::from_utf8_unchecked(self)
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

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::Arc;

    #[test]
    fn drop() {
        let arc = Arc::new(0);

        {
            let mut arr: PushArray<_, 3> = PushArray::new();
            for _ in 0..3 {
                arr.push(arc.clone());
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
    fn clear() {
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
    fn pop_drop() {
        let arc = Arc::new(0);
        let mut arr: PushArray<_, 1> = PushArray::new();

        arr.push(arc.clone());
        assert_eq!(Arc::strong_count(&arc), 2);

        arr.pop().unwrap();
        assert_eq!(Arc::strong_count(&arc), 1);
    }

    #[test]
    fn pop_str() {
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
    fn partial_eq() {
        let mut arr1: PushArray<u64, 2> = PushArray::new();
        arr1.push(5);
        arr1.push(10);

        let mut arr2: PushArray<u64, 2> = PushArray::new();
        arr2.push(5);
        arr2.push(10);

        assert_eq!(arr1, arr2);
    }

    #[test]
    fn into_iter() {
        let mut arr: PushArray<u64, 2> = PushArray::new();
        arr.push(5);
        arr.push(10);

        let sum: u64 = arr.into_iter().sum();
        assert_eq!(sum, 15);
    }

    #[test]
    fn deref_to_slice() {
        let mut arr: PushArray<u8, 5> = PushArray::new();
        arr.push_str("World").unwrap();

        let slice: &[u8] = &*arr;

        assert_eq!(slice, arr.as_slice());
    }

    #[test]
    fn extend_from_slice_fails_when_not_enough_capacity() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        let zeroes = [0, 0, 0, 0];

        assert!(arr.extend_from_slice(&zeroes).is_none());
    }

    #[test]
    fn push_array_fails_when_not_enough_capacity() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        let zeroes = [0, 0, 0, 0];

        assert!(arr.push_array(zeroes).is_none());
    }

    #[test]
    fn push_checked() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        assert!(arr.push_checked(10).is_some());
        assert!(arr.push_checked(20).is_some());
        assert!(arr.push_checked(30).is_some());

        // Not enough capacity!
        assert!(arr.push_checked(50).is_none());
        assert!(arr.push_checked(60).is_none());
    }

    #[test]
    fn length() {
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
    fn push_array() {
        let mut bytes: PushArray<u8, 10> = PushArray::new();
        let hello = [b'H', b'e', b'l', b'l', b'o'];
        bytes.extend_from_slice(&hello).unwrap();
        assert_eq!(bytes.as_str(), Some("Hello"));

        bytes.push_array(hello).unwrap();
        assert_eq!(bytes.as_str(), Some("HelloHello"));
    }

    #[test]
    fn as_str_and_push_str() {
        let mut bytes: PushArray<u8, 11> = PushArray::new();
        bytes.push_str("Hello").unwrap();
        assert_eq!(bytes.as_str(), Some("Hello"));

        bytes.push(b' ');
        assert_eq!(bytes.as_str(), Some("Hello "));

        bytes.push_str("World").unwrap();
        assert_eq!(bytes.as_str(), Some("Hello World"));
    }

    #[test]
    fn extend_from_slice() {
        let mut arr: PushArray<_, 10usize> = PushArray::new();
        let byte_slice = b"rogue-like";

        arr.extend_from_slice(byte_slice).unwrap();

        assert_eq!(arr.as_slice(), byte_slice)
    }

    #[test]
    fn get() {
        let mut arr: PushArray<u8, 10> = PushArray::new();
        arr.push_str("Hey").unwrap();

        assert_eq!(arr.get(0), Some(&b'H'));
        assert_eq!(arr.get(1), Some(&b'e'));
        assert_eq!(arr.get(2), Some(&b'y'));
        assert_eq!(arr.get(3), None);
    }

    #[test]
    fn get_mut() {
        let mut arr: PushArray<u8, 3> = PushArray::new();
        arr.push_str("Hey").unwrap();

        assert_eq!(arr.as_str().unwrap(), "Hey");

        let t = arr.get_mut(1).unwrap();
        *t = b'a';

        assert_eq!(arr.as_str().unwrap(), "Hay");
    }

    #[test]
    fn index_impl() {
        let mut arr: PushArray<u8, 3> = PushArray::new();

        arr.push_str("Hey").unwrap();

        assert_eq!(arr[0], b'H');
        assert_eq!(arr[1], b'e');
        assert_eq!(arr[2], b'y');
    }

    #[test]
    #[should_panic]
    fn index_panics_when_out_of_bounds() {
        let mut arr: PushArray<u8, 3> = PushArray::new();

        arr.push_str("Hey").unwrap();

        assert_eq!(arr[0], b'H');
        assert_eq!(arr[1], b'e');
        assert_eq!(arr[2], b'y');
        arr[3]; // uh-oh
    }

    #[test]
    #[should_panic]
    fn panics_when_overflows() {
        let mut numbers: PushArray<u32, 1> = PushArray::new();
        numbers.push(2); // ok
        numbers.push(3); // uh-oh!
    }

    #[test]
    fn initialized_i32() {
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
    fn initialized_str() {
        let mut words: PushArray<&str, 50> = PushArray::new();
        for word in ["hey", "there", "friend"] {
            words.push(word);
        }

        assert_eq!(words, &["hey", "there", "friend"]);

        words.push("miss ya");
        assert_eq!(words, &["hey", "there", "friend", "miss ya"]);
    }

    #[test]
    fn initiliazed_when_uninitialized() {
        let numbers: PushArray<u8, 20> = PushArray::new();
        assert_eq!(numbers, &[])
    }

    #[test]
    fn collect_iterator() {
        let array = [1, 2, 3, 4];
        let numbers: PushArray<u8, 20> = array.iter().copied().collect();

        assert_eq!(numbers.as_slice(), array.as_slice());
    }

    #[test]
    #[should_panic]
    fn collect_iterator_capacity_error() {
        let array = [1, 2, 3, 4];
        let numbers: PushArray<u8, 3> = array.iter().copied().collect();

        assert_eq!(numbers.as_ref(), array.as_slice());
    }

    #[test]
    fn collect_iterator_empty_without_capacity_dont_panic() {
        let array = [];
        let numbers: PushArray<u8, 0> = array.iter().copied().collect();

        assert_eq!(numbers.as_slice(), array.as_slice());
    }
}
