use core::slice;
use std::mem::MaybeUninit;
use std::ptr;

use crate::{AbstractSnytaxTree, Equation};

fn suffix_postfix(len: usize) -> (String, String) {
    if len == 0 {
        ("".into(), "".into())
    } else {
        (0..(len / 2)).map(|_| (" ", " ")).collect()
    }
}

impl<T> Equation for T 
where 
    T: AbstractSnytaxTree,
    T::A: std::fmt::Display,
{
    fn solve(&self, vars: &[f32]) -> f32 {
        AbstractSnytaxTree::solve(self, vars)
    }

    fn render_tree(&self) -> Vec<String> {
        let mut display: Vec<String> = Vec::new();
        let (left, right, op) = self.get_values();
        let left = left.render_tree();
        let right = right.render_tree();
        let height = std::cmp::max(left.len(), right.len());
        let (ol, or) = (height - left.len(), height - right.len());
        for i in 0..height {
            match (i >= ol, i >= or) {
                (true, false) => {
                    let val = format!("{}  ", left.get(i - ol).cloned().unwrap_or_default());
                    let (pf, sf) = suffix_postfix(val.len() - 3);
                    display.push(val);
                    display.push(format!("{pf}\\{op} {sf}"));
                }
                (false, true) => {
                    let val = format!("  {}", right.get(i - or).cloned().unwrap_or_default());
                    let (pf, sf) = suffix_postfix(val.len() - 3);
                    display.push(val);
                    display.push(format!("{pf} {op}/{sf}"));
                }
                _ => {
                    let val = format!(
                        "{} {}",
                        left.get(i - ol).cloned().unwrap_or_default(),
                        right.get(i - or).cloned().unwrap_or_default()
                    );
                    let (pf, sf) = suffix_postfix(val.len() - 3);
                    display.push(val);
                    display.push(format!("{pf}\\{op}/{sf}"));
                }
            }
        }
        display
    }
}
impl<T: AbstractSnytaxTree, const N: usize> Equation for MathParser<T, N> where T::A: std::fmt::Display {
    fn solve(&self, vars: &[f32]) -> f32 {
        if let Some(e) = self.last() {
            AbstractSnytaxTree::solve(e, vars)
        } else {
            0.0
        }
    }

    fn render_tree(&self) -> Vec<String> {
        self.last()
            .map(|r| {
                // println!("Attempting to render tree {}", self.len());
                // println!("{:?}", self.as_slice());
                r.render_tree()
            })
            .unwrap_or_else(|| {
                // println!("No final item found {}", self.len());
                // println!("{:?}", self.as_slice());
                Vec::new()
            })
    }
}

pub struct MathParser<T, const N: usize> {
    // pub(crate) focus_of_eq: crate::graphing::Axis,
    pub(crate) l_len: usize,
    pub(crate) r_len: usize,
    pub(crate) _cached_ans: Option<f32>,
    pub(crate) equation: [MaybeUninit<T>; N],
}

impl<T, const N: usize> MathParser<T, N>
where
    T: Equation,
{
    pub fn solve(&self, vars: &[f32]) -> f32 {
        if let Some(e) = self.last() {
            e.solve(vars)
        } else {
            0.0
        }
    }
}

#[allow(unused, clippy::result_unit_err, clippy::missing_safety_doc)]
impl<T, const N: usize> MathParser<T, N> {
    const ELEM: MaybeUninit<T> = MaybeUninit::uninit();
    const INIT: [MaybeUninit<T>; N] = [Self::ELEM; N];

    pub fn new() -> Self {
        MathParser {
            equation: Self::INIT,
            ..Default::default()
        }
    }

    /// Pushes parts of the AST into the stack memory and returns their pointer
    unsafe fn left_ptr_push_unchecked(&mut self, item: T) -> usize {
        debug_assert!(!self.is_full());
        let mem_slot = unsafe { self.equation.get_unchecked_mut(self.l_len) };
        self.l_len += 1;
        mem_slot.write(item);
        mem_slot.as_ptr() as usize
    }

    /// Pushes parts of the AST into the stack memory and returns their pointer
    pub fn left_ptr_push(&mut self, val: T) -> usize {
        if self.l_len + self.r_len < self.capacity() {
            unsafe { self.left_ptr_push_unchecked(val) }
        } else {
            0
        }
    }

    unsafe fn right_ptr_push_unchecked(&mut self, item: T) -> usize {
        debug_assert!(!self.is_full());
        let mem_slot = unsafe { self.equation.get_unchecked_mut(self.r_len) };
        self.r_len -= 1;
        mem_slot.write(item);
        mem_slot.as_ptr() as usize
    }

    /// Pushes parts of the AST into the stack memory and returns their pointer
    pub fn right_ptr_push(&mut self, val: T) -> usize {
        if self.l_len + self.r_len < self.capacity() {
            unsafe { self.right_ptr_push_unchecked(val) }
        } else {
            0
        }
    }

    // ###############################
    // #   FURTHER IMPLEMENTATIONS   #
    // ###############################

    /// Constructs a new MathParsertor with a fixed capacity of `N` and fills it
    /// with the provided slice.
    ///
    /// This is equivalent to the following code:
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut v: MathParser<u8, 16> = MathParser::new();
    /// v.extend_from_slice(&[1, 2, 3]).unwrap();
    /// ```
    #[inline]
    pub fn from_slice(other: &[T]) -> Result<Self, ()>
    where
        T: Clone,
    {
        let mut v = MathParser::new();
        v.extend_from_slice(other)?;
        Ok(v)
    }

    /// Clones a MathParser into a new MathParser
    pub(crate) fn clone(&self) -> Self
    where
        T: Clone,
    {
        let mut new = Self::new();
        // avoid `extend_from_slice` as that introduces a runtime check / panicking branch
        for elem in self {
            unsafe {
                new.push_unchecked(elem.clone());
            }
        }
        new
    }

    /// Returns a raw pointer to the MathParsertor’s equation.
    pub fn as_ptr(&self) -> *const T {
        self.equation.as_ptr() as *const T
    }

    /// Returns a raw pointer to the MathParsertor’s equation, which may be mutated through.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.equation.as_mut_ptr() as *mut T
    }

    /// Extracts a slice containing the entire MathParsertor.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    /// let equation: MathParser<u8, 5> = MathParser::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// assert_eq!(equation.as_slice(), &[1, 2, 3, 5, 8]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &equation[..self.len]
        unsafe { slice::from_raw_parts(self.equation.as_ptr() as *const T, self.l_len) }
    }

    /// Returns the contents of the MathParsertor as an array of length `M` if the length
    /// of the MathParsertor is exactly `M`, otherwise returns `Err(self)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    /// let equation: MathParser<u8, 42> = MathParser::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// let array: [u8; 5] = equation.into_array().unwrap();
    /// assert_eq!(array, [1, 2, 3, 5, 8]);
    /// ```
    pub fn into_array<const M: usize>(self) -> Result<[T; M], Self> {
        if self.len() == M {
            // This is how the unstable `MaybeUninit::array_assume_init` method does it
            let array = unsafe { (&self.equation as *const _ as *const [T; M]).read() };

            // We don't want `self`'s destructor to be called because that would drop all the
            // items in the array
            core::mem::forget(self);

            Ok(array)
        } else {
            Err(self)
        }
    }

    /// Extracts a mutable slice containing the entire MathParsertor.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    /// let mut equation: MathParser<u8, 5> = MathParser::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// equation[0] = 9;
    /// assert_eq!(equation.as_slice(), &[9, 2, 3, 5, 8]);
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut equation[..self.len]
        unsafe { slice::from_raw_parts_mut(self.equation.as_mut_ptr() as *mut T, self.l_len) }
    }

    /// Returns the maximum number of elements the MathParsertor can hold.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Clears the MathParsertor, removing all values.
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Extends the MathParser from an iterator.
    ///
    /// # Panic
    ///
    /// Panics if the MathParser cannot hold all elements of the iterator.
    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for elem in iter {
            self.push(elem).ok().unwrap()
        }
    }

    /// Clones and appends all elements in a slice to the `MathParser`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `MathParser`. The `other` MathParsertor is traversed in-order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut MathParser = MathParser::<u8, 8>::new();
    /// MathParser.push(1).unwrap();
    /// MathParser.extend_from_slice(&[2, 3, 4]).unwrap();
    /// assert_eq!(*MathParser, [1, 2, 3, 4]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), ()>
    where
        T: Clone,
    {
        if self.l_len + other.len() > self.capacity() {
            // won't fit in the `MathParser`; don't modify anything and return an error
            Err(())
        } else {
            for elem in other {
                unsafe {
                    self.push_unchecked(elem.clone());
                }
            }
            Ok(())
        }
    }

    /// Removes the last element from a MathParsertor and returns it, or `None` if it's empty
    pub fn pop(&mut self) -> Option<T> {
        if self.l_len != 0 {
            Some(unsafe { self.pop_unchecked() })
        } else {
            None
        }
    }

    /// Appends an `item` to the back of the collection
    ///
    /// Returns back the `item` if the MathParsertor is full
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.l_len < self.capacity() {
            unsafe { self.push_unchecked(item) }
            Ok(())
        } else {
            Err(item)
        }
    }

    /// Removes the last element from a MathParsertor and returns it
    ///
    /// # Safety
    ///
    /// This assumes the MathParser to have at least one element.
    pub unsafe fn pop_unchecked(&mut self) -> T {
        debug_assert!(!self.is_empty());

        self.l_len -= 1;
        unsafe { self.equation.get_unchecked_mut(self.l_len).as_ptr().read() }
    }

    /// Appends an `item` to the back of the collection
    ///
    /// # Safety
    ///
    /// This assumes the MathParser is not full.
    pub unsafe fn push_unchecked(&mut self, item: T) {
        // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
        // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
        debug_assert!(!self.is_full());

        *unsafe { self.equation.get_unchecked_mut(self.l_len) } = MaybeUninit::new(item);

        self.l_len += 1;
    }

    /// Shortens the MathParsertor, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        // This is safe because:
        //
        // * the slice passed to `drop_in_place` is valid; the `len > self.len`
        //   case avoids creating an invalid slice, and
        // * the `len` of the MathParsertor is shrunk before calling `drop_in_place`,
        //   such that no value will be dropped twice in case `drop_in_place`
        //   were to panic once (if it panics twice, the program aborts).
        unsafe {
            // Note: It's intentional that this is `>` and not `>=`.
            //       Changing it to `>=` has negative performance
            //       implications in some cases. See rust-lang/rust#78884 for more.
            if len > self.l_len {
                return;
            }
            let remaining_len = self.l_len - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            self.l_len = len;
            ptr::drop_in_place(s);
        }
    }

    /// Resizes the MathParser in-place so that len is equal to new_len.
    ///
    /// If new_len is greater than len, the MathParser is extended by the
    /// difference, with each additional slot filled with value. If
    /// new_len is less than len, the MathParser is simply truncated.
    ///
    /// See also [`resize_default`](Self::resize_default).
    pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), ()>
    where
        T: Clone,
    {
        if new_len > self.capacity() {
            return Err(());
        }

        if new_len > self.l_len {
            while self.l_len < new_len {
                self.push(value.clone()).ok();
            }
        } else {
            self.truncate(new_len);
        }

        Ok(())
    }

    /// Resizes the `MathParser` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `MathParser` is extended by the
    /// difference, with each additional slot filled with `Default::default()`.
    /// If `new_len` is less than `len`, the `MathParser` is simply truncated.
    ///
    /// See also [`resize`](Self::resize).
    pub fn resize_default(&mut self, new_len: usize) -> Result<(), ()>
    where
        T: Clone + Default,
    {
        self.resize(new_len, T::default())
    }

    /// Forces the length of the MathParsertor to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a MathParsertor
    /// is done using one of the safe operations instead, such as
    /// [`truncate`], [`resize`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: Self::truncate
    /// [`resize`]: Self::resize
    /// [`extend`]: core::iter::Extend
    /// [`clear`]: Self::clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: Self::capacity
    ///
    /// # Examples
    ///
    /// This method can be useful for situations in which the MathParsertor
    /// is serving as a equation for other code, particularly over FFI:
    ///
    /// ```no_run
    /// # #![allow(dead_code)]
    /// use heapless::MathParser;
    ///
    /// # // This is just a minimal skeleton for the doc example;
    /// # // don't use this as a starting point for a real library.
    /// # pub struct StreamWrapper { strm: *mut core::ffi::c_void }
    /// # const Z_OK: i32 = 0;
    /// # extern "C" {
    /// #     fn deflateGetDictionary(
    /// #         strm: *mut core::ffi::c_void,
    /// #         dictionary: *mut u8,
    /// #         dictLength: *mut usize,
    /// #     ) -> i32;
    /// # }
    /// # impl StreamWrapper {
    /// pub fn get_dictionary(&self) -> Option<MathParser<u8, 32768>> {
    ///     // Per the FFI method's docs, "32768 bytes is always enough".
    ///     let mut dict = MathParser::new();
    ///     let mut dict_length = 0;
    ///     // SAFETY: When `deflateGetDictionary` returns `Z_OK`, it holds that:
    ///     // 1. `dict_length` elements were initialized.
    ///     // 2. `dict_length` <= the capacity (32_768)
    ///     // which makes `set_len` safe to call.
    ///     unsafe {
    ///         // Make the FFI call...
    ///         let r = deflateGetDictionary(self.strm, dict.as_mut_ptr(), &mut dict_length);
    ///         if r == Z_OK {
    ///             // ...and update the length to what was initialized.
    ///             dict.set_len(dict_length);
    ///             Some(dict)
    ///         } else {
    ///             None
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    ///
    /// While the following example is sound, there is a memory leak since
    /// the inner MathParsertors were not freed prior to the `set_len` call:
    ///
    /// ```
    /// use core::iter::FromIterator;
    /// use heapless::MathParser;
    ///
    /// let mut MathParser = MathParser::<MathParser<u8, 3>, 3>::from_iter(
    ///     [
    ///         MathParser::from_iter([1, 0, 0].iter().cloned()),
    ///         MathParser::from_iter([0, 1, 0].iter().cloned()),
    ///         MathParser::from_iter([0, 0, 1].iter().cloned()),
    ///     ]
    ///     .iter()
    ///     .cloned()
    /// );
    /// // SAFETY:
    /// // 1. `old_len..0` is empty so no elements need to be initialized.
    /// // 2. `0 <= capacity` always holds whatever `capacity` is.
    /// unsafe {
    ///     MathParser.set_len(0);
    /// }
    /// ```
    ///
    /// Normally, here, one would use [`clear`] instead to correctly drop
    /// the contents and thus not leak memory.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity());

        self.l_len = new_len
    }

    /// Removes an element from the MathParsertor and returns it.
    ///
    /// The removed element is replaced by the last element of the MathParsertor.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///// use heapless::consts::*;
    ///
    /// let mut v: MathParser<_, 8> = MathParser::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(&*v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(&*v, ["baz", "qux"]);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        assert!(index < self.l_len);
        unsafe { self.swap_remove_unchecked(index) }
    }

    /// Removes an element from the MathParsertor and returns it.
    ///
    /// The removed element is replaced by the last element of the MathParsertor.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Safety
    ///
    ///  Assumes `index` within bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut v: MathParser<_, 8> = MathParser::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(unsafe { v.swap_remove_unchecked(1) }, "bar");
    /// assert_eq!(&*v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(unsafe { v.swap_remove_unchecked(0) }, "foo");
    /// assert_eq!(&*v, ["baz", "qux"]);
    /// ```
    pub unsafe fn swap_remove_unchecked(&mut self, index: usize) -> T {
        let length = self.len();
        debug_assert!(index < length);
        let value = unsafe { ptr::read(self.as_ptr().add(index)) };
        let base_ptr = self.as_mut_ptr();
        unsafe { ptr::copy(base_ptr.add(length - 1), base_ptr.add(index), 1) };
        self.l_len -= 1;
        value
    }

    /// Returns true if the MathParser is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.l_len + self.r_len == self.capacity()
    }

    /// Returns true if the MathParser is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.l_len + self.r_len == 0
    }

    /// Returns `true` if `needle` is a prefix of the MathParser.
    ///
    /// Always returns `true` if `needle` is an empty slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let v: MathParser<_, 8> = MathParser::from_slice(b"abc").unwrap();
    /// assert_eq!(v.starts_with(b""), true);
    /// assert_eq!(v.starts_with(b"ab"), true);
    /// assert_eq!(v.starts_with(b"bc"), false);
    /// ```
    #[inline]
    pub fn starts_with(&self, needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = needle.len();
        self.l_len >= n && needle == &self[..n]
    }

    /// Returns `true` if `needle` is a suffix of the MathParser.
    ///
    /// Always returns `true` if `needle` is an empty slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let v: MathParser<_, 8> = MathParser::from_slice(b"abc").unwrap();
    /// assert_eq!(v.ends_with(b""), true);
    /// assert_eq!(v.ends_with(b"ab"), false);
    /// assert_eq!(v.ends_with(b"bc"), true);
    /// ```
    #[inline]
    pub fn ends_with(&self, needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let (v, n) = (self.len(), needle.len());
        v >= n && needle == &self[v - n..]
    }

    /// Inserts an element at position `index` within the MathParsertor, shifting all
    /// elements after it to the right.
    ///
    /// Returns back the `element` if the MathParsertor is full.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut MathParser: MathParser<_, 8> = MathParser::from_slice(&[1, 2, 3]).unwrap();
    /// MathParser.insert(1, 4);
    /// assert_eq!(MathParser, [1, 4, 2, 3]);
    /// MathParser.insert(4, 5);
    /// assert_eq!(MathParser, [1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
        let len = self.len();
        if index > len {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        // check there's space for the new element
        if self.is_full() {
            return Err(element);
        }

        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().add(index);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
        }

        Ok(())
    }

    /// Removes and returns the element at position `index` within the MathParsertor,
    /// shifting all elements after it to the left.
    ///
    /// Note: Because this shifts over the remaining elements, it has a
    /// worst-case performance of *O*(*n*). If you don't need the order of
    /// elements to be preserved, use [`swap_remove`] instead. If you'd like to
    /// remove elements from the beginning of the `MathParser`, consider using
    /// [`Deque::pop_front`] instead.
    ///
    /// [`swap_remove`]: MathParser::swap_remove
    /// [`Deque::pop_front`]: crate::Deque::pop_front
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut v: MathParser<_, 8> = MathParser::from_slice(&[1, 2, 3]).unwrap();
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, [1, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        if index >= len {
            panic!("removal index (is {}) should be < len (is {})", index, len);
        }
        unsafe {
            // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().add(index);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the MathParsertor at the same time.
                ret = ptr::read(ptr);

                // Shift everything down to fill in that spot.
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut MathParser: MathParser<_, 8> = MathParser::from_slice(&[1, 2, 3, 4]).unwrap();
    /// MathParser.retain(|&x| x % 2 == 0);
    /// assert_eq!(MathParser, [2, 4]);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut MathParser: MathParser<_, 8> = MathParser::from_slice(&[1, 2, 3, 4, 5]).unwrap();
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// MathParser.retain(|_| *iter.next().unwrap());
    /// assert_eq!(MathParser, [2, 3, 5]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate, passing a mutable reference to it.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::MathParser;
    ///
    /// let mut MathParser: MathParser<_, 8> = MathParser::from_slice(&[1, 2, 3, 4]).unwrap();
    /// MathParser.retain_mut(|x| if *x <= 3 {
    ///     *x += 1;
    ///     true
    /// } else {
    ///     false
    /// });
    /// assert_eq!(MathParser, [2, 3, 4]);
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let original_len = self.len();
        // Avoid double drop if the drop guard is not executed,
        // since we may make some holes during the process.
        unsafe { self.set_len(0) };

        // MathParser: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //      |<-              processed len   ->| ^- next to check
        //                  |<-  deleted cnt     ->|
        //      |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct BackshiftOnDrop<'a, T, const N: usize> {
            v: &'a mut MathParser<T, N>,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl<T, const N: usize> Drop for BackshiftOnDrop<'_, T, N> {
            fn drop(&mut self) {
                if self.deleted_cnt > 0 {
                    // SAFETY: Trailing unchecked items must be valid since we never touch them.
                    unsafe {
                        ptr::copy(
                            self.v.as_ptr().add(self.processed_len),
                            self.v
                                .as_mut_ptr()
                                .add(self.processed_len - self.deleted_cnt),
                            self.original_len - self.processed_len,
                        );
                    }
                }
                // SAFETY: After filling holes, all items are in contiguous memory.
                unsafe {
                    self.v.set_len(self.original_len - self.deleted_cnt);
                }
            }
        }

        let mut g = BackshiftOnDrop {
            v: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        fn process_loop<F, T, const N: usize, const DELETED: bool>(
            original_len: usize,
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, T, N>,
        ) where
            F: FnMut(&mut T) -> bool,
        {
            while g.processed_len != original_len {
                let p = g.v.as_mut_ptr();
                // SAFETY: Unchecked element must be valid.
                let cur = unsafe { &mut *p.add(g.processed_len) };
                if !f(cur) {
                    // Advance early to avoid double drop if `drop_in_place` panicked.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    // SAFETY: We never touch this element again after dropped.
                    unsafe { ptr::drop_in_place(cur) };
                    // We already advanced the counter.
                    if DELETED {
                        continue;
                    } else {
                        break;
                    }
                }
                if DELETED {
                    // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with current element.
                    // We use copy for move, and never touch this element again.
                    unsafe {
                        let hole_slot = p.add(g.processed_len - g.deleted_cnt);
                        ptr::copy_nonoverlapping(cur, hole_slot, 1);
                    }
                }
                g.processed_len += 1;
            }
        }

        // Stage 1: Nothing was deleted.
        process_loop::<F, T, N, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, T, N, true>(original_len, &mut f, &mut g);

        // All item are processed. This can be optimized to `set_len` by LLVM.
        drop(g);
    }
}

// Trait implementations

impl<T, const N: usize> Default for MathParser<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> core::fmt::Debug for MathParser<T, N>
where
    T: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <[T] as core::fmt::Debug>::fmt(self, f)
    }
}

impl<const N: usize> core::fmt::Write for MathParser<u8, N> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        match self.extend_from_slice(s.as_bytes()) {
            Ok(()) => Ok(()),
            Err(_) => Err(core::fmt::Error),
        }
    }
}

impl<T, const N: usize> Drop for MathParser<T, N> {
    fn drop(&mut self) {
        // We drop each element used in the MathParsertor by turning into a &mut[T]
        unsafe {
            ptr::drop_in_place(self.as_mut_slice());
        }
    }
}

impl<'a, T: Clone, const N: usize> TryFrom<&'a [T]> for MathParser<T, N> {
    type Error = ();

    fn try_from(slice: &'a [T]) -> Result<Self, Self::Error> {
        MathParser::from_slice(slice)
    }
}

impl<T, const N: usize> Extend<T> for MathParser<T, N> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.extend(iter)
    }
}

impl<'a, T, const N: usize> Extend<&'a T> for MathParser<T, N>
where
    T: 'a + Copy,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.extend(iter.into_iter().cloned())
    }
}

impl<T, const N: usize> core::hash::Hash for MathParser<T, N>
where
    T: core::hash::Hash,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        <[T] as core::hash::Hash>::hash(self, state)
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a MathParser<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut MathParser<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const N: usize> FromIterator<T> for MathParser<T, N> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut math_parser = MathParser::new();
        for i in iter {
            math_parser
                .push(i)
                .ok()
                .expect("MathParser::from_iter overflow");
        }
        math_parser
    }
}

/// An iterator that moves out of an [`MathParser`][`MathParser`].
///
/// This struct is created by calling the `into_iter` method on [`MathParser`][`MathParser`].
pub struct IntoIter<T, const N: usize> {
    math_parser: MathParser<T, N>,
    next: usize,
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.math_parser.len() {
            let item = unsafe {
                self
                    .math_parser
                    .equation
                    .get_unchecked_mut(self.next)
                    .as_ptr()
                    .read()
            };
            self.next += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<T, const N: usize> Clone for IntoIter<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut math_parser = MathParser::new();

        if self.next < self.math_parser.len() {
            let s = unsafe {
                slice::from_raw_parts(
                    (self.math_parser.equation.as_ptr() as *const T).add(self.next),
                    self.math_parser.len() - self.next,
                )
            };
            math_parser.extend_from_slice(s).ok();
        }

        Self {
            math_parser,
            next: 0,
        }
    }
}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        unsafe {
            // Drop all the elements that have not been moved out of MathParser
            ptr::drop_in_place(&mut self.math_parser.as_mut_slice()[self.next..]);
            // Prevent dropping of other elements
            self.math_parser.l_len = 0;
            self.math_parser.r_len = 0;
        }
    }
}

impl<T, const N: usize> IntoIterator for MathParser<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            math_parser: self,
            next: 0,
        }
    }
}

impl<A, B, const N1: usize, const N2: usize> PartialEq<MathParser<B, N2>> for MathParser<A, N1>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &MathParser<B, N2>) -> bool {
        <[A]>::eq(self, &**other)
    }
}

// MathParser<A, N> == [B]
impl<A, B, const N: usize> PartialEq<[B]> for MathParser<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B]) -> bool {
        <[A]>::eq(self, other)
    }
}

// [B] == MathParser<A, N>
impl<A, B, const N: usize> PartialEq<MathParser<A, N>> for [B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &MathParser<A, N>) -> bool {
        <[A]>::eq(other, self)
    }
}

// MathParser<A, N> == &[B]
impl<A, B, const N: usize> PartialEq<&[B]> for MathParser<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// &[B] == MathParser<A, N>
impl<A, B, const N: usize> PartialEq<MathParser<A, N>> for &[B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &MathParser<A, N>) -> bool {
        <[A]>::eq(other, &self[..])
    }
}

// MathParser<A, N> == &mut [B]
impl<A, B, const N: usize> PartialEq<&mut [B]> for MathParser<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&mut [B]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// &mut [B] == MathParser<A, N>
impl<A, B, const N: usize> PartialEq<MathParser<A, N>> for &mut [B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &MathParser<A, N>) -> bool {
        <[A]>::eq(other, &self[..])
    }
}

// MathParser<A, N> == [B; M]
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<[B; M]> for MathParser<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B; M]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// [B; M] == MathParser<A, N>
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<MathParser<A, N>> for [B; M]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &MathParser<A, N>) -> bool {
        <[A]>::eq(other, &self[..])
    }
}

// MathParser<A, N> == &[B; M]
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<&[B; M]> for MathParser<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B; M]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// &[B; M] == MathParser<A, N>
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<MathParser<A, N>> for &[B; M]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &MathParser<A, N>) -> bool {
        <[A]>::eq(other, &self[..])
    }
}

// Implements Eq if underlying data is Eq
impl<T, const N: usize> Eq for MathParser<T, N> where T: Eq {}

impl<T, const N1: usize, const N2: usize> PartialOrd<MathParser<T, N2>> for MathParser<T, N1>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &MathParser<T, N2>) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T, const N: usize> Ord for MathParser<T, N>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T, const N: usize> std::ops::Deref for MathParser<T, N> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> std::ops::DerefMut for MathParser<T, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> AsRef<MathParser<T, N>> for MathParser<T, N> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T, const N: usize> AsMut<MathParser<T, N>> for MathParser<T, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T, const N: usize> AsRef<[T]> for MathParser<T, N> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> AsMut<[T]> for MathParser<T, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> Clone for MathParser<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        self.clone()
    }
}
