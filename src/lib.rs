#![no_std]
#![warn(missing_docs, missing_copy_implementations)]

//! A linked list that allows bidirectional traversal while only using one
//! pointer per node. [How it works.](https://en.wikipedia.org/wiki/Xor_linked_list)
//!
//! `XorLinkedLists` have a few advantages over traditional linked lists. Besides the
//! obvious space savings that are achieved by only using one pointer per node, another
//! advantage is that reversing an `XorLinkedList` is an *O*(1) operation, as you only have to swap
//! the head and tail pointers. That's why the [`XorLinkedList`] provides a [`reverse`] method
//! while the standard library [`LinkedList`] doesn't.
//!
//! [`LinkedList`]: https://doc.rust-lang.org/stable/alloc/collections/linked_list/struct.LinkedList.html
//! [`XorLinkedList`]: crate::XorLinkedList
//! [`reverse`]: crate::XorLinkedList::reverse

use core::{
    fmt::{self, Debug},
    hash::Hash,
    hash::Hasher,
    iter::{FromIterator, FusedIterator},
    marker::PhantomData,
    ptr::null_mut,
};

extern crate alloc;

use alloc::boxed::Box;

fn xor<T>(lhs: *mut T, rhs: *mut T) -> *mut T {
    (lhs as usize ^ rhs as usize) as *mut T
}

struct Node<T> {
    ptr: *mut Node<T>,
    val: T,
}

impl<T> Node<T> {
    fn new(val: T) -> *mut Self {
        let node = Self {
            val,
            ptr: null_mut(),
        };
        Box::into_raw(Box::new(node))
    }
}

/// A linked list that allows bidirectional traversal while only using one
/// pointer per node. [How it works.](https://en.wikipedia.org/wiki/Xor_linked_list)
///
/// Xor Linked Lists have a few advantages over traditional linked lists. Besides the
/// obvious space savings that are achieved by only using one pointer per node, another
/// advantage is that reversing a linked list is an *O*(1) operation, as you only have to swap
/// the head and tail pointers. That's why the [`XorLinkedList`] provides a [`reverse`] method
/// while the standard library [`LinkedList`] doesn't.
///
/// [`LinkedList`]: alloc::collections::LinkedList
/// [`XorLinkedList`]: crate::XorLinkedList
/// [`reverse`]: crate::XorLinkedList::reverse
pub struct XorLinkedList<T> {
    head: *mut Node<T>,
    tail: *mut Node<T>,
    len: usize,
}

impl<T> XorLinkedList<T> {
    /// Creates a new empty linked list
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::XorLinkedList;
    ///
    /// let list: XorLinkedList<i32> = XorLinkedList::new();
    /// ```
    /// Alternatively you can use the [`xll`] macro to construct the list
    /// ```rust
    /// use xorlinkedlist::{XorLinkedList, xll};
    ///
    /// let list: XorLinkedList<i32> = xll![];
    /// ```
    pub fn new() -> Self {
        Self {
            head: null_mut(),
            tail: null_mut(),
            len: 0,
        }
    }

    /// Returns the length of a given list. This is an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![];
    /// assert_eq!(ll.len(), 0);
    ///
    /// ll.push_front(3);
    /// assert_eq!(ll.len(), 1);
    ///
    /// ll.push_front(2);
    /// assert_eq!(ll.len(), 2);
    ///
    /// ll.push_front(1);
    /// assert_eq!(ll.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns whether a given list is empty. This is an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![];
    /// assert!(ll.is_empty());
    ///
    /// ll.push_back(1);
    /// assert!(!ll.is_empty());
    ///
    /// ll.pop_back();
    /// assert!(ll.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    // SAFETY: We only ever dereference raw pointers which are given to us in unsafe functions
    unsafe fn push_back_node(&mut self, node: *mut Node<T>) {
        if self.is_empty() {
            debug_assert_eq!(self.head, null_mut());
            debug_assert_eq!(self.tail, null_mut());
            self.head = node;
            self.tail = node;
            self.len = 1;
        } else {
            debug_assert_ne!(self.head, null_mut());
            debug_assert_ne!(self.tail, null_mut());
            self.len += 1;
            let tail = &mut *self.tail;
            tail.ptr = xor(tail.ptr, node);
            (*node).ptr = tail;
            self.tail = node;
        }
    }

    /// Appends a value to the back of the list. This should be an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![];
    ///
    /// ll.push_back(1);
    /// ll.push_back(2);
    /// ll.push_back(3);
    ///
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn push_back(&mut self, val: T) {
        let node = Node::new(val);
        // SAFETY: Node::new is guaranteed to return a valid pointer, so giving it to push_back_node is safe
        unsafe { self.push_back_node(node) }
    }

    // SAFETY: We only ever dereference raw pointers which are given to us in unsafe functions
    unsafe fn push_front_node(&mut self, node: *mut Node<T>) {
        if self.is_empty() {
            debug_assert_eq!(self.head, null_mut());
            debug_assert_eq!(self.tail, null_mut());
            self.head = node;
            self.tail = node;
            self.len = 1;
        } else {
            debug_assert_ne!(self.head, null_mut());
            debug_assert_ne!(self.tail, null_mut());
            self.len += 1;
            let head = &mut *self.head;
            head.ptr = xor(head.ptr, node);
            (*node).ptr = head;
            self.head = node;
        }
    }

    /// Prepends a value at the front of the list. This should be an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![];
    ///
    /// ll.push_front(3);
    /// ll.push_front(2);
    /// ll.push_front(1);
    ///
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn push_front(&mut self, val: T) {
        let node = Node::new(val);
        // SAFETY: Node::new is guaranteed to return a valid pointer, so giving it to push_back_node is safe
        unsafe { self.push_front_node(node) }
    }

    /// Attempts to remove a value from the front of the list. If the list is empty, it returns `None`.
    /// This should be an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![1, 2, 3];
    ///
    /// assert_eq!(ll.pop_front(), Some(1));
    /// assert_eq!(ll.pop_front(), Some(2));
    /// assert_eq!(ll.pop_front(), Some(3));
    /// assert!(ll.is_empty())
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        if self.head.is_null() {
            None
        } else if self.len == 1 {
            debug_assert_ne!(self.head, null_mut());
            debug_assert_eq!(self.head, self.tail);
            let node = core::mem::replace(&mut self.head, null_mut());
            self.tail = null_mut();
            self.len = 0;
            unsafe { Some(Box::from_raw(node).val) }
        } else {
            self.len -= 1;
            // SAFETY: If self.head isn't null, it's guaranteed to be valid by the push methods
            unsafe {
                let head = &mut *self.head;
                let next = match head.ptr {
                    n if n.is_null() => None,
                    n => Some(&mut *n),
                };
                if let Some(next) = next {
                    next.ptr = xor(next.ptr, head);
                }
                self.head = head.ptr;
                Some(Box::from_raw(head).val)
            }
        }
    }

    /// Attempts to remove a value from the back of the list. If the list is empty, it returns `None`.
    /// This should be an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![1, 2, 3];
    ///
    /// assert_eq!(ll.pop_back(), Some(3));
    /// assert_eq!(ll.pop_back(), Some(2));
    /// assert_eq!(ll.pop_back(), Some(1));
    /// assert!(ll.is_empty())
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        if self.tail.is_null() {
            None
        } else if self.len == 1 {
            debug_assert_ne!(self.head, null_mut());
            debug_assert_eq!(self.head, self.tail);
            let node = core::mem::replace(&mut self.head, null_mut());
            self.tail = null_mut();
            self.len = 0;
            unsafe { Some(Box::from_raw(node).val) }
        } else {
            self.len -= 1;
            unsafe {
                let tail = &mut *self.tail;
                let prev = match tail.ptr {
                    n if n.is_null() => None,
                    n => Some(&mut *n),
                };
                if let Some(prev) = prev {
                    prev.ptr = xor(prev.ptr, tail);
                }
                self.tail = tail.ptr;
                Some(Box::from_raw(tail).val)
            }
        }
    }

    /// Returns a reference to the first element in the list or `None` if the list is empty.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::{xll, XorLinkedList};
    /// let ll = xll![1, 2, 3];
    ///
    /// assert_eq!(ll.front(), Some(&1));
    /// assert_eq!(xll![<i32>].front(), None);
    /// ```
    pub fn front(&self) -> Option<&T> {
        if self.head.is_null() {
            None
        } else {
            // SAFETY: If self.head isn't null, it's guaranteed to be valid by the push_back method
            let head = unsafe { &*self.head };
            Some(&head.val)
        }
    }

    /// Returns a mutable reference to the first element in the list or `None` if the list is empty.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::{xll, XorLinkedList};
    ///
    /// let mut ll = xll![2, 2, 3];
    ///
    /// *ll.front_mut().unwrap() -= 1;
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// assert_eq!(xll![<i32>].front_mut(), None);
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if self.head.is_null() {
            None
        } else {
            // SAFETY: If self.head isn't null, it's guaranteed to be valid by the push_back method
            let head = unsafe { &mut *self.head };
            Some(&mut head.val)
        }
    }

    /// Returns a reference to the last element in the list or `None` if the list is empty.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::{xll, XorLinkedList};
    /// let ll = xll![1, 2, 3];
    ///
    /// assert_eq!(ll.back(), Some(&3));
    /// assert_eq!(xll![<i32>].back(), None);
    /// ```
    pub fn back(&self) -> Option<&T> {
        if self.head.is_null() {
            None
        } else {
            // SAFETY: If self.tail isn't null, it's guaranteed to be valid by the push_back method
            let tail = unsafe { &*self.tail };
            Some(&tail.val)
        }
    }

    /// Returns a mutable reference to the last element in the list or `None` if the list is empty.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::{xll, XorLinkedList};
    ///
    /// let mut ll = xll![1, 2, 4];
    ///
    /// *ll.back_mut().unwrap() -= 1;
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// assert_eq!(xll![<i32>].back_mut(), None);
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        if self.head.is_null() {
            None
        } else {
            // SAFETY: If self.tail isn't null, it's guaranteed to be valid by the push_back method
            let tail = unsafe { &mut *self.tail };
            Some(&mut tail.val)
        }
    }

    /// Returns an iterator over the list which gives immutable access to items and allows forward
    /// and reverse iteration.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let ll = xll![1, 2, 3, 4];
    ///
    /// assert!(ll.iter().copied().eq(1..=4));
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }

    /// Returns an iterator over the list which gives mutable access to items and allows forward
    /// and reverse iteration.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![0, 1, 2, 3];
    ///
    /// ll.iter_mut().for_each(|n| *n += 1);
    ///
    /// assert!(ll.iter().copied().eq(1..=4));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut::new(self)
    }

    /// Appends all items of a one list to another list. This leaves the list whose items are appended
    /// empty. This operation an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll1 = xll![1, 2, 3];
    /// let mut ll2 = xll![4, 5, 6];
    ///
    /// ll1.append(&mut ll2);
    ///
    /// assert_eq!(ll1, xll![1, 2, 3, 4, 5, 6]);
    /// assert!(ll2.is_empty());
    ///
    /// ```
    pub fn append(&mut self, rhs: &mut Self) {
        if rhs.is_empty() {
            return;
        }
        if self.is_empty() {
            core::mem::swap(self, rhs);
        } else {
            assert_ne!(self.head, null_mut());
            assert_ne!(self.tail, null_mut());
            assert_ne!(rhs.head, null_mut());
            assert_ne!(rhs.tail, null_mut());
            unsafe {
                let self_tail = &mut *self.tail;
                let rhs_head = &mut *rhs.head;
                self_tail.ptr = xor(self_tail.ptr, rhs_head);
                rhs_head.ptr = xor(self_tail, rhs_head.ptr);
                self.tail = rhs.tail;
                self.len += rhs.len;
                rhs.head = null_mut();
                rhs.tail = null_mut();
                rhs.len = 0;
            }
        }
    }
    /// Prepends all items of a one list to another list. This leaves the list whose items are prepended
    /// empty. This operation is *O*(1).
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll1 = xll![1, 2, 3];
    /// let mut ll2 = xll![4, 5, 6];
    ///
    /// ll2.prepend(&mut ll1);
    ///
    /// assert!(ll1.is_empty());
    /// assert_eq!(ll2, xll![1, 2, 3, 4, 5, 6]);
    ///
    /// ```
    pub fn prepend(&mut self, rhs: &mut Self) {
        if rhs.is_empty() {
            return;
        }
        if self.is_empty() {
            core::mem::swap(self, rhs);
        } else {
            assert_ne!(self.head, null_mut());
            assert_ne!(self.tail, null_mut());
            assert_ne!(rhs.head, null_mut());
            assert_ne!(rhs.tail, null_mut());
            unsafe {
                let self_head = &mut *self.head;
                let rhs_tail = &mut *rhs.tail;
                self_head.ptr = xor(self_head.ptr, rhs_tail);
                rhs_tail.ptr = xor(self_head, rhs_tail.ptr);
                self.head = rhs.head;
                self.len += rhs.len;
                rhs.head = null_mut();
                rhs.tail = null_mut();
                rhs.len = 0;
            }
        }
    }

    /// Clears the list and destroys all its items. This operation should take *O*(n) time.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![1, 2, 3];
    ///
    /// assert_eq!(ll.len(), 3);
    /// assert_eq!(ll.front(), Some(&1));
    ///
    /// ll.clear();
    ///
    /// assert!(ll.is_empty());
    /// assert_eq!(ll.front(), None);
    /// ```
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// Returns whether the list contains a value. This operation should take *O*(n) time.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let ll = xll![1, 2, 3];
    ///
    /// assert!(ll.contains(&1));
    /// assert!(ll.contains(&2));
    /// assert!(ll.contains(&3));
    /// assert!(!ll.contains(&4));
    /// ```
    pub fn contains(&self, val: &T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|t| t == val)
    }

    /// Reverses the linked list. This is an *O*(1) operation.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![1, 2, 3, 4, 5];
    ///
    /// ll.reverse();
    /// assert_eq!(ll, xll![5, 4, 3, 2, 1]);
    ///
    /// ll.reverse();
    /// assert_eq!(ll, xll![1, 2, 3, 4, 5]);
    /// ```
    pub fn reverse(&mut self) {
        core::mem::swap(&mut self.head, &mut self.tail);
    }

    /// Returns a [`Cursor`] pointing to the first element of the list.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let ll = xll![1, 2, 3];
    ///
    /// let mut cursor = ll.cursor_front();
    /// assert_eq!(cursor.current(), Some(&1));
    ///
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&2));
    ///
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&3));
    ///
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), None);
    ///
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&1));
    /// ```
    pub fn cursor_front(&self) -> Cursor<T> {
        Cursor::new_front(self)
    }

    /// Returns a [`Cursor`] pointing to the last element of the list.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let ll = xll![1, 2, 3];
    ///
    /// let mut cursor = ll.cursor_back();
    /// assert_eq!(cursor.current(), Some(&3));
    ///
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&2));
    ///
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&1));
    ///
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), None);
    ///
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&3));
    /// ```
    pub fn cursor_back(&self) -> Cursor<T> {
        Cursor::new_back(self)
    }

    /// Returns a [`CursorMut`] pointing to the first element of the list.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![0, 1, 2];
    ///
    /// let mut cursor = ll.cursor_front_mut();
    /// while let Some(n) = cursor.current() {
    ///     *n += 1;
    ///     drop(n);
    ///     cursor.move_next();
    /// }
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn cursor_front_mut(&mut self) -> CursorMut<T> {
        CursorMut::new_front(self)
    }

    /// Returns a [`CursorMut`] pointing to the last element of the list.
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    ///
    /// let mut ll = xll![2, 3, 4];
    ///
    /// let mut cursor = ll.cursor_back_mut();
    /// while let Some(n) = cursor.current() {
    ///     *n -= 1;
    ///     drop(n);
    ///     cursor.move_prev();
    /// }
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn cursor_back_mut(&mut self) -> CursorMut<T> {
        CursorMut::new_back(self)
    }

    unsafe fn unlink_node(&mut self, node: *mut Node<T>, prev: *mut Node<T>, next: *mut Node<T>) {
        debug_assert_ne!(node, null_mut());
        debug_assert_ne!(prev, null_mut());
        debug_assert_ne!(next, null_mut());
        debug_assert_ne!(self.len, 0);

        let prev = &mut *prev;
        let next = &mut *next;

        prev.ptr = xor(prev.ptr, node);
        next.ptr = xor(next.ptr, node);

        prev.ptr = xor(prev.ptr, next);
        next.ptr = xor(next.ptr, prev);

        (*node).ptr = null_mut();

        self.len -= 1;
    }
}

impl<T> Drop for XorLinkedList<T> {
    fn drop(&mut self) {
        unsafe {
            let mut prev_ptr = null_mut();
            let mut cur_ptr = self.head;
            let mut i = 0;
            while !cur_ptr.is_null() {
                i += 1;
                let cur = &mut *cur_ptr;
                let next_ptr = xor(cur.ptr, prev_ptr);
                prev_ptr = cur_ptr;
                cur_ptr = next_ptr;
                Box::from_raw(cur);
            }
            debug_assert_eq!(self.len, i);
        }
    }
}

impl<T> Default for XorLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for XorLinkedList<T> {
    fn clone(&self) -> Self {
        let mut ll = Self::new();
        for t in self {
            ll.push_back(t.clone());
        }
        ll
    }
}

impl<T: PartialEq> PartialEq for XorLinkedList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for XorLinkedList<T> {
    fn assert_receiver_is_total_eq(&self) {}
}

impl<T> FromIterator<T> for XorLinkedList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut ll = Self::new();
        for t in iter {
            ll.push_back(t);
        }
        ll
    }
}

impl<T> Extend<T> for XorLinkedList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for t in iter {
            self.push_back(t);
        }
    }
}

impl<T: Hash> Hash for XorLinkedList<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for t in self {
            t.hash(state);
        }
    }
}

impl<T: PartialOrd> PartialOrd for XorLinkedList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for XorLinkedList<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T> IntoIterator for XorLinkedList<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { ll: self }
    }
}

impl<'a, T> IntoIterator for &'a XorLinkedList<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut XorLinkedList<T> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An owning iterator over an [`XorLinkedList`]'s elements.
///
/// This `struct` is created by the [`into_iter`] method on an [`XorLinkedList`].
///
/// [`into_iter`]: crate::XorLinkedList::into_iter
pub struct IntoIter<T> {
    ll: XorLinkedList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.ll.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.ll.len, Some(self.ll.len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.ll.pop_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.ll.len
    }
}

/// A borrowing iterator over an [`XorLinkedList`]'s elements.
///
/// This `struct` is created by the [`iter`] method on an [`XorLinkedList`]
///
/// [`iter`]: crate::XorLinkedList::iter
pub struct Iter<'a, T: 'a> {
    prev_front: *mut Node<T>,
    cur_front: *mut Node<T>,
    prev_back: *mut Node<T>,
    cur_back: *mut Node<T>,
    len: usize,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T: 'a> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        unsafe { core::mem::transmute_copy(self) }
    }
}

impl<'a, T: 'a> Iter<'a, T> {
    fn new(ll: &'a XorLinkedList<T>) -> Self {
        Self {
            prev_front: null_mut(),
            cur_front: ll.head,
            prev_back: null_mut(),
            cur_back: ll.tail,
            len: ll.len,
            _marker: PhantomData,
        }
    }
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 || self.cur_front.is_null() {
            return None;
        }

        self.len -= 1;

        // SAFETY: The public API never allows the user injecting any raw pointers. Since every raw pointer
        // injected by the internal API is valid, it's safe to dereference the raw pointer
        unsafe {
            let cur = &*self.cur_front;
            let next = xor(cur.ptr, self.prev_front);
            self.prev_front = self.cur_front;
            self.cur_front = next;
            Some(&cur.val)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 || self.cur_back.is_null() {
            return None;
        }

        self.len -= 1;

        // SAFETY: The public API never allows the user injecting any raw pointers. Since every raw pointer
        // injected by the internal API is valid, it's safe to dereference them
        unsafe {
            let cur = &*self.cur_back;
            let next = xor(cur.ptr, self.prev_back);
            self.prev_back = self.cur_back;
            self.cur_back = next;
            Some(&cur.val)
        }
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T: Debug> Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone().into_iter()).finish()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

/// A mutably borrowing iterator over an [`XorLinkedList`]'s elements.
///
/// This `struct` is created by the [`iter_mut`] method on an [`XorLinkedList`]
///
/// [`iter_mut`]: crate::XorLinkedList::iter_mut
pub struct IterMut<'a, T: 'a> {
    prev_front: *mut Node<T>,
    cur_front: *mut Node<T>,
    prev_back: *mut Node<T>,
    cur_back: *mut Node<T>,
    len: usize,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T: 'a> IterMut<'a, T> {
    fn new(ll: &'a XorLinkedList<T>) -> Self {
        Self {
            prev_front: null_mut(),
            cur_front: ll.head,
            prev_back: null_mut(),
            cur_back: ll.tail,
            len: ll.len,
            _marker: PhantomData,
        }
    }
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 || self.cur_front.is_null() {
            return None;
        }

        self.len -= 1;

        // SAFETY: The public API never allows the user injecting any raw pointers. Since every raw pointer
        // injected by the internal API is valid, it's safe to dereference the raw pointer
        unsafe {
            let cur = &mut *self.cur_front;
            let next = xor(cur.ptr, self.prev_front);
            self.prev_front = self.cur_front;
            self.cur_front = next;
            Some(&mut cur.val)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len == 0 || self.cur_back.is_null() {
            return None;
        }

        self.len -= 1;

        // SAFETY: The public API never allows the user injecting any raw pointers. Since every raw pointer
        // injected by the internal API is valid, it's safe to dereference the raw pointer
        unsafe {
            let cur = &mut *self.cur_back;
            let next = xor(cur.ptr, self.prev_back);
            self.prev_back = self.cur_back;
            self.cur_back = next;
            Some(&mut cur.val)
        }
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T: fmt::Debug> fmt::Debug for IterMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let it = unsafe { core::ptr::read(self) };
        f.debug_list().entries(it).finish()
    }
}

impl<T> FusedIterator for IterMut<'_, T> {}

impl<T: fmt::Debug> fmt::Debug for XorLinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// A cursor over an [`XorLinkedList`]
///
/// A `Cursor` is like an iterator, except it can freely seek back-and-forth.
///
/// Cursors always rest between two elements in the list, and index in a logically
/// circular way. To accomodate this, there is a "ghost" non-element that yields `None` between
/// the head and the tail of the list.
pub struct Cursor<'a, T: 'a> {
    prev: *mut Node<T>,
    cur: *mut Node<T>,
    next: *mut Node<T>,
    index: usize,
    ll: &'a XorLinkedList<T>,
}

impl<'a, T: 'a> Cursor<'a, T> {
    /// Creates a new `Cursor` pointing to the first element of the list.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2, 3];
    /// let _cursor = ll.cursor_front();
    /// ```
    fn new_front(ll: &'a XorLinkedList<T>) -> Self {
        let cur = ll.head;
        let next = if !cur.is_null() {
            unsafe { (*cur).ptr }
        } else {
            null_mut()
        };
        Self {
            prev: null_mut(),
            cur,
            next,
            index: 0,
            ll,
        }
    }

    /// Creates a new `Cursor` pointing to the last element of the list.///
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2, 3];
    /// let _cursor = ll.cursor_back();
    /// ```
    fn new_back(ll: &'a XorLinkedList<T>) -> Self {
        let cur = ll.tail;
        let prev = if !cur.is_null() {
            unsafe { (*cur).ptr }
        } else {
            null_mut()
        };
        Self {
            prev,
            cur,
            next: null_mut(),
            index: ll.len.saturating_sub(1),
            ll,
        }
    }

    /// Returns the current index of the `Cursor`. If the cursor is pointing to the "ghost" non-element,
    /// this returns `None`.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front();
    /// assert_eq!(cursor.index(), Some(0));
    /// cursor.move_next();
    /// assert_eq!(cursor.index(), Some(1));
    /// cursor.move_next();
    /// assert_eq!(cursor.index(), None);
    /// cursor.move_next();
    /// assert_eq!(cursor.index(), Some(0));
    /// ```
    pub fn index(&self) -> Option<usize> {
        if self.cur.is_null() {
            None
        } else {
            Some(self.index)
        }
    }

    /// Returns a reference to the object that the `Cursor` is currently poinint to.
    /// If the cursor is pointing to the "ghost" non-element, this return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front();
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&2));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), None);
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&1));
    /// ```
    pub fn current(&self) -> Option<&'a T> {
        if self.cur.is_null() {
            None
        } else {
            unsafe { Some(&(*self.cur).val) }
        }
    }

    /// Moves the `Cursor` to the next position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front();
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&2));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), None);
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&1));
    /// ```
    pub fn move_next(&mut self) {
        if self.cur.is_null() {
            self.cur = self.ll.head;
            self.prev = null_mut();
            self.next = null_mut();
            self.index = 0;
        } else {
            unsafe {
                let next_ptr = xor((*self.cur).ptr, self.prev);
                self.next = if !next_ptr.is_null() {
                    xor(self.cur, (*next_ptr).ptr)
                } else {
                    null_mut()
                };
                self.prev = self.cur;
                self.cur = next_ptr;
                self.index += 1;
            }
        }
    }

    /// Moves the `Cursor` to the previous position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2];
    /// let mut cursor = ll.cursor_back();
    /// assert_eq!(cursor.current(), Some(&2));
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&1));
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), None);
    /// cursor.move_prev();
    /// assert_eq!(cursor.current(), Some(&2));
    /// ```
    pub fn move_prev(&mut self) {
        if self.cur.is_null() {
            self.cur = self.ll.tail;
            self.prev = null_mut();
            self.next = null_mut();
            self.index = self.ll.len.saturating_sub(1);
        } else {
            unsafe {
                let prev_ptr = xor((*self.cur).ptr, self.next);
                self.prev = if !prev_ptr.is_null() {
                    xor(self.cur, (*prev_ptr).ptr)
                } else {
                    null_mut()
                };
                self.next = self.cur;
                self.cur = prev_ptr;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.ll.len());
            }
        }
    }

    /// Returns a reference to the previous position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front();
    /// assert_eq!(cursor.current(), Some(&1));
    /// assert_eq!(cursor.peek_prev(), None);
    /// ```
    pub fn peek_prev(&self) -> Option<&'a T> {
        if self.prev.is_null() {
            None
        } else {
            unsafe { Some(&(*self.prev).val) }
        }
    }

    /// Returns a reference to the next position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front();
    /// assert_eq!(cursor.current(), Some(&1));
    /// assert_eq!(cursor.peek_next(), Some(&2));
    /// ```
    pub fn peek_next(&self) -> Option<&'a T> {
        if self.next.is_null() {
            None
        } else {
            unsafe { Some(&(*self.next).val) }
        }
    }
}

impl<'a, T: 'a> Clone for Cursor<'a, T> {
    fn clone(&self) -> Self {
        unsafe { core::mem::transmute_copy(self) }
    }
}

impl<T: fmt::Debug> fmt::Debug for Cursor<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Cursor")
            .field(&self.ll)
            .field(&self.index())
            .finish()
    }
}

/// A mutable Cursor over an [`XorLinkedList`].
///
/// A `Cursor` is like an iterator, except it can freely seek back-and-forth.
///
/// Cursors always rest between two elements in the list, and index in a logically
/// circular way. To accomodate this, there is a "ghost" non-element that yields `None` between
/// the head and the tail of the list.
pub struct CursorMut<'a, T: 'a> {
    prev: *mut Node<T>,
    cur: *mut Node<T>,
    next: *mut Node<T>,
    index: usize,
    ll: &'a mut XorLinkedList<T>,
}

impl<'a, T: 'a> CursorMut<'a, T> {
    fn new_front(ll: &'a mut XorLinkedList<T>) -> Self {
        let cur = ll.head;
        let next = if !cur.is_null() {
            unsafe { (*cur).ptr }
        } else {
            null_mut()
        };
        Self {
            prev: null_mut(),
            cur,
            next,
            index: 0,
            ll,
        }
    }

    fn new_back(ll: &'a mut XorLinkedList<T>) -> Self {
        let cur = ll.tail;
        let prev = if !cur.is_null() {
            unsafe { (*cur).ptr }
        } else {
            null_mut()
        };
        Self {
            prev,
            cur,
            next: null_mut(),
            index: ll.len.saturating_sub(1),
            ll,
        }
    }

    /// Returns the current index of the `Cursor`. If the cursor is pointing to the "ghost" non-element,
    /// this returns `None`.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front_mut();
    /// assert_eq!(cursor.index(), Some(0));
    /// cursor.move_next();
    /// assert_eq!(cursor.index(), Some(1));
    /// cursor.move_next();
    /// assert_eq!(cursor.index(), None);
    /// cursor.move_next();
    /// assert_eq!(cursor.index(), Some(0));
    /// ```
    pub fn index(&self) -> Option<usize> {
        if self.cur.is_null() {
            None
        } else {
            Some(self.index)
        }
    }

    /// Returns a reference to the object that the `Cursor` is currently poinint to.
    /// If the cursor is pointing to the "ghost" non-element, this return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front_mut();
    /// assert_eq!(cursor.current(), Some(&mut 1));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&mut 2));
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), None);
    /// cursor.move_next();
    /// assert_eq!(cursor.current(), Some(&mut 1));
    /// *cursor.current().unwrap() *= 2;
    /// assert_eq!(cursor.current(), Some(&mut 2));
    /// ```
    pub fn current(&mut self) -> Option<&mut T> {
        if self.cur.is_null() {
            None
        } else {
            unsafe { Some(&mut (*self.cur).val) }
        }
    }

    /// Returns an immutable [`Cursor`] pointing to the current position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1];
    /// let cursor = ll.cursor_front_mut();
    /// assert_eq!(cursor.as_cursor().current(), Some(&1));
    /// ```
    pub fn as_cursor(&self) -> Cursor<T> {
        Cursor {
            prev: self.prev,
            cur: self.cur,
            next: self.next,
            index: self.index,
            ll: self.ll,
        }
    }

    /// Moves the `Cursor` to the next position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.move_next();
    /// assert_eq!(ll, xll![1, 2]);
    /// ```
    pub fn move_next(&mut self) {
        if self.cur.is_null() {
            self.cur = self.ll.head;
            self.prev = null_mut();
            self.next = null_mut();
            self.index = 0;
        } else {
            unsafe {
                let next_ptr = xor((*self.cur).ptr, self.prev);
                self.next = if !next_ptr.is_null() {
                    xor(self.cur, (*next_ptr).ptr)
                } else {
                    null_mut()
                };
                self.prev = self.cur;
                self.cur = next_ptr;
                self.index += 1;
            }
        }
    }

    /// Moves the `Cursor` to the previous position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2];
    /// let mut cursor = ll.cursor_back_mut();
    /// while cursor.index().is_some() {
    ///     *cursor.current().unwrap() *= 2;
    ///     cursor.move_prev();
    /// }
    /// assert_eq!(ll, xll![2, 4]);
    /// ```
    pub fn move_prev(&mut self) {
        if self.cur.is_null() {
            self.cur = self.ll.tail;
            self.prev = null_mut();
            self.next = null_mut();
            self.index = self.ll.len.saturating_sub(1);
        } else {
            unsafe {
                let prev_ptr = xor((*self.cur).ptr, self.next);
                self.prev = if !prev_ptr.is_null() {
                    xor(self.cur, (*prev_ptr).ptr)
                } else {
                    null_mut()
                };
                self.next = self.cur;
                self.cur = prev_ptr;
                self.index = self.index.checked_sub(1).unwrap_or_else(|| self.ll.len());
            }
        }
    }

    /// Returns a reference to the previous position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front_mut();
    /// assert_eq!(cursor.current(), Some(&mut 1));
    /// assert_eq!(cursor.peek_prev(), None);
    /// ```
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        if self.prev.is_null() {
            None
        } else {
            unsafe { Some(&mut (*self.prev).val) }
        }
    }

    /// Returns a reference to the next position.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2];
    /// let mut cursor = ll.cursor_front_mut();
    /// assert_eq!(cursor.current(), Some(&mut 1));
    /// assert_eq!(cursor.peek_next(), Some(&mut 2));
    /// ```
    pub fn peek_next(&mut self) -> Option<&mut T> {
        if self.next.is_null() {
            None
        } else {
            unsafe { Some(&mut (*self.next).val) }
        }
    }

    /// Inserts an element in the list after the `Cursor`.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 3, 5];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.insert_after(2);
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.insert_after(4);
    /// assert_eq!(ll, xll![1, 2, 3, 4, 5]);
    /// ```
    pub fn insert_after(&mut self, val: T) {
        if self.cur.is_null() {
            self.ll.push_front(val);
            if self.prev.is_null() {
                self.prev = self.ll.tail;
            }
            if self.next.is_null() {
                self.next = self.ll.head;
            }
        } else if self.next.is_null() {
            self.ll.push_back(val);
            self.next = self.ll.tail;
        } else {
            unsafe {
                let new_node = Node::new(val);
                let cur_node = &mut *self.cur;
                let next_node = &mut *self.next;
                cur_node.ptr = xor(cur_node.ptr, next_node);
                cur_node.ptr = xor(cur_node.ptr, new_node);
                next_node.ptr = xor(next_node.ptr, cur_node);
                next_node.ptr = xor(next_node.ptr, new_node);
                (*new_node).ptr = xor(cur_node, next_node);
                self.ll.len += 1;
                self.next = new_node;
            }
        }
    }

    /// Inserts an element in the list after the `Cursor`.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![2, 4, 5];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.insert_before(1);
    /// cursor.move_next();
    /// cursor.insert_before(3);
    /// assert_eq!(ll, xll![1, 2, 3, 4, 5]);
    /// ```
    pub fn insert_before(&mut self, val: T) {
        if self.cur.is_null() {
            self.ll.push_back(val);
            if self.prev.is_null() {
                self.prev = self.ll.head;
            }
            if self.next.is_null() {
                self.next = self.ll.tail;
            }
        } else if self.prev.is_null() {
            self.ll.push_front(val);
            self.prev = self.ll.head;
            self.index += 1;
        } else {
            unsafe {
                let new_node = Node::new(val);
                let cur_node = &mut *self.cur;
                let prev_node = &mut *self.prev;
                cur_node.ptr = xor(cur_node.ptr, prev_node);
                cur_node.ptr = xor(cur_node.ptr, new_node);
                prev_node.ptr = xor(prev_node.ptr, cur_node);
                prev_node.ptr = xor(prev_node.ptr, new_node);
                (*new_node).ptr = xor(cur_node, prev_node);
                self.ll.len += 1;
                self.prev = new_node;
            }
        }
    }

    fn remove_current_node(&mut self) -> Option<*mut Node<T>> {
        if self.cur.is_null() {
            None
        } else {
            let (node, prev, next) = (self.cur, self.prev, self.next);
            unsafe {
                if next.is_null() {
                    self.cur = null_mut();
                    self.next = self.ll.head;
                } else {
                    let next_next_ptr = xor((*next).ptr, node);
                    self.cur = self.next;
                    self.next = next_next_ptr;
                }
                self.ll.unlink_node(node, prev, next);
                Some(node)
            }
        }
    }

    /// Removes the current value from the list.
    ///
    /// Returns `None` if the list is empty.
    /// # Examples
    ///
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2, 2, 3];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.move_next();
    /// assert_eq!(cursor.remove_current(), Some(2));
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn remove_current(&mut self) -> Option<T> {
        self.remove_current_node()
            .map(|n| unsafe { Box::from_raw(n).val })
    }

    /// Removes the current value and returns a new list with the removed value as its only element.
    ///
    /// Returns `None` if the list is empty.
    /// This doesn't require any allocations.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2, 2, 3];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.move_next();
    /// assert_eq!(cursor.remove_current_as_list(), Some(xll![2]));
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn remove_current_as_list(&mut self) -> Option<XorLinkedList<T>>
    where
        T: Debug,
    {
        self.remove_current_node().map(|n| XorLinkedList {
            head: n,
            tail: n,
            len: 1,
        })
    }

    /// Inserts the given list after the current position.
    ///
    /// This doesn't require any allocations and is an *O*(1) operation.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 4, 5];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.splice_after(xll![2, 3]);
    /// assert_eq!(ll, xll![1, 2, 3, 4, 5]);
    /// ```
    pub fn splice_after(&mut self, mut list: XorLinkedList<T>) {
        if list.is_empty() {
            core::mem::forget(list);
            return;
        }
        if self.cur.is_null() {
            self.ll.prepend(&mut list);
            self.next = self.ll.head;
            core::mem::forget(list);
        } else if self.next.is_null() {
            self.next = list.head;
            self.ll.append(&mut list);
            core::mem::forget(list);
        } else {
            self.ll.len += list.len;
            unsafe {
                let cur = self.cur.as_mut().unwrap();
                let next = self.next.as_mut().unwrap();

                cur.ptr = xor(cur.ptr, next);
                next.ptr = xor(next.ptr, cur);

                let head = list.head.as_mut().unwrap();
                let tail = list.tail.as_mut().unwrap();

                cur.ptr = xor(cur.ptr, head);
                head.ptr = xor(head.ptr, cur);

                next.ptr = xor(next.ptr, tail);
                tail.ptr = xor(tail.ptr, next);
            }
            core::mem::forget(list);
        }
    }

    /// Inserts the given list before the current item.
    ///
    /// This doesn't require any allocations and is an *O*(1) operation.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2, 5];
    /// let mut cursor = ll.cursor_back_mut();
    /// cursor.splice_before(xll![3, 4]);
    /// assert_eq!(ll, xll![1, 2, 3, 4, 5]);
    /// ```
    pub fn splice_before(&mut self, mut list: XorLinkedList<T>) {
        if list.is_empty() {
            core::mem::forget(list);
            return;
        }
        if self.cur.is_null() {
            self.ll.append(&mut list);
            self.prev = self.ll.tail;
            core::mem::forget(list);
        } else if self.prev.is_null() {
            self.prev = list.tail;
            self.ll.prepend(&mut list);
            core::mem::forget(list);
        } else {
            self.ll.len += list.len;
            unsafe {
                let cur = self.cur.as_mut().unwrap();
                let prev = self.prev.as_mut().unwrap();

                cur.ptr = xor(cur.ptr, prev);
                prev.ptr = xor(prev.ptr, cur);

                let head = list.head.as_mut().unwrap();
                let tail = list.tail.as_mut().unwrap();

                cur.ptr = xor(cur.ptr, tail);
                tail.ptr = xor(tail.ptr, cur);

                prev.ptr = xor(prev.ptr, head);
                head.ptr = xor(head.ptr, prev);
            }
            core::mem::forget(list);
        }
    }

    /// Splits the list and returns a new list containing all the elements after the current one.
    ///
    /// This requires no allocations and is an *O*(1) operation.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2, 1, 2, 3];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.move_next();
    /// assert_eq!(cursor.split_after(), xll![1, 2, 3]);
    /// assert_eq!(ll, xll![1, 2]);
    /// ```
    pub fn split_after(&mut self) -> XorLinkedList<T> {
        if self.cur.is_null() {
            core::mem::replace(self.ll, xll!())
        } else {
            if self.next.is_null() {
                return xll!();
            }
            unsafe {
                let cur = &mut *self.cur;
                let next = &mut *self.next;
                let idx = self.index;
                let len = self.ll.len - idx - 1;
                self.ll.len = idx + 1;
                cur.ptr = self.prev;
                next.ptr = xor(next.ptr, cur);
                let tail = core::mem::replace(&mut self.ll.tail, self.cur);
                let head = core::mem::replace(&mut self.next, null_mut());
                XorLinkedList { len, tail, head }
            }
        }
    }
    /// Splits the list and returns a new list containing all the elements before the current one.
    ///
    /// This requires no allocations and is an *O*(1) operation.
    ///
    /// # Examples
    /// ```rust
    /// use xorlinkedlist::xll;
    /// let mut ll = xll![1, 2, 1, 2, 3];
    /// let mut cursor = ll.cursor_front_mut();
    /// cursor.move_next();
    /// cursor.move_next();
    /// assert_eq!(cursor.split_before(), xll![1, 2]);
    /// assert_eq!(ll, xll![1, 2, 3]);
    /// ```
    pub fn split_before(&mut self) -> XorLinkedList<T> {
        if self.cur.is_null() {
            core::mem::replace(self.ll, xll!())
        } else {
            if self.prev.is_null() {
                return xll!();
            }
            unsafe {
                let cur = &mut *self.cur;
                let prev = &mut *self.prev;
                let idx = self.index;
                let len = self.ll.len - idx - 1;
                self.ll.len = idx + 1;
                cur.ptr = self.next;
                prev.ptr = xor(prev.ptr, cur);
                let tail = core::mem::replace(&mut self.prev, null_mut());
                let head = core::mem::replace(&mut self.ll.head, self.cur);
                XorLinkedList { len, tail, head }
            }
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for CursorMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("CursorMut")
            .field(&self.ll)
            .field(&self.index)
            .finish()
    }
}

// SAFETY: We never mutate the node from a shared reference so thread safety is guaranteed
unsafe impl<T: Sync> Sync for Node<T> {}
unsafe impl<T: Send> Send for Node<T> {}
// SAFETY: We never mutate the list from a shared reference so thread safety is guaranteed
unsafe impl<T: Sync> Sync for XorLinkedList<T> {}
unsafe impl<T: Send> Send for XorLinkedList<T> {}
// SAFETY: We never mutate the list through iterators from a shared reference so thread safety is guaranteed
unsafe impl<T: Sync> Sync for Iter<'_, T> {}
unsafe impl<T: Send> Send for Iter<'_, T> {}
unsafe impl<T: Sync> Sync for IterMut<'_, T> {}
unsafe impl<T: Send> Send for IterMut<'_, T> {}
unsafe impl<T: Sync> Sync for Cursor<'_, T> {}
unsafe impl<T: Send> Send for Cursor<'_, T> {}
unsafe impl<T: Sync> Sync for CursorMut<'_, T> {}
unsafe impl<T: Send> Send for CursorMut<'_, T> {}

/// A macro for creating [`XorLinkedList`]s similar to [`vec`](https://doc.rust-lang.org/stable/alloc/macro.vec.html).
///
/// # Examples
/// ```rust
/// use xorlinkedlist::{xll, XorLinkedList};
/// // Create an empty list.
/// let ll: XorLinkedList<i32> = xll![];
/// // Create a list with the given elements.
/// let ll = xll![1, 2, 3];
/// // Create a list with the given element and length.
/// let ll = xll![1; 3];
/// // Create an empty list of a given type.
/// let ll = xll![<i32>];
/// ```
#[macro_export]
macro_rules! xll {
    [] => {
        $crate::XorLinkedList::new()
    };
    [<$t: ty>] => {
        $crate::XorLinkedList::<$t>::new()
    };
    [$($e: expr), +] => {{
        let mut ll = xll![];
        $(ll.push_back($e);)*
        ll
    }};
    [$($e: expr,) +] => {
        $crate::xll![$($e),+]
    };
    [$e: expr; $n: expr] => {{
        match $n {
            0 => $crate::xll![],
            1 =>  $crate::xll![$e],
            n => {
                let e = $e;
                let mut ll = $crate::xll![];
                for _ in 0..n - 1 {
                    ll.push_back(e.clone());
                }
                ll.push_back(e);
                ll
            }
        }
    }};
}

#[cfg(test)]
mod tests {
    use super::XorLinkedList;

    #[test]
    fn push_back() {
        let mut ll = XorLinkedList::new();
        for i in 0..20 {
            ll.push_back(i);
        }
        assert!(ll.into_iter().eq(0..20));
    }

    #[test]
    fn push_front() {
        let mut ll = XorLinkedList::new();
        for i in 0..20 {
            ll.push_front(i);
        }
        assert!(ll.into_iter().eq((0..20).rev()));
    }

    #[test]
    fn pop_back() {
        let mut ll = xll!(1, 2, 3, 4);
        assert!(ll.iter().copied().eq(1..=4));
        assert_eq!(ll.len(), 4);
        ll.pop_back();
        assert!(ll.iter().copied().eq(1..=3));
        assert_eq!(ll.len(), 3);
    }

    #[test]
    fn pop_front() {
        let mut ll = xll!(1, 2, 3, 4);
        assert!(ll.iter().copied().eq(1..=4));
        assert_eq!(ll.len(), 4);
        ll.pop_front();
        assert!(ll.iter().copied().eq(2..=4));
        assert_eq!(ll.len(), 3);
    }

    #[test]
    fn xll() {
        let mut ll = xll![0, 1, 2];
        ll.push_back(3);
        let mut ll2 = xll![0, 1, 2];
        ll2.push_back(3);
        let ll3 = xll![1; 4];
        assert_eq!(ll, ll2);
        assert!(ll.into_iter().eq(0..4));
        assert!(ll3.into_iter().eq((0..4).map(|_| 1)));
    }

    #[test]
    fn reverse() {
        let mut ll = xll!(1, 2, 3);
        assert!(ll.iter().copied().eq(1..=3));
        ll.reverse();
        assert!(ll.iter().copied().eq((1..=3).rev()));
    }

    #[test]
    fn cursor() {
        let ll = xll!(1, 2, 3, 4);
        let mut cursor = ll.cursor_front();
        for i in ll.iter() {
            assert_eq!(Some(i), cursor.current());
            cursor.move_next();
        }
        for i in ll.iter() {
            cursor.move_next();
            assert_eq!(Some(i), cursor.current());
        }
        let mut cursor = ll.cursor_back();
        for i in ll.iter().rev() {
            assert_eq!(Some(i), cursor.current());
            cursor.move_prev();
        }
        for i in ll.iter().rev() {
            cursor.move_prev();
            assert_eq!(Some(i), cursor.current());
        }
    }

    #[test]
    fn cursor_mut() {
        let mut ll = xll!(1, 2, 3, 4);
        let mut cursor = ll.cursor_front_mut();
        for i in 1..=4 {
            assert_eq!(Some(i), cursor.current().copied());
            *cursor.current().unwrap() += 1;
            assert_eq!(Some(i + 1), cursor.current().copied());
            *cursor.current().unwrap() -= 1;
            assert_eq!(Some(i), cursor.current().copied());
            cursor.move_next();
        }
        for i in 1..=4 {
            cursor.move_next();
            assert_eq!(Some(i), cursor.current().copied());
            *cursor.current().unwrap() += 1;
            assert_eq!(Some(i + 1), cursor.current().copied());
            *cursor.current().unwrap() -= 1;
            assert_eq!(Some(i), cursor.current().copied());
        }
        cursor = ll.cursor_front_mut();
        cursor.move_next();
        cursor.splice_after(xll!(5, 6));
        drop(cursor);
        assert!(ll.iter().eq([1, 2, 5, 6, 3, 4].iter()));
        cursor = ll.cursor_front_mut();
        cursor.move_next();
        cursor.move_next();
        assert_eq!(cursor.remove_current(), Some(5));
        assert_eq!(cursor.remove_current(), Some(6));
        drop(cursor);
        assert!(ll.iter().eq([1, 2, 3, 4].iter()));
    }
}
