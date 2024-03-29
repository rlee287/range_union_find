#![forbid(unsafe_code)]
#![no_std]
#![doc(html_root_url = "https://docs.rs/range_union_find/0.5.0")]

//! Provides a data structure backed by a vector for unioning ranges of integers.
//! We intelligently merge inserted ranges to minimize required storage.
//! 
//! Example usage:
//! ```
//! # use range_union_find::*;
//! let mut range_holder = RangeUnionFind::<u32>::new();
//! range_holder.insert_range(&(4..=8))?;
//! range_holder.insert_range(&(6..=10))?;
//! assert_eq!(range_holder.has_range(&(2..=12))?, OverlapType::Partial(7));
//! assert_eq!(range_holder.has_range(&(5..=9))?, OverlapType::Contained);
//! # Ok::<(), RangeOperationError>(())
//! ```
//! 
//! The main type is the [`RangeUnionFind`] struct, with the [`NumInRange`] trait implemented for primitive integer and float types that can be used to form ranges. While we make a best effort to support floating point ranges, unexpected issues may arise with floating point imprecision.
#[cfg(any(feature = "std", test))]
#[macro_use]
extern crate std;

extern crate alloc;

use core::ops::{Bound, RangeBounds, RangeInclusive};
use core::ops::{BitOr, BitOrAssign, Sub, SubAssign, BitAnd, BitAndAssign, Not, BitXor, BitXorAssign};
use core::cmp::{min, max};

use alloc::vec::Vec;
use sorted_vec::SortedVec;
use core::iter::FromIterator;
use core::borrow::Borrow;

use core::fmt;
use alloc::format;
use alloc::string::String;

#[cfg(feature = "include_serde")]
use serde::{Serialize, Deserialize};

mod num_trait;
use num_trait::get_normalized_range;
pub use num_trait::{NumInRange, Steppable, RangeOperationError};

mod float_helpers;
pub use float_helpers::{NonNanFloat, FloatIsNan};

/// Enum describing what location an element has in a range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ContainedType {
    /// Element is outside a range.
    Exterior,
    /// Element is at the beginning of a range.
    Start,
    /// Element is in the middle of a range.
    Interior,
    /// Element is at the end of a range.
    End
}
/// Enum describing how a range may overlap with another range.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OverlapType<T: NumInRange> {
    /// Range does not overlap at all.
    Disjoint,
    /// Range overlaps partially, with parameter being overlap count.
    Partial(T),
    /// Range is contained in the data structure.
    Contained
}

#[inline]
fn get_result_wrapped_val<T>(res: Result<T,T>) -> T {
    match res {
        Ok(val) => val,
        Err(val) => val
    }
}

#[derive(Default, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "include_serde", derive(Serialize, Deserialize))]
/*
 * Stores ranges in the following form:
 * range_storage [a_1, b_1, a_2, b_2, ...]
 * Ranges are [a_i, b_i] and include both ends
 * assert always b_i < a_{i+1}; ranges are disjoint
 * We also assume ranges are always as optimized as possible
 */
/// Struct representing a union of ranges. See the documentation for [`NonNanFloat`]'s impl of the [`Steppable`] trait for caveats when using this type with floating-point numbers.
pub struct RangeUnionFind<T: NumInRange> {
    range_storage: SortedVec<T>,
}

impl<T: NumInRange> RangeUnionFind<T>
{
    /// Constructs a new [`RangeUnionFind`] object.
    pub fn new() -> Self {
        RangeUnionFind {
            range_storage: SortedVec::new(),
        }
    }

    /// Clears all the ranges stored in this object.
    pub fn clear(&mut self) {
        self.range_storage.clear();
    }

    /// Returns a tuple describing the range the element is in, as well as its location.
    /// The range_id is a count of which range the element is in.
    /// The enum indicates where the element is in the range, with
    /// `(Exterior,i)` meaning the exterior region before the i'th range.
    /// See [`ContainedType`] for an explanation of the enum values.
    /// 
    /// If the element is in a single-element range of the form `a..=a`,
    /// the enum will not be `Exterior`, but its exact value is otherwise unspecified.
    ///
    /// # Example
    ///
    /// ```
    /// # use range_union_find::*;
    /// let mut range_obj = RangeUnionFind::new();
    /// range_obj.insert_range(&(10..20));
    /// assert_eq!(range_obj.has_element_enum(&0),
    ///     (ContainedType::Exterior, 0));
    /// assert_eq!(range_obj.has_element_enum(&10),
    ///     (ContainedType::Start, 0));
    /// assert_eq!(range_obj.has_element_enum(&15),
    ///     (ContainedType::Interior, 0));
    /// assert_eq!(range_obj.has_element_enum(&19),
    ///     (ContainedType::End, 0));
    /// assert_eq!(range_obj.has_element_enum(&25),
    ///     (ContainedType::Exterior, 1));
    /// ```
    /// 
    /// ```
    /// # use range_union_find::*;
    /// let mut range_obj = RangeUnionFind::new();
    /// range_obj.insert_range(&(8..=8));
    /// let (contain_enum, contain_id) = range_obj.has_element_enum(&8);
    /// assert_ne!(contain_enum, ContainedType::Exterior);
    /// assert_eq!(contain_id, 0);
    /// ```
    pub fn has_element_enum(&self, element: &T) -> (ContainedType, usize) {
        assert!(self.range_storage.len() % 2 == 0);
        /*
         * Ok(pos) -> element in list -> endpoint
         * Err(pos) -> element not in list -> strictly inside or outside
         */
        let would_insert_loc = self.range_storage.binary_search(element);
        let enum_val = match would_insert_loc {
            Ok(pos) => match pos % 2 {
                0 => ContainedType::Start,
                1 => ContainedType::End,
                _ => unreachable!()
            },
            Err(pos) => match pos % 2 {
                0 => ContainedType::Exterior,
                1 => ContainedType::Interior,
                _ => unreachable!()
            }
        };
        // Range id => indexes into vector are id*2, id*2+1
        // Using round-down division here
        (enum_val, get_result_wrapped_val(would_insert_loc)/2)
    }
    /// Returns whether the element is contained in the stored ranges.
    /// Returns `false` when [`Self::has_element_enum`] returns a
    /// [`ContainedType::Exterior`] enum, and `true` otherwise.
    pub fn has_element(&self, element: &T) -> bool {
        !matches!(self.has_element_enum(element),
            (ContainedType::Exterior, _))
    }

    // Returns whether the given range_id is a singleton of the form `a..=a`.
    fn is_range_singleton(&self, range_id: usize) -> Option<bool> {
        match self.range_storage.get(2*range_id..=2*range_id+1) {
            None => None,
            Some([a, b]) => Some(a == b),
            _ => unreachable!()
        }
    }

    /// Returns how the given range overlaps with the stored ranges.
    /// See [`OverlapType`] for a description of the enum values.
    /// 
    /// # Example
    ///
    /// ```
    /// # use range_union_find::*;
    /// let mut range_obj = RangeUnionFind::new();
    /// range_obj.insert_range(&(10..20));
    /// range_obj.insert_range(&(-20..-10));
    /// assert_eq!(range_obj.has_range(&(15..17))?,
    ///     OverlapType::Contained);
    /// assert_eq!(range_obj.has_range(&(-5..5))?,
    ///     OverlapType::Disjoint);
    /// assert_eq!(range_obj.has_range(&(0..20))?,
    ///     OverlapType::Partial(10));
    /// assert_eq!(range_obj.has_range(&(-15..15))?,
    ///     OverlapType::Partial(10));
    /// # Ok::<(), RangeOperationError>(())
    /// ```
    ///
    /// # Errors
    ///
    /// Returns [`RangeOperationError`] if given range is invalid.
    pub fn has_range<U: RangeBounds<T>>(&self, range: &U)
            -> Result<OverlapType<T>,RangeOperationError> {
        let (input_start, input_end) = match get_normalized_range(range) {
            Ok((val_start,val_end)) => (val_start,val_end),
            Err(err) => return Err(err)
        };
        self.has_range_pair(&input_start, &input_end)
    }
    /// Functions like [`Self::has_range`] given input `start..=end`.
    pub fn has_range_pair(&self, start: &T, end: &T) -> Result<OverlapType<T>, RangeOperationError> {
        if start > end {
            return Err(RangeOperationError::IsDecreasingOrEmpty);
        }
        let vec_count = self.range_storage.len();
        let (range_start_enum, range_start_id) = self.has_element_enum(&start);
        let (range_end_enum, range_end_id) = self.has_element_enum(&end);
        assert!(range_end_id >= range_start_id);
        if range_start_id == range_end_id {
            // Single range, given endpoint<=a contained range endpoint
            if range_start_enum != ContainedType::Exterior {
                assert!(range_end_enum != ContainedType::Exterior);
                return Ok(OverlapType::Contained);
            } else {
                return match range_end_enum {
                    ContainedType::Exterior => Ok(OverlapType::Disjoint),
                    ContainedType::Start => {
                        let stored_range_start = &self.range_storage[2*range_start_id];
                        assert!(end == stored_range_start);
                        // Overlap is 1 for integer types and 0 for real types
                        Ok(OverlapType::Partial(
                            T::range_tuple_size(stored_range_start, end).unwrap()))
                    },
                    ContainedType::Interior => {
                        let stored_range_start = &self.range_storage[2*range_start_id];
                        //let overlap = *end-stored_range_start+T::one();
                        let overlap = T::range_tuple_size(stored_range_start, end).unwrap();
                        Ok(OverlapType::Partial(overlap))
                    }
                    ContainedType::End => {
                        let stored_range_start = &self.range_storage[2*range_start_id];
                        let stored_range_end = &self.range_storage[2*range_end_id+1];
                        //let overlap = *end-stored_range_start+T::one();
                        let overlap = T::range_tuple_size(stored_range_start, end).unwrap();
                        assert!(end == stored_range_end);
                        Ok(OverlapType::Partial(overlap))
                    }
                };
            }
        } else if range_end_id == range_start_id+1
                && range_end_enum == ContainedType::Exterior {
            // Single range, given endpoint>a contained range endpoint
            let contained_range_start = &self.range_storage[2*range_start_id];
            let contained_range_end = &self.range_storage[2*range_start_id+1];
            match range_start_enum {
                ContainedType::Exterior | ContainedType::Start => {
                    //let size = contained_range_end-contained_range_start+T::one();
                    let size = T::range_tuple_size(contained_range_start, contained_range_end).unwrap();
                    if range_start_enum == ContainedType::Start {
                        assert!(start == contained_range_start);
                    }
                    return Ok(OverlapType::Partial(size));
                },
                ContainedType::Interior => {
                    //let size = contained_range_end-*start+T::one();
                    let size = T::range_tuple_size(start, &contained_range_end).unwrap();
                    return Ok(OverlapType::Partial(size));
                },
                ContainedType::End => {
                    assert!(start == contained_range_end);
                    // Overlap is 1 for integer types and 0 for real types
                    return Ok(OverlapType::Partial(
                        T::range_tuple_size(start, &contained_range_end).unwrap()));
                }
            }
        } else {
            // Multiple ranges
            // The answer must be partial, but we need to find the count
            assert!(
                !(range_end_enum==ContainedType::Exterior
                && range_end_id==0)
            );
            assert!(
                !(range_start_enum==ContainedType::Exterior
                && range_start_id==vec_count)
            );
            // Count overlap for range_start_id range
            let mut partial_count = match range_start_enum {
                ContainedType::Exterior | ContainedType::Start => {
                    let contained_range_start = &self.range_storage[2*range_start_id];
                    let contained_range_end = &self.range_storage[2*range_start_id+1];
                    if range_start_enum == ContainedType::Start {
                        assert!(start == contained_range_start);
                    }
                    //contained_range_end-contained_range_start+T::one()
                    T::range_tuple_size(contained_range_start, contained_range_end).unwrap()
                },
                ContainedType::Interior => {
                    let contained_range_end = &self.range_storage[2*range_start_id+1];
                    //contained_range_end-*start+T::one()
                    T::range_tuple_size(start, contained_range_end).unwrap()
                }
                ContainedType::End => {
                    let contained_range_end = &self.range_storage[2*range_start_id+1];
                    assert!(start == contained_range_end);
                    // Overlap is 1 for integer types and 0 for real types
                    T::range_tuple_size(start, contained_range_end).unwrap()
                }
            };
            // Count overlap for range_end_id range
            if range_end_enum!=ContainedType::Exterior {
                let contained_range_begin = &self.range_storage[2*range_end_id];
                //let size = *end-contained_range_begin+T::one();
                let size = T::range_tuple_size(contained_range_begin, end).unwrap();
                // Asserts
                match range_end_enum {
                    ContainedType::Exterior => unreachable!(),
                    ContainedType::Start => {
                        // 1 for integer types and 0 for real types
                    },
                    ContainedType::Interior => (), // No assert needed
                    ContainedType::End => {
                        let contained_range_end = &self.range_storage[2*range_end_id+1];
                        assert!(end == contained_range_end);
                    }
                }
                partial_count = partial_count + size;
            }
            // Count overlap for intermediate ranges
            for selected_id in range_start_id+1..range_end_id {
                let selected_range_begin = &self.range_storage[2*selected_id];
                let selected_range_end = &self.range_storage[2*selected_id+1];
                //let size = selected_range_end-selected_range_begin+T::one();
                let size = T::range_tuple_size(selected_range_begin, selected_range_end).unwrap();
                partial_count = partial_count + size;
            }
            return Ok(OverlapType::Partial(partial_count));
        }
    }

    /// Returns the range the element is in.
    /// If the element is in a range, return `Ok(range_with_element)`.
    /// Otherwise, return `Err(range_between_stored_ranges)`.
    ///
    /// *Warning: the `impl RangeBounds<T>` object does not include a `Debug` impl, so `unwrap` and `unwrap_err` cannot be used on the returned result.*
    ///
    /// # Example
    ///
    /// ```
    /// # use range_union_find::*;
    /// # use std::ops::{Bound, RangeBounds};
    /// let mut range_obj = RangeUnionFind::<i32>::new();
    /// range_obj.insert_range(&(10..=20));
    ///
    /// let one_result = range_obj.find_range_with_element(&1);
    /// assert!(match one_result {
    ///     Err(one_err) => {
    ///         assert_eq!(one_err.start_bound(), Bound::Unbounded);
    ///         assert_eq!(one_err.end_bound(), Bound::Excluded(&10));
    ///         true
    ///     },
    ///     Ok(_) => false
    /// });
    ///
    /// let twelve_result = range_obj.find_range_with_element(&12);
    /// assert!(match twelve_result {
    ///     Ok(twelve_range) => {
    ///         assert_eq!(twelve_range.start_bound(), Bound::Included(&10));
    ///         assert_eq!(twelve_range.end_bound(), Bound::Included(&20));
    ///         true
    ///     },
    ///     Err(_) => false
    /// });
    ///
    /// let seventy_result = range_obj.find_range_with_element(&70);
    /// assert!(match seventy_result {
    ///     Err(seventy_err) => {
    ///         assert_eq!(seventy_err.start_bound(), Bound::Excluded(&20));
    ///         assert_eq!(seventy_err.end_bound(), Bound::Unbounded);
    ///         true
    ///     },
    ///     Ok(_) => false
    /// });
    /// ```
    pub fn find_range_with_element(&self, element: &T) -> Result<impl RangeBounds<T>, impl RangeBounds<T>> {
        let (element_enum, element_range_id) = self.has_element_enum(element);
        let range_count = self.range_storage.len() / 2;
        if element_enum == ContainedType::Exterior {
            if element_range_id == 0 {
                return Err((
                    Bound::Unbounded,
                    Bound::Excluded(self.range_storage[0].clone())
                ));
            } else if element_range_id == range_count {
                let end_index = 2*element_range_id-1;
                return Err((
                    Bound::Excluded(self.range_storage[end_index].clone()),
                    Bound::Unbounded
                ));
            } else {
                let next_range_start = self.range_storage[2*element_range_id].clone();
                // 2*(element_range_id-1)+1
                let prev_range_end = self.range_storage[2*element_range_id-1].clone();
                return Err((
                    Bound::Excluded(prev_range_end),
                    Bound::Excluded(next_range_start)
                ));
            }
        } else {
            let range_start = self.range_storage[2*element_range_id].clone();
            let range_end = self.range_storage[2*element_range_id+1].clone();
            return Ok((
                Bound::Included(range_start),
                Bound::Included(range_end)
            ));
        }
    }

    /// Inserts the range into the set of ranges.
    ///
    /// # Errors
    ///
    /// Returns [`RangeOperationError`] if the given range is invalid.
    pub fn insert_range<U: RangeBounds<T>>(&mut self, range: &U)
            -> Result<(), RangeOperationError> {
        let (input_start, input_end) = match get_normalized_range(range) {
            Ok((val_start,val_end)) => (val_start,val_end),
            Err(err) => return Err(err)
        };
        self.insert_range_pair(&input_start, &input_end)
    }
    /// Functions like [`Self::insert_range`] given input `start..=end`.
    pub fn insert_range_pair(&mut self, start: &T, end: &T)
            -> Result<(), RangeOperationError> {
        assert!(self.range_storage.len() % 2 == 0);
        if start > end {
            return Err(RangeOperationError::IsDecreasingOrEmpty);
        }
        match self.has_range_pair(&start, &end).unwrap() {
            OverlapType::Disjoint => {
                // Use match arms to catch potential overflows
                let prev_adj = match *start == T::min_value() {
                    true => Err(0), // start index, guaranteed not present
                    false => self.range_storage.binary_search(&start.step_decr())
                };
                let next_adj = match *end == T::max_value() {
                    true => Err(self.range_storage.len()), // end index, guaranteed not present
                    false => self.range_storage.binary_search(&end.step_incr())
                };
                if let (Ok(prev_val), Ok(next_val)) = (prev_adj, next_adj) {
                    // For a single-point range, binary search may have found "wrong" element
                    // If so, we increment the first index to remove by 1
                    // And/or decrement the second index to remove by 1

                    // Element fills gap between ranges
                    assert!(prev_val % 2 == 1 || self.range_storage[prev_val] == self.range_storage[prev_val+1]);
                    assert!(next_val % 2 == 0 || self.range_storage[next_val-1] == self.range_storage[next_val]);
                    let index_remove = match prev_val % 2 {
                        0 => prev_val + 1,
                        1 => prev_val,
                        _ => unreachable!()
                    };
                    let index_remove_incr = match next_val % 2 {
                        0 => next_val,
                        1 => next_val - 1,
                        _ => unreachable!()
                    };
                    assert!(index_remove + 1 == index_remove_incr);
                    // Remove both endpoints
                    self.range_storage.drain(index_remove..=index_remove+1);
                } else if let Ok(prev_val) = prev_adj {
                    // For a single-point range, binary search may have found first element
                    // If so, we increment the index to remove by 1
                    assert!(prev_val % 2 == 1 || self.range_storage[prev_val] == self.range_storage[prev_val+1]);
                    // Extend start range by one, and insert other end
                    let index_remove = match prev_val % 2 {
                        0 => prev_val + 1,
                        1 => prev_val,
                        _ => unreachable!()
                    };
                    self.range_storage.remove_index(index_remove);
                    self.range_storage.insert(end.clone());
                } else if let Ok(next_val) = next_adj {
                    // For a single-point range, binary search may have found second element
                    // If so, we decrement the index to remove by 1
                    assert!(next_val % 2 == 0 || self.range_storage[next_val-1] == self.range_storage[next_val]);
                    // Extend end range by one, and insert other end
                    let index_remove = match next_val % 2 {
                        0 => next_val,
                        1 => next_val - 1,
                        _ => unreachable!()
                    };
                    self.range_storage.remove_index(index_remove);
                    self.range_storage.insert(start.clone());
                } else {
                    assert_eq!(prev_adj.unwrap_err() % 2, 0);
                    assert_eq!(prev_adj.unwrap_err(), next_adj.unwrap_err());
                    // Insert entirely new range
                    self.range_storage.insert(start.clone());
                    self.range_storage.insert(end.clone());
                }
            }
            OverlapType::Partial(_) => {
                // Subsume all the intermediate ranges in the middle
                let del_index_start = {
                    let (_, start_range_id) = self.has_element_enum(&start);
                    2*start_range_id+1
                };
                let del_index_end = {
                    let (end_enum, end_range_id) = self.has_element_enum(&end);
                    match end_enum {
                        ContainedType::Exterior => {
                            // end_range_id==0 -> range isn't partial
                            debug_assert_ne!(end_range_id, 0);
                            2*(end_range_id-1)
                        },
                        _ => 2*end_range_id
                    }
                };
                assert!(del_index_start % 2 == 1);
                assert!(del_index_end % 2 == 0);
                if del_index_end > del_index_start {
                    // Guaranteed by asserts above
                    //assert!((del_index_end - del_index_start + 1) % 2 == 0);
                    self.range_storage.drain(del_index_start..=del_index_end);
                } else {
                    assert_eq!(del_index_start, del_index_end + 1);
                }

                // Adjust the start point
                let (start_enum, start_range_id) = self.has_element_enum(&start);
                if start_enum == ContainedType::Exterior {
                    let index_rm = 2*start_range_id;
                    if start_range_id > 0
                            && self.range_storage[index_rm-1] == start.step_decr() {
                        // End of prev range is adjacent to new one-merge ranges
                        // Removing gap is justified because overlap is partial
                        // start_range_id > 0 -> ranges do not involve 0
                        self.range_storage.drain(index_rm-1..=index_rm);
                    } else {
                        // Extend range with new starting position
                        let old_element = self.range_storage[index_rm].clone();
                        let insert_pos = self.range_storage.insert(start.clone());
                        assert_eq!(insert_pos, index_rm);
                        let removed_element = self.range_storage.remove_index(index_rm+1);
                        assert!(old_element == removed_element);
                    }
                }
                // Adjust the end point
                let (end_enum, end_range_id) = self.has_element_enum(&end);
                if end_enum == ContainedType::Exterior {
                    // end_range_id==0 -> range isn't partial
                    debug_assert_ne!(end_range_id, 0);
                    let old_index_rm = 2*(end_range_id-1)+1;
                    if old_index_rm < (self.range_storage.len()-1)
                            && self.range_storage[old_index_rm+1] == end.step_incr() {
                        // Start of next range is adjacent to inserted range
                        self.range_storage.drain(old_index_rm..=old_index_rm+1);
                    } else {
                        // Extend range with new ending position
                        let old_element = self.range_storage[old_index_rm].clone();
                        let insert_pos = self.range_storage.insert(end.clone());
                        assert_eq!(insert_pos, old_index_rm+1);
                        let removed_element = self.range_storage.remove_index(old_index_rm);
                        assert!(old_element == removed_element);
                    }
                }
            }
            OverlapType::Contained => {
                // Do nothing
            }
        }
        Ok(())
    }

    /// Removes the range from the set of ranges.
    ///
    /// # Errors
    ///
    /// Returns [`RangeOperationError`] if the given range is invalid.
    pub fn remove_range<U: RangeBounds<T>>(&mut self, range: &U)
            -> Result<(), RangeOperationError> {
        let (input_start, input_end) = match get_normalized_range(range) {
            Ok((val_start,val_end)) => (val_start,val_end),
            Err(err) => return Err(err)
        };
        self.remove_range_pair(&input_start, &input_end)
    }
    /// Functions like [`Self::remove_range`] given input `start..=end`.
    pub fn remove_range_pair(&mut self, start: &T, end: &T)
            -> Result<(), RangeOperationError> {
        assert!(self.range_storage.len() % 2 == 0);
        if start > end {
            return Err(RangeOperationError::IsDecreasingOrEmpty);
        }
        match self.has_range_pair(&start, &end).unwrap() {
            OverlapType::Disjoint => {
                // Do nothing
            }
            OverlapType::Partial(_) => {
                // Delete all the intermediate ranges in the middle
                let del_index_start = {
                    let (start_enum, start_range_id) = self.has_element_enum(&start);
                    match start_enum {
                        ContainedType::Exterior => 2*start_range_id,
                        _ => 2*(start_range_id+1)
                    }
                };
                let del_index_end_opt = {
                    let (_, end_range_id) = self.has_element_enum(&end);
                    // Exterior -> subtract to the range before
                    // else -> skip past the range the endpoint lies in
                    // Computation result is the same regardless
                    // Checked sub to catch 0 underflow
                    (2*end_range_id).checked_sub(1)
                };
                // These should be true, except for overflow prevention
                //assert!(del_index_start % 2 == 0);
                //assert!(del_index_end % 2 == 1);
                if let Some(del_index_end) = del_index_end_opt {
                    if del_index_end > del_index_start {
                        // Guaranteed by above asserts
                        //assert!((del_index_end - del_index_start + 1) % 2 == 0);
                        self.range_storage.drain(del_index_start..=del_index_end);
                    } else {
                        assert_eq!(del_index_start, del_index_end + 1);
                    }
                } else {
                    // "Correct" behavior: start=0 and end=-1
                    // This is also the only time this branch should ever be taken
                    assert_eq!(del_index_start, 0);
                }

                // Also do singleton checks as exact loc enum for singleton ranges is unspecified
                // Adjust the start point
                let (start_enum, start_range_id) = self.has_element_enum(&start);
                if start_enum == ContainedType::Start ||
                        (start_enum != ContainedType::Exterior && self.is_range_singleton(start_range_id).unwrap()) {
                    // Given start lines up with start of a range
                    // Was partial -> delete this entire range
                    self.range_storage.drain(
                        2*start_range_id..=2*start_range_id+1);
                } else if start_enum != ContainedType::Exterior {
                    // Move the endpoint to new location
                    self.range_storage.remove_index(2*start_range_id+1);
                    let insert_pos = {
                        let ret_pos = self.range_storage.insert(start.step_decr());
                        match ret_pos % 2 {
                            0 => {
                                // Should only hit this if a singleton is left
                                assert!(self.range_storage[ret_pos] == self.range_storage[ret_pos+1]);
                                ret_pos + 1
                            }
                            1 => ret_pos,
                            _ => unreachable!()
                        }
                    };
                    assert!(insert_pos == 2*start_range_id+1);
                }
                // Adjust the end point
                let (end_enum, end_range_id) = self.has_element_enum(&end);
                if end_enum == ContainedType::End ||
                        (end_enum != ContainedType::Exterior && self.is_range_singleton(end_range_id).unwrap()){
                    // Given end lines up with end of a range
                    // Was partial -> delete this entire range
                    self.range_storage.drain(
                        2*end_range_id..=2*end_range_id+1);
                } else if end_enum != ContainedType::Exterior {
                    // Move the startpoint to new location
                    self.range_storage.remove_index(2*end_range_id);
                    let insert_pos = {
                        let ret_pos = self.range_storage.insert(end.step_incr());
                        match ret_pos % 2 {
                            0 => ret_pos,
                            1 => {
                                // Should only hit this if a singleton is left
                                // Theoretical as of now due to implementation-defined characteristics of binary search
                                assert!(self.range_storage[ret_pos-1] == self.range_storage[ret_pos]);
                                ret_pos - 1
                            }
                            _ => unreachable!()
                        }
                    };
                    assert_eq!(insert_pos, 2*end_range_id);
                }
            }
            OverlapType::Contained => {
                let prev_adj = self.range_storage.binary_search(start);
                let next_adj = self.range_storage.binary_search(end);
                if let (Ok(prev_val), Ok(next_val)) = (prev_adj, next_adj) {
                    if prev_val == next_val {
                        // Range has single element, equal to an endpoint
                        let old_endpoint = self.range_storage.remove_index(prev_val);
                        let replacement_endpoint = match prev_val % 2 {
                            0 => old_endpoint.step_incr(), // Was beginning
                            1 => old_endpoint.step_decr(), // Was end
                            _ => unreachable!()
                        };
                        self.range_storage.insert(replacement_endpoint);
                    } else {
                        assert_eq!(prev_val+1, next_val);
                        // Range exactly matches an existing range
                        // Remove both endpoints
                        self.range_storage.drain(prev_val..=prev_val+1);
                    }
                } else if let (Ok(prev_val), Err(next_val)) = (prev_adj, next_adj) {
                    assert_eq!(prev_val+1, next_val);
                    assert_eq!(prev_val % 2, 0);
                    // Shrink start range by replacing start point
                    self.range_storage.remove_index(prev_val);
                    self.range_storage.insert(end.step_incr());
                } else if let (Err(prev_val), Ok(next_val)) = (prev_adj, next_adj) {
                    assert_eq!(prev_val, next_val);
                    assert_eq!(prev_val % 2, 1);
                    // Extend end range by one, and insert other end
                    self.range_storage.remove_index(next_val);
                    self.range_storage.insert(start.step_decr());
                } else {
                    // Subtract entirely new range
                    self.range_storage.insert(start.step_decr());
                    self.range_storage.insert(end.step_incr());
                }
            }
        }
        Ok(())
    }

    /// Creates a collection of [`RangeInclusive`] with element type `T` from a [`RangeUnionFind`] object.
    pub fn into_collection<U>(self) -> U
    where
        U: FromIterator<RangeInclusive<T>>
    {
        assert!(self.range_storage.len() % 2 == 0);
        let size = self.range_storage.len() / 2;
        let mut self_iter = self.range_storage.into_vec().into_iter();
        let mut collect_vec = Vec::with_capacity(size);
        while let (Some(begin), Some(end)) = (self_iter.next(), self_iter.next()) {
            collect_vec.push(begin..=end);
        };
        collect_vec.into_iter().collect::<U>()
    }
    /// Converts a [`RangeUnionFind`] object into a collection of [`RangeInclusive`] with element type `T`.
    pub fn to_collection<U>(&self) -> U
    where
        U: FromIterator<RangeInclusive<T>>
    {
        self.clone().into_collection()
    }
}

impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> BitOr<B> for &RangeUnionFind<T> {
    type Output = RangeUnionFind<T>;
    /// Computes the union of the two [`RangeUnionFind`] objects.
    fn bitor(self, rhs: B) -> Self::Output {
        let mut dup_obj = self.clone();
        dup_obj |= rhs;
        dup_obj
    }
}
impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> BitOrAssign<B> for RangeUnionFind<T> {
    fn bitor_assign(&mut self, rhs: B) {
        self.extend(rhs.borrow().to_collection::<Vec<_>>())
    }
}

impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> Sub<B> for &RangeUnionFind<T> {
    type Output = RangeUnionFind<T>;
    /// Subtracts the rhs [`RangeUnionFind`] object from the lhs one.
    fn sub(self, rhs: B) -> Self::Output {
        let mut dup_obj = self.clone();
        dup_obj -= rhs;
        dup_obj
    }
}
impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> SubAssign<B> for RangeUnionFind<T> {
    fn sub_assign(&mut self, rhs: B) {
        for range in rhs.borrow().to_collection::<Vec<_>>() {
            self.remove_range(&range).unwrap();
        }
    }
}

impl<T: NumInRange> Not for &RangeUnionFind<T> {
    type Output = RangeUnionFind<T>;
    fn not(self) -> Self::Output {
        let mut full_obj = RangeUnionFind::new();
        full_obj.insert_range(&(..)).unwrap();
        &full_obj - self
    }
}

impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> BitXor<B> for &RangeUnionFind<T> {
    type Output = RangeUnionFind<T>;
    fn bitxor(self, rhs: B) -> Self::Output {
        let mut dup_obj = self.clone();
        dup_obj ^= rhs;
        dup_obj
    }
}
impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> BitXorAssign<B> for RangeUnionFind<T> {
    fn bitxor_assign(&mut self, rhs: B) {
        let rhs_ref = rhs.borrow();
        let intersection = &self.clone() & rhs_ref;
        self.extend(rhs_ref.to_collection::<Vec<_>>());
        for range in intersection.to_collection::<Vec<_>>() {
            self.remove_range(&range).unwrap();
        }
    }
}

impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> BitAnd<B> for &RangeUnionFind<T> {
    type Output = RangeUnionFind<T>;
    /// Computes the union of the two [`RangeUnionFind`] objects.
    fn bitand(self, rhs: B) -> Self::Output {
        let mut first_range_iter = self.to_collection::<Vec<_>>()
            .into_iter().peekable();
        let mut second_range_iter = rhs.borrow().to_collection::<Vec<_>>()
            .into_iter().peekable();
        // We rely on the iteration being in increasing order here
        let mut result_vec: Vec<RangeInclusive<T>> = Vec::new();
        // min_compare variables only used for asserting the above ordering
        #[cfg_attr(not(debug_assertions),
            allow(unused_variables), allow(unused_mut))]
        let mut min_compare_first = T::min_value();
        #[cfg_attr(not(debug_assertions),
            allow(unused_variables), allow(unused_mut))]
        let mut min_compare_second = T::min_value();
        loop {
            // One iter is out -> no more overlaps possible
            let first_range_option = first_range_iter.peek();
            if first_range_option.is_none() {
                break;
            }
            let second_range_option = second_range_iter.peek();
            if second_range_option.is_none() {
                break;
            }
            let first_range = get_normalized_range(first_range_option.unwrap()).unwrap();
            let second_range = get_normalized_range(second_range_option.unwrap()).unwrap();

            // Identify overlap and add overlap range to vec
            let start_overlap = max(&first_range.0, &second_range.0);
            let end_overlap = min(&first_range.1, &second_range.1);
            let overlap_range = start_overlap.clone()..=end_overlap.clone();
            if get_normalized_range(&overlap_range).is_ok() {
                result_vec.push(overlap_range);
            }

            // Advance the correct iterator and assert next elements are larger
            // Wrap asserts in cfg block in case assignment has side effects
            if first_range.1 <= second_range.1 {
                first_range_iter.next();
                #[cfg(debug_assertions)]
                {
                    debug_assert!(min_compare_first <= first_range.0);
                    debug_assert!(first_range.0 <= first_range.1);
                    min_compare_first = first_range.1;
                }
            } else {
                second_range_iter.next();
                #[cfg(debug_assertions)]
                {
                    debug_assert!(min_compare_second <= second_range.0);
                    debug_assert!(second_range.0 <= second_range.1);
                    min_compare_second = second_range.1;
                }
            }
        }
        RangeUnionFind::from_iter(result_vec.into_iter())
    }
}
impl<T: NumInRange, B: Borrow<RangeUnionFind<T>>> BitAndAssign<B> for RangeUnionFind<T> {
    fn bitand_assign(&mut self, rhs: B) {
        *self = (self as &Self) & rhs;
    }
}

impl<T> fmt::Debug for RangeUnionFind<T>
where
    T: NumInRange + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.range_storage.len() % 2 != 0 {
            let raw_vec_str = format!("{:?}", self.range_storage.to_vec());
            panic!("Invalid internal storage {}", raw_vec_str);
        }
        write!(f, "[")?;
        let mut pairs: Vec<String> = Vec::with_capacity(
            self.range_storage.len()/2);
        let mut range_pairs = self.range_storage.chunks_exact(2);
        loop {
            let range = match range_pairs.next() {
                None => {
                    debug_assert!(range_pairs.remainder().is_empty());
                    break;
                },
                Some(val) => val
            };
            pairs.push(format!("{:?}..={:?}", range[0], range[1]));
        }
        write!(f, "{}", pairs.join(", "))?;
        return write!(f, "]");
    }
}

impl<T, U> Extend<U> for RangeUnionFind<T>
where
    T: NumInRange,
    U: RangeBounds<T>
{
    /// Calls [`Self::insert_range`] for each range in the iterator.
    ///
    /// # Panics
    ///
    /// Panics if any of the range insertions return an `Err`.
    fn extend<I: IntoIterator<Item=U>>(&mut self, iter: I) {
        for range in iter {
            self.insert_range(&range).unwrap()
        }
    }
}

impl<T, U> FromIterator<U> for RangeUnionFind<T>
where
    T: NumInRange,
    U: RangeBounds<T>
{
    /// Calls [`Self::insert_range`] for each range in the iterator.
    ///
    /// # Panics
    ///
    /// Panics if any of the range insertions return an `Err`.
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = U>
    {
        let mut new_range_obj = RangeUnionFind::new();
        new_range_obj.extend(iter);
        new_range_obj
    }
}

// TODO: other Vec types?
impl<T: NumInRange> From<RangeUnionFind<T>> for Vec<RangeInclusive<T>> {
    fn from(union_obj: RangeUnionFind<T>) -> Vec<RangeInclusive<T>> {
        union_obj.into_collection()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use num_traits::Float;

    fn wrap_fp_range<F: Float, R: RangeBounds<F>>(range: &R) -> Result<(Bound<NonNanFloat<F>>, Bound<NonNanFloat<F>>), FloatIsNan> {
        let new_start = match range.start_bound() {
            Bound::Included(f) => Bound::Included(NonNanFloat::try_new(*f)?),
            Bound::Excluded(f) => Bound::Excluded(NonNanFloat::try_new(*f)?),
            Bound::Unbounded => Bound::Unbounded,
        };
        let new_end = match range.end_bound() {
            Bound::Included(f) => Bound::Included(NonNanFloat::try_new(*f)?),
            Bound::Excluded(f) => Bound::Excluded(NonNanFloat::try_new(*f)?),
            Bound::Unbounded => Bound::Unbounded,
        };
        Ok((new_start, new_end))
    }

    #[test]
    fn find_range_with_i32_element_in_triple() {
        let mut range_obj = RangeUnionFind::<i32>::new();
        range_obj.insert_range(&(0..=4)).unwrap();
        range_obj.insert_range(&(8..=8)).unwrap();
        range_obj.insert_range(&(10..=16)).unwrap();

        let minus_one_result = range_obj.find_range_with_element(&-1);
        if let Err(minus_one_err) = minus_one_result {
            assert_eq!(get_normalized_range(&minus_one_err).unwrap(),
                (i32::MIN, -1));
        } else {
            panic!("-1 was in range {:?}", range_obj);
        }
        let two_result = range_obj.find_range_with_element(&2);
        if let Ok(two_ok) = two_result {
            assert_eq!(get_normalized_range(&two_ok).unwrap(),
                (0, 4));
        } else {
            panic!("2 was not in range {:?}", range_obj);
        }
        let nine_result = range_obj.find_range_with_element(&9);
        if let Err(nine_err) = nine_result {
            assert_eq!(get_normalized_range(&nine_err).unwrap(),
                (9, 9));
        } else {
            panic!("9 was in range {:?}", range_obj);
        }
        let twenty_result = range_obj.find_range_with_element(&20);
        if let Err(twenty_err) = twenty_result {
            assert_eq!(get_normalized_range(&twenty_err).unwrap(),
                (17, i32::MAX));
        } else {
            panic!("20 was in range {:?}", range_obj);
        }
    }

    #[test]
    fn find_range_with_f64_element_in_triple() {
        let mut range_obj = RangeUnionFind::<NonNanFloat<f64>>::new();
        range_obj.insert_range(&wrap_fp_range(&(-2.0..=4.0)).unwrap()).unwrap();
        range_obj.insert_range(&wrap_fp_range(&(8.0..=8.0)).unwrap()).unwrap();
        range_obj.insert_range(&wrap_fp_range(&(10.0..16.0)).unwrap()).unwrap();

        let minus_three_result = range_obj.find_range_with_element(&NonNanFloat::new(-3.0));
        if let Err(minus_one_err) = minus_three_result {
            assert_eq!(get_normalized_range(&minus_one_err).unwrap(),
                (NonNanFloat::new(f64::NEG_INFINITY), NonNanFloat::new(-2.0).step_decr()));
        } else {
            panic!("-3 was in range {:?}", range_obj);
        }
        let two_result = range_obj.find_range_with_element(&NonNanFloat::new(2.0));
        if let Ok(two_ok) = two_result {
            assert_eq!(get_normalized_range(&two_ok).unwrap(),
                (NonNanFloat::new(-2.0), NonNanFloat::new(4.0)));
        } else {
            panic!("2 was not in range {:?}", range_obj);
        }
        let nine_result = range_obj.find_range_with_element(&NonNanFloat::new(9.0));
        if let Err(nine_err) = nine_result {
            assert_eq!(get_normalized_range(&nine_err).unwrap(),
            (NonNanFloat::new(8.0).step_incr(), NonNanFloat::new(10.0).step_decr()));
        } else {
            panic!("9 was in range {:?}", range_obj);
        }
        let twenty_result = range_obj.find_range_with_element(&NonNanFloat::new(20.0));
        if let Err(twenty_err) = twenty_result {
            assert_eq!(get_normalized_range(&twenty_err).unwrap(),
            (NonNanFloat::new(16.0), NonNanFloat::new(f64::INFINITY)));
        } else {
            panic!("20 was in range {:?}", range_obj);
        }
    }
}
