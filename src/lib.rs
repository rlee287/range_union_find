#![forbid(unsafe_code)]
#![doc(html_root_url = "https://docs.rs/range_union_find/0.3.0-dev")]

//! Provides a data structure backed by a vector for unioning ranges of integers.
//! We intelligently merge inserted ranges to minimize required storage.
//! 
//! Example usage:
//! ```
//! # use range_union_find::*;
//! let mut range_holder = IntRangeUnionFind::<u32>::new();
//! range_holder.insert_range(&(4..=8))?;
//! range_holder.insert_range(&(6..=10))?;
//! assert_eq!(range_holder.has_range(&(2..=12))?, OverlapType::Partial(7));
//! assert_eq!(range_holder.has_range(&(5..=9))?, OverlapType::Contained);
//! # Ok::<(), RangeOperationError>(())
//! ```
//! 
//! All the functionality is in the [`IntRangeUnionFind`] struct (though we may add `RangeUnionFind` structs for different element types in the future).
use std::ops::{Bound, RangeBounds, RangeInclusive};
use std::ops::{BitOr, Sub, BitAnd, Not, BitXor};
use std::cmp::{min, max};
use num_traits::PrimInt;
use sorted_vec::SortedVec;
use std::iter::FromIterator;

use std::fmt;

use std::error::Error;

/// Enum describing how a range may be invalid.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RangeOperationError {
    /// Range operation caused an overflow.
    WouldOverflow,
    /// Range is decreasing or empty.
    IsDecreasingOrEmpty
}
impl fmt::Display for RangeOperationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let description_str = match self {
            RangeOperationError::WouldOverflow =>
                "range normalization would overflow type",
            RangeOperationError::IsDecreasingOrEmpty =>
                "range has no elements"
        };
        write!(f, "{}", description_str)
    }
}
impl Error for RangeOperationError {}

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
pub enum OverlapType<T: PrimInt> {
    /// Range does not overlap at all.
    Disjoint,
    /// Range overlaps partially, with parameter being overlap count.
    Partial(T),
    /// Range is contained in the data structure.
    Contained
}

// Normalized = verified increasing + inclusive ends
fn get_normalized_range<T, U>(range: &U) -> Result<(T, T), RangeOperationError>
where
    T: PrimInt,
    U: RangeBounds<T>
{
    let start = match range.start_bound() {
        Bound::Included(val) => *val,
        Bound::Excluded(val) => match *val == T::max_value() {
            true => return Err(RangeOperationError::WouldOverflow),
            false => *val+T::one()
        }
        Bound::Unbounded => T::min_value()
    };
    let end = match range.end_bound() {
        Bound::Included(val) => *val,
        Bound::Excluded(val) => match *val == T::min_value() {
            true => return Err(RangeOperationError::WouldOverflow),
            false => *val-T::one()
        }
        Bound::Unbounded => T::max_value()
    };
    if start > end {
        Err(RangeOperationError::IsDecreasingOrEmpty)
    } else {
        Ok((start, end))
    }
}

#[inline]
fn get_result_wrapped_val<T>(res: Result<T,T>) -> T {
    match res {
        Ok(val) => val,
        Err(val) => val
    }
}

#[derive(Default, Clone, PartialEq, Eq, Hash)]
/*
 * Stores ranges in the following form:
 * range_storage [a_1, b_1, a_2, b_2, ...]
 * Ranges are [a_i, b_i] and include both ends
 * assert always b_i < a_{i+1}; ranges are disjoint
 * We also assume ranges are always as optimized as possible
 */
/// Struct representing a union of integer ranges.
pub struct IntRangeUnionFind<T>
where
    T: PrimInt
{
    range_storage: SortedVec<T>,
}

impl<T> IntRangeUnionFind<T>
where
    T: PrimInt
{
    /// Constructs a new [`IntRangeUnionFind`] object.
    pub fn new() -> Self {
        IntRangeUnionFind {
            range_storage: SortedVec::new(),
        }
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
    /// let mut range_obj = IntRangeUnionFind::new();
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
    /// let mut range_obj = IntRangeUnionFind::new();
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
        let (start, end) = match self.range_storage.get(2*range_id..=2*range_id+1) {
            None => return None,
            Some([a, b]) => (a, b),
            _ => unreachable!()
        };
        Some(start == end)
    }

    /// Returns how the given range overlaps with the stored ranges.
    /// See [`OverlapType`] for a description of the enum values.
    /// 
    /// # Example
    ///
    /// ```
    /// # use range_union_find::*;
    /// let mut range_obj = IntRangeUnionFind::new();
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
                        let stored_range_start = self.range_storage[2*range_start_id];
                        assert!(*end == stored_range_start);
                        Ok(OverlapType::Partial(T::one()))
                    },
                    ContainedType::Interior => {
                        let stored_range_start = self.range_storage[2*range_start_id];
                        let overlap = *end-stored_range_start+T::one();
                        Ok(OverlapType::Partial(overlap))
                    }
                    ContainedType::End => {
                        let stored_range_start = self.range_storage[2*range_start_id];
                        let stored_range_end = self.range_storage[2*range_end_id+1];
                        let overlap = *end-stored_range_start+T::one();
                        assert!(*end == stored_range_end);
                        Ok(OverlapType::Partial(overlap))
                    }
                };
            }
        } else if range_end_id == range_start_id+1
                && range_end_enum == ContainedType::Exterior {
            // Single range, given endpoint>a contained range endpoint
            let contained_range_start = self.range_storage[2*range_start_id];
            let contained_range_end = self.range_storage[2*range_start_id+1];
            match range_start_enum {
                ContainedType::Exterior | ContainedType::Start => {
                    let size = contained_range_end-contained_range_start+T::one();
                    if range_start_enum == ContainedType::Start {
                        assert!(*start == contained_range_start);
                    }
                    return Ok(OverlapType::Partial(size));
                },
                ContainedType::Interior => {
                    let size = contained_range_end-*start+T::one();
                    return Ok(OverlapType::Partial(T::from(size).unwrap()));
                },
                ContainedType::End => {
                    assert!(*start == contained_range_end);
                    return Ok(OverlapType::Partial(T::one()));
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
            let mut partial_count: T = T::zero();
            // Count overlap for range_start_id range
            partial_count = partial_count + match range_start_enum {
                ContainedType::Exterior | ContainedType::Start => {
                    let contained_range_start = self.range_storage[2*range_start_id];
                    let contained_range_end = self.range_storage[2*range_start_id+1];
                    if range_start_enum == ContainedType::Start {
                        assert!(*start == contained_range_start);
                    }
                    contained_range_end-contained_range_start+T::one()
                },
                ContainedType::Interior => {
                    let contained_range_end = self.range_storage[2*range_start_id+1];
                    contained_range_end-*start+T::one()
                }
                ContainedType::End => {
                    let contained_range_end = self.range_storage[2*range_start_id+1];
                    assert!(*start == contained_range_end);
                    T::one()
                }
            };
            // Count overlap for range_end_id range
            if range_end_enum!=ContainedType::Exterior {
                let contained_range_begin = self.range_storage[2*range_end_id];
                let size = *end-contained_range_begin+T::one();
                // Asserts
                match range_end_enum {
                    ContainedType::Exterior => unreachable!(),
                    ContainedType::Start => assert!(size == T::one()),
                    ContainedType::Interior => (), // No assert needed
                    ContainedType::End => {
                        let contained_range_end = self.range_storage[2*range_end_id+1];
                        assert!(*end == contained_range_end);
                    }
                }
                partial_count = partial_count + size;
            }
            // Count overlap for intermediate ranges
            for selected_id in range_start_id+1..range_end_id {
                let selected_range_begin = self.range_storage[2*selected_id];
                let selected_range_end = self.range_storage[2*selected_id+1];
                let size = selected_range_end-selected_range_begin+T::one();
                partial_count = partial_count + size;
            }
            return Ok(OverlapType::Partial(partial_count));
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
                    false => self.range_storage.binary_search(&(*start-T::one()))
                };
                let next_adj = match *end == T::max_value() {
                    true => Err(self.range_storage.len()), // end index, guaranteed not present
                    false => self.range_storage.binary_search(&(*end+T::one()))
                };
                if let (Ok(prev_val), Ok(next_val)) = (prev_adj, next_adj) {
                    // Element fills gap between ranges
                    assert_eq!(prev_val % 2, 1);
                    assert_eq!(next_val % 2, 0);
                    let index_remove = prev_val;
                    assert!(index_remove + 1 == next_val);
                    // Remove both endpoints
                    self.range_storage.drain(index_remove..=index_remove+1);
                } else if let Ok(prev_val) = prev_adj {
                    assert_eq!(prev_val % 2, 1);
                    // Extend start range by one, and insert other end
                    self.range_storage.remove_index(prev_val);
                    self.range_storage.insert(*end);
                } else if let Ok(next_val) = next_adj {
                    assert_eq!(next_val % 2, 0);
                    // Extend end range by one, and insert other end
                    self.range_storage.remove_index(next_val);
                    self.range_storage.insert(*start);
                } else {
                    assert_eq!(prev_adj.unwrap_err() % 2, 0);
                    assert_eq!(prev_adj.unwrap_err(), next_adj.unwrap_err());
                    // Insert entirely new range
                    self.range_storage.insert(*start);
                    self.range_storage.insert(*end);
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
                            && self.range_storage[index_rm-1] == *start-T::one() {
                        // End of prev range is adjacent to new one-merge ranges
                        // Removing gap is justified because overlap is partial
                        // start_range_id > 0 -> ranges do not involve 0
                        self.range_storage.drain(index_rm-1..=index_rm);
                    } else {
                        // Extend range with new starting position
                        let old_element = self.range_storage[index_rm];
                        let insert_pos = self.range_storage.insert(*start);
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
                            && self.range_storage[old_index_rm+1] == *end+T::one() {
                        // Start of next range is adjacent to inserted range
                        self.range_storage.drain(old_index_rm..=old_index_rm+1);
                    } else {
                        // Extend range with new ending position
                        let old_element = self.range_storage[old_index_rm];
                        let insert_pos = self.range_storage.insert(*end);
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
                let del_index_end = {
                    let (_, end_range_id) = self.has_element_enum(&end);
                    // Exterior -> subtract to the range before
                    // else -> skip past the range the endpoint lies in
                    // Computation result is the same regardless
                    // Saturating sub+equality check below to catch overflow
                    (2*end_range_id).saturating_sub(1)
                };
                // These should be true, except for overflow prevention
                //assert!(del_index_start % 2 == 0);
                //assert!(del_index_end % 2 == 1);
                if del_index_end > del_index_start {
                    // Guaranteed by above asserts
                    //assert!((del_index_end - del_index_start + 1) % 2 == 0);
                    self.range_storage.drain(del_index_start..=del_index_end);
                } else if del_index_end < del_index_start {
                    assert_eq!(del_index_start, del_index_end + 1);
                } else {
                    // "Correct" behavior: start=0 and end=-1
                    // This is also the only time this branch should ever be taken
                    assert_eq!(del_index_start, 0);
                    assert_eq!(del_index_end, 0);
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
                    let insert_pos = self.range_storage.insert(*start-T::one());
                    assert_eq!(insert_pos, 2*start_range_id+1);
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
                    let insert_pos = self.range_storage.insert(*end+T::one());
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
                            0 => old_endpoint+T::one(), // Was beginning
                            1 => old_endpoint-T::one(), // Was end
                            _ => unreachable!()
                        };
                        self.range_storage.insert(replacement_endpoint);
                    } else {
                        assert_eq!(prev_val+1, next_val);
                        // Range exactly matches an existing range
                        // Remove both endpoints
                        self.range_storage.remove_index(prev_val);
                        self.range_storage.remove_index(prev_val);
                    }
                } else if let (Ok(prev_val), Err(next_val)) = (prev_adj, next_adj) {
                    assert_eq!(prev_val+1, next_val);
                    assert_eq!(prev_val % 2, 0);
                    // Shrink start range by replacing start point
                    self.range_storage.remove_index(prev_val);
                    self.range_storage.insert(*end+T::one());
                } else if let (Err(prev_val), Ok(next_val)) = (prev_adj, next_adj) {
                    assert_eq!(prev_val, next_val);
                    assert_eq!(prev_val % 2, 1);
                    // Extend end range by one, and insert other end
                    self.range_storage.remove_index(next_val);
                    self.range_storage.insert(*start-T::one());
                } else {
                    // Subtract entirely new range
                    self.range_storage.insert(*start-T::one());
                    self.range_storage.insert(*end+T::one());
                }
            }
        }
        Ok(())
    }

    /// Creates a collection of [`RangeInclusive`] with element type `T` from a [`IntRangeUnionFind`] object.
    pub fn to_collection<U>(&self) -> U
    where
        U: FromIterator<RangeInclusive<T>>
    {
        assert!(self.range_storage.len() % 2 == 0);
        let size = self.range_storage.len() / 2;
        let mut self_iter = self.range_storage.to_vec().into_iter();
        let mut collect_vec = Vec::with_capacity(size);
        while let (Some(begin), Some(end)) = (self_iter.next(), self_iter.next()) {
            collect_vec.push(begin..=end);
        };
        collect_vec.into_iter().collect::<U>()
    }
    /// Converts a [`IntRangeUnionFind`] object into a collection of [`RangeInclusive`] with element type `T`.
    pub fn into_collection<U>(self) -> U
    where
        U: FromIterator<RangeInclusive<T>>
    {
        self.to_collection()
    }
}

impl<T: PrimInt> BitOr<&IntRangeUnionFind<T>> for &IntRangeUnionFind<T> {
    type Output = IntRangeUnionFind<T>;
    /// Computes the union of the two [`IntRangeUnionFind`] objects.
    fn bitor(self, rhs: &IntRangeUnionFind<T>) -> Self::Output {
        let mut dup_obj = self.clone();
        dup_obj.extend(rhs.to_collection::<Vec<RangeInclusive<T>>>());
        dup_obj
    }
}

impl<T: PrimInt> Sub<&IntRangeUnionFind<T>> for &IntRangeUnionFind<T> {
    type Output = IntRangeUnionFind<T>;
    /// Subtracts the rhs [`IntRangeUnionFind`] object from the lhs one.
    fn sub(self, rhs: &IntRangeUnionFind<T>) -> Self::Output {
        let mut dup_obj = self.clone();
        for range in rhs.to_collection::<Vec<RangeInclusive<T>>>() {
            dup_obj.remove_range(&range).unwrap();
        }
        dup_obj
    }
}

impl<T: PrimInt> Not for &IntRangeUnionFind<T> {
    type Output = IntRangeUnionFind<T>;
    fn not(self) -> Self::Output {
        let mut full_obj = IntRangeUnionFind::new();
        full_obj.insert_range(&(..)).unwrap();
        &full_obj - self
    }
}

impl<T: PrimInt> BitXor<&IntRangeUnionFind<T>> for &IntRangeUnionFind<T> {
    type Output = IntRangeUnionFind<T>;
    fn bitxor(self, rhs: &IntRangeUnionFind<T>) -> Self::Output {
        let first_diff_half = self - rhs;
        let second_diff_half = rhs - self;
        &first_diff_half | &second_diff_half
    }
}

impl<T: PrimInt> BitAnd<&IntRangeUnionFind<T>> for &IntRangeUnionFind<T> {
    type Output = IntRangeUnionFind<T>;
    /// Computes the union of the two [`IntRangeUnionFind`] objects.
    fn bitand(self, rhs: &IntRangeUnionFind<T>) -> Self::Output {
        let mut first_range_iter = self.to_collection::<Vec<_>>()
            .into_iter().peekable();
        let mut second_range_iter = rhs.to_collection::<Vec<_>>()
            .into_iter().peekable();
        // We rely on the iteration being in increasing order here
        let mut result_vec: Vec<RangeInclusive<T>> = Vec::new();
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
            let start_overlap = max(first_range.0, second_range.0);
            let end_overlap = min(first_range.1, second_range.1);
            let overlap_range = start_overlap..=end_overlap;
            if get_normalized_range(&overlap_range).is_ok() {
                result_vec.push(overlap_range);
            }

            // Advance the correct iterator
            if first_range.1 <= second_range.1 {
                first_range_iter.next();
            } else {
                second_range_iter.next();
            }
        }
        IntRangeUnionFind::from_iter(result_vec.into_iter())
    }
}

impl<T> fmt::Debug for IntRangeUnionFind<T>
where
    T: PrimInt + fmt::Debug,
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

impl<T, U> Extend<U> for IntRangeUnionFind<T>
where
    T: PrimInt,
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

impl<T, U> FromIterator<U> for IntRangeUnionFind<T>
where
    T: PrimInt,
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
        let mut new_range_obj = IntRangeUnionFind::new();
        new_range_obj.extend(iter);
        new_range_obj
    }
}

// TODO: other Vec types?
impl<T: PrimInt> From<IntRangeUnionFind<T>> for Vec<RangeInclusive<T>> {
    fn from(union_obj: IntRangeUnionFind<T>) -> Vec<RangeInclusive<T>> {
        union_obj.into_collection()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_max_size_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(0..=0xff)).unwrap();
        for i in 0..=0xff {
            assert!(range_obj.has_element(&i));
        }
        assert_eq!(range_obj.has_range(&(0..=0xff)).unwrap(),
            OverlapType::Contained);

        let mut unbounded_range_obj = IntRangeUnionFind::<u8>::new();
        unbounded_range_obj.insert_range(&(..)).unwrap();
        assert_eq!(range_obj, unbounded_range_obj);
    }
    #[test]
    fn reject_bad_ranges() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(5..=2)).unwrap_err();
        range_obj.insert_range_pair(&5, &2).unwrap_err();

        range_obj.has_range(&(5..=2)).unwrap_err();
        range_obj.has_range_pair(&5, &2).unwrap_err();

        range_obj.remove_range(&(5..=2)).unwrap_err();
        range_obj.remove_range_pair(&5, &2).unwrap_err();
    }
    #[test]
    fn make_from_iter() {
        let range_vec = vec![1..3, 5..7];
        let range_obj = IntRangeUnionFind::<u8>::from_iter(range_vec);

        let mut range_obj_ref = IntRangeUnionFind::<u8>::new();
        range_obj_ref.insert_range(&(1..3)).unwrap();
        range_obj_ref.insert_range(&(5..7)).unwrap();
        assert_eq!(range_obj, range_obj_ref);
    }
    #[test]
    fn turn_into_iter() {
        let range_vec = vec![1..=3, 5..=7, 10..=16];
        let range_obj = IntRangeUnionFind::<u8>::from_iter(range_vec.clone());
        let extract_vec: Vec<RangeInclusive<u8>> = range_obj.into_collection();
        assert_eq!(range_vec, extract_vec);
    }
    #[test]
    fn extend_bitor_equivalence() {
        let range_vec_full = vec![1..=3, 5..=7, 10..=16];
        let range_obj_full = IntRangeUnionFind::<u8>::from_iter(range_vec_full);

        let range_vec_second = vec![5..=7, 10..=16];
        let range_obj_second = IntRangeUnionFind::<u8>::from_iter(range_vec_second);

        let mut range_obj_first = IntRangeUnionFind::<u8>::default();
        range_obj_first.insert_range(&(1..=3)).unwrap();
        let mut range_obj_build = range_obj_first.clone();

        let range_obj_final = &range_obj_first | &range_obj_second;
        assert_eq!(range_obj_full, range_obj_final);

        range_obj_build = &range_obj_build | &range_obj_second;
        assert_eq!(range_obj_full, range_obj_build);
    }

    #[test]
    fn print_dual_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(0..=4)).unwrap();
        range_obj.insert_range(&(8..=16)).unwrap();
        let formatted = format!("{:?}",range_obj);
        assert_eq!(formatted, "[0..=4, 8..=16]");
    }

    #[test]
    fn single_range_has_element() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        for i in 0..=7 {
            assert!(!range_obj.has_element(&i));
        }
        for i in 8..=16 {
            assert!(range_obj.has_element(&i));
        }
        for i in 17..=20 {
            assert!(!range_obj.has_element(&i));
        }
    }
    #[test]
    fn dual_range_singleton_has_element() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(4..=4)).unwrap();
        for i in 0..=3 {
            assert!(!range_obj.has_element(&i));
        }
        assert!(range_obj.has_element(&4));
        for i in 5..=7 {
            assert!(!range_obj.has_element(&i));
        }
        for i in 8..=16 {
            assert!(range_obj.has_element(&i));
        }
        for i in 17..=20 {
            assert!(!range_obj.has_element(&i));
        }
    }
    #[test]
    fn dual_range_has_element() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(20..=40)).unwrap();
        for i in 0..=7 {
            assert!(!range_obj.has_element(&i));
        }
        for i in 8..=16 {
            assert!(range_obj.has_element(&i));
        }
        for i in 17..=19 {
            assert!(!range_obj.has_element(&i));
        }
        for i in 20..=40 {
            assert!(range_obj.has_element(&i));
        }
        for i in 41..=50 {
            assert!(!range_obj.has_element(&i));
        }
    }

    #[test]
    fn single_range_range_disjoint() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();

        assert_eq!(range_obj.has_range(&(0..=7)).unwrap(),OverlapType::Disjoint);
        assert_eq!(range_obj.has_range(&(17..=25)).unwrap(),OverlapType::Disjoint);
    }
    #[test]
    fn single_range_has_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();

        assert_eq!(range_obj.has_range(&(8..=16)).unwrap(),OverlapType::Contained);
        assert_eq!(range_obj.has_range(&(8..=11)).unwrap(),OverlapType::Contained);
        assert_eq!(range_obj.has_range(&(12..=14)).unwrap(),OverlapType::Contained);
        assert_eq!(range_obj.has_range(&(15..=16)).unwrap(),OverlapType::Contained);
    }
    #[test]
    fn single_range_range_partial() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();

        assert_eq!(range_obj.has_range(&(0..=8)).unwrap(),OverlapType::Partial(1));
        assert_eq!(range_obj.has_range(&(0..=9)).unwrap(),OverlapType::Partial(2));
        assert_eq!(range_obj.has_range(&(16..=20)).unwrap(),OverlapType::Partial(1));
        assert_eq!(range_obj.has_range(&(15..=20)).unwrap(),OverlapType::Partial(2));
        assert_eq!(range_obj.has_range(&(0..=24)).unwrap(),OverlapType::Partial(9));
        assert_eq!(range_obj.has_range(&(0..=16)).unwrap(),OverlapType::Partial(9));
        assert_eq!(range_obj.has_range(&(8..=24)).unwrap(),OverlapType::Partial(9));
    }
    #[test]
    fn multi_range_range_partial() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(4..=7)).unwrap();
        range_obj.insert_range(&(12..=15)).unwrap();
        range_obj.insert_range(&(20..=23)).unwrap();

        assert_eq!(range_obj.has_range(&(2..=10)).unwrap(),OverlapType::Partial(4));
        assert_eq!(range_obj.has_range(&(4..=10)).unwrap(),OverlapType::Partial(4));
        assert_eq!(range_obj.has_range(&(4..=12)).unwrap(),OverlapType::Partial(5));
        assert_eq!(range_obj.has_range(&(4..=14)).unwrap(),OverlapType::Partial(7));
        assert_eq!(range_obj.has_range(&(4..=15)).unwrap(),OverlapType::Partial(8));
        assert_eq!(range_obj.has_range(&(4..=20)).unwrap(),OverlapType::Partial(9));
        assert_eq!(range_obj.has_range(&(4..=22)).unwrap(),OverlapType::Partial(11));
        assert_eq!(range_obj.has_range(&(4..=23)).unwrap(),OverlapType::Partial(12));

        assert_eq!(range_obj.has_range(&(5..=23)).unwrap(),OverlapType::Partial(11));
        assert_eq!(range_obj.has_range(&(7..=23)).unwrap(),OverlapType::Partial(9));
    }
    #[test]
    fn dual_range_singleton_has_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(4..=4)).unwrap();
        assert!(range_obj.has_range(&(0..=3)).unwrap()==OverlapType::Disjoint);
        assert!(range_obj.has_range(&(4..=4)).unwrap()==OverlapType::Contained);
        assert!(range_obj.has_range(&(5..=7)).unwrap()==OverlapType::Disjoint);
        assert!(range_obj.has_range(&(8..=16)).unwrap()==OverlapType::Contained);
        assert!(range_obj.has_range(&(17..=20)).unwrap()==OverlapType::Disjoint);

        assert!(range_obj.has_range(&(0..8)).unwrap()==OverlapType::Partial(1));
    }

    #[test]
    fn insert_contained_range_over_single_range() {
        let mut range_obj_old = IntRangeUnionFind::<u32>::new();
        range_obj_old.insert_range(&(8..=16)).unwrap();

        let mut range_obj_new = range_obj_old.clone();
        range_obj_new.insert_range(&(12..=14)).unwrap();
        assert_eq!(range_obj_old, range_obj_new);

        let mut range_obj_new = range_obj_old.clone();
        range_obj_new.insert_range(&(8..=14)).unwrap();
        assert_eq!(range_obj_old, range_obj_new);

        let mut range_obj_new = range_obj_old.clone();
        range_obj_new.insert_range(&(12..=16)).unwrap();
        assert_eq!(range_obj_old, range_obj_new);
    }
    #[test]
    fn insert_partial_range_over_single_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(0..=12)).unwrap();

        let mut range_obj_single = IntRangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(0..=16)).unwrap();
        assert_eq!(range_obj, range_obj_single);

        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(8..=24)).unwrap();

        let mut range_obj_single = IntRangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(8..=24)).unwrap();
        assert_eq!(range_obj, range_obj_single);

        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(0..=24)).unwrap();

        let mut range_obj_single = IntRangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(0..=24)).unwrap();
        assert_eq!(range_obj, range_obj_single);
    }
    #[test]
    fn insert_partial_overarch_adj_range_over_single_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(12..=16)).unwrap();
        range_obj.insert_range(&(11..=15)).unwrap();

        let mut range_obj_final = IntRangeUnionFind::<u32>::new();
        range_obj_final.insert_range(&(11..=16)).unwrap();
        assert_eq!(range_obj, range_obj_final);
    }
    #[test]
    fn insert_partial_overarch_full_valuespan() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(0..=0)).unwrap();
        range_obj.insert_range(&(0xff..=0xff)).unwrap();

        range_obj.insert_range(&(0..=0xff)).unwrap();

        let mut range_obj_final = IntRangeUnionFind::<u8>::new();
        range_obj_final.insert_range(&(0..=0xff)).unwrap();
        assert_eq!(range_obj, range_obj_final);
    }
    #[test]
    fn insert_partial_overarch_adj_range_over_dual_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(12..=16)).unwrap();
        range_obj.insert_range(&(4..=8)).unwrap();
        let mut range_obj_2 = range_obj.clone();
        let mut range_obj_3 = range_obj.clone();

        range_obj.insert_range(&(0..=11)).unwrap();

        let mut range_obj_final = IntRangeUnionFind::<u32>::new();
        range_obj_final.insert_range(&(0..=16)).unwrap();
        assert_eq!(range_obj, range_obj_final);

        range_obj_2.insert_range(&(9..=20)).unwrap();
        let mut range_obj_final = IntRangeUnionFind::<u32>::new();
        range_obj_final.insert_range(&(4..=20)).unwrap();
        assert_eq!(range_obj_2, range_obj_final);

        range_obj_3.insert_range(&(4..=16)).unwrap();
        let mut range_obj_final = IntRangeUnionFind::<u32>::new();
        range_obj_final.insert_range(&(4..=16)).unwrap();
        assert_eq!(range_obj_3, range_obj_final);
    }
    #[test]
    fn insert_partial_overarch_all_range_over_multi_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(12..=16)).unwrap();
        range_obj.insert_range(&(4..=8)).unwrap();
        let mut range_obj_3 = range_obj.clone();

        range_obj.insert_range(&(0..=20)).unwrap();

        let mut range_obj_single = IntRangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(0..=20)).unwrap();
        assert_eq!(range_obj, range_obj_single);

        range_obj_3.insert_range(&(6..=14)).unwrap();
        let mut range_obj_single_3 = IntRangeUnionFind::<u32>::new();
        range_obj_single_3.insert_range(&(4..=16)).unwrap();
        assert_eq!(range_obj_3, range_obj_single_3);

        let mut range_obj_2 = IntRangeUnionFind::<u32>::new();
        range_obj_2.insert_range(&(0..=3)).unwrap();
        range_obj_2.insert_range(&(5..=7)).unwrap();
        range_obj_2.insert_range(&(9..=11)).unwrap();
        range_obj_2.insert_range(&(13..=15)).unwrap();
        range_obj_2.insert_range(&(17..=20)).unwrap();

        range_obj_2.insert_range(&(0..=20)).unwrap();
        assert_eq!(range_obj_2, range_obj_single);
    }
    #[test]
    fn insert_partial_gapfill_range_over_dual_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(12..=16)).unwrap();
        range_obj.insert_range(&(4..=8)).unwrap();

        range_obj.insert_range(&(0..=3)).unwrap();

        let mut range_obj_combined = IntRangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=8)).unwrap();
        range_obj_combined.insert_range(&(12..=16)).unwrap();
        assert_eq!(range_obj, range_obj_combined);

        range_obj.insert_range(&(17..=20)).unwrap();

        let mut range_obj_combined = IntRangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=8)).unwrap();
        range_obj_combined.insert_range(&(12..=20)).unwrap();
        assert_eq!(range_obj, range_obj_combined);

        range_obj.insert_range(&(9..=11)).unwrap();

        let mut range_obj_combined = IntRangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=20)).unwrap();
        assert_eq!(range_obj, range_obj_combined);
    }
    #[test]
    fn insert_single_element_adj_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(11..20)).unwrap();
        range_obj.insert_range(&(10..=10)).unwrap();
        range_obj.insert_range(&(20..=20)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u32>::new();
        expected_obj.insert_range(&(10..=20)).unwrap();

        assert_eq!(expected_obj, range_obj);
    }
    #[test]
    fn insert_range_over_endpoint_singletons() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(10..=10)).unwrap();
        range_obj.insert_range(&(20..=20)).unwrap();
        let mut range_obj_2 = range_obj.clone();
        range_obj.insert_range(&(11..=19)).unwrap();
        range_obj_2.insert_range(&(10..=20)).unwrap();
        assert_eq!(range_obj, range_obj_2);

        let mut expected_obj = IntRangeUnionFind::<u32>::new();
        expected_obj.insert_range(&(10..=20)).unwrap();

        assert_eq!(expected_obj, range_obj);
    }
    #[test]
    fn insert_gapfill_element_over_dual_range() {
        let mut range_obj = IntRangeUnionFind::<u32>::new();
        range_obj.insert_range(&(10..=16)).unwrap();
        range_obj.insert_range(&(0..=8)).unwrap();

        range_obj.insert_range(&(9..=9)).unwrap();

        let mut range_obj_combined = IntRangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=16)).unwrap();
        assert_eq!(range_obj, range_obj_combined);
    }

    #[test]
    fn remove_disjoint_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..20)).unwrap();
        let expected_obj = range_obj.clone();
        range_obj.remove_range(&(0..10)).unwrap();
        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_entire_single_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..=12)).unwrap();
        range_obj.remove_range(&(4..=12)).unwrap();

        let expected_obj = IntRangeUnionFind::<u8>::new();
        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_partial_single_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..=12)).unwrap();
        range_obj.remove_range(&(4..=7)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(8..=12)).unwrap();
        assert_eq!(range_obj, expected_obj);

        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..=12)).unwrap();
        range_obj.remove_range(&(10..=12)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(4..=9)).unwrap();
        assert_eq!(range_obj, expected_obj);

        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..=12)).unwrap();
        range_obj.remove_range(&(5..=11)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(4..=4)).unwrap();
        expected_obj.insert_range(&(12..=12)).unwrap();
        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_endpoint_overlap_single_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..=12)).unwrap();
        range_obj.remove_range(&(4..=4)).unwrap();
        range_obj.remove_range(&(12..=12)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(5..=11)).unwrap();
        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_overlap_single_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..=12)).unwrap();
        let mut range_obj_2 = range_obj.clone();
        range_obj.remove_range(&(0..=8)).unwrap();
        range_obj_2.remove_range(&(10..=15)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(9..=12)).unwrap();
        assert_eq!(range_obj, expected_obj);

        let mut expected_obj_2 = IntRangeUnionFind::<u8>::new();
        expected_obj_2.insert_range(&(4..=9)).unwrap();
        assert_eq!(range_obj_2, expected_obj_2);
    }
    #[test]
    fn remove_overarch_partial_match() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(4..8)).unwrap();
        range_obj.remove_range(&(0..10)).unwrap();

        let expected_obj = IntRangeUnionFind::<u8>::new();
        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_partial_multiple_ranges() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();
        range_obj.insert_range(&(30..=40)).unwrap();
        range_obj.insert_range(&(50..=60)).unwrap();
        range_obj.remove_range(&(15..=55)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(10..=14)).unwrap();
        expected_obj.insert_range(&(56..=60)).unwrap();

        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_partial_multiple_ranges_rangeswallow() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();
        range_obj.insert_range(&(30..=40)).unwrap();
        range_obj.insert_range(&(50..=60)).unwrap();
        range_obj.insert_range(&(70..=80)).unwrap();

        range_obj.remove_range(&(30..=60)).unwrap();

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(10..=20)).unwrap();
        expected_obj.insert_range(&(70..=80)).unwrap();

        assert_eq!(range_obj, expected_obj);
    }
    #[test]
    fn remove_sub_equivalence() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();
        range_obj.insert_range(&(30..=40)).unwrap();
        range_obj.insert_range(&(50..=60)).unwrap();
        range_obj.insert_range(&(70..=80)).unwrap();

        let full_obj = range_obj.clone();
        range_obj.remove_range(&(30..=60)).unwrap();
        range_obj.remove_range(&(11..16)).unwrap();

        let mut range_rhs = IntRangeUnionFind::<u8>::new();
        range_rhs.insert_range(&(30..=60)).unwrap();
        range_rhs.insert_range(&(11..16)).unwrap();

        let sub_obj = &full_obj - &range_rhs;
        assert_eq!(range_obj, sub_obj);
    }
    #[test]
    fn remove_over_valuespan_singletons() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(2..=0xfd)).unwrap();
        range_obj.insert_range(&(0..=0)).unwrap();
        range_obj.insert_range(&(0xff..=0xff)).unwrap();

        let mut range_obj_rm_upper = range_obj.clone();
        let mut range_obj_rm_lower = range_obj.clone();

        let mut lower_half_obj = IntRangeUnionFind::<u8>::new();
        lower_half_obj.insert_range(&(2..=0x7f)).unwrap();
        lower_half_obj.insert_range(&(0..=0)).unwrap();
        range_obj_rm_upper.remove_range(&(0x80..=0xff)).unwrap();
        assert_eq!(lower_half_obj, range_obj_rm_upper);

        let mut upper_half_obj = IntRangeUnionFind::<u8>::new();
        upper_half_obj.insert_range(&(0x80..=0xfd)).unwrap();
        upper_half_obj.insert_range(&(0xff..=0xff)).unwrap();
        range_obj_rm_lower.remove_range(&(0..0x80)).unwrap();
        assert_eq!(upper_half_obj, range_obj_rm_lower);
    }

    #[test]
    fn bitand_same_obj() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();
        range_obj.insert_range(&(30..=40)).unwrap();

        let anded_obj = &range_obj & &range_obj;
        assert_eq!(range_obj, anded_obj);
    }
    #[test]
    fn bitand_when_contained() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=50)).unwrap();

        let mut rhs_obj = IntRangeUnionFind::<u8>::new();
        rhs_obj.insert_range(&(20..=30)).unwrap();

        let anded_obj_1 = &range_obj & &rhs_obj;
        let anded_obj_2 = &rhs_obj & &range_obj;
        assert_eq!(anded_obj_1, anded_obj_2);

        assert_eq!(anded_obj_1, rhs_obj);
    }
    #[test]
    fn bitand_when_disjoint() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=15)).unwrap();

        let mut rhs_obj = IntRangeUnionFind::<u8>::new();
        rhs_obj.insert_range(&(20..=30)).unwrap();

        let anded_obj_1 = &range_obj & &rhs_obj;
        let anded_obj_2 = &rhs_obj & &range_obj;
        assert_eq!(anded_obj_1, anded_obj_2);

        let expected_obj = IntRangeUnionFind::<u8>::new();
        assert_eq!(anded_obj_1, expected_obj);
    }
    #[test]
    fn bitand_overarch_subselect() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();
        range_obj.insert_range(&(30..=40)).unwrap();
        range_obj.insert_range(&(50..=60)).unwrap();
        range_obj.insert_range(&(70..=80)).unwrap();

        let mut rhs_obj = IntRangeUnionFind::<u8>::new();
        rhs_obj.insert_range(&(0..35)).unwrap();

        let anded_obj_1 = &range_obj & &rhs_obj;
        let anded_obj_2 = &rhs_obj & &range_obj;
        assert_eq!(anded_obj_1, anded_obj_2);

        let mut expected_obj = IntRangeUnionFind::<u8>::new();
        expected_obj.insert_range(&(10..=20)).unwrap();
        expected_obj.insert_range(&(30..=34)).unwrap();
        assert_eq!(anded_obj_1, expected_obj);
    }

    #[test]
    fn inverse_range() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();

        let mut expected_inverted_range = IntRangeUnionFind::<u8>::new();
        expected_inverted_range.insert_range(&(..=9)).unwrap();
        expected_inverted_range.insert_range(&(21..)).unwrap();

        assert_eq!(!&range_obj, expected_inverted_range);
    }

    #[test]
    fn xor_partial() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();

        let mut rhs_obj = IntRangeUnionFind::<u8>::new();
        rhs_obj.insert_range(&(15..=25)).unwrap();

        assert_eq!(&range_obj ^ &rhs_obj, &rhs_obj ^ &range_obj);

        let mut expected_xor_obj = IntRangeUnionFind::<u8>::new();
        expected_xor_obj.insert_range(&(10..=14)).unwrap();
        expected_xor_obj.insert_range(&(21..=25)).unwrap();

        assert_eq!(&range_obj ^ &rhs_obj, expected_xor_obj);
    }

    #[test]
    fn range_set_boolean_ops_demorgan() {
        let mut range_obj = IntRangeUnionFind::<u8>::new();
        range_obj.insert_range(&(10..=20)).unwrap();
        range_obj.insert_range(&(30..=40)).unwrap();
        range_obj.insert_range(&(50..=60)).unwrap();
        range_obj.insert_range(&(70..=80)).unwrap();

        let mut range_obj_2 = IntRangeUnionFind::<u8>::new();
        range_obj_2.insert_range(&(30..=60)).unwrap();
        range_obj_2.insert_range(&(11..16)).unwrap();

        let range_obj_or_given = &range_obj | &range_obj_2;
        let range_obj_and_given = &range_obj & &range_obj_2;
        let range_obj_xor_given = &range_obj ^ &range_obj_2;

        assert_eq!(range_obj_xor_given, &range_obj_or_given - &range_obj_and_given);

        let range_obj_or_then_not = !&range_obj_or_given;
        let range_obj_and_then_not = !&range_obj_and_given;

        let range_obj_not_then_or = &!&range_obj | &!&range_obj_2;
        let range_obj_not_then_and = &!&range_obj & &!&range_obj_2;

        assert_eq!(range_obj_not_then_and, range_obj_or_then_not);
        assert_eq!(range_obj_not_then_or, range_obj_and_then_not);
    }
}
