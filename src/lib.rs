#![forbid(unsafe_code)]

//! Provides a data structure backed by a vector for unioning ranges of integers.
//! We intelligently merge inserted ranges to minimize required storage.
//! 
//! Example usage:
//! ```
//! # use range_union_find::*;
//! let mut range_holder = RangeUnionFind::<u32>::new();
//! range_holder.insert_range(&(4..=8))?;
//! range_holder.insert_range(&(6..=10))?;
//! assert_eq!(range_holder.range_contained(&(2..=12)).unwrap(), OverlapType::Partial(7));
//! assert_eq!(range_holder.range_contained(&(5..=9)).unwrap(), OverlapType::Contained);
//! # Ok::<(), RangeOperationError>(())
//! ```
//! 
//! All the functionality is in the [RangeUnionFind] struct.
use std::ops::{Bound, RangeBounds};
use num_traits::PrimInt;
use sorted_vec::SortedVec;

use std::fmt;

/// Enum describing how a range may be invalid.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeOperationError {
    /// Range has an unbounded end.
    HasUnbounded,
    /// Range operation caused an overflow.
    WouldOverflow,
    /// Range is decreasing or empty.
    IsDecreasingOrEmpty
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ContainedType {
    Start,
    Interior,
    End,
    Exterior
}
/// Enum describing how a range may overlap with another range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OverlapType<T> {
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
        Bound::Unbounded => return Err(RangeOperationError::HasUnbounded)
    };
    let end = match range.end_bound() {
        Bound::Included(val) => *val,
        Bound::Excluded(val) => match *val == T::min_value() {
            true => return Err(RangeOperationError::WouldOverflow),
            false => *val-T::one()
        }
        Bound::Unbounded => return Err(RangeOperationError::HasUnbounded)
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

#[derive(Default, Clone, Debug, PartialEq, Eq)]
/*
 * Stores ranges in the following form:
 * range_storage [a_1, b_1, a_2, b_2, ...]
 * Ranges are [a_i, b_i] and include both ends
 * assert always b_i < a_{i+1}; ranges are disjoint
 * We also assume ranges are always as optimized as possible
 */
/// Struct representing a union of ranges.
pub struct RangeUnionFind<T>
where
    T: PrimInt
{
    range_storage: SortedVec<T>,
}

impl<T> RangeUnionFind<T>
where
    T: PrimInt
{
    /// Constructs a new [RangeUnionFind] object.
    pub fn new() -> Self {
        RangeUnionFind {
            range_storage: SortedVec::new(),
        }
    }
    /*
     * Tuple is enum, range_id (a count of which range the element is in)
     * Exterior,i means the exterior region before the i'th range
     * Range id => indexes into vector are id*2, id*2+1
     */
    fn element_contained_enum(&self, element: &T) -> (ContainedType, usize) {
        assert!(self.range_storage.len() % 2 == 0);
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
        // Using round-down division here
        (enum_val, get_result_wrapped_val(would_insert_loc)/2)
    }
    /// Returns whether `element` is contained in the stored ranges.
    pub fn element_contained(&self, element: &T) -> bool {
        match self.element_contained_enum(element) {
            (ContainedType::Exterior, _) => false,
            _ => true
        }
    }
    /// Returns how the given range overlaps with the stored ranges.
    /// * `Disjoint`: No elements overlap
    /// * `Partial(T)`: Some(count) elements overlap
    /// * `Contained`: Range is entirely contained inside the struct
    /// 
    /// Returns [RangeOperationError] if given range is invalid.
    pub fn range_contained<U: RangeBounds<T>>(&self, range: &U)
            -> Result<OverlapType<T>,RangeOperationError> {
        let (input_start, input_end) = match get_normalized_range(range) {
            Ok((val_start,val_end)) => (val_start,val_end),
            Err(err) => return Err(err)
        };
        self.range_contained_pair(&input_start, &input_end)
    }
    /// Functions like [Self::range_contained] given input `start..=end`.
    pub fn range_contained_pair(&self, start: &T, end: &T) -> Result<OverlapType<T>, RangeOperationError> {
        if start > end {
            return Err(RangeOperationError::IsDecreasingOrEmpty);
        }
        let vec_count = self.range_storage.len();
        let (range_start_enum, range_start_id) = self.element_contained_enum(&start);
        let (range_end_enum, range_end_id) = self.element_contained_enum(&end);
        //println!("{:?}{} {:?}{}", range_start_enum, range_start_id, range_end_enum, range_end_id);
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
    /// Inserts the range into the set of ranges. Returns [RangeOperationError] if the given range is invalid.
    pub fn insert_range<U: RangeBounds<T>>(&mut self, range: &U)
            -> Result<(), RangeOperationError> {
        let (start, end) = match get_normalized_range(range) {
            Ok((val_start,val_end)) => (val_start,val_end),
            Err(err) => return Err(err)
        };
        match self.range_contained_pair(&start, &end).unwrap() {
            OverlapType::Disjoint => {
                //let prev_adj = self.range_storage.binary_search(&(start-T::one()));
                let prev_adj = match start == T::min_value() {
                    true => Err(0), // contained value is dontcare
                    false => self.range_storage.binary_search(&(start-T::one()))
                };
                //let next_adj = self.range_storage.binary_search(&(end+T::one()));
                let next_adj = match end == T::max_value() {
                    true => Err(0), // contained value is dontcare
                    false => self.range_storage.binary_search(&(end+T::one()))
                };
                if prev_adj.is_ok() && next_adj.is_ok() {
                    // Element fills gap between ranges
                    let index_remove = prev_adj.unwrap();
                    assert!(index_remove + 1 == next_adj.unwrap());
                    // Remove both endpoints
                    self.range_storage.remove_index(index_remove);
                    self.range_storage.remove_index(index_remove);
                } else if prev_adj.is_ok() {
                    // Extend start range by one, and insert other end
                    self.range_storage.remove_index(prev_adj.unwrap());
                    self.range_storage.insert(end);
                } else if next_adj.is_ok() {
                    // Extend end range by one, and insert other end
                    self.range_storage.remove_index(next_adj.unwrap());
                    self.range_storage.insert(start);
                } else {
                    // Insert entirely new range
                    self.range_storage.insert(start);
                    self.range_storage.insert(end);
                }
            }
            OverlapType::Partial(_) => {
                // TODO: check adjacency
                let (start_enum, start_range_id) = self.element_contained_enum(&start);
                let (end_enum, end_range_id) = self.element_contained_enum(&end);
                if start_enum == ContainedType::Exterior {
                    let old_element = self.range_storage[2*start_range_id];
                    let insert_pos = self.range_storage.insert(start);
                    assert!(insert_pos == 2*start_range_id);
                    let removed_element = self.range_storage.remove_index(2*start_range_id+1);
                    assert!(old_element == removed_element);
                } // else we do not need to adjust the start point
                if end_enum == ContainedType::Exterior {
                    let old_element = self.range_storage[2*(end_range_id-1)+1];
                    let insert_pos = self.range_storage.insert(end);
                    assert!(insert_pos == 2*(end_range_id-1)+1+1);
                    let removed_element = self.range_storage.remove_index(2*(end_range_id-1)+1);
                    assert!(old_element == removed_element);
                } // else we do not need to adjust the end point

                // Delete intermediate ranges
                if end_range_id != start_range_id {
                    let middle_range_count = (end_range_id-start_range_id+1)-2;
                    for _ in 0..2*middle_range_count {
                        self.range_storage.remove_index(2*start_range_id+1);
                    }
                }
            }
            OverlapType::Contained => {
                // Do nothing
            }
        }
        return Ok(());
    }
}

impl<T> fmt::Display for RangeUnionFind<T>
where
    T: PrimInt + fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        assert!(self.range_storage.len()%2 == 0);
        write!(f, "[")?;
        let mut pairs: Vec<String> = Vec::with_capacity(
            self.range_storage.len()/2);
        let mut range_pairs = self.range_storage.chunks_exact(2);
        loop {
            let range = match range_pairs.next() {
                None => {
                    assert!(range_pairs.remainder().len()==0);
                    break;
                },
                Some(val) => val
            };
            pairs.push(format!("[{}, {}]", range[0], range[1]));
        }
        write!(f, "{}", pairs.join(", "))?;
        return write!(f, "]");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_max_size_range() {
        let mut range_obj = RangeUnionFind::<u8>::new();
        range_obj.insert_range(&(0..=0xff)).unwrap();
        for i in 0..=0xff {
            assert!(range_obj.element_contained(&i));
        }
    }
    #[test]
    fn insert_bad_range() {
        let mut range_obj = RangeUnionFind::<u8>::new();
        range_obj.insert_range(&(5..=2)).unwrap_err();
    }
    #[test]
    fn print_dual_range() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(0..=4)).unwrap();
        range_obj.insert_range(&(8..=16)).unwrap();
        let formatted = format!("{}",range_obj);
        assert_eq!(formatted, "[[0, 4], [8, 16]]");
    }
    #[test]
    fn single_range_element_contained() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        for i in 0..=7 {
            assert!(!range_obj.element_contained(&i));
        }
        for i in 8..=16 {
            assert!(range_obj.element_contained(&i));
        }
        for i in 17..=20 {
            assert!(!range_obj.element_contained(&i));
        }
    }
    #[test]
    fn dual_range_singleton_element_contained() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(4..=4)).unwrap();
        for i in 0..=3 {
            assert!(!range_obj.element_contained(&i));
        }
        assert!(range_obj.element_contained(&4));
        for i in 5..=7 {
            assert!(!range_obj.element_contained(&i));
        }
        for i in 8..=16 {
            assert!(range_obj.element_contained(&i));
        }
        for i in 17..=20 {
            assert!(!range_obj.element_contained(&i));
        }
    }
    #[test]
    fn dual_range_element_contained() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(20..=40)).unwrap();
        for i in 0..=7 {
            assert!(!range_obj.element_contained(&i));
        }
        for i in 8..=16 {
            assert!(range_obj.element_contained(&i));
        }
        for i in 17..=19 {
            assert!(!range_obj.element_contained(&i));
        }
        for i in 20..=40 {
            assert!(range_obj.element_contained(&i));
        }
        for i in 41..=50 {
            assert!(!range_obj.element_contained(&i));
        }
    }

    #[test]
    fn single_range_range_disjoint() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();

        assert_eq!(range_obj.range_contained(&(0..=7)).unwrap(),OverlapType::Disjoint);
        assert_eq!(range_obj.range_contained(&(17..=25)).unwrap(),OverlapType::Disjoint);
    }
    #[test]
    fn single_range_range_contained() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();

        assert_eq!(range_obj.range_contained(&(8..=16)).unwrap(),OverlapType::Contained);
        assert_eq!(range_obj.range_contained(&(8..=11)).unwrap(),OverlapType::Contained);
        assert_eq!(range_obj.range_contained(&(12..=14)).unwrap(),OverlapType::Contained);
        assert_eq!(range_obj.range_contained(&(15..=16)).unwrap(),OverlapType::Contained);
    }
    #[test]
    fn single_range_range_partial() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();

        assert_eq!(range_obj.range_contained(&(0..=8)).unwrap(),OverlapType::Partial(1));
        assert_eq!(range_obj.range_contained(&(0..=9)).unwrap(),OverlapType::Partial(2));
        assert_eq!(range_obj.range_contained(&(16..=20)).unwrap(),OverlapType::Partial(1));
        assert_eq!(range_obj.range_contained(&(15..=20)).unwrap(),OverlapType::Partial(2));
        assert_eq!(range_obj.range_contained(&(0..=24)).unwrap(),OverlapType::Partial(9));
        assert_eq!(range_obj.range_contained(&(0..=16)).unwrap(),OverlapType::Partial(9));
        assert_eq!(range_obj.range_contained(&(8..=24)).unwrap(),OverlapType::Partial(9));
    }
    #[test]
    fn multi_range_range_partial() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(4..=7)).unwrap();
        range_obj.insert_range(&(12..=15)).unwrap();
        range_obj.insert_range(&(20..=23)).unwrap();

        assert_eq!(range_obj.range_contained(&(2..=10)).unwrap(),OverlapType::Partial(4));
        assert_eq!(range_obj.range_contained(&(4..=10)).unwrap(),OverlapType::Partial(4));
        assert_eq!(range_obj.range_contained(&(4..=12)).unwrap(),OverlapType::Partial(5));
        assert_eq!(range_obj.range_contained(&(4..=14)).unwrap(),OverlapType::Partial(7));
        assert_eq!(range_obj.range_contained(&(4..=15)).unwrap(),OverlapType::Partial(8));
        assert_eq!(range_obj.range_contained(&(4..=20)).unwrap(),OverlapType::Partial(9));
        assert_eq!(range_obj.range_contained(&(4..=22)).unwrap(),OverlapType::Partial(11));
        assert_eq!(range_obj.range_contained(&(4..=23)).unwrap(),OverlapType::Partial(12));

        assert_eq!(range_obj.range_contained(&(5..=23)).unwrap(),OverlapType::Partial(11));
        assert_eq!(range_obj.range_contained(&(7..=23)).unwrap(),OverlapType::Partial(9));
    }
    #[test]
    fn dual_range_singleton_range_contained() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(4..=4)).unwrap();
        assert!(range_obj.range_contained(&(0..=3)).unwrap()==OverlapType::Disjoint);
        assert!(range_obj.range_contained(&(4..=4)).unwrap()==OverlapType::Contained);
        assert!(range_obj.range_contained(&(5..=7)).unwrap()==OverlapType::Disjoint);
        assert!(range_obj.range_contained(&(8..=16)).unwrap()==OverlapType::Contained);
        assert!(range_obj.range_contained(&(17..=20)).unwrap()==OverlapType::Disjoint);
    }
    #[test]
    fn insert_contained_range_over_single_range() {
        let mut range_obj_old = RangeUnionFind::<u32>::new();
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
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(0..=12)).unwrap();

        let mut range_obj_single = RangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(0..=16)).unwrap();
        assert_eq!(range_obj, range_obj_single);

        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(8..=16)).unwrap();
        range_obj.insert_range(&(8..=24)).unwrap();

        let mut range_obj_single = RangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(8..=24)).unwrap();
        assert_eq!(range_obj, range_obj_single);
    }
    #[test]
    fn insert_partial_overarch_range_over_dual_range() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(12..=16)).unwrap();
        range_obj.insert_range(&(4..=8)).unwrap();

        range_obj.insert_range(&(0..=20)).unwrap();

        let mut range_obj_single = RangeUnionFind::<u32>::new();
        range_obj_single.insert_range(&(0..=20)).unwrap();
        assert_eq!(range_obj, range_obj_single);
    }
    #[test]
    fn insert_partial_gapfill_range_over_dual_range() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(12..=16)).unwrap();
        range_obj.insert_range(&(4..=8)).unwrap();

        range_obj.insert_range(&(0..=3)).unwrap();

        let mut range_obj_combined = RangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=8)).unwrap();
        range_obj_combined.insert_range(&(12..=16)).unwrap();
        assert_eq!(range_obj, range_obj_combined);

        range_obj.insert_range(&(17..=20)).unwrap();

        let mut range_obj_combined = RangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=8)).unwrap();
        range_obj_combined.insert_range(&(12..=20)).unwrap();
        assert_eq!(range_obj, range_obj_combined);

        range_obj.insert_range(&(9..=11)).unwrap();

        let mut range_obj_combined = RangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=20)).unwrap();
        assert_eq!(range_obj, range_obj_combined);
    }

    #[test]
    fn insert_gapfill_element_over_dual_range() {
        let mut range_obj = RangeUnionFind::<u32>::new();
        range_obj.insert_range(&(10..=16)).unwrap();
        range_obj.insert_range(&(0..=8)).unwrap();

        range_obj.insert_range(&(9..=9)).unwrap();

        let mut range_obj_combined = RangeUnionFind::<u32>::new();
        range_obj_combined.insert_range(&(0..=16)).unwrap();
        assert_eq!(range_obj, range_obj_combined);
    }
}
