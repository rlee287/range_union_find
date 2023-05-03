use num_traits::{PrimInt, Num};

use core::ops::{Add, Bound, RangeBounds};
use core::borrow::Borrow;

use core::fmt;

#[cfg(feature = "std")]
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
#[cfg(feature = "std")]
impl Error for RangeOperationError {}

// Normalized = verified increasing + inclusive ends
// Do not use range_size in here to prevent recursion
pub(crate) fn get_normalized_range<N, B, R>(range: &R) -> Result<(N, N), RangeOperationError>
where
    N: NumInRange,
    B: Borrow<N>,
    R: RangeBounds<B>
{
    let start: N = match range.start_bound() {
        Bound::Included(val) => val.borrow().clone(),
        Bound::Excluded(val) => {
            if N::MAX_INCR_IS_OVERFLOW && (val.borrow() == &N::max_value()) {
                return Err(RangeOperationError::WouldOverflow);
            }
            val.borrow().step_incr()
        }
        Bound::Unbounded => N::min_value()
    };
    let end: N = match range.end_bound() {
        Bound::Included(val) => val.borrow().clone(),
        Bound::Excluded(val) => {
            if N::MIN_DECR_IS_UNDERFLOW && val.borrow() == &N::min_value() {
                return Err(RangeOperationError::WouldOverflow);
            }
            val.borrow().step_decr()
        }
        Bound::Unbounded => N::max_value()
    };
    if start > end {
        Err(RangeOperationError::IsDecreasingOrEmpty)
    } else {
        Ok((start, end))
    }
}

/// Trait representing number types which can be incrementally stepped.
/// # Safety
/// This trait is not `unsafe`, so do not use custom implementers of this trait in unsafe contexts (e.g. a custom `NumInRange` as indexes to track initialized buckets in a custom HashMap) without auditing the exact implementation.
pub trait Steppable: Clone + PartialOrd + Ord {
    /// Return the smallest possible value larger than the input value. Should saturate at the maximum possible value.
    fn step_incr(&self) -> Self;
    /// Return the largest possible value smaller than the input value. Should saturate at the minimum possible value.
    fn step_decr(&self) -> Self;

    /// Return the size of the range.
    fn range_size<N: Borrow<Self>, R: RangeBounds<N>>(range: R) -> Result<Self, RangeOperationError>;
    fn range_tuple_size<N: Borrow<Self>>(start: N, end: N) -> Result<Self, RangeOperationError> {
        Self::range_size((Bound::Included(start), Bound::Included(end)))
    }
}

/// Trait representing number types over which intervals can be constructed.
/// # Safety
/// This trait is not `unsafe`, so do not use custom implementers of this trait in unsafe contexts (e.g. a custom `NumInRange` as indexes to track initialized buckets in a custom HashMap) without auditing the exact implementation.
pub trait NumInRange: Steppable + Add<Output = Self> + Clone + PartialOrd + Ord + PartialEq + Eq {
    /// Return the minimum possible value the number can take.
    fn min_value() -> Self;
    /// Return the maximum possible value the number can take.
    fn max_value() -> Self;
    /// Whether caling [`Steppable::step_decr`] on the min value would underflow the type.
    const MIN_DECR_IS_UNDERFLOW: bool;
    /// Whether caling [`Steppable::step_incr`] on the max value would overflow the type.
    const MAX_INCR_IS_OVERFLOW: bool;
}

impl<T: PrimInt> NumInRange for T {
    #[inline(always)]
    fn min_value() -> Self {
        T::min_value()
    }
    #[inline(always)]
    fn max_value() -> Self{
        T::max_value()
    }
    const MIN_DECR_IS_UNDERFLOW: bool = true;
    const MAX_INCR_IS_OVERFLOW: bool = true;
}
impl<T: PrimInt> Steppable for T {
    #[inline(always)]
    fn step_incr(&self) -> Self {
        let retval = self.saturating_add(Self::one());
        if self == &Self::max_value() {
            debug_assert!(self == &retval);
        }
        retval
    }
    #[inline(always)]
    fn step_decr(&self) -> Self {
        let retval = self.saturating_sub(Self::one());
        if self == &Self::min_value() {
            debug_assert!(self == &retval);
        }
        retval
    }

    fn range_size<B: Borrow<Self>, R: RangeBounds<B>>(range: R) -> Result<Self, RangeOperationError> {
        let (start_inclusive, end_inclusive) = get_normalized_range(&range)?;
        let size = (end_inclusive-start_inclusive).step_incr();
        assert!(size > T::zero());
        Ok(size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_i8_full() {
        for i in i8::MIN..=i8::MAX {
            let i_minus_minus = i.step_decr();
            let i_plus_plus = i.step_incr();
            if i != i8::MIN {
                assert_ne!(i, i_minus_minus);
                assert_eq!(i-1, i_minus_minus);
            } else {
                assert_eq!(i, i_minus_minus);
            }
            if i != i8::MAX {
                assert_ne!(i, i_plus_plus);
                assert_eq!(i+1, i_plus_plus);
            } else {
                assert_eq!(i, i_plus_plus);
            }
        }
    }
}
