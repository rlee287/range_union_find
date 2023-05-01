use num_traits::PrimInt;

/// A trait to represent the possible number types over which intervals can be constructed.
/// # Safety
/// This trait is not `unsafe`, so do not use custom implementers of this trait in unsafe contexts (e.g. a custom `NumInRange` as indexes to track initialized buckets in a custom HashMap) without auditing the exact implementation.
pub trait NumInRange: PartialOrd + Ord + PartialEq + Eq {
    /// Return the minimum possible value the number can take.
    fn min() -> Self;
    /// Return the maximum possible value the number can take.
    fn max() -> Self;

    /// Return the smallest possible value larger than the input value.
    fn step_incr(&self) -> Self;
    /// Return the largest possible value smaller than the input value.
    fn step_decr(&self) -> Self;
}
impl<T: PrimInt+core::fmt::Debug> NumInRange for T {
    fn min() -> Self {
        T::min_value()
    }
    fn max() -> Self{
        T::max_value()
    }

    fn step_incr(&self) -> Self {
        let retval = self.saturating_add(Self::one());
        if self == &<Self as NumInRange>::max() {
            debug_assert_eq!(self, &retval);
        }
        retval
    }
    fn step_decr(&self) -> Self {
        let retval = self.saturating_sub(Self::one());
        if self == &<Self as NumInRange>::min() {
            debug_assert_eq!(self, &retval);
        }
        retval
    }
}
