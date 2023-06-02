use crate::num_trait::{get_normalized_range, Steppable, NumInRange, RangeOperationError};

use core::fmt;

use core::borrow::Borrow;
use core::convert::TryFrom;
use core::ops::{Add, Deref, RangeBounds};
use core::hash::{Hash, Hasher};

use num_traits::{Float, Zero};

#[cfg(feature = "include_serde")]
use serde::{Serialize, Deserialize};

#[cfg(any(feature = "std", feature = "libm"))]
#[derive(Debug, Clone, Copy, Hash)]
/// Error returned when the float is NaN.
pub struct FloatIsNan {}
impl fmt::Display for FloatIsNan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Float is NaN")
    }
}
#[cfg(feature = "std")]
impl std::error::Error for FloatIsNan {}

// Do not use ordered-float crate due to orphan rules
#[repr(transparent)]
#[derive(Debug, Default, Clone, Copy, PartialEq, PartialOrd)]
#[cfg_attr(feature = "include_serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "include_serde", serde(transparent))]
/// Wrapper for non-NaN floats that implements Eq and Ord.
pub struct NonNanFloat<T: Float>(T);

macro_rules! impl_float_interconv {
    ($float: ty, $wrap: ty) => {
        impl Hash for NonNanFloat<$float> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                let bits = if self.is_zero() {
                    <$float>::zero().to_bits()
                } else {
                    self.0.to_bits()
                };
                bits.hash(state)
            }
        }
        impl TryFrom<$float> for $wrap {
            type Error = FloatIsNan;

            fn try_from(value: $float) -> Result<Self, Self::Error> {
                if value.is_nan() {
                    Err(FloatIsNan {})
                } else {
                    Ok(<$wrap>::new(value))
                }
            }
        }
        impl From<$wrap> for $float {
            fn from(value: $wrap) -> Self {
                value.0
            }
        }
    };
}

impl_float_interconv!(f32, NonNanFloat<f32>);
impl_float_interconv!(f64, NonNanFloat<f64>);

impl<T: Float> NonNanFloat<T> {
    #[inline(always)]
    /// Try to wrap a float, returning an Error if the float is NaN.
    pub fn try_new(val: T) -> Result<Self, FloatIsNan> {
        if val.is_nan() {
            Err(FloatIsNan {})
        } else {
            Ok(NonNanFloat(val))
        }
    }
    #[inline(always)]
    /// Try to wrap a float, panicking if the float is NaN.
    pub fn new(val: T) -> Self {
        Self::try_new(val).unwrap()
    }
    #[inline(always)]
    pub fn into_inner(&self) -> T {
        self.0
    }
}
impl<T: Float> Deref for NonNanFloat<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Float> Eq for NonNanFloat<T> {}
impl<T: Float> Ord for NonNanFloat<T> {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: Float> PartialEq<T> for NonNanFloat<T> {
    fn eq(&self, other: &T) -> bool {
        if other.is_nan() {
            return false;
        }
        self.0 == *other
    }
}
impl<T: Float> PartialOrd<T> for NonNanFloat<T> {
    fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
        self.0.partial_cmp(other)
    }
}

macro_rules! impl_float_steppable {
    ($float: ty, $wrap: ty, $next_after: expr) => {
        impl Steppable for $wrap {
            //! Considerations for stepping floating-point types:
            //!  - Steps are performed to the next possible representable value, so the size of the step varies with the original number's magnitude.
            //!  - Approximations and floating-point error can lead to miniscule gaps and other unexpected behaviors. For example, 0.3-0.2-0.1=-2.7755575615628914e-17 will not be contained in a nonnegative range starting at 0.
            fn step_incr(&self) -> Self {
                <$wrap>::new($next_after(self.0, Self::max_value().0))
            }
            fn step_decr(&self) -> Self {
                <$wrap>::new($next_after(self.0, Self::min_value().0))
            }

            fn range_size<B: Borrow<Self>, R: RangeBounds<B>>(range: R) -> Result<Self, RangeOperationError> {
                let (start_inclusive, end_inclusive) = get_normalized_range(&range)?;
                let size = <$wrap>::new(end_inclusive.0-start_inclusive.0).step_incr();
                // Technically correct to .step_incr() to include endpoint
                assert!(size.0 > <$float>::zero());
                Ok(size)
            }
        }
    }
}

impl<T: Float> Add for NonNanFloat<T> {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.0 + rhs.0)
    }
}

impl<T: Float> NumInRange for NonNanFloat<T>
where
    NonNanFloat<T>: Steppable
{
    #[inline(always)]
    fn min_value() -> Self {
        Self::new(T::neg_infinity())
    }
    #[inline(always)]
    fn max_value() -> Self {
        Self::new(T::infinity())
    }
    const MIN_DECR_IS_UNDERFLOW: bool = false;
    const MAX_INCR_IS_OVERFLOW: bool = false;
}

impl_float_steppable!(f32, NonNanFloat<f32>, nextafterf);
impl_float_steppable!(f64, NonNanFloat<f64>, nextafter);

// impl<T: Float> NumInRange for NonNanFloat<T> forbidden

// Ported from musl libc: https://github.com/ifduyue/musl/blob/master/src/math/nextafterf.c
// Original code doesn't have many comments so my comments may be wrong
fn nextafterf(x: f32, y: f32) -> f32 {
    if x.is_nan() || y.is_nan() {
        return x+y;
    }
    let mut ux: u32 = x.to_bits();
    let uy: u32 = y.to_bits();
    // Bitwise equality (NaN != NaN but we checked for that already)
    if ux==uy {
        return y;
    }
    // Get absolute value by zeroing the sign bit
    let ax = ux & 0x7fffffff;
    let ay = ux & 0x7fffffff;
    if ax==0 {
        if ay==0 {
            // Value equality, which catches signed zeros
            return y;
        }
        // Step x the smallest possible amount in the correct direction
        ux = (uy & 0x80000000) | 1;
    } else if ax > ay || ((ux ^ uy) & 0x80000000) != 0 {
        ux -= 1;
    } else {
        ux += 1;
    }
    // Extract exponent bits
    let e = ux & 0x7f800000;
    /* raise overflow if ux.f is infinite and x is finite */
    if e == 0x7f800000 {
        core::hint::black_box(x+x);
    }
    let ux_f = f32::from_bits(ux);
    /* raise underflow if ux.f is subnormal or zero */
    if e == 0 {
        core::hint::black_box(x*x + ux_f*ux_f);
    }
    return ux_f;
}
/*
#include "libm.h"

float nextafterf(float x, float y)
{
	union {float f; uint32_t i;} ux={x}, uy={y};
	uint32_t ax, ay, e;

	if (isnan(x) || isnan(y))
		return x + y;
	if (ux.i == uy.i)
		return y;
	ax = ux.i & 0x7fffffff;
	ay = uy.i & 0x7fffffff;
	if (ax == 0) {
		if (ay == 0)
			return y;
		ux.i = (uy.i & 0x80000000) | 1;
	} else if (ax > ay || ((ux.i ^ uy.i) & 0x80000000))
		ux.i--;
	else
		ux.i++;
	e = ux.i & 0x7f800000;
	/* raise overflow if ux.f is infinite and x is finite */
	if (e == 0x7f800000)
		FORCE_EVAL(x+x);
	/* raise underflow if ux.f is subnormal or zero */
	if (e == 0)
		FORCE_EVAL(x*x + ux.f*ux.f);
	return ux.f;
}
*/
// Ported from musl libc: https://github.com/ifduyue/musl/blob/master/src/math/nextafter.c
// Original code doesn't have many comments so my comments may be wrong
fn nextafter(x: f64, y: f64) -> f64 {
    if x.is_nan() || y.is_nan() {
        return x+y;
    }
    let mut ux: u64 = x.to_bits();
    let uy: u64 = y.to_bits();
    // Bitwise equality (NaN != NaN but we checked for that already)
    if ux==uy {
        return y;
    }
    // Get absolute value by zeroing the sign bit
    let ax = ux & 0x7fff_ffff_ffff_ffff;
    let ay = ux & 0x7fff_ffff_ffff_ffff;
    if ax==0 {
        if ay==0 {
            // Value equality, which catches signed zeros
            return y;
        }
        // Step x the smallest possible amount in the correct direction
        ux = (uy & 0x8000_0000_0000_0000) | 1;
    } else if ax > ay || ((ux ^ uy) & 0x8000_0000_0000_0000) != 0 {
        ux -= 1;
    } else {
        ux += 1;
    }
    // Extract exponent bits
    let e = (ux >> 52) & 0x7ff;
    /* raise overflow if ux.f is infinite and x is finite */
    if e == 0x7ff {
        core::hint::black_box(x+x);
    }
    let ux_f = f64::from_bits(ux);
    /* raise underflow if ux.f is subnormal or zero */
    if e == 0 {
        core::hint::black_box(x*x + ux_f*ux_f);
    }
    return ux_f;
}
/*
double nextafter(double x, double y)
{
	union {double f; uint64_t i;} ux={x}, uy={y};
	uint64_t ax, ay;
	int e;

	if (isnan(x) || isnan(y))
		return x + y;
	if (ux.i == uy.i)
		return y;
	ax = ux.i & -1ULL/2;
	ay = uy.i & -1ULL/2;
	if (ax == 0) {
		if (ay == 0)
			return y;
		ux.i = (uy.i & 1ULL<<63) | 1;
	} else if (ax > ay || ((ux.i ^ uy.i) & 1ULL<<63))
		ux.i--;
	else
		ux.i++;
	e = ux.i >> 52 & 0x7ff;
	/* raise overflow if ux.f is infinite and x is finite */
	if (e == 0x7ff)
		FORCE_EVAL(x+x);
	/* raise underflow if ux.f is subnormal or zero */
	if (e == 0)
		FORCE_EVAL(x*x + ux.f*ux.f);
	return ux.f;
}
*/