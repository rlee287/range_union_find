use range_union_find::{RangeUnionFind, NonNanFloat, FloatIsNan, OverlapType, Steppable};

use core::ops::{Bound, RangeBounds};

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
fn insert_max_size_range() {
    let mut range_obj = RangeUnionFind::<NonNanFloat<f32>>::new();
    range_obj.insert_range(&wrap_fp_range(&(f32::NEG_INFINITY..=f32::INFINITY)).unwrap()).unwrap();
    let mut f_neg = NonNanFloat::new(f32::NEG_INFINITY).step_incr();
    let mut f_pos = NonNanFloat::new(f32::INFINITY).step_decr();
    for _ in 0..128 {
        assert!(range_obj.has_element(&f_pos));
        assert!(range_obj.has_element(&f_neg));
        f_neg = f_neg.step_incr();
        f_pos = f_pos.step_decr();
    }
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(f32::NEG_INFINITY..=f32::INFINITY)).unwrap()).unwrap(),
        OverlapType::Contained);

    let mut unbounded_range_obj = RangeUnionFind::<NonNanFloat<f32>>::new();
    unbounded_range_obj.insert_range(&(..)).unwrap();
    assert_eq!(range_obj, unbounded_range_obj);
}