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

#[test]
fn fp_range_merge() {
    let mut range_obj_ref = RangeUnionFind::<NonNanFloat<f64>>::new();
    range_obj_ref.insert_range(&wrap_fp_range(&(0.5..2.5)).unwrap()).unwrap();

    let mut range_obj_one = RangeUnionFind::<NonNanFloat<f64>>::new();
    range_obj_one.insert_range(&wrap_fp_range(&(0.5..=1.5)).unwrap()).unwrap();
    range_obj_one.insert_range(&wrap_fp_range(&(1.5..2.5)).unwrap()).unwrap();

    let mut range_obj_two = RangeUnionFind::<NonNanFloat<f64>>::new();
    range_obj_two.insert_range(&wrap_fp_range(&(0.5..1.5)).unwrap()).unwrap();
    range_obj_two.insert_range(&wrap_fp_range(&(1.5..2.5)).unwrap()).unwrap();

    assert_eq!(range_obj_ref, range_obj_one);
    assert_eq!(range_obj_ref, range_obj_two);
}

#[test]
fn single_inf_range_range_checks() {
    let mut range_obj = RangeUnionFind::<NonNanFloat<f32>>::new();
    range_obj.insert_range(&wrap_fp_range(&(0.0..=f32::INFINITY)).unwrap()).unwrap();

    assert_eq!(range_obj.has_range(&wrap_fp_range(&(0.1..=44.0)).unwrap()).unwrap(),OverlapType::Contained);
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(0.1..=f32::INFINITY)).unwrap()).unwrap(),OverlapType::Contained);
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(0.0..=f32::INFINITY)).unwrap()).unwrap(),OverlapType::Contained);
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(-0.1..=f32::INFINITY)).unwrap()).unwrap(),OverlapType::Partial(NonNanFloat::new(f32::INFINITY)));
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(-0.1..5.0)).unwrap()).unwrap(),OverlapType::Partial(NonNanFloat::new(5.0)));
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(f32::NEG_INFINITY..-5.0)).unwrap()).unwrap(),OverlapType::Disjoint);
}
#[test]
fn multi_range_range_partial() {
    let mut range_obj = RangeUnionFind::<NonNanFloat<f64>>::new();
    range_obj.insert_range(&wrap_fp_range(&(-8.0..=-4.0)).unwrap()).unwrap();
    range_obj.insert_range(&wrap_fp_range(&(4.0..=8.0)).unwrap()).unwrap();
    // fp 8.0 step_incr is twice as large as 4.0 step_incr
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(-10.0..=-1.0)).unwrap()).unwrap(),OverlapType::Partial(NonNanFloat::new(4.0).step_incr()));
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(-1.0..=9.0)).unwrap()).unwrap(),OverlapType::Partial(NonNanFloat::new(4.0).step_incr()));
    assert_eq!(range_obj.has_range(&wrap_fp_range(&(-10.0..=9.0)).unwrap()).unwrap(),OverlapType::Partial(NonNanFloat::new(8.0).step_incr()));
}