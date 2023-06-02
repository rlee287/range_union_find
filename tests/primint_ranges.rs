use range_union_find::{RangeUnionFind, OverlapType};

use core::ops::RangeInclusive;
use core::iter::FromIterator;

#[test]
fn insert_max_size_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(0..=0xff)).unwrap();
    for i in 0..=0xff {
        assert!(range_obj.has_element(&i));
    }
    assert_eq!(range_obj.has_range(&(0..=0xff)).unwrap(),
        OverlapType::Contained);

    let mut unbounded_range_obj = RangeUnionFind::<u8>::new();
    unbounded_range_obj.insert_range(&(..)).unwrap();
    assert_eq!(range_obj, unbounded_range_obj);
}
#[test]
fn reject_bad_ranges() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(5..=2)).unwrap_err();
    range_obj.insert_range_pair(&5, &2).unwrap_err();

    range_obj.has_range(&(5..=2)).unwrap_err();
    range_obj.has_range_pair(&5, &2).unwrap_err();

    range_obj.remove_range(&(5..=2)).unwrap_err();
    range_obj.remove_range_pair(&5, &2).unwrap_err();

    range_obj.has_range(&(7..7)).unwrap_err();
}
#[test]
fn make_from_iter() {
    let range_vec = vec![1..3, 5..7];
    let range_obj = RangeUnionFind::<u8>::from_iter(range_vec);

    let mut range_obj_ref = RangeUnionFind::<u8>::new();
    range_obj_ref.insert_range(&(1..3)).unwrap();
    range_obj_ref.insert_range(&(5..7)).unwrap();
    assert_eq!(range_obj, range_obj_ref);
}
#[test]
fn turn_into_iter() {
    let range_vec = vec![1..=3, 5..=7, 10..=16];
    let range_obj = RangeUnionFind::<u8>::from_iter(range_vec.clone());
    let extract_vec: Vec<RangeInclusive<u8>> = range_obj.into_collection();
    assert_eq!(range_vec, extract_vec);
}
#[test]
fn extend_bitor_equivalence() {
    let range_vec_full = vec![1..=3, 5..=7, 10..=16];
    let range_obj_full = RangeUnionFind::<u8>::from_iter(range_vec_full);

    let range_vec_second = vec![5..=7, 10..=16];
    let range_obj_second = RangeUnionFind::<u8>::from_iter(range_vec_second);

    let mut range_obj_first = RangeUnionFind::<u8>::default();
    range_obj_first.insert_range(&(1..=3)).unwrap();
    let mut range_obj_build = range_obj_first.clone();

    let range_obj_final = &range_obj_first | &range_obj_second;
    assert_eq!(range_obj_full, range_obj_final);

    range_obj_build = &range_obj_build | &range_obj_second;
    assert_eq!(range_obj_full, range_obj_build);
}

#[test]
fn print_dual_range() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(0..=4)).unwrap();
    range_obj.insert_range(&(8..=16)).unwrap();
    let formatted = format!("{:?}",range_obj);
    assert_eq!(formatted, "[0..=4, 8..=16]");
}

#[test]
fn single_range_has_element() {
    let mut range_obj = RangeUnionFind::<u32>::new();
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
    let mut range_obj = RangeUnionFind::<u32>::new();
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
    let mut range_obj = RangeUnionFind::<u32>::new();
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
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(8..=16)).unwrap();

    assert_eq!(range_obj.has_range(&(0..=7)).unwrap(),OverlapType::Disjoint);
    assert_eq!(range_obj.has_range(&(17..=25)).unwrap(),OverlapType::Disjoint);
}
#[test]
fn single_range_has_range() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(8..=16)).unwrap();

    assert_eq!(range_obj.has_range(&(8..=16)).unwrap(),OverlapType::Contained);
    assert_eq!(range_obj.has_range(&(8..=11)).unwrap(),OverlapType::Contained);
    assert_eq!(range_obj.has_range(&(12..=14)).unwrap(),OverlapType::Contained);
    assert_eq!(range_obj.has_range(&(15..=16)).unwrap(),OverlapType::Contained);
}
#[test]
fn single_range_range_partial() {
    let mut range_obj = RangeUnionFind::<u32>::new();
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
    let mut range_obj = RangeUnionFind::<u32>::new();
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
    let mut range_obj = RangeUnionFind::<u32>::new();
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

    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(8..=16)).unwrap();
    range_obj.insert_range(&(0..=24)).unwrap();

    let mut range_obj_single = RangeUnionFind::<u32>::new();
    range_obj_single.insert_range(&(0..=24)).unwrap();
    assert_eq!(range_obj, range_obj_single);
}
#[test]
fn insert_partial_overarch_adj_range_over_single_range() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(12..=16)).unwrap();
    range_obj.insert_range(&(11..=15)).unwrap();

    let mut range_obj_final = RangeUnionFind::<u32>::new();
    range_obj_final.insert_range(&(11..=16)).unwrap();
    assert_eq!(range_obj, range_obj_final);
}
#[test]
fn insert_partial_overarch_full_valuespan() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(0..=0)).unwrap();
    range_obj.insert_range(&(0xff..=0xff)).unwrap();

    range_obj.insert_range(&(0..=0xff)).unwrap();

    let mut range_obj_final = RangeUnionFind::<u8>::new();
    range_obj_final.insert_range(&(0..=0xff)).unwrap();
    assert_eq!(range_obj, range_obj_final);
}
#[test]
fn insert_partial_overarch_adj_range_over_dual_range() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(12..=16)).unwrap();
    range_obj.insert_range(&(4..=8)).unwrap();
    let mut range_obj_2 = range_obj.clone();
    let mut range_obj_3 = range_obj.clone();

    range_obj.insert_range(&(0..=11)).unwrap();

    let mut range_obj_final = RangeUnionFind::<u32>::new();
    range_obj_final.insert_range(&(0..=16)).unwrap();
    assert_eq!(range_obj, range_obj_final);

    range_obj_2.insert_range(&(9..=20)).unwrap();
    let mut range_obj_final = RangeUnionFind::<u32>::new();
    range_obj_final.insert_range(&(4..=20)).unwrap();
    assert_eq!(range_obj_2, range_obj_final);

    range_obj_3.insert_range(&(4..=16)).unwrap();
    let mut range_obj_final = RangeUnionFind::<u32>::new();
    range_obj_final.insert_range(&(4..=16)).unwrap();
    assert_eq!(range_obj_3, range_obj_final);
}
#[test]
fn insert_partial_overarch_all_range_over_multi_range() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(12..=16)).unwrap();
    range_obj.insert_range(&(4..=8)).unwrap();
    let mut range_obj_3 = range_obj.clone();

    range_obj.insert_range(&(0..=20)).unwrap();

    let mut range_obj_single = RangeUnionFind::<u32>::new();
    range_obj_single.insert_range(&(0..=20)).unwrap();
    assert_eq!(range_obj, range_obj_single);

    range_obj_3.insert_range(&(6..=14)).unwrap();
    let mut range_obj_single_3 = RangeUnionFind::<u32>::new();
    range_obj_single_3.insert_range(&(4..=16)).unwrap();
    assert_eq!(range_obj_3, range_obj_single_3);

    let mut range_obj_2 = RangeUnionFind::<u32>::new();
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
fn insert_single_element_adj_range() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(11..20)).unwrap();
    range_obj.insert_range(&(10..=10)).unwrap();
    range_obj.insert_range(&(20..=20)).unwrap();

    let mut expected_obj = RangeUnionFind::<u32>::new();
    expected_obj.insert_range(&(10..=20)).unwrap();

    assert_eq!(expected_obj, range_obj);
}
#[test]
fn insert_repeated_points() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(10..=10)).unwrap();
    range_obj.insert_range(&(11..=11)).unwrap();
    range_obj.insert_range(&(13..=13)).unwrap();
    range_obj.insert_range(&(12..=12)).unwrap();

    range_obj.insert_range(&(15..=15)).unwrap();
    range_obj.insert_range(&(16..=16)).unwrap();
    range_obj.insert_range(&(18..=18)).unwrap();
    range_obj.insert_range(&(17..=17)).unwrap();

    range_obj.insert_range(&(21..=21)).unwrap();
    range_obj.insert_range(&(20..=20)).unwrap();
    range_obj.insert_range(&(23..=23)).unwrap();
    range_obj.insert_range(&(22..=22)).unwrap();

    range_obj.insert_range(&(25..=25)).unwrap();
    range_obj.insert_range(&(27..=27)).unwrap();
    range_obj.insert_range(&(26..=26)).unwrap();
    let mut expected_obj = RangeUnionFind::<u32>::new();
    expected_obj.insert_range(&(10..=13)).unwrap();
    expected_obj.insert_range(&(15..=18)).unwrap();
    expected_obj.insert_range(&(20..=23)).unwrap();
    expected_obj.insert_range(&(25..=27)).unwrap();

    assert_eq!(expected_obj, range_obj);
}
#[test]
fn insert_range_over_endpoint_singletons() {
    let mut range_obj = RangeUnionFind::<u32>::new();
    range_obj.insert_range(&(10..=10)).unwrap();
    range_obj.insert_range(&(20..=20)).unwrap();
    let mut range_obj_2 = range_obj.clone();
    range_obj.insert_range(&(11..=19)).unwrap();
    range_obj_2.insert_range(&(10..=20)).unwrap();
    assert_eq!(range_obj, range_obj_2);

    let mut expected_obj = RangeUnionFind::<u32>::new();
    expected_obj.insert_range(&(10..=20)).unwrap();

    assert_eq!(expected_obj, range_obj);
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

#[test]
fn remove_disjoint_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..20)).unwrap();
    let expected_obj = range_obj.clone();
    range_obj.remove_range(&(0..10)).unwrap();
    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_entire_single_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..=12)).unwrap();
    range_obj.remove_range(&(4..=12)).unwrap();

    let expected_obj = RangeUnionFind::<u8>::new();
    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_partial_single_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..=12)).unwrap();
    range_obj.remove_range(&(4..=7)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(8..=12)).unwrap();
    assert_eq!(range_obj, expected_obj);

    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..=12)).unwrap();
    range_obj.remove_range(&(10..=12)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(4..=9)).unwrap();
    assert_eq!(range_obj, expected_obj);

    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..=12)).unwrap();
    range_obj.remove_range(&(5..=11)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(4..=4)).unwrap();
    expected_obj.insert_range(&(12..=12)).unwrap();
    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_endpoint_overlap_single_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..=12)).unwrap();
    range_obj.remove_range(&(4..=4)).unwrap();
    range_obj.remove_range(&(12..=12)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(5..=11)).unwrap();
    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_overlap_single_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..=12)).unwrap();
    let mut range_obj_2 = range_obj.clone();
    range_obj.remove_range(&(0..=8)).unwrap();
    range_obj_2.remove_range(&(10..=15)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(9..=12)).unwrap();
    assert_eq!(range_obj, expected_obj);

    let mut expected_obj_2 = RangeUnionFind::<u8>::new();
    expected_obj_2.insert_range(&(4..=9)).unwrap();
    assert_eq!(range_obj_2, expected_obj_2);
}
#[test]
fn remove_overarch_partial_match() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(4..8)).unwrap();
    range_obj.remove_range(&(0..10)).unwrap();

    let expected_obj = RangeUnionFind::<u8>::new();
    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_partial_multiple_ranges() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();
    range_obj.insert_range(&(30..=40)).unwrap();
    range_obj.insert_range(&(50..=60)).unwrap();
    range_obj.remove_range(&(15..=55)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(10..=14)).unwrap();
    expected_obj.insert_range(&(56..=60)).unwrap();

    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_partial_multiple_ranges_rangeswallow() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();
    range_obj.insert_range(&(30..=40)).unwrap();
    range_obj.insert_range(&(50..=60)).unwrap();
    range_obj.insert_range(&(70..=80)).unwrap();

    range_obj.remove_range(&(30..=60)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(10..=20)).unwrap();
    expected_obj.insert_range(&(70..=80)).unwrap();

    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_point_make_points() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(1..=3)).unwrap();
    range_obj.remove_range(&(2..=2)).unwrap();

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(1..=1)).unwrap();
    expected_obj.insert_range(&(3..=3)).unwrap();

    assert_eq!(range_obj, expected_obj);
}
#[test]
fn remove_sub_equivalence() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();
    range_obj.insert_range(&(30..=40)).unwrap();
    range_obj.insert_range(&(50..=60)).unwrap();
    range_obj.insert_range(&(70..=80)).unwrap();

    let full_obj = range_obj.clone();
    range_obj.remove_range(&(30..=60)).unwrap();
    range_obj.remove_range(&(11..16)).unwrap();

    let mut range_rhs = RangeUnionFind::<u8>::new();
    range_rhs.insert_range(&(30..=60)).unwrap();
    range_rhs.insert_range(&(11..16)).unwrap();

    let sub_obj = &full_obj - &range_rhs;
    assert_eq!(range_obj, sub_obj);
}
#[test]
fn remove_over_valuespan_singletons() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(2..=0xfd)).unwrap();
    range_obj.insert_range(&(0..=0)).unwrap();
    range_obj.insert_range(&(0xff..=0xff)).unwrap();

    let mut range_obj_rm_upper = range_obj.clone();
    let mut range_obj_rm_lower = range_obj.clone();

    let mut lower_half_obj = RangeUnionFind::<u8>::new();
    lower_half_obj.insert_range(&(2..=0x7f)).unwrap();
    lower_half_obj.insert_range(&(0..=0)).unwrap();
    range_obj_rm_upper.remove_range(&(0x80..=0xff)).unwrap();
    assert_eq!(lower_half_obj, range_obj_rm_upper);

    let mut upper_half_obj = RangeUnionFind::<u8>::new();
    upper_half_obj.insert_range(&(0x80..=0xfd)).unwrap();
    upper_half_obj.insert_range(&(0xff..=0xff)).unwrap();
    range_obj_rm_lower.remove_range(&(0..0x80)).unwrap();
    assert_eq!(upper_half_obj, range_obj_rm_lower);
}
#[test]
fn remove_partial_with_singleton_leftovers() {
    // Leaving behind an endpoint singleton on the right
    // See regression_issue_1 for an endpoint singleton on the leftt
    let mut inv = RangeUnionFind::<i32>::new();
    inv.insert_range(&(14..=20)).unwrap();
    inv.remove_range(&(0..=19)).unwrap();
    // Inserted check for final result not in the original issue
    let mut expected_inv = RangeUnionFind::<i32>::new();
    expected_inv.insert_range(&(20..21)).unwrap();
    assert_eq!(inv, expected_inv);
}

#[test]
fn bitand_same_obj() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();
    range_obj.insert_range(&(30..=40)).unwrap();

    let anded_obj = &range_obj & &range_obj;
    assert_eq!(range_obj, anded_obj);
}
#[test]
fn bitand_when_contained() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=50)).unwrap();

    let mut rhs_obj = RangeUnionFind::<u8>::new();
    rhs_obj.insert_range(&(20..=30)).unwrap();

    let anded_obj_1 = &range_obj & &rhs_obj;
    let anded_obj_2 = &rhs_obj & &range_obj;
    assert_eq!(anded_obj_1, anded_obj_2);

    assert_eq!(anded_obj_1, rhs_obj);
}
#[test]
fn bitand_when_disjoint() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=15)).unwrap();

    let mut rhs_obj = RangeUnionFind::<u8>::new();
    rhs_obj.insert_range(&(20..=30)).unwrap();

    let anded_obj_1 = &range_obj & &rhs_obj;
    let anded_obj_2 = &rhs_obj & &range_obj;
    assert_eq!(anded_obj_1, anded_obj_2);

    let expected_obj = RangeUnionFind::<u8>::new();
    assert_eq!(anded_obj_1, expected_obj);
}
#[test]
fn bitand_overarch_subselect() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();
    range_obj.insert_range(&(30..=40)).unwrap();
    range_obj.insert_range(&(50..=60)).unwrap();
    range_obj.insert_range(&(70..=80)).unwrap();

    let mut rhs_obj = RangeUnionFind::<u8>::new();
    rhs_obj.insert_range(&(0..35)).unwrap();

    let anded_obj_1 = &range_obj & &rhs_obj;
    let anded_obj_2 = &rhs_obj & &range_obj;
    assert_eq!(anded_obj_1, anded_obj_2);

    let mut expected_obj = RangeUnionFind::<u8>::new();
    expected_obj.insert_range(&(10..=20)).unwrap();
    expected_obj.insert_range(&(30..=34)).unwrap();
    assert_eq!(anded_obj_1, expected_obj);
}

#[test]
fn inverse_range() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();

    let mut expected_inverted_range = RangeUnionFind::<u8>::new();
    expected_inverted_range.insert_range(&(..=9)).unwrap();
    expected_inverted_range.insert_range(&(21..)).unwrap();

    assert_eq!(!&range_obj, expected_inverted_range);
}

#[test]
fn xor_partial() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();

    let mut rhs_obj = RangeUnionFind::<u8>::new();
    rhs_obj.insert_range(&(15..=25)).unwrap();

    assert_eq!(&range_obj ^ &rhs_obj, &rhs_obj ^ &range_obj);

    let mut expected_xor_obj = RangeUnionFind::<u8>::new();
    expected_xor_obj.insert_range(&(10..=14)).unwrap();
    expected_xor_obj.insert_range(&(21..=25)).unwrap();

    assert_eq!(&range_obj ^ &rhs_obj, expected_xor_obj);
}

#[test]
fn range_set_boolean_ops_demorgan() {
    let mut range_obj = RangeUnionFind::<u8>::new();
    range_obj.insert_range(&(10..=20)).unwrap();
    range_obj.insert_range(&(30..=40)).unwrap();
    range_obj.insert_range(&(50..=60)).unwrap();
    range_obj.insert_range(&(70..=80)).unwrap();

    let mut range_obj_2 = RangeUnionFind::<u8>::new();
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