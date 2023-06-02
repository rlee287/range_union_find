use range_union_find::RangeUnionFind;

#[test]
fn regression_issue_1() {
    let mut inv = RangeUnionFind::<i32>::new();
    inv.insert_range(&(14..=20)).unwrap();
    inv.remove_range(&(15..=25)).unwrap();
    // Inserted check for final result not in the original issue
    let mut expected_inv = RangeUnionFind::<i32>::new();
    expected_inv.insert_range(&(14..15)).unwrap();
    assert_eq!(inv, expected_inv);
}