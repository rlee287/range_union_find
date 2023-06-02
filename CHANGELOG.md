# Changelog

## v0.5.0
- Replace `IntRangeUnionFind` with a generic `RangeUnionFind` type that works with a `NumInRange` trait, impl'ed on PrimInts and floats
- Add the `*Assign` variants of the impl'd `core::ops` traits and let all of them accept the rhs by value as well as by reference

## v0.4.4
- Fix a false positive index assertion in removal code that did not account for singleton ranges being left behind

## v0.4.3
- Fix panic that could occur when inserting adjacent to ranges with a single element

## v0.4.2
- Bump dependency versions

## v0.4.1
- Fix html\_root\_url version number copy

## v0.4.0
- This release should not have any API incompatibilities with v0.3.0
- Add method to determine which range an element is a part of
- Add `no_std` support via optional (but default-enabled) `std` feature
- Add optional `serde` support via the `include_serde` feature

## v0.3.0
- Add range removal functionality
- Add a clear method to remove all ranges
- Remove `BitOrAssign` impl and change `BitOr` impl to use references (like `BTreeSet`)
- Implement `Sub`
- Implement `BitAnd` and `BitXor`
- Allow unbounded ranges (with the corresponding natural meaning)

## v0.2.2
- Fix major bugs in insertion code

## v0.2.1
- Nicer prints (`Debug` panic on invalid struct, and Error `Display`)
- Use `drain` when removing internal elements for slightly improved performance

## v0.2.0
- Remove `Display` implementation (should have been `Debug` impl)
- Nicer formatting for `Debug` impl (with painc fallback if invariants violated)
- Implement `BitOr`
- Miscellaneous code cleanup

## v0.1.0
- Initial release
