# Changelog

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