# Changelog

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