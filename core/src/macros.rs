#![macro_use]
macro_rules! assert_ok(
    ($result:expr) => (assert!($result.is_ok(), "Not ok: {:?}", $result.unwrap_err()));
);
