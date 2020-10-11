#![macro_use]
macro_rules! assert_ok(
    ($result:expr) => (assert!($result.is_ok(), format!("Not ok: {:?}", $result.unwrap_err())));
);
