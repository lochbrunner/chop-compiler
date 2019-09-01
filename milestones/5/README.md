# Milestone 5 - Primitive types

Types are

* Integral types
  * `i8`
  * `i16`
  * `i32`
  * `i64`
  * `u8`
  * `u16`
  * `u32`
  * `u64`
* Floating point types
  * `f8`
  * `f16`
  * `f32`
  * `f64`

> This milestone also contains generics.

## Example

```chop
#!/usr/bin/env ichop

a: i32 := 3
b: i8 := a as i8 + 5
c: i8 := 7

stdout max(b,c)
```