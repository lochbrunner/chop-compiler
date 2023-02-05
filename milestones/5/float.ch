#!/usr/bin/env ichop

a: f32 := 3.
b: f64 := a as f64 + 5.5
c := 7. as f64

stdout max(b,c)