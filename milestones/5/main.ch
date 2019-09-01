#!/usr/bin/env ichop

a: i32 := 3
b: i8 := a as i8 + 5
c: i8 := 7

stdout max(b,c)