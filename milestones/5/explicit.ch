#!/usr/bin/env ichop

a: i32 := 3
b: i8 := a as i8 + 5 as i8
c: i8 := 7 as i8

stdout max(b,c)