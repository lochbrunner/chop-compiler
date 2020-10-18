#!/usr/bin/env ichop

a: i32 := 3
b: u8 := a as u8 + 5
c: u8 := 7

stdout max(b,c)