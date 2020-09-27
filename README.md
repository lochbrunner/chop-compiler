
[![build status](https://travis-ci.org/lochbrunner/chop-compiler.svg?branch=master)](https://travis-ci.org/lochbrunner/chop-compiler)
[![GitHub Actions status](https://github.com/lochbrunner/chop-compiler/workflows/test/badge.svg)](https://github.com/lochbrunner/chop-compiler/actions?workflow=test)
[![GitHub Actions status](https://github.com/lochbrunner/chop-compiler/workflows/milestones/badge.svg)](https://github.com/lochbrunner/chop-compiler/actions?workflow=milestones)


# Reference implementation for chop-lang


This is a reference implementation of [Chop Language](https://github.com/lochbrunner/chop-specs/blob/master/README.md).

## Prerequisites

* [Rust](https://www.rust-lang.org/)
* LLVM Tools

```bash
sudo apt install libpython2.7 libxml2 clang llvm-dev
```

## Setup

```bash
cargo install --path ichop --force
cargo install --path cchop --force
```

## Usage

### Interpret

```bash
ichop <code filename>
```

> Hint: Usage of shebang is also possible.

### Compilation

```bash
cchop <code filename> -o <output filename>
```

## Milestones

1. [Interpret MVP](./milestones/1) :heavy_check_mark:
1. [Compile MVP via LLVM](./milestones/2) :heavy_check_mark:
1. [Mathematical operations and build-in functions](./milestones/3) :heavy_check_mark:
1. [Variables](./milestones/4) :heavy_check_mark:
1. [Primitive Types](./milestones/5)
1. [Objects](./milestones/6)
1. [Functions](./milestones/7)
1. [Code generation from intermediate steps](./milestones/8)
1. Enums
1. Control flow
1. Caching
1. Imports and Exports
1. Meta Programming
1. Borrowing (and checks)
1. FFI
1. Debugging

## Goal - Self hosted language

* Rewrite compiler and interpreter in chop.
* Adjust and extend the language specs with findings on that way.

...
Finally solve some of [Graydon Hoare's problems](https://graydon2.dreamwidth.org/253769.html)