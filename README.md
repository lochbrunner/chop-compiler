
<a href="https://travis-ci.org/lochbrunner/chop-compiler"><img src="https://travis-ci.org/lochbrunner/chop-compiler.svg?branch=master" alt="Build Status"></a>

# Reference implementation for chop-lang


This is a reference implementation of [Chop Language](https://github.com/lochbrunner/chop-specs/blob/master/README.md).

## Prerequisites

* [Rust](https://www.rust-lang.org/)
* LLVM Tools

```bash
sudo apt install libpython2.7 libxml2 clang
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
1. [Variables](./milestones/4)
1. Objects
1. Functions