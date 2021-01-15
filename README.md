# `HAS`: The HACK Application Suite

[![GitHub](https://img.shields.io/github/license/fredmorcos/has?style=for-the-badge)](https://github.com/fredmorcos/has/blob/master/LICENSE)
[![GitHub release (latest SemVer)](https://img.shields.io/github/v/release/fredmorcos/has?sort=semver&style=for-the-badge)](https://github.com/fredmorcos/has/releases)

https://github.com/fredmorcos/has

`HAS` is MIT licensed (see the `LICENSE` file) unless otherwise stated
at the top of a file.

## About

The HACK Application Suite is a library and a program for handling
various tasks related to the HACK CPU and instruction set as well as
the JACK programming language. HAS currently consists of the
following:

- [x] HACK assembler
- [x] HACK disassembler
- [ ] HACK interpreter
- [ ] HACK CPU emulator
- [ ] JACK compiler

## Usage

`HAS` makes use of subcommands.

`cargo run -- --help` or `has --help`:

```
has 0.2.0
The HACK Application Suite

USAGE:
    has [FLAGS] <SUBCOMMAND>

FLAGS:
    -h, --help       Prints help information
    -V, --version    Prints version information
    -v, --verbose    Verbose output (can be specified multiple times)

SUBCOMMANDS:
    asm     Assemble a HACK file
    dis     Disassemble a HACK file
    help    Prints this message or the help of the given subcommand(s)
```

### Assembler

The assembler can only build a single file at a time. The output file
must not already exist.

`has asm --help`:

```
has-asm 0.2.0
Assemble a HACK file

USAGE:
    has asm [FLAGS] <FILE> --out <OUT>

FLAGS:
    -h, --help       Prints help information
    -t, --text       Output a text instead of binary file
    -V, --version    Prints version information

OPTIONS:
    -o, --out <OUT>    Output file (must not exist)

ARGS:
    <FILE>    Hack assembly file to compile
```

### Disassembler

The disassembler can only disassemble a single file at a time. The
output file must not already exist.

`has dis --help`:

```
has-dis 0.2.0
Disassemble a HACK file

USAGE:
    has dis [FLAGS] <FILE> --out <OUT>

FLAGS:
    -h, --help       Prints help information
    -t, --text       The input is a text instead of a binary file
    -V, --version    Prints version information

OPTIONS:
    -o, --out <OUT>    Output file (must not exist)

ARGS:
    <FILE>    Hack file to disassemble
```

## Examples

Assemble a `.asm` file with logging enabled: `has -vvv asm infile.asm -o outfile.hack`

## Installation

Cargo can be used to install `HAS` into `~/.cargo/bin`: `cargo install --path .`

## Tests

To test the `HAS` library, execute `cargo test` in the top-level directory.
