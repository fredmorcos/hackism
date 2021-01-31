# `HAS`: The HACK Application Suite

[![License](https://img.shields.io/github/license/fredmorcos/has?style=for-the-badge)](https://github.com/fredmorcos/has/blob/master/LICENSE)
[![Release (latest SemVer)](https://img.shields.io/github/v/release/fredmorcos/has?sort=semver&style=for-the-badge)](https://github.com/fredmorcos/has/releases)
[![Release](https://img.shields.io/github/workflow/status/fredmorcos/has/Release?label=Release&style=for-the-badge)](https://github.com/fredmorcos/has/releases)
[![CI](https://img.shields.io/github/workflow/status/fredmorcos/has/CI?label=Master&style=for-the-badge)](https://github.com/fredmorcos/has/actions)

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
- [ ] JACK virtual machine
- [ ] JACK compiler

## Usage

`HAS` makes use of subcommands.

`cargo run -- --help` or `has --help`:

```
has 0.3.0
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
has-asm 0.3.0
Assemble a HACK file

USAGE:
    has asm [FLAGS] <FILE> --out <OUT>

FLAGS:
    -b, --bintext    Output a bintext instead of binary file
    -h, --help       Prints help information
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
has-dis 0.3.0
Disassemble a HACK file

USAGE:
    has dis [FLAGS] <FILE> --out <OUT>

FLAGS:
    -b, --bintext    The input is a bintext instead of a binary file
    -h, --help       Prints help information
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
