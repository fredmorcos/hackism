# `Hackism`: A HACK & JACK Application Suite

[![License](https://img.shields.io/github/license/fredmorcos/hackism?style=for-the-badge)](https://github.com/fredmorcos/hackism/blob/master/LICENSE)
[![Release (latest SemVer)](https://img.shields.io/github/v/release/fredmorcos/hackism?sort=semver&style=for-the-badge)](https://github.com/fredmorcos/hackism/releases)
[![Release](https://img.shields.io/github/workflow/status/fredmorcos/hackism/Release?label=Release&style=for-the-badge)](https://github.com/fredmorcos/hackism/releases)
[![CI](https://img.shields.io/github/workflow/status/fredmorcos/hackism/CI?label=Master&style=for-the-badge)](https://github.com/fredmorcos/hackism/actions)

https://github.com/fredmorcos/hackism

The `Hackism` project is MIT licensed (see the `LICENSE` file). Some
test files are licensed differently and such is stated at the top of
the file.

## About

The `Hackism` project is a suite of applications related to the HACK
machine and JACK programming language and VM taught by the
[`Nand2Tetris`](https://www.nand2tetris.org/) course. The application
suite is a library and set of programs for handling various tasks
related to the HACK CPU, micro-architecture and instruction set as
well as the JACK programming language and virtual machine. `Hackism`
currently consists of the following:

- [x] Library for parsing HACK assembly
- [x] HACK assembler and disassembler
- [ ] HACK interpreter
- [ ] HACK CPU emulator
- [ ] JACK virtual machine
- [ ] JACK compiler

## Usage

`Hackism` executables can be run using `cargo run --bin <NAME>` in the
project directory or as standalone executables such as
`hackism-NAME`. The `--help` flag is available on all `Hackism`
executables and can be used to discover more information about each
command. The `--verbose` flag is also available on all `Hackism`
programs for more verbose output.

### Examples

To assemble a `.asm` HACK file with logging enabled: `hackism-asm -vvv
infile.asm -o outfile.hack`.

To disassemble a `.hack` file: `hackism-dis infile.hack -o
outfile.asm`.

## `Bin` and `Bintext`

The tools provided by the `Nand2Tetris` course primarily deal with
what I call `bintext`: A textual representation of values in binary
form. This is generally awkward but a good way to teach the concepts
without having to teach how to deal with binary data.

The predecessor of `hackism` dealt with both types of data (e.g. by
passing a `--bintext` flag when `bintext` was involved or
desired). However, I decided that continuing to do so was not worth
the abstraction hassles. Hence, `hackism` only deals with `bintext`.

## Building and Installation

Cargo can be used to build and install `hackism` programs into
`~/.cargo/bin` using `cargo install --path .` (note the `dot` at the
end of the command). The program names are all prefixed with
`hackism-` (e.g. `hackism-asm`, `hackism-dis`, etc...).

## Testing

To test the `hackism` library, execute `cargo test` in the top-level
directory of the project.
