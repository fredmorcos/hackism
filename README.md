# has
Hack Assembler: An assembler for the Hack machine.

```
has 0.1.0

USAGE:
    has [FLAGS] <FILE>...

FLAGS:
    -h, --help       Prints help information
    -t, --text       Output text files instead of binary
    -V, --version    Prints version information
    -v, --verbose    Verbose output (can be specified multiple times)

ARGS:
    <FILE>...    Hack assembly file(s) to load
```

**Testing:** `cargo test` or `cargo test -- --nocapture --test-threads 1`

**Running:** `cargo run -- FILE1 FILE2...`

**Logging:** `cargo run -- -vvv FILE1 FILE2...`

**Help:** `cargo run -- --help`

**Install:** `cargo install --path .`
