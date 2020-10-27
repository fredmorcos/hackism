use std::convert::TryFrom;
use std::io::Write;

use criterion::{criterion_group, criterion_main, Criterion};
use has::prog::Prog;

static INPUT: &[u8] = include_bytes!("../tests/data/Pong.asm");
static OUTPUT: &[u8] = include_bytes!("../tests/fixtures/Pong.hack");

fn criterion_benchmark(c: &mut Criterion) {
  let mut prog = None;

  c.bench_function("Parse Pong.asm", |b| {
    b.iter(|| prog = Some(Prog::try_from(INPUT).unwrap()))
  });

  let mut prog = prog.unwrap();

  c.bench_function("Encode Pong.asm", |b| {
    b.iter(|| {
      let mut output = Vec::new();

      for inst in &mut prog {
        output.write_all(&Prog::text_encode(inst)).unwrap();
        output.write_all(&[b'\n']).unwrap();
      }

      assert_eq!(output.as_slice(), OUTPUT);
    })
  });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
