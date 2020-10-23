use has::prog::{Prog, Txt};

static INPUT: &[u8] = include_bytes!("../tests/data/Pong.asm");

fn main() {
  for _ in 0..10000 {
    let mut tbuf = Txt::new();
    let _ = Prog::try_from(INPUT, &mut tbuf).unwrap();
  }
}
