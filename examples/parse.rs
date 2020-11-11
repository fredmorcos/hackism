use has::prog::Prog;

static INPUT: &[u8] = include_bytes!("../tests/fixtures/Pong.asm");

fn main() {
  for _ in 0..10000 {
    let _ = Prog::try_from(INPUT).unwrap();
  }
}
