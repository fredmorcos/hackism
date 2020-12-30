#![warn(clippy::all)]

#[cfg(test)]
mod asm_fixtures {
  use has::asm;

  use std::convert::TryFrom;
  use std::fs;
  use std::fs::File;
  use std::io::BufWriter;
  use std::io::Read;
  use std::io::Write;

  #[test]
  fn test_programs() {
    for file in fs::read_dir("tests/asm/fixtures").unwrap() {
      let file = file.unwrap();
      let mut file_path = file.path();
      let file_ext = file_path.extension().unwrap().to_str().unwrap();

      if file_ext == "asm" {
        println!("Testing fixture {}", file_path.display());

        let mut input = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut input).unwrap();
        let mut prog = asm::prog::Prog::try_from(input.as_slice()).unwrap();

        file_path.set_extension("hack");
        let mut fixture = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut fixture).unwrap();

        let mut output = Vec::with_capacity(1024);
        {
          let mut writer = BufWriter::new(&mut output);

          for inst in prog.text_encoder() {
            let inst = &inst.unwrap();
            writer.write_all(inst).unwrap();
            writer.write_all(&[b'\n']).unwrap();
          }
        }

        assert_eq!(&output, &fixture);
      }
    }
  }
}
