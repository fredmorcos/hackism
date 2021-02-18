#![warn(clippy::all)]

#[cfg(test)]
mod programs {
  use has::HackProg;
  use std::fs;
  use std::fs::File;
  use std::io::BufWriter;
  use std::io::Read;
  use std::io::Write;

  #[test]
  fn assembler() {
    for file in fs::read_dir("tests/programs").unwrap() {
      let file = file.unwrap();
      let mut file_path = file.path();
      let file_ext = file_path.extension().unwrap().to_str().unwrap();

      if file_ext == "asm" {
        println!("Testing assembler with fixture {}", file_path.display());

        let mut input = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut input).unwrap();
        let prog = HackProg::from_source(input.as_slice()).unwrap();

        file_path.set_extension("hack");
        let mut fixture = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut fixture).unwrap();

        let mut output = Vec::with_capacity(1024);
        {
          let mut writer = BufWriter::new(&mut output);

          for inst in prog.to_bintext() {
            let inst = inst.unwrap();
            writer.write_all(&inst).unwrap();
            writer.write_all(&[b'\n']).unwrap();
          }
        }

        assert_eq!(&output, &fixture);
      }
    }
  }

  #[test]
  fn disassembler_text() {
    for file in fs::read_dir("tests/programs").unwrap() {
      let file = file.unwrap();
      let mut file_path = file.path();
      let file_ext = file_path.extension().unwrap().to_str().unwrap();

      if file_ext == "hack" {
        println!("Testing disassembler with fixture {}", file_path.display());

        let mut input = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut input).unwrap();
        let prog = HackProg::from_bintext(input.as_slice()).unwrap();

        file_path.set_extension("dis");
        let mut fixture = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut fixture).unwrap();

        let mut output = Vec::with_capacity(1024);
        {
          let mut writer = BufWriter::new(&mut output);

          for inst in prog.to_source() {
            writer.write_all(inst.as_bytes()).unwrap();
            writer.write_all(&[b'\n']).unwrap();
          }
        }

        assert_eq!(&output, &fixture);
      }
    }
  }

  #[test]
  fn disassembler_bin() {
    for file in fs::read_dir("tests/programs").unwrap() {
      let file = file.unwrap();
      let mut file_path = file.path();
      let file_ext = file_path.extension().unwrap().to_str().unwrap();

      if file_ext == "hack_bin" {
        println!("Testing fixture {}", file_path.display());

        let mut input = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut input).unwrap();
        let prog = HackProg::from_bin(input.as_slice()).unwrap();

        file_path.set_extension("dis");
        let mut fixture = Vec::with_capacity(1024);
        File::open(&file_path).unwrap().read_to_end(&mut fixture).unwrap();

        let mut output = Vec::with_capacity(1024);
        {
          let mut writer = BufWriter::new(&mut output);

          for inst in prog.to_source() {
            writer.write_all(inst.as_bytes()).unwrap();
            writer.write_all(&[b'\n']).unwrap();
          }
        }

        assert_eq!(&output, &fixture);
      }
    }
  }
}
