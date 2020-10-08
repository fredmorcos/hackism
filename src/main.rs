#![warn(clippy::all)]

mod inst;
mod lex;
mod parse;
mod pos;

use std::fs::File;
use std::io::BufWriter;
use std::io::Write;
use std::io::{self, BufReader, Read};
use std::{iter::Iterator, path::PathBuf};

use derive_more::From;
use log::{debug, info, trace};
use parse::Parse;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct HasOptions {
  /// Verbose output (can be specified multiple times)
  #[structopt(short, long, parse(from_occurrences))]
  verbose: u8,

  /// Output text files instead of binary
  #[structopt(short, long)]
  text: bool,

  /// Hack assembly file(s) to load
  #[structopt(name = "FILE", parse(from_os_str), required = true, min_values = 1)]
  files: Vec<PathBuf>,
}

#[derive(Debug, From)]
enum Err {
  IO(io::Error),
  Logger(log::SetLoggerError),
  Parse(parse::Err),
}

fn encode(val: u16) -> [u8; 16] {
  const VALS: [u8; 2] = [b'0', b'1'];
  [
    VALS[(val >> 15 & 1) as usize],
    VALS[(val >> 14 & 1) as usize],
    VALS[(val >> 13 & 1) as usize],
    VALS[(val >> 12 & 1) as usize],
    VALS[(val >> 11 & 1) as usize],
    VALS[(val >> 10 & 1) as usize],
    VALS[(val >> 9 & 1) as usize],
    VALS[(val >> 8 & 1) as usize],
    VALS[(val >> 7 & 1) as usize],
    VALS[(val >> 6 & 1) as usize],
    VALS[(val >> 5 & 1) as usize],
    VALS[(val >> 4 & 1) as usize],
    VALS[(val >> 3 & 1) as usize],
    VALS[(val >> 2 & 1) as usize],
    VALS[(val >> 1 & 1) as usize],
    VALS[(val & 1) as usize],
  ]
}

fn main() -> Result<(), Err> {
  let opt = HasOptions::from_args();

  let log_level = match opt.verbose {
    0 => log::LevelFilter::Warn,
    1 => log::LevelFilter::Info,
    2 => log::LevelFilter::Debug,
    _ => log::LevelFilter::Trace,
  };

  env_logger::Builder::new()
    .filter_level(log_level)
    .try_init()?;

  info!("Informational output enabled");
  debug!("Debug output enabled");
  trace!("Tracing output enabled");

  for filename in opt.files {
    let input = File::open(&filename)?;
    let reader = BufReader::new(input);
    info!("Reading file from {}", filename.display());

    let output_filename = filename.with_extension("hack");
    if output_filename.exists() {
      return Err(Err::IO(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!("File {} already exists", output_filename.display()),
      )));
    }

    let output = File::create(&output_filename)?;
    let mut writer = BufWriter::new(output);
    info!("Writing to file {}", output_filename.display());

    for inst in Parse::new(reader.bytes()) {
      let inst = inst?;
      debug!("Instruction {:#?}", inst);
      let inst = inst.encode();
      if opt.text {
        writer.write_all(&encode(inst))?;
        writer.write_all(&[b'\n'])?;
      } else {
        writer.write_all(&[(inst >> 8) as u8, inst as u8])?;
      }
    }
  }

  Ok(())
}
