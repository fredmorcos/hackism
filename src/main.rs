#![warn(clippy::all)]

use std::convert::TryFrom;
use std::fmt;
use std::fs::File;
use std::io::BufWriter;
use std::io::Write;
use std::io::{self, Read};
use std::{iter::Iterator, path::PathBuf};

use derive_more::From;
use has::prog::{self, Prog};
use log::{debug, info, trace};
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

#[derive(From)]
enum Err {
  Io(io::Error),
  Prog(prog::Err),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Io(e) => write!(f, "IO error: {}", e),
      Err::Prog(e) => write!(f, "Program error: {}", e),
    }
  }
}

impl fmt::Debug for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Display).fmt(f)
  }
}

fn main() -> Result<(), Err> {
  let opt = HasOptions::from_args();

  let log_level = match opt.verbose {
    0 => log::LevelFilter::Warn,
    1 => log::LevelFilter::Info,
    2 => log::LevelFilter::Debug,
    _ => log::LevelFilter::Trace,
  };

  let log_res = env_logger::Builder::new()
    .filter_level(log_level)
    .try_init();

  match log_res {
    Ok(_) => {}
    Err(e) => eprintln!("Error initializing logger: {}", e),
  }

  info!("Informational output enabled");
  debug!("Debug output enabled");
  trace!("Tracing output enabled");

  for filename in opt.files {
    let mut buf = Vec::with_capacity(1024);
    let bytes = File::open(&filename)?.read_to_end(&mut buf)?;
    info!("Read {} bytes from {}", bytes, filename.display());

    let output_filename = filename.with_extension("hack");
    if output_filename.exists() {
      return Err(Err::Io(io::Error::new(
        io::ErrorKind::AlreadyExists,
        format!("File {} already exists", output_filename.display()),
      )));
    }

    let output = File::create(&output_filename)?;
    let mut writer = BufWriter::new(output);
    info!("Writing to file {}", output_filename.display());

    let mut prog = Prog::try_from(buf.as_slice())?;
    info!(
      "Program has {} statements and {} labels",
      prog.num_statements(),
      prog.num_labels()
    );
    for inst in &mut prog {
      if opt.text {
        writer.write_all(&Prog::text_encode(inst))?;
        writer.write_all(&[b'\n'])?;
      } else {
        writer.write_all(&[(inst >> 8) as u8, inst as u8])?;
      }
    }
  }

  Ok(())
}
