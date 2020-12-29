#![warn(clippy::all)]

use has::prog;
use has::prog::Prog;

use std::convert::TryFrom;
use std::fmt;
use std::fs::File;
use std::io::BufWriter;
use std::io::Write;
use std::io::{self, Read};
use std::path::PathBuf;

use derive_more::From;
use log::{debug, info, trace};
use structopt::StructOpt;

#[derive(From)]
enum Err {
  Io(io::Error),
  Prog(prog::Err),
  Encode(prog::EncodeErr),
}

impl fmt::Display for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Err::Io(e) => write!(f, "IO error: {}", e),
      Err::Prog(e) => write!(f, "Program error: {}", e),
      Err::Encode(e) => write!(f, "Encoding error: {}", e),
    }
  }
}

impl fmt::Debug for Err {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    (self as &dyn fmt::Display).fmt(f)
  }
}

/// The HACK Application Suite.
#[derive(Debug, StructOpt)]
#[structopt(name = "has")]
struct Opt {
  /// Verbose output (can be specified multiple times)
  #[structopt(short, long, parse(from_occurrences))]
  verbose: u8,

  #[structopt(subcommand)]
  command: Command,
}

#[derive(Debug, StructOpt)]
enum Command {
  /// Assemble a HACK file.
  Asm {
    /// Output a text instead of binary file
    #[structopt(short, long)]
    text: bool,

    /// Output file (must not exist)
    #[structopt(short, long, name = "OUT", parse(from_os_str))]
    out: PathBuf,

    /// Hack assembly file to compile
    #[structopt(name = "FILE", parse(from_os_str))]
    file: PathBuf,
  },
}

impl Command {
  fn execute(self) -> Result<(), Err> {
    match self {
      Command::Asm { text, out, file } => {
        let mut buf = Vec::with_capacity(1024);
        let bytes = File::open(&file)?.read_to_end(&mut buf)?;
        info!("Read {} bytes from {}", bytes, file.display());

        if out.exists() {
          return Err(Err::Io(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!("File {} already exists", out.display()),
          )));
        }

        info!("Parsing {}", file.display());
        let mut prog = Prog::try_from(buf.as_slice())?;

        let output = File::create(&out)?;
        let mut writer = BufWriter::new(output);
        info!("Writing to file {}", out.display());

        if text {
          for inst in prog.text_encoder() {
            let inst = &inst?;
            writer.write_all(inst)?;
            writer.write_all(&[b'\n'])?;
          }
        } else {
          for inst in prog.encoder() {
            let inst = inst?;
            writer.write_all(&inst)?;
          }
        }

        Ok(())
      }
    }
  }
}

fn main() -> Result<(), Err> {
  let opt = Opt::from_args();

  let log_level = match opt.verbose {
    0 => log::LevelFilter::Warn,
    1 => log::LevelFilter::Info,
    2 => log::LevelFilter::Debug,
    _ => log::LevelFilter::Trace,
  };

  let log_res = env_logger::Builder::new().filter_level(log_level).try_init();

  match log_res {
    Ok(_) => {}
    Err(e) => eprintln!("Error initializing logger: {}", e),
  }

  info!("Informational output enabled");
  debug!("Debug output enabled");
  trace!("Tracing output enabled");

  opt.command.execute()
}
