//! The `auslander` command: inspection and replay of portable values, and
//! the derived classification of connected gentle algebras.

mod classify;
mod files;

use std::process::ExitCode;

const HELP: &str = "\
usage: auslander <command> [options]

Inspects and replays portable Auslander values, and classifies connected
gentle algebras up to derived equivalence.

commands:
  inspect FILE        parse a value and print its summary, without replay
  verify FILE         replay a value, then print its status and summary
  canonicalize FILE   replay a value, then print its canonical JSON
  fingerprint FILE    replay a value, then print its fingerprint
  classify gentle     classify connected gentle algebras and write an atlas

Run `auslander <command> --help` for the options of one command.

Exit status: 0 on success, 1 when a value is rejected, replay stops, or a
classification fails, and 2 on a usage error.
";

/// Why a command failed.
enum Failure {
    /// The arguments are wrong. `command` names the help to point to, and
    /// is empty for the top-level help.
    Usage {
        command: &'static str,
        message: String,
    },
    /// The command ran and failed.
    Failed(String),
}

impl Failure {
    fn usage(command: &'static str, message: impl Into<String>) -> Failure {
        let message = message.into();
        Failure::Usage { command, message }
    }

    fn failed(error: impl std::fmt::Display) -> Failure {
        Failure::Failed(error.to_string())
    }
}

/// Whether `argument` asks for help.
fn is_help(argument: &str) -> bool {
    matches!(argument, "-h" | "--help")
}

fn run(arguments: &[String]) -> Result<(), Failure> {
    let Some((command, rest)) = arguments.split_first() else {
        return Err(Failure::usage("", "missing command"));
    };
    match command.as_str() {
        name if name == "help" || is_help(name) => {
            print!("{HELP}");
            Ok(())
        }
        "classify" => classify::run(rest),
        name => files::run(name, rest),
    }
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match run(&arguments) {
        Ok(()) => ExitCode::SUCCESS,
        Err(Failure::Failed(message)) => {
            eprintln!("auslander: {message}");
            ExitCode::FAILURE
        }
        Err(Failure::Usage { command, message }) => {
            let command = if command.is_empty() {
                String::new()
            } else {
                format!("{command} ")
            };
            eprintln!("auslander: {message}");
            eprintln!("Run `auslander {command}--help` for usage.");
            ExitCode::from(2)
        }
    }
}
