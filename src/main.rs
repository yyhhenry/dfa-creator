mod utils;
use anyhow::Result;
use clap::{Parser, Subcommand};
use utils::{
    minimize::{minimize, MinimizeArgs},
    nfa2dfa::{nfa2dfa, N2DArgs},
    reg2nfa::{reg2nfa, R2NArgs},
    run::{run, RunArgs},
};
#[derive(Subcommand)]
enum Commands {
    /// Minimize a DFA
    #[clap(name = "min")]
    Minimize(MinimizeArgs),
    /// Convert an NFA to a DFA
    #[clap(name = "n2d")]
    NFA2DFA(N2DArgs),
    /// Convert a regex to an NFA
    #[clap(name = "r2n")]
    Reg2NFA(R2NArgs),
    /// Run a DFA or an NFA
    #[clap(name = "run")]
    Run(RunArgs),
}

#[derive(Parser)]
struct Args {
    #[clap(subcommand)]
    sub_command: Commands,
}

fn main() -> Result<()> {
    let args = Args::parse();
    match args.sub_command {
        Commands::Minimize(args) => {
            minimize(args)?;
        }
        Commands::NFA2DFA(args) => {
            nfa2dfa(args)?;
        }
        Commands::Reg2NFA(args) => {
            reg2nfa(args)?;
        }
        Commands::Run(args) => {
            run(args)?;
        }
    }
    Ok(())
}
