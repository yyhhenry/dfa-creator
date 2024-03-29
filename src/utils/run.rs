use anyhow::{anyhow, Result};
use clap::Parser;
use dfa_creator::{dfa, nfa};

#[derive(Parser)]
pub struct RunArgs {
    /// The string to match
    string: String,
    /// Input file
    /// Supported formats: json.
    #[clap(short, long)]
    input: String,
    /// Enable DFA mode (default is NFA mode)
    #[clap(short, long)]
    nfa: bool,
}

pub fn run(args: RunArgs) -> Result<()> {
    let input = std::path::Path::new(&args.input).with_extension("json");
    if !input.exists() {
        return Err(anyhow!("Input file does not exist"));
    }
    let json = std::fs::read_to_string(&input)?;
    if args.nfa {
        let nfa = nfa::NFA::from_json(&json)?;
        let result = nfa.test(&args.string);
        println!("{}", result);
    } else {
        let dfa = dfa::DFA::from_json(&json)?;
        let result = dfa.test(&args.string);
        println!("{}", result);
    }
    Ok(())
}
