use std::path::Path;

use anyhow::Result;
use clap::Parser;
use dfa_creator::dfa;

#[derive(Parser)]
struct Args {
    /// The target string to match.
    target: String,
    /// Input file
    /// Only supported format: json.
    #[clap(short, long)]
    input: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let path = Path::new(&args.input).with_extension("json");
    let content = std::fs::read_to_string(&path)?;
    let dfa = dfa::DFA::from_json(&content)?;
    let result = dfa.test(&args.target);
    println!("{}", result);
    Ok(())
}
