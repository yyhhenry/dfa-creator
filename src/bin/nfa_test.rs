use std::path::Path;

use anyhow::Result;
use clap::Parser;
use dfa_creator::nfa;

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
    let nfa = nfa::NFA::from_json(&content)?;
    let result = nfa.test(&args.target);
    println!("{}", result);
    Ok(())
}
