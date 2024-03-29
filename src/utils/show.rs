use anyhow::{anyhow, Result};
use clap::Parser;
use dfa_creator::{dfa, nfa};

#[derive(Parser)]
pub struct ShowArgs {
    /// Input file
    /// Supported formats: json.
    input: String,
    /// Output file
    /// Supported formats: md.
    #[clap(short, long)]
    output: String,
    /// Enable DFA mode (default is NFA mode)
    #[clap(short, long)]
    nfa: bool,
}

pub fn show(args: ShowArgs) -> Result<()> {
    let input = std::path::Path::new(&args.input).with_extension("json");
    if !input.exists() {
        return Err(anyhow!("Input file does not exist"));
    }
    let json = std::fs::read_to_string(&input)?;
    let output = std::path::Path::new(&args.output).with_extension("md");
    let folder = output
        .parent()
        .ok_or_else(|| anyhow!("Invalid output path"))?;
    std::fs::create_dir_all(folder)?;
    if args.nfa {
        let nfa = nfa::NFA::from_json(&json)?;
        let md = nfa.to_markdown("NFA", "Show NFA");
        std::fs::write(&output, md)?;
    } else {
        let dfa = dfa::DFA::from_json(&json)?;
        let md = dfa.to_markdown("DFA", "Show DFA");
        std::fs::write(&output, md)?;
    }
    Ok(())
}
