use anyhow::{anyhow, Result};
use clap::Parser;
use dfa_creator::nfa;

#[derive(Parser)]
struct Args {
    /// Input NFA file
    /// Supported formats: json.
    input: String,
    /// Output file
    /// `md` for markdown about the conversion.
    /// `json` for the DFA.
    /// Supported formats: md, json.
    #[clap(short, long)]
    output: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let input = std::path::Path::new(&args.input).with_extension("json");
    if !input.exists() {
        return Err(anyhow!("Input file does not exist"));
    }
    let nfa_json = std::fs::read_to_string(&input)?;
    let nfa = nfa::NFA::from_json(&nfa_json)?;
    let (dfa, markdown) = nfa.to_dfa();
    let output = std::path::Path::new(&args.output);
    let folder = output
        .parent()
        .ok_or_else(|| anyhow!("Invalid output path"))?;
    std::fs::create_dir_all(folder)?;
    let ext = output.extension().and_then(|s| s.to_str()).unwrap_or("md");
    let output = output.with_extension(ext);
    let content = match ext {
        "md" => markdown,
        "json" => dfa.to_json(),
        _ => return Err(anyhow!("Invalid format")),
    };
    std::fs::write(&output, content)?;
    Ok(())
}
