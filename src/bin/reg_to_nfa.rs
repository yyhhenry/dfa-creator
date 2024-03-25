use anyhow::{anyhow, Result};
use clap::Parser;
use dfa_creator::nfa;

#[derive(Parser)]
struct Args {
    regex: String,
    /// Output file
    /// If not provided, the output will be printed to stdout.
    #[clap(short, long)]
    output: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let nfa = nfa::NFA::from_regex(&args.regex)?;
    if let Some(output) = args.output {
        let path = std::path::Path::new(&output).with_extension("md");
        let folder = path
            .parent()
            .ok_or_else(|| anyhow!("Invalid output path"))?;
        std::fs::create_dir_all(folder)?;
        let markdown = nfa.to_markdown(
            "NFA",
            &format!("NFA created from regular expression: `{}`.", args.regex),
        );
        std::fs::write(path, markdown)?;
        println!("Markdown created");
    } else {
        println!("{}", nfa.to_mermaid());
    }
    Ok(())
}
