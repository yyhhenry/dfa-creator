use anyhow::{anyhow, Result};
use clap::Parser;
use dfa_creator::nfa;

#[derive(Parser)]
struct Args {
    /// Regular expression.
    /// Supported operators: `*`, `|`, `()`.
    regex: String,
    /// Output file
    /// If not provided, the output will be printed to stdout.
    /// Supported formats: md, json.
    #[clap(short, long)]
    output: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let nfa = nfa::NFA::from_regex(&args.regex)?;
    if let Some(output) = args.output {
        let path = std::path::Path::new(&output);
        let format = path.extension().and_then(|s| s.to_str()).unwrap_or("md");
        let path = path.with_extension(format);
        let folder = path
            .parent()
            .ok_or_else(|| anyhow!("Invalid output path"))?;
        std::fs::create_dir_all(folder)?;
        let content = match format {
            "md" => nfa.to_markdown(
                "NFA",
                &format!("NFA created from regular expression: `{}`.", args.regex),
            ),
            "json" => nfa.to_json(),
            _ => return Err(anyhow!("Invalid format")),
        };
        std::fs::write(&path, content)?;
        println!("{} created", path.display());
    } else {
        println!("{}", nfa.to_mermaid());
    }
    Ok(())
}
