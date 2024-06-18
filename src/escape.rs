use thiserror::Error;
use v_htmlescape;
pub fn mermaid_escape(c: char) -> String {
    let s = match c {
        ' ' => "[space]".to_string(),
        '\n' => "[newline]".to_string(),
        '\t' => "[tab]".to_string(),
        '\r' => "[return]".to_string(),
        c => c.to_string(),
    };
    format!("\"{}\"", v_htmlescape::escape(&s).to_string())
}
pub fn katex_escape(c: char) -> String {
    match c {
        ' ' => "[space]".to_string(),
        '\n' => "\\backslash n".to_string(),
        '\t' => "\\backslash t".to_string(),
        '\r' => "\\backslash r".to_string(),
        '\\' => "\\backslash".to_string(),
        '{' => "`\\{`".to_string(),
        '}' => "`\\}`".to_string(),
        '$' => "\\$".to_string(),
        '&' => "\\&".to_string(),
        '#' => "\\#".to_string(),
        '_' => "\\_".to_string(),
        '%' => "\\%".to_string(),
        '^' => "\\^{\\ }".to_string(),
        '~' => "\\~{\\ }".to_string(),
        c => c.to_string(),
    }
}
#[derive(Error, Debug)]
pub enum RegexEscapeError {
    #[error("Invalid escape sequence: {0}")]
    InvalidEscapeSequence(String),
}
/// We only support the following operators:
/// '|', '*', '(', ')'.
/// Use backslash to escape special characters:
/// `\*`, `\|`, `\(`, `\)`, `\\`, `\n`, `\r`, `\t`.
pub enum RegexToken {
    Char(char),
    Star,
    Or,
    LParen,
    RParen,
}
/// Tokenize a regular expression string.
/// Returns a list of (position, token) pairs.
/// See `RegexToken` for supported operators.
pub fn regex_tokenizer(s: &str) -> Result<Vec<(usize, RegexToken)>, RegexEscapeError> {
    let mut tokens = vec![];
    let mut chars = s.chars().enumerate();
    use RegexEscapeError::*;
    use RegexToken::*;
    while let Some((i, c)) = chars.next() {
        match c {
            '*' => tokens.push((i, Star)),
            '|' => tokens.push((i, Or)),
            '(' => tokens.push((i, LParen)),
            ')' => tokens.push((i, RParen)),
            '\\' => match chars.next() {
                None => {
                    return Err(InvalidEscapeSequence("\\<EOF>".to_string()));
                }
                Some((_, c)) => match c {
                    '*' => tokens.push((i, Char('*'))),
                    '|' => tokens.push((i, Char('|'))),
                    '(' => tokens.push((i, Char('('))),
                    ')' => tokens.push((i, Char(')'))),
                    '\\' => tokens.push((i, Char('\\'))),
                    'n' => tokens.push((i, Char('\n'))),
                    'r' => tokens.push((i, Char('\r'))),
                    't' => tokens.push((i, Char('\t'))),
                    c => {
                        return Err(InvalidEscapeSequence(c.to_string()));
                    }
                },
            },
            c => tokens.push((i, Char(c))),
        }
    }
    Ok(tokens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mermaid_escape() {
        assert_eq!(mermaid_escape(' '), "\"[space]\"");
        assert_eq!(mermaid_escape('|'), "\"|\"");
        assert_eq!(mermaid_escape('"'), "\"&quot;\"");
    }

    #[test]
    fn test_katex_escape() {
        assert_eq!(katex_escape(' '), "\\_space\\_");
        assert_eq!(katex_escape('|'), "|");
        assert_eq!(katex_escape('"'), "&quot;");
    }
}
