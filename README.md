# DFA Creator

## Description

Tool for creating NFA and DFA.

## Usage

```bash
# Regex to NFA Markdown
cargo r -r -- r2n "(a|b)*aab" -o tmp/r2n
# Regex to NFA JSON
cargo r -r -- r2n "(a|b)*aab" -o tmp/nfa.json
# Test NFA JSON
cargo r -r -- run "baaab" -i tmp/nfa -n
# NFA JSON to DFA Markdown
cargo r -r -- n2d tmp/nfa -o tmp/n2d
# NFA JSON to DFA JSON
cargo r -r -- n2d tmp/nfa -o tmp/n2d.json
# Minimize DFA
cargo r -r -- min tmp/n2d -o tmp/dfa
# Minimize DFA to JSON
cargo r -r -- min tmp/n2d -o tmp/dfa.json
# Test DFA JSON
cargo r -r -- run "baaab" -i tmp/dfa
# Show DFA JSON as Markdown
cargo r -r -- show tmp/dfa -o tmp/show
```
