# DFA Creator

## Description

Tool for creating NFA and DFA.

## Usage for executable

```bash
# Build dfac (or download from releases)
cargo b -r -F dfac
cp ./target/release/dfac . # or dfac.exe for Windows

# Show help
./dfac -h
./dfac r2n -h
# ...

# Regex to NFA Markdown
./dfac r2n "(a|b)*aab" -o tmp/r2n
# Regex to NFA JSON
./dfac r2n "(a|b)*aab" -o tmp/nfa.json
# Test NFA JSON
./dfac run "baaab" -i tmp/nfa -n
# NFA JSON to DFA Markdown
./dfac n2d tmp/nfa -o tmp/n2d
# NFA JSON to DFA JSON
./dfac n2d tmp/nfa -o tmp/n2d.json
# Minimize DFA
./dfac min tmp/n2d -o tmp/dfa
# Minimize DFA to JSON
./dfac min tmp/n2d -o tmp/dfa.json
# Test DFA JSON
./dfac run "baaab" -i tmp/dfa
# Show DFA JSON as Markdown
./dfac show tmp/dfa -o tmp/show
```
