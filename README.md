# DFA Creator

## Description

Tool for creating NFA and DFA.

## Usage

```bash
# Regex to NFA Markdown
cargo r -r --bin reg_to_nfa -- "(a|b)*aab" -o tmp/nfa
# Regex to NFA JSON
cargo r -r --bin reg_to_nfa -- "(a|b)*aab" -o tmp/nfa.json
# Test NFA JSON
cargo r -r --bin nfa_test -- "baaab" -i tmp/nfa
# NFA JSON to DFA Markdown
cargo r -r --bin nfa_to_dfa -- tmp/nfa -o tmp/dfa
# NFA JSON to DFA JSON
cargo r -r --bin nfa_to_dfa -- tmp/nfa -o tmp/dfa.json
# Test DFA JSON
cargo r -r --bin dfa_test -- "baaab" -i tmp/dfa
```
