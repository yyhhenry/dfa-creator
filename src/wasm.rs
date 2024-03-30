use crate::{dfa::DFA, nfa::NFA};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
/// Convert a DFA JSON to a mermaid graph
pub fn dfa2mermaid(dfa_json: String) -> String {
    let dfa = DFA::from_json(&dfa_json).unwrap();
    dfa.to_mermaid()
}

#[wasm_bindgen]
/// Convert a NFA JSON to a mermaid graph
pub fn nfa2mermaid(nfa_json: String) -> String {
    let nfa = NFA::from_json(&nfa_json).unwrap();
    nfa.to_mermaid()
}

#[wasm_bindgen]
/// Construct a NFA from a regular expression
/// and return the JSON representation
/// We only support the following syntax:
/// ```txt
/// <regex> ::= <term> '|' <regex> | <term>
/// <term> ::= <factor> <term> | <factor>
/// <factor> ::= <base> '*' | <base>
/// <base> ::= <char> | '(' <regex> ')'
/// ```
pub fn reg2nfa(reg: String) -> String {
    let nfa = NFA::from_regex(&reg).unwrap();
    nfa.to_json()
}

#[wasm_bindgen]
/// Convert a NFA JSON to a DFA JSON
pub fn nfa2dfa(nfa_json: String) -> String {
    let nfa = NFA::from_json(&nfa_json).unwrap();
    let (dfa, _) = nfa.to_dfa();
    dfa.to_json()
}

#[wasm_bindgen]
/// Convert a NFA to a DFA
/// and return a markdown representation of the process
pub fn nfa2dfa_markdown(nfa_json: String) -> String {
    let nfa = NFA::from_json(&nfa_json).unwrap();
    let (_, markdown) = nfa.to_dfa();
    markdown
}

#[wasm_bindgen]
/// Minimize a DFA
pub fn minimize_dfa(dfa_json: String) -> String {
    let dfa = DFA::from_json(&dfa_json).unwrap();
    let (min_dfa, _) = dfa.minimize();
    min_dfa.to_json()
}

#[wasm_bindgen]
/// Minimize a DFA
/// and return a markdown representation of the process
pub fn minimize_dfa_markdown(dfa_json: String) -> String {
    let dfa = DFA::from_json(&dfa_json).unwrap();
    let (_, markdown) = dfa.minimize();
    markdown
}
