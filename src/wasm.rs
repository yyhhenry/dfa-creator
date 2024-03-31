use crate::{dfa::DFA, nfa::NFA};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
/// Convert DFA to mermaid graph
/// Throws when the JSON is invalid
pub fn dfa2mermaid(dfa_json: String) -> Result<String, JsError> {
    let dfa = DFA::from_json(&dfa_json).map_err(JsError::from)?;
    Ok(dfa.to_mermaid())
}

#[wasm_bindgen]
/// Convert NFA to mermaid graph
/// Throws when the JSON is invalid
pub fn nfa2mermaid(nfa_json: String) -> Result<String, JsError> {
    let nfa = NFA::from_json(&nfa_json).map_err(JsError::from)?;
    Ok(nfa.to_mermaid())
}

#[wasm_bindgen]
/// Construct NFA from regular expression
/// and return the JSON representation
/// Throws when the regular expression is invalid
/// We only support the following syntax:
/// ```txt
/// <regex> ::= <term> '|' <regex> | <term>
/// <term> ::= <factor> <term> | <factor>
/// <factor> ::= <base> '*' | <base>
/// <base> ::= <char> | '(' <regex> ')'
/// ```
pub fn reg2nfa(reg: String) -> Result<String, JsError> {
    let nfa = NFA::from_regex(&reg).map_err(JsError::from)?;
    Ok(nfa.to_json())
}

#[wasm_bindgen]
/// Convert NFA to DFA
/// Returns (dfa_json, markdown)
/// Throws when the NFA JSON is invalid
pub fn nfa2dfa(nfa_json: String) -> Result<Vec<String>, JsError> {
    let nfa = NFA::from_json(&nfa_json).map_err(JsError::from)?;
    let (dfa, markdown) = nfa.to_dfa();
    Ok(vec![dfa.to_json(), markdown])
}

#[wasm_bindgen]
/// Minimize DFA
/// Returns (min_dfa_json, markdown)
/// Throws when the DFA JSON is invalid
pub fn minimize_dfa(dfa_json: String) -> Result<Vec<String>, JsError> {
    let dfa = DFA::from_json(&dfa_json).map_err(JsError::from)?;
    let (min_dfa, markdown) = dfa.minimize();
    Ok(vec![min_dfa.to_json(), markdown])
}

#[wasm_bindgen]
/// Test if the input string is accepted by the DFA
/// Returns true if accepted, false otherwise
/// Throws when the DFA JSON is invalid
pub fn test_dfa(dfa_json: String, input: String) -> Result<bool, JsError> {
    let dfa = DFA::from_json(&dfa_json).map_err(JsError::from)?;
    Ok(dfa.test(&input))
}

#[wasm_bindgen]
/// Test if the input string is accepted by the NFA
/// Returns true if accepted, false otherwise
/// Throws when the NFA JSON is invalid
pub fn test_nfa(nfa_json: String, input: String) -> Result<bool, JsError> {
    let nfa = NFA::from_json(&nfa_json).map_err(JsError::from)?;
    Ok(nfa.test(&input))
}
