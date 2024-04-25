use crate::{dfa::Dfa, nfa::Nfa};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use tsify::Tsify;
use wasm_bindgen::prelude::*;

/// CamelCase for JS/TS
#[allow(non_snake_case)]
mod ts_interface {

    use super::*;

    pub type Result<T, E = JsError> = std::result::Result<T, E>;

    #[derive(Tsify, Debug, Clone, Serialize, Deserialize)]
    #[tsify(into_wasm_abi, from_wasm_abi)]
    pub struct DfaJson {
        pub start: usize,
        pub accept: BTreeSet<usize>,
        pub transitions: Vec<(usize, char, usize)>,
    }

    #[derive(Tsify, Debug, Clone, Serialize, Deserialize)]
    #[tsify(into_wasm_abi, from_wasm_abi)]
    pub struct NfaJson {
        pub start: usize,
        pub accept: usize,
        pub transitions: Vec<(usize, Option<char>, usize)>,
    }

    /// Convert DFA to mermaid graph
    #[wasm_bindgen]
    pub fn dfaToMermaid(dfa: DfaJson) -> String {
        let dfa: Dfa = dfa.into();
        dfa.to_mermaid()
    }

    /// Convert NFA to mermaid graph
    #[wasm_bindgen]
    pub fn nfaToMermaid(nfa: NfaJson) -> String {
        let nfa: Nfa = nfa.into();
        nfa.to_mermaid()
    }

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
    #[wasm_bindgen]
    pub fn regexToNfa(reg: &str) -> Result<NfaJson> {
        let nfa = Nfa::from_regex(reg).map_err(JsError::from)?;
        Ok(nfa.into())
    }

    #[derive(Tsify, Serialize, Deserialize)]
    #[tsify(into_wasm_abi, from_wasm_abi)]
    pub struct NfaToDfaResult {
        pub dfa: DfaJson,
        pub markdown: String,
    }

    /// Convert NFA to DFA
    #[wasm_bindgen]
    pub fn nfaToDfa(nfa: NfaJson) -> NfaToDfaResult {
        let nfa: Nfa = nfa.into();
        let (dfa, markdown) = nfa.to_dfa();
        NfaToDfaResult {
            dfa: dfa.into(),
            markdown,
        }
    }

    /// Regex -> NFA -> DFA
    #[wasm_bindgen]
    pub fn regexToDfa(reg: &str) -> Result<DfaJson> {
        let nfa = Nfa::from_regex(reg).map_err(JsError::from)?;
        Ok(nfa.to_dfa().0.into())
    }

    #[derive(Tsify, Serialize, Deserialize)]
    #[tsify(into_wasm_abi, from_wasm_abi)]
    pub struct MinimizeResult {
        pub minDfa: DfaJson,
        pub markdown: String,
    }

    /// Minimize DFA
    #[wasm_bindgen]
    pub fn minimizeDfa(dfa: DfaJson) -> MinimizeResult {
        let dfa: Dfa = dfa.into();
        let (min_dfa, markdown) = dfa.minimize();
        MinimizeResult {
            minDfa: min_dfa.into(),
            markdown,
        }
    }

    /// Regex -> NFA -> DFA -> Minimized DFA
    #[wasm_bindgen]
    pub fn regexToMinDfa(reg: &str) -> Result<DfaJson> {
        let nfa = Nfa::from_regex(reg).map_err(JsError::from)?;
        let (dfa, _) = nfa.to_dfa();
        let (min_dfa, _) = dfa.minimize();
        Ok(min_dfa.into())
    }

    /// Test if the input string is accepted by the DFA
    /// Returns true if accepted, false otherwise
    #[wasm_bindgen]
    pub fn testDfa(dfa: DfaJson, input: &str) -> bool {
        let dfa: Dfa = dfa.into();
        dfa.test(input)
    }

    /// Test if the input string is accepted by the NFA
    /// Returns true if accepted, false otherwise
    #[wasm_bindgen]
    pub fn testNfa(nfa: NfaJson, input: &str) -> bool {
        let nfa: Nfa = nfa.into();
        nfa.test(input)
    }
}
pub use ts_interface::{DfaJson, NfaJson};
