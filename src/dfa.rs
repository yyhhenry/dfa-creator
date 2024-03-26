use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    ops::Range,
};
type DFAToken = char;
type DFATransition = HashMap<DFAToken, usize>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DFAJson {
    pub states: Range<usize>,
    pub start: usize,
    pub accept: HashSet<usize>,
    pub transitions: Vec<(usize, DFAToken, usize)>,
}

#[derive(Debug, Clone)]
pub struct DFA {
    /// The set of states in the DFA.
    states: Range<usize>,
    /// The start state of the DFA.
    start: usize,
    /// The set of accept states in the DFA.
    accept: HashSet<usize>,
    /// The transition function of the DFA.
    /// state -> (token -> state)
    transitions: HashMap<usize, DFATransition>,
}
impl DFA {
    pub fn to_json(&self) -> String {
        serde_json::to_string(&DFAJson::from(self.clone())).unwrap()
    }
    pub fn from_json(json: &str) -> serde_json::error::Result<Self> {
        let dfa_json: DFAJson = serde_json::from_str(json)?;
        Ok(DFA::from(dfa_json))
    }
}
impl From<DFAJson> for DFA {
    fn from(json: DFAJson) -> Self {
        let mut transitions = HashMap::new();
        for (from, token, to) in json.transitions {
            transitions
                .entry(from)
                .or_insert_with(HashMap::new)
                .insert(token, to);
        }
        Self {
            states: json.states,
            start: json.start,
            accept: json.accept,
            transitions,
        }
    }
}
impl From<DFA> for DFAJson {
    fn from(dfa: DFA) -> Self {
        let mut transitions = Vec::new();
        for (from, transition) in dfa.transitions {
            for (token, to) in transition {
                transitions.push((from, token, to));
            }
        }
        Self {
            states: dfa.states,
            start: dfa.start,
            accept: dfa.accept,
            transitions,
        }
    }
}
