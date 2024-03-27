use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

use crate::nfa::NFA;
type DFAState = usize;
type DFAToken = char;
type DFATransition = HashMap<DFAToken, usize>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DFAJson {
    pub start: DFAState,
    pub accept: HashSet<DFAState>,
    pub transitions: Vec<(DFAState, DFAToken, DFAState)>,
}

#[derive(Debug, Clone)]
pub struct DFA {
    /// The start state of the DFA.
    start: DFAState,
    /// The set of accept states in the DFA.
    accept: HashSet<DFAState>,
    /// The transition function of the DFA.
    /// state -> (token -> state)
    transitions: HashMap<DFAState, DFATransition>,
}
impl DFA {
    pub fn to_json(&self) -> String {
        serde_json::to_string(&DFAJson::from(self.clone())).unwrap()
    }
    fn add(&mut self, state: DFAState, token: DFAToken, to: DFAState) {
        self.transitions
            .entry(state)
            .or_insert_with(HashMap::new)
            .insert(token, to);
    }
    pub fn from_json(json: &str) -> serde_json::error::Result<Self> {
        let dfa_json: DFAJson = serde_json::from_str(json)?;
        Ok(DFA::from(dfa_json))
    }
    pub fn to_nfa(&self) -> NFA {
        unimplemented!("DFA to NFA conversion")
    }
}
impl From<DFAJson> for DFA {
    fn from(json: DFAJson) -> Self {
        let mut dfa = Self {
            start: json.start,
            accept: json.accept,
            transitions: HashMap::new(),
        };
        for (from, token, to) in json.transitions {
            dfa.add(from, token, to);
        }
        dfa
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
            start: dfa.start,
            accept: dfa.accept,
            transitions,
        }
    }
}
