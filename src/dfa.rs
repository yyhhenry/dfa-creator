use crate::{
    nfa::{NFAJson, NFA},
    numberer::{DisjointSet, Numberer},
};
use serde::{Deserialize, Serialize};
use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum FromJsonError {
    #[error("From Json Error: {0}")]
    SyntaxError(#[from] serde_json::error::Error),
}

type Token = char;
type Transition = HashMap<Token, usize>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DFAJson {
    pub start: usize,
    pub accept: HashSet<usize>,
    pub transitions: Vec<(usize, Token, usize)>,
}
impl DFAJson {
    /// Re-index the DFAJson to start from `index`.
    /// Returns the new size of the DFAJson and the re-indexed DFAJson.
    pub fn re_index(&self, index: usize) -> (usize, Self) {
        let mut r = Numberer::from(index);
        let start = r.i(self.start);
        let mut transitions = self.transitions.clone();
        transitions.sort();
        let transitions: Vec<_> = transitions
            .into_iter()
            .map(|(s, c, n)| (r.i(s), c, r.i(n)))
            .collect();
        let accept = self.accept.iter().map(|i| r.i(*i)).collect();
        (
            r.len(),
            Self {
                start,
                accept,
                transitions,
            },
        )
    }
    /// Merge the states by the disjoint set.
    /// You should ensure that the disjoint set is generated from the same DFA.
    /// In other words, the DFA should be re-indexed from 0 before merging.
    pub fn merge_by(&self, m: DisjointSet) -> Self {
        let m = m.to_map();
        let start = m[&self.start];
        let transitions: Vec<_> = self
            .transitions
            .iter()
            .map(|(s, c, n)| (m[s], *c, m[n]))
            .collect();
        let accept = self.accept.iter().map(|i| m[i]).collect();
        Self {
            start,
            accept,
            transitions,
        }
    }
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
    pub fn from_json(json: &str) -> Result<Self, FromJsonError> {
        serde_json::from_str(json).map_err(FromJsonError::SyntaxError)
    }
    pub fn to_mermaid(&self) -> String {
        let mut result = "".to_string();
        result.push_str("%%{ init: { 'theme': 'neutral' } }%%\n");
        result.push_str("graph TD\n");
        let (size, dfa) = self.re_index(0);
        for state in 0..size {
            let name = if state == dfa.start {
                format!("S{}", state)
            } else {
                format!("{}", state)
            };
            let shape = if dfa.accept.contains(&state) {
                format!("((({})))", name)
            } else {
                format!("(({}))", name)
            };
            result.push_str(&format!("{}{}\n", state, shape));
        }
        for (state, c, next) in dfa.transitions {
            result.push_str(&format!("{} --> |{}| {};\n", state, c, next));
        }
        result
    }
    pub fn to_inline_mermaid(&self) -> String {
        let mermaid = self.to_mermaid();
        format!("#\n```mermaid\n{}\n```\n", mermaid)
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        let mermaid = self.to_inline_mermaid();
        format!("# {}\n\n{}\n\n{}", title, description, mermaid)
    }
}

#[derive(Debug, Clone)]
pub struct DFA {
    /// The start state of the DFA.
    start: usize,
    /// The set of accept states in the DFA.
    accept: HashSet<usize>,
    /// The transition function of the DFA.
    /// state -> (token -> state)
    transitions: HashMap<usize, Transition>,
}
impl DFA {
    pub fn to_json(&self) -> String {
        let dfa_json: DFAJson = self.into();
        dfa_json.to_json()
    }
    pub fn from_json(json: &str) -> Result<Self, FromJsonError> {
        let dfa_json = DFAJson::from_json(json)?;
        Ok(Self::from(dfa_json))
    }
    pub fn to_mermaid(&self) -> String {
        let dfa_json: DFAJson = self.into();
        dfa_json.to_mermaid()
    }
    pub fn to_inline_mermaid(&self) -> String {
        let dfa_json: DFAJson = self.into();
        dfa_json.to_inline_mermaid()
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        let dfa_json: DFAJson = self.into();
        dfa_json.to_markdown(title, description)
    }
    fn add(&mut self, state: usize, token: Token, to: usize) {
        self.transitions
            .entry(state)
            .or_insert_with(HashMap::new)
            .insert(token, to);
    }
    pub fn to_nfa(&self) -> NFA {
        let (size, dfa_json) = DFAJson::from(self).re_index(0);
        let tt = size;
        let mut transitions = dfa_json
            .transitions
            .into_iter()
            .map(|(s, c, n)| (s, Some(c), n))
            .collect::<Vec<_>>();
        transitions.extend(dfa_json.accept.iter().map(|&i| (i, None, tt)));
        let nfa_json = NFAJson {
            start: 0,
            accept: tt,
            transitions,
        };
        NFA::from(nfa_json)
    }
    pub fn test(&self, input: &str) -> bool {
        let mut state = self.start;
        for c in input.chars() {
            state = match self.transitions.get(&state).and_then(|t| t.get(&c)) {
                Some(&to) => to,
                None => return false,
            };
        }
        self.accept.contains(&state)
    }
}
impl<T: Borrow<DFAJson>> From<T> for DFA {
    fn from(json: T) -> Self {
        let json: &DFAJson = json.borrow();
        let mut dfa = Self {
            start: json.start,
            accept: json.accept.clone(),
            transitions: HashMap::new(),
        };
        for (from, token, to) in json.transitions.iter() {
            dfa.add(*from, *token, *to);
        }
        dfa
    }
}
impl<T: Borrow<DFA>> From<T> for DFAJson {
    fn from(dfa: T) -> Self {
        let dfa: &DFA = dfa.borrow();
        let mut transitions = Vec::new();
        for (from, transition) in dfa.transitions.iter() {
            for (token, to) in transition {
                transitions.push((*from, *token, *to));
            }
        }
        transitions.sort();
        Self {
            start: dfa.start,
            accept: dfa.accept.clone(),
            transitions,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn json_test() {
        let dfa_json = DFAJson {
            start: 0,
            accept: [1].into(),
            transitions: vec![(0, 'a', 1), (0, 'b', 1)],
        };
        let dfa = DFA::from(&dfa_json);
        assert_eq!(dfa_json.to_json(), dfa.to_json());
    }

    #[test]
    fn test_fn_test() {
        let dfa_json = DFAJson {
            start: 0,
            accept: [1].into(),
            transitions: vec![(0, 'a', 1), (1, 'b', 0)],
        };
        let dfa = DFA::from(dfa_json);
        assert_eq!(dfa.test("ab"), false);
        assert_eq!(dfa.test("ba"), false);
        assert_eq!(dfa.test("a"), true);
        assert_eq!(dfa.test("aba"), true);
    }
}
