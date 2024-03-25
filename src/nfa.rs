use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    ops::{Add, BitOr, Mul, Range},
};
type NFAToken = Option<char>;
type NFATransition = HashMap<NFAToken, HashSet<usize>>;
#[allow(dead_code)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NFA {
    /// States of the NFA.
    states: Range<usize>,
    /// The start state of the NFA.
    start: usize,
    /// The accept state of the NFA.
    /// If multiple accept states are needed, add a new state and transition to it from the original accept state.
    accept: usize,
    /// Transitions of the NFA.
    /// state -> (character -> states)
    /// The key None represents epsilon transitions.
    transitions: HashMap<usize, NFATransition>,
}
impl NFA {
    pub fn re_index(&self, start: usize) -> Self {
        let id = |d: &usize| *d - self.states.start + start;
        let re_index_transition = |transition: &NFATransition| {
            transition
                .iter()
                .map(|(c, set)| (c.clone(), set.iter().map(id).collect()))
                .collect()
        };
        let transitions = self
            .transitions
            .iter()
            .map(|(state, map)| (id(state), re_index_transition(map)))
            .collect();
        NFA {
            states: start..start + self.states.len(),
            start: self.start + start,
            accept: self.accept + start,
            transitions,
        }
    }
    pub fn star(&self) -> NFA {
        let mut transitions = self.transitions.clone();
        transitions
            .entry(self.accept)
            .or_insert_with(NFATransition::new)
            .entry(None)
            .or_insert_with(HashSet::new)
            .insert(self.start);
        NFA {
            states: self.states.clone(),
            start: self.start,
            accept: self.accept,
            transitions,
        }
    }
    pub fn or(&self, rhs: &Self) -> NFA {
        let rhs = rhs.re_index(self.states.end);
        let mut transitions = self.transitions.clone();
        for (state, map) in rhs.transitions {
            transitions.insert(state, map);
        }
        transitions
            .entry(self.accept)
            .or_insert_with(NFATransition::new)
            .entry(None)
            .or_insert_with(HashSet::new)
            .insert(rhs.start);
        NFA {
            states: self.states.start..rhs.states.end,
            start: self.start,
            accept: rhs.accept,
            transitions,
        }
    }
    pub fn concat(&self, rhs: &Self) -> NFA {
        let rhs = rhs.re_index(self.states.end);
        let mut transitions = self.transitions.clone();
        for (state, map) in rhs.transitions {
            transitions.insert(state, map);
        }
        transitions
            .entry(self.accept)
            .or_insert_with(NFATransition::new)
            .entry(None)
            .or_insert_with(HashSet::new)
            .insert(rhs.start);
        NFA {
            states: self.states.start..rhs.states.end,
            start: self.start,
            accept: rhs.accept,
            transitions,
        }
    }
    pub fn to_mermaid(&self) -> String {
        let mut result = "graph LR\n".to_string();
        for (state, map) in self.transitions.iter() {
            for (c, set) in map.iter() {
                let c = c.unwrap_or('ε');
                for next in set.iter() {
                    result.push_str(&format!("{}-|{}|->{};\n", state, c, next));
                }
            }
        }
        result
    }
    pub fn concat_all(nfa_list: &[Self]) -> Self {
        let mut result = NFA::from(None);
        for nfa in nfa_list {
            result = result.concat(nfa);
        }
        result
    }
    pub fn or_all(nfa_list: &[Self]) -> Self {
        let mut result = NFA::from(None);
        for nfa in nfa_list {
            result = result.or(nfa);
        }
        result
    }
    /// Create an NFA from a regular expression.
    /// We only support the following syntax:
    /// <regex> ::= <term> '|' <regex> | <term>
    /// <term> ::= <factor> <term> | <factor>
    /// <factor> ::= <base> '*' | <base>
    /// <base> ::= <char> | '(' <regex> ')'
    pub fn from_regex(reg: &str) -> Result<Self> {
        enum Elem {
            Base(NFA),
            Star,
            Or,
        }
        let mut stack = vec![];
        let mut elem_list = vec![];
        for (i, c) in reg.chars().enumerate() {
            match c {
                '(' => stack.push(i),
                ')' => {
                    let start = stack.pop().ok_or(anyhow!("Unmatched ')'"))?;
                    let elem = &reg[start + 1..i];
                    elem_list.push(Elem::Base(NFA::from_regex(elem)?));
                }
                '*' => elem_list.push(Elem::Star),
                '|' => elem_list.push(Elem::Or),
                _ => elem_list.push(Elem::Base(NFA::from(Some(c)))),
            }
        }
        // Apply all stars
        let origin_elem_list = elem_list.drain(..).collect::<Vec<_>>();
        for elem in origin_elem_list {
            match elem {
                Elem::Star => match elem_list.pop() {
                    Some(Elem::Base(prev)) => elem_list.push(Elem::Base(prev.star())),
                    _ => return Err(anyhow!("No NFA to apply star")),
                },
                elem => elem_list.push(elem),
            }
        }
        let mut result = vec![NFA::from(None)];
        for elem in elem_list {
            match elem {
                Elem::Base(nfa) => {
                    let prev = result.pop().ok_or(anyhow!("No NFA to concat"))?;
                    result.push(prev.concat(&nfa));
                }
                _ => {
                    result.push(NFA::from(None));
                }
            }
        }
        Ok(Self::or_all(&result))
    }
}
impl From<NFAToken> for NFA {
    fn from(c: NFAToken) -> Self {
        if c.is_some() {
            NFA {
                states: 0..2,
                start: 0,
                accept: 1,
                transitions: [(0, [(c, [1].into())].into())].into(),
            }
        } else {
            NFA {
                states: 0..1,
                start: 0,
                accept: 0,
                transitions: [].into(),
            }
        }
    }
}
