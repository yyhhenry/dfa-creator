use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    ops::Range,
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
        let mut nfa = self.re_index(self.states.start);
        nfa.add(nfa.accept, None, nfa.start);
        nfa.accept = nfa.start;
        nfa
    }
    fn add(&mut self, state: usize, c: NFAToken, next: usize) {
        self.transitions
            .entry(state)
            .or_insert_with(NFATransition::new)
            .entry(c)
            .or_insert_with(HashSet::new)
            .insert(next);
    }
    pub fn or(&self, rhs: &Self) -> NFA {
        let start = self.states.start;
        let lhs = self.re_index(self.states.start + 1);
        let rhs = rhs.re_index(lhs.states.end);
        let accept = rhs.states.end;
        let end = accept + 1;
        let mut transitions = lhs.transitions;
        transitions.extend(rhs.transitions);
        let mut nfa = NFA {
            states: start..end,
            start,
            accept,
            transitions,
        };
        nfa.add(start, None, lhs.start);
        nfa.add(start, None, rhs.start);
        nfa.add(lhs.accept, None, accept);
        nfa.add(rhs.accept, None, accept);
        nfa
    }
    pub fn concat(&self, rhs: &Self) -> NFA {
        // If one of the NFA is empty, return the other one.
        if self.states.len() == 1 {
            return rhs.clone();
        } else if rhs.states.len() == 1 {
            return self.clone();
        }
        let rhs = rhs.re_index(self.states.end);
        let mut transitions = self.transitions.clone();
        for (state, map) in rhs.transitions {
            transitions.insert(state, map);
        }
        let mut nfa = NFA {
            states: self.states.start..rhs.states.end,
            start: self.start,
            accept: rhs.accept,
            transitions,
        };
        nfa.add(self.accept, None, rhs.start);
        nfa
    }
    pub fn to_mermaid(&self) -> String {
        let mut result = "graph TD\n".to_string();
        for state in self.states.clone() {
            let name = if state == self.start {
                format!("S{}", state)
            } else {
                format!("{}", state)
            };
            let shape = if state == self.accept {
                format!("((({})))", name)
            } else {
                format!("(({}))", name)
            };
            result.push_str(&format!("{}{}\n", state, shape));
        }
        for (state, map) in self.transitions.iter() {
            for (c, set) in map.iter() {
                let c = c.unwrap_or('ε');
                for next in set.iter() {
                    result.push_str(&format!("{} --> |{}| {};\n", state, c, next));
                }
            }
        }
        result
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        let mermaid = self.to_mermaid();
        format!(
            "# {}\n\n{}\n\n```mermaid\n{}\n```\n",
            title, description, mermaid
        )
    }
    pub fn concat_all(nfa_list: &[Self]) -> Self {
        let mut result = NFA::from(None);
        for nfa in nfa_list {
            result = result.concat(nfa);
        }
        result
    }
    pub fn or_all(nfa_list: &[Self]) -> Self {
        let mut result = nfa_list[0].clone();
        for nfa in nfa_list.iter().skip(1) {
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
        #[derive(Debug)]
        enum Elem {
            Base(NFA),
            Star,
            Or,
        }
        let mut stack = vec![];
        let mut elem_list = vec![];
        for (i, c) in reg.chars().enumerate() {
            match (c, stack.len()) {
                ('(', _) => stack.push(i),
                (')', _) => {
                    let start = stack.pop().ok_or(anyhow!("Unmatched ')'"))?;
                    let elem = &reg[start + 1..i];
                    elem_list.push(Elem::Base(NFA::from_regex(elem)?));
                }
                ('*', 0) => elem_list.push(Elem::Star),
                ('|', 0) => elem_list.push(Elem::Or),
                (_, 0) => elem_list.push(Elem::Base(NFA::from(Some(c)))),
                _ => {}
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
        let result = Self::or_all(&result);
        Ok(result)
    }
    pub fn epsilon_closure(&self, state: HashSet<usize>) -> HashSet<usize> {
        let mut result = state.clone();
        let mut stack = state.iter().cloned().collect::<Vec<_>>();
        while let Some(state) = stack.pop() {
            if let Some(set) = self.transitions.get(&state) {
                if let Some(next_set) = set.get(&None) {
                    for next in next_set {
                        if result.insert(*next) {
                            stack.push(*next);
                        }
                    }
                }
            }
        }
        result
    }
    pub fn test(&self, s: &str) -> bool {
        let mut current = self.epsilon_closure([self.start].into());
        for c in s.chars() {
            let mut next = HashSet::new();
            for state in current {
                if let Some(set) = self.transitions.get(&state) {
                    if let Some(next_set) = set.get(&Some(c)) {
                        next.extend(next_set);
                    }
                }
            }
            current = self.epsilon_closure(next);
        }
        current.contains(&self.accept)
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
