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
pub struct NFAJson {
    states: Range<usize>,
    start: usize,
    accept: usize,
    transitions: Vec<(usize, Option<char>, usize)>,
}
#[derive(Debug, Clone)]
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
        let l_pure = (self.is_pure_start(), self.is_pure_accept());
        let r_pure = (rhs.is_pure_start(), rhs.is_pure_accept());
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
        let mut p = vec![lhs.start, lhs.accept, rhs.start, rhs.accept];
        if l_pure.0 {
            (nfa, p) = nfa.merge_state(p[0], nfa.start, p);
        }
        if l_pure.1 {
            (nfa, p) = nfa.merge_state(p[1], nfa.accept, p);
        }
        if r_pure.0 {
            (nfa, p) = nfa.merge_state(p[2], nfa.start, p);
        }
        if r_pure.1 {
            (nfa, _) = nfa.merge_state(p[3], nfa.accept, p);
        }
        nfa
    }
    fn merge_state(&self, mut a: usize, mut b: usize, list: Vec<usize>) -> (Self, Vec<usize>) {
        if a > b {
            (a, b) = (b, a);
        }
        assert!(
            self.states.start <= a && a < b && b < self.states.end,
            "Invalid merge state {} {} {:?}",
            a,
            b,
            self.states
        );
        let mut nfa_json = NFAJson::from(self.clone());
        let id = |u: usize| match u {
            u if u < b => u,
            u if u == b => a,
            u => u - 1,
        };
        nfa_json.start = id(nfa_json.start);
        nfa_json.accept = id(nfa_json.accept);
        nfa_json.transitions = nfa_json
            .transitions
            .into_iter()
            .map(|(s, c, n)| (id(s), c, id(n)))
            .filter(|(s, c, n)| *s != *n || c.is_some())
            .collect();
        nfa_json.states = self.states.start..self.states.end - 1;
        let list = list.into_iter().map(id).collect();
        (NFA::from(nfa_json), list)
    }
    pub fn concat(&self, rhs: &Self) -> NFA {
        let pure = self.is_pure_accept() || rhs.is_pure_start();
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
        if pure {
            (nfa, _) = nfa.merge_state(self.accept, rhs.start, vec![]);
        }
        nfa
    }
    pub fn to_mermaid(&self) -> String {
        NFAJson::from(self.clone()).to_mermaid()
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        NFAJson::from(self.clone()).to_markdown(title, description)
    }
    pub fn to_json(&self) -> Result<String> {
        let json = NFAJson::from(self.clone());
        serde_json::to_string_pretty(&json).map_err(Into::into)
    }
    pub fn from_json(json: &str) -> Result<Self> {
        let json: NFAJson = serde_json::from_str(json)?;
        Ok(NFA::from(json))
    }
    pub fn concat_all(nfa_list: &[Self]) -> Self {
        let mut result = NFA::from(None);
        for nfa in nfa_list {
            result = result.concat(nfa);
        }
        result
    }
    pub fn out_degree(&self, state: usize) -> usize {
        self.transitions.get(&state).map_or(0, |map| map.len())
    }
    pub fn in_degree(&self, state: usize) -> usize {
        self.transitions
            .iter()
            .flat_map(|(_, map)| map.values())
            .filter(|set| set.contains(&state))
            .count()
    }
    pub fn is_pure_start(&self) -> bool {
        self.in_degree(self.start) == 0
    }
    pub fn is_pure_accept(&self) -> bool {
        self.out_degree(self.accept) == 0
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
                    if stack.is_empty() {
                        elem_list.push(Elem::Base(NFA::from_regex(&reg[start + 1..i])?));
                    }
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
impl From<NFAJson> for NFA {
    fn from(json: NFAJson) -> Self {
        let mut nfa = NFA {
            states: json.states,
            start: json.start,
            accept: json.accept,
            transitions: [].into(),
        };
        for (state, c, next) in json.transitions {
            nfa.add(state, c, next);
        }
        nfa
    }
}
impl From<NFA> for NFAJson {
    fn from(nfa: NFA) -> Self {
        let mut transitions = vec![];
        for (state, map) in nfa.transitions {
            for (c, set) in map {
                for next in set {
                    transitions.push((state, c, next));
                }
            }
        }
        transitions.sort();
        NFAJson {
            states: nfa.states,
            start: nfa.start,
            accept: nfa.accept,
            transitions,
        }
    }
}
impl NFAJson {
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
        for (state, c, next) in self.transitions.iter() {
            let c = c.unwrap_or('ε');
            result.push_str(&format!("{} --> |{}| {};\n", state, c, next));
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
}
