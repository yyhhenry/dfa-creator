use serde::{Deserialize, Serialize};
use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
};
use thiserror::Error;

use crate::{
    dfa::{DFAJson, DFA},
    numberer::{DisjointSet, Numberer},
};
#[derive(Error, Debug)]
pub enum RegexSyntaxError {
    #[error("Unmatched Parentheses: {0}")]
    UnmatchedParentheses(String),
    #[error("No Element to Star: {0}")]
    NoElementToStar(String),
}
#[derive(Error, Debug)]
pub enum FromJsonError {
    #[error("From Json Error: {0}")]
    SyntaxError(#[from] serde_json::error::Error),
}
type Token = Option<char>;
type Transition = HashMap<Token, HashSet<usize>>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NFAJson {
    pub start: usize,
    pub accept: usize,
    pub transitions: Vec<(usize, Token, usize)>,
}
impl NFAJson {
    /// Re-index the states of the NFA.
    /// Returns the new size and the re-indexed NFA.
    pub fn re_index(&self, index: usize) -> (usize, Self) {
        let mut r = Numberer::from(index);
        let start = r.i(self.start);
        let mut transitions = self.transitions.clone();
        transitions.sort();
        let transitions: Vec<_> = transitions
            .into_iter()
            .map(|(s, c, n)| (r.i(s), c, r.i(n)))
            .collect();
        let accept = r.i(self.accept);
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
    /// You should ensure that the disjoint set is generated from the same NFA.
    /// In other words, the NFA should be re-indexed from 0 before merging.
    pub fn merge_by(&self, m: DisjointSet) -> Self {
        let m = m.to_map();
        let transitions: Vec<_> = self
            .transitions
            .iter()
            .map(|(s, c, n)| (m[s], *c, m[n]))
            .filter(|(s, c, n)| s != n || c.is_some())
            .collect();
        Self {
            start: m[&self.start],
            accept: m[&self.accept],
            transitions,
        }
    }
    /// Check if the start has no incoming transitions and the accept has no outgoing transitions.
    /// Returns (is_pure_start, is_pure_accept)
    pub fn is_pure(&self) -> (bool, bool) {
        (
            self.transitions.iter().all(|(_, _, t)| t != &self.start),
            self.transitions.iter().all(|(s, _, _)| s != &self.accept),
        )
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
        let (size, nfa) = self.re_index(0);
        for state in 0..size {
            let name = if state == nfa.start {
                format!("S{}", state)
            } else {
                format!("{}", state)
            };
            let shape = if state == nfa.accept {
                format!("((({})))", name)
            } else {
                format!("(({}))", name)
            };
            result.push_str(&format!("{}{}\n", state, shape));
        }
        for (state, c, next) in nfa.transitions {
            let c = c.unwrap_or('ε');
            result.push_str(&format!("{} --> |{}| {};\n", state, c, next));
        }
        result
    }
    pub fn to_inline_mermaid(&self) -> String {
        let mermaid = self.to_mermaid();
        format!("\n```mermaid\n{}\n```\n", mermaid)
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        let mermaid = self.to_inline_mermaid();
        format!("# {}\n\n{}\n{}", title, description, mermaid)
    }
}

#[derive(Debug, Clone)]
pub struct NFA {
    /// The start state of the NFA.
    start: usize,
    /// The accept state of the NFA.
    /// If multiple accept states are needed, add a new state and transition to it from the original accept state.
    accept: usize,
    /// Transitions of the NFA.
    /// state -> (character -> states)
    /// The key None represents epsilon transitions.
    transitions: HashMap<usize, Transition>,
}
impl NFA {
    /// Re-index the states of the NFA.
    /// Returns the new size and the re-indexed NFA.
    pub fn re_index(&self, index: usize) -> (usize, Self) {
        let (size, json) = NFAJson::from(self).re_index(index);
        (size, NFA::try_from(json).unwrap())
    }
    /// Merge the states by the disjoint set.
    /// You should ensure that the disjoint set is generated from the same NFA.
    /// In other words, the NFA should be re-indexed from 0 before merging.
    pub fn merge_by(&self, m: DisjointSet) -> Self {
        let json = NFAJson::from(self).merge_by(m);
        NFA::try_from(json).unwrap()
    }
    pub fn star(&self) -> NFA {
        let (size, mut nfa) = self.re_index(0);
        if nfa.start == nfa.accept {
            // No need to add a new start state
            return nfa;
        }
        let pure = nfa.is_pure();
        let (ss, s, t) = (size, nfa.start, nfa.accept);
        let size = size + 1;
        nfa.add(ss, None, s);
        nfa.add(t, None, ss);
        nfa.start = ss;
        nfa.accept = ss;
        let mut m = DisjointSet::new(size);
        if pure.0 {
            m.union(ss, s);
        }
        if pure.1 {
            m.union(ss, t);
        }
        nfa.merge_by(m)
    }
    fn add(&mut self, state: usize, c: Token, next: usize) {
        self.transitions
            .entry(state)
            .or_insert_with(Transition::new)
            .entry(c)
            .or_insert_with(HashSet::new)
            .insert(next);
    }
    pub fn or(&self, rhs: &Self) -> NFA {
        let (sl, lhs) = self.re_index(0);
        let (sr, rhs) = rhs.re_index(sl);

        let l_pure = lhs.is_pure();
        let r_pure = rhs.is_pure();

        let mut r = Numberer::from(sl + sr);
        let (ls, lt) = (lhs.start, lhs.accept);
        let (rs, rt) = (rhs.start, rhs.accept);
        let (ss, tt) = (r.i("ss"), r.i("tt"));
        let size = r.end();

        let mut nfa = NFA {
            start: ss,
            accept: tt,
            transitions: lhs.transitions.into_iter().chain(rhs.transitions).collect(),
        };
        nfa.add(ss, None, ls);
        nfa.add(ss, None, rs);
        nfa.add(lt, None, tt);
        nfa.add(rt, None, tt);
        let mut m = DisjointSet::new(size);
        if l_pure.0 && !m.same(ls, tt) {
            m.union(ls, ss);
        }
        if l_pure.1 && !m.same(lt, ss) {
            m.union(lt, tt);
        }
        if r_pure.0 && !m.same(rs, tt) {
            m.union(rs, ss);
        }
        if r_pure.1 && !m.same(rt, ss) {
            m.union(rt, tt);
        }
        nfa.merge_by(m)
    }
    pub fn concat(&self, rhs: &Self) -> NFA {
        let (sl, lhs) = self.re_index(0);
        let (sr, rhs) = rhs.re_index(sl);

        let l_pure = lhs.is_pure();
        let r_pure = rhs.is_pure();

        let (ls, lt) = (lhs.start, lhs.accept);
        let (rs, rt) = (rhs.start, rhs.accept);
        let size = sl + sr;

        let mut nfa = NFA {
            start: ls,
            accept: rt,
            transitions: lhs.transitions.into_iter().chain(rhs.transitions).collect(),
        };
        nfa.add(lt, None, rs);
        let mut m = DisjointSet::new(size);
        if l_pure.1 || r_pure.0 {
            m.union(lt, rs);
        }
        nfa.merge_by(m)
    }
    pub fn to_mermaid(&self) -> String {
        NFAJson::from(self).to_mermaid()
    }
    pub fn to_inline_mermaid(&self) -> String {
        NFAJson::from(self).to_inline_mermaid()
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        NFAJson::from(self).to_markdown(title, description)
    }
    pub fn to_json(&self) -> String {
        let json = NFAJson::from(self);
        json.to_json()
    }
    pub fn from_json(json: &str) -> Result<Self, FromJsonError> {
        let json = NFAJson::from_json(json)?;
        Ok(Self::from(json))
    }
    pub fn concat_all(nfa_list: &[Self]) -> Self {
        let mut result = NFA::from(None);
        for nfa in nfa_list {
            result = result.concat(nfa);
        }
        result
    }
    pub fn is_pure(&self) -> (bool, bool) {
        NFAJson::from(self).is_pure()
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
    /// ```txt
    /// <regex> ::= <term> '|' <regex> | <term>
    /// <term> ::= <factor> <term> | <factor>
    /// <factor> ::= <base> '*' | <base>
    /// <base> ::= <char> | '(' <regex> ')'
    /// ```
    pub fn from_regex(reg: &str) -> Result<Self, RegexSyntaxError> {
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
                    let start = stack.pop().ok_or_else(|| {
                        RegexSyntaxError::UnmatchedParentheses(format!("')' at {} in {}", i, reg))
                    })?;
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
        if !stack.is_empty() {
            return Err(RegexSyntaxError::UnmatchedParentheses(format!(
                "'(' at {} in {}",
                stack[0], reg
            )));
        }
        // Apply all stars
        let origin_elem_list = elem_list.drain(..).collect::<Vec<_>>();
        for elem in origin_elem_list {
            match elem {
                Elem::Star => match elem_list.pop() {
                    Some(Elem::Base(prev)) => elem_list.push(Elem::Base(prev.star())),
                    _ => return Err(RegexSyntaxError::NoElementToStar(reg.to_string())),
                },
                elem => elem_list.push(elem),
            }
        }
        let mut result = vec![NFA::from(None)];
        for elem in elem_list {
            match elem {
                Elem::Base(nfa) => {
                    let prev = result.pop().unwrap();
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
    pub fn epsilon_closure(&self, state: impl Borrow<HashSet<usize>>) -> HashSet<usize> {
        let state: &HashSet<_> = state.borrow();
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
    /// Convert the NFA to a DFA.
    /// Use subset construction.
    /// Returns the DFA and a Markdown string of the process.
    pub fn to_dfa(&self) -> (DFA, String) {
        fn set2s(set: impl Borrow<HashSet<usize>>) -> String {
            let mut sorted = set.borrow().iter().collect::<Vec<_>>();
            sorted.sort_unstable();
            format!(
                "{{ {} }}",
                sorted
                    .iter()
                    .map(|s| s.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }

        let mut state_sets = vec![self.epsilon_closure(HashSet::from([self.start]))];
        let mut current = 0;
        let dfa_start = 0;
        let mut dfa_transitions = vec![];
        let mut markdown = "# NFA to DFA\n".to_string();
        markdown.push_str("\n## NFA\n");
        markdown.push_str(&self.to_inline_mermaid());
        markdown.push_str("\n## Process\n");
        markdown.push_str(&format!("\n- $T_0 = {}$\n", set2s(&state_sets[0])));
        let mut r = Numberer::new();
        r.i(set2s(&state_sets[0]));
        let mut dfa_accept = HashSet::new();
        while current < state_sets.len() {
            let state_set = &state_sets[current];
            current += 1;
            if state_set.contains(&self.accept) {
                dfa_accept.insert(current);
            }
            let mut transitions: HashMap<char, HashSet<usize>> = HashMap::new();
            for state in state_set {
                for (c, next_set) in self.transitions.get(state).unwrap_or(&Transition::new()) {
                    if let Some(c) = c {
                        transitions
                            .entry(*c)
                            .or_insert_with(HashSet::new)
                            .extend(self.epsilon_closure(next_set));
                    }
                }
            }
            for (c, next_set) in transitions {
                let next = r.i(set2s(&next_set));
                markdown.push_str(&format!(
                    "\n- $\\epsilon\\-closure(move(T_{{{}}}, {})) = {} = T_{{{}}}$\n",
                    current,
                    c,
                    set2s(&next_set),
                    next
                ));
                dfa_transitions.push((current, c, next));
                if next == state_sets.len() {
                    state_sets.push(next_set);
                }
            }
        }
        let dfa_json = DFAJson {
            start: dfa_start,
            accept: dfa_accept,
            transitions: dfa_transitions,
        };
        let dfa = DFA::from(dfa_json);
        markdown.push_str("\n## Result\n");
        markdown.push_str(&dfa.to_inline_mermaid());
        (dfa, markdown)
    }
    pub fn test(&self, s: &str) -> bool {
        let mut current = self.epsilon_closure(HashSet::from([self.start]));
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
impl From<Token> for NFA {
    fn from(c: Token) -> Self {
        if c.is_some() {
            NFA {
                start: 0,
                accept: 1,
                transitions: [(0, [(c, [1].into())].into())].into(),
            }
        } else {
            NFA {
                start: 0,
                accept: 0,
                transitions: [].into(),
            }
        }
    }
}
impl<T: Borrow<NFAJson>> From<T> for NFA {
    fn from(nfa_json: T) -> Self {
        let json: &NFAJson = nfa_json.borrow();
        let mut nfa = NFA {
            start: json.start,
            accept: json.accept,
            transitions: [].into(),
        };
        for (state, c, next) in json.transitions.iter() {
            nfa.add(*state, *c, *next);
        }
        nfa
    }
}
impl<T: Borrow<NFA>> From<T> for NFAJson {
    fn from(nfa: T) -> Self {
        let nfa: &NFA = nfa.borrow();
        let mut transitions = vec![];
        for (state, map) in nfa.transitions.iter() {
            for (c, set) in map {
                for next in set {
                    transitions.push((*state, *c, *next));
                }
            }
        }
        transitions.sort();
        NFAJson {
            start: nfa.start,
            accept: nfa.accept,
            transitions,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn basic_test() {
        let nfa = NFA::from_regex("a(b|c)*d").unwrap();
        assert_eq!(nfa.test("ad"), true);
        assert_eq!(nfa.test("abd"), true);
        assert_eq!(nfa.test("acd"), true);
        assert_eq!(nfa.test("abbd"), true);
        assert_eq!(nfa.test("abccccbcd"), true);
        assert_eq!(nfa.test("a"), false);
        assert_eq!(nfa.test("aabcccd"), false);
        assert_eq!(nfa.test("abccc"), false);
        assert_eq!(nfa.test("_"), false);
    }
    #[test]
    fn re_index_test() {
        let nfa = NFA::from_regex("a(b|c)*d").unwrap();
        let (size, nfa_a) = nfa.re_index(0);
        let nfa_b = nfa_a.merge_by(DisjointSet::new(size));
        let test_all = |s: &str| {
            assert_eq!(nfa.test(s), nfa_a.test(s));
            assert_eq!(nfa.test(s), nfa_b.test(s));
        };
        test_all("ad");
        test_all("abd");
        test_all("acd");
        test_all("abbd");
        test_all("abccccbcd");
        test_all("a");
        test_all("aabcccd");
        test_all("abccc");
        test_all("_");
    }
    #[test]
    fn nest_test() {
        let nfa = NFA::from_regex("_|((a|b)*|(c|d)*)").unwrap();
        assert_eq!(nfa.test("_"), true);
        assert_eq!(nfa.test("abbab"), true);
        assert_eq!(nfa.test("cdcd"), true);
        assert_eq!(nfa.test("abcd"), false);
        assert_eq!(nfa.test("_a"), false);
        assert_eq!(nfa.test("_abcd"), false);
    }

    #[test]
    fn priority_test() {
        let nfa_a = NFA::from_regex("a*|b*").unwrap();
        let nfa_b = NFA::from_regex("(a|b)*").unwrap();
        let nfa_c = NFA::from_regex("a*b*").unwrap();
        let test_all = |s: &str| (nfa_a.test(s), nfa_b.test(s), nfa_c.test(s));
        assert_eq!(test_all("aaa"), (true, true, true));
        assert_eq!(test_all("bbb"), (true, true, true));
        assert_eq!(test_all("abb"), (false, true, true));
        assert_eq!(test_all("aba"), (false, true, false));
    }

    #[test]
    fn syntax_error_test() {
        // Unmatched '('
        let nfa = NFA::from_regex("a(b|c*d");
        assert_eq!(
            nfa.unwrap_err().to_string(),
            "Unmatched Parentheses: '(' at 1 in a(b|c*d"
        );
        // Unmatched '('
        let nfa = NFA::from_regex("a(b|c)*d)");
        assert_eq!(
            nfa.unwrap_err().to_string(),
            "Unmatched Parentheses: ')' at 8 in a(b|c)*d)"
        );
        // No element to star
        let nfa = NFA::from_regex("a(*b|c)d");
        assert_eq!(nfa.unwrap_err().to_string(), "No Element to Star: *b|c");

        let nfa = NFA::from_regex("a|*c");
        assert_eq!(nfa.unwrap_err().to_string(), "No Element to Star: a|*c");
    }

    #[test]
    fn json_test() {
        let nfa = NFA::from_regex("a(b|c)*d").unwrap();
        let json = nfa.to_json();
        let nfa2 = NFA::from_json(&json).unwrap();
        assert_eq!(nfa.test("ad"), nfa2.test("ad"));
        assert_eq!(nfa.test("abd"), nfa2.test("abd"));
        assert_eq!(nfa.test("acd"), nfa2.test("acd"));
        assert_eq!(nfa.test("abbd"), nfa2.test("abbd"));
        assert_eq!(nfa.test("abccccbcd"), nfa2.test("abccccbcd"));
        assert_eq!(nfa.test("a"), nfa2.test("a"));
        assert_eq!(nfa.test("aabcccd"), nfa2.test("aabcccd"));
        assert_eq!(nfa.test("abccc"), nfa2.test("abccc"));
        assert_eq!(nfa.test("_"), nfa2.test("_"));
    }

    #[test]
    fn json_order_test() {
        let nfa = NFA::from_regex("a(b|c)*d").unwrap();
        let json = nfa.to_json();
        let nfa2 = NFA::from_json(&json).unwrap();
        assert_eq!(nfa.to_json(), nfa2.to_json());
    }

    #[test]
    fn empty_test() {
        let nfa = NFA::from_regex("").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("a"), false);

        let nfa = NFA::from_regex("(|b)|").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("b"), true);
        assert_eq!(nfa.test("a"), false);
        assert_eq!(nfa.test("bb"), false);
    }

    #[test]
    fn star_test() {
        let nfa = NFA::from_regex("(a*b)*").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("a"), false);
        assert_eq!(nfa.test("b"), true);
        assert_eq!(nfa.test("abbaab"), true);
        assert_eq!(nfa.test("ababa"), false);

        let nfa = NFA::from_regex("(ab*)*").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("a"), true);
        assert_eq!(nfa.test("b"), false);
        assert_eq!(nfa.test("abbaab"), true);
        assert_eq!(nfa.test("baa"), false);
    }
}
