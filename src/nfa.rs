use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet},
};
use thiserror::Error;

use crate::{
    dfa::Dfa,
    escape::{katex_escape, mermaid_escape, regex_tokenizer, RegexEscapeError, RegexToken},
    numberer::{set2s, DisjointSet, Numberer},
    wasm::{DfaJson, NfaJson},
};

#[derive(Error, Debug)]
pub enum RegexSyntaxError {
    #[error("Unmatched Parentheses: {0}")]
    UnmatchedParentheses(String),
    #[error("No Element to Star: {0}")]
    NoElementToStar(String),
    #[error(transparent)]
    InvalidEscapeSequence(#[from] RegexEscapeError),
}
#[derive(Error, Debug)]
pub enum FromJsonError {
    #[error(transparent)]
    SyntaxError(#[from] serde_json::error::Error),
}
type Token = Option<char>;
type Transition = BTreeMap<Token, BTreeSet<usize>>;

impl NfaJson {
    /// Re-index the states of the NFA.
    /// Returns the new size and the re-indexed NFA.
    pub fn re_index(&self, index: usize) -> (usize, Self) {
        let mut r = Numberer::from(index);
        let mut states: Vec<_> = self
            .transitions
            .iter()
            .flat_map(|(s, _, n)| [*s, *n])
            .chain([self.start, self.accept])
            .collect();
        states.sort_unstable();
        for state in states {
            r.i(state);
        }
        let start = r.i(self.start);
        let transitions: Vec<_> = self
            .transitions
            .iter()
            .cloned()
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
        serde_json::to_string(self).unwrap()
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
            let c = mermaid_escape(c.unwrap_or('ε'));
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
pub struct Nfa {
    /// The start state of the NFA.
    start: usize,
    /// The accept state of the NFA.
    /// If multiple accept states are needed, add a new state and transition to it from the original accept state.
    accept: usize,
    /// Transitions of the NFA.
    /// state -> (character -> states)
    /// The key None represents epsilon transitions.
    transitions: BTreeMap<usize, Transition>,
}
impl Nfa {
    /// Re-index the states of the NFA.
    /// Returns the new size and the re-indexed NFA.
    pub fn re_index(&self, index: usize) -> (usize, Self) {
        let (size, json) = NfaJson::from(self).re_index(index);
        (size, Nfa::try_from(json).unwrap())
    }
    /// Merge the states by the disjoint set.
    /// You should ensure that the disjoint set is generated from the same NFA.
    /// In other words, the NFA should be re-indexed from 0 before merging.
    pub fn merge_by(&self, m: DisjointSet) -> Self {
        let json = NfaJson::from(self).merge_by(m);
        Nfa::try_from(json).unwrap()
    }
    pub fn star(&self) -> Nfa {
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
            .or_insert_with(BTreeSet::new)
            .insert(next);
    }
    pub fn or(&self, rhs: &Self) -> Nfa {
        let (sl, lhs) = self.re_index(0);
        let (sr, rhs) = rhs.re_index(sl);

        if lhs.transitions.is_empty() && rhs.transitions.is_empty() {
            // Only Accept the empty string
            // But we will get a epsilon transition using union rules below
            return Nfa::from(None);
        }

        let l_pure = lhs.is_pure();
        let r_pure = rhs.is_pure();

        let mut r = Numberer::from(sl + sr);
        let (ls, lt) = (lhs.start, lhs.accept);
        let (rs, rt) = (rhs.start, rhs.accept);
        let (ss, tt) = (r.i("ss"), r.i("tt"));
        let size = r.end();

        let mut nfa = Nfa {
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
    pub fn concat(&self, rhs: &Self) -> Nfa {
        let (sl, lhs) = self.re_index(0);
        let (sr, rhs) = rhs.re_index(sl);

        let l_pure = lhs.is_pure();
        let r_pure = rhs.is_pure();

        let (ls, lt) = (lhs.start, lhs.accept);
        let (rs, rt) = (rhs.start, rhs.accept);
        let size = sl + sr;

        let mut nfa = Nfa {
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
        NfaJson::from(self).to_mermaid()
    }
    pub fn to_inline_mermaid(&self) -> String {
        NfaJson::from(self).to_inline_mermaid()
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        NfaJson::from(self).to_markdown(title, description)
    }
    pub fn to_json(&self) -> String {
        let json = NfaJson::from(self);
        json.to_json()
    }
    pub fn from_json(json: &str) -> Result<Self, FromJsonError> {
        let json = NfaJson::from_json(json)?;
        Ok(Self::from(json))
    }
    pub fn concat_all(nfa_list: &[Self]) -> Self {
        let mut result = Nfa::from(None);
        for nfa in nfa_list {
            result = result.concat(nfa);
        }
        result
    }
    pub fn is_pure(&self) -> (bool, bool) {
        NfaJson::from(self).is_pure()
    }
    pub fn or_all(nfa_list: &[Self]) -> Self {
        let mut result = nfa_list[0].clone();
        for nfa in nfa_list.iter().skip(1) {
            result = result.or(nfa);
        }
        result
    }
    fn from_regex_tokens(
        origin: &str,
        tokens: &[(usize, RegexToken)],
    ) -> Result<Nfa, RegexSyntaxError> {
        use RegexSyntaxError::*;
        use RegexToken::*;
        let mut l_parens = vec![];
        let mut to_or = vec![];
        let mut term = vec![];
        for (i, (pos, token)) in tokens.iter().enumerate() {
            match (token, l_parens.is_empty()) {
                (LParen, _) => {
                    l_parens.push(i);
                }
                (RParen, _) => {
                    let start = l_parens.pop().ok_or_else(|| {
                        UnmatchedParentheses(format!("')' at {} in {}", pos, origin))
                    })?;
                    if l_parens.is_empty() {
                        term.push(Self::from_regex_tokens(origin, &tokens[start + 1..i])?);
                    }
                }
                (Star, true) => match term.pop() {
                    Some(nfa) => term.push(nfa.star()),
                    _ => return Err(NoElementToStar(format!("'*' at {} in {}", pos, origin))),
                },
                (Or, true) => {
                    to_or.push(Self::concat_all(&term));
                    term.clear();
                }
                (Char(c), true) => term.push(Self::from(Some(*c))),
                _ => {}
            }
        }
        if let Some(i) = l_parens.pop() {
            let pos = tokens[i].0;
            return Err(UnmatchedParentheses(format!(
                "'(' at {} in {}",
                pos, origin
            )));
        }
        to_or.push(Self::concat_all(&term));
        Ok(Self::or_all(&to_or))
    }
    /// Create an NFA from a regular expression.
    /// We only support the following syntax:
    /// ```txt
    /// <regex> ::= <regex> '|' <term>  | <term>
    /// <term> ::= <term> <factor> | epsilon
    /// <factor> ::= <factor> '*' | <base>
    /// <base> ::= <char> | '(' <regex> ')'
    /// ```
    /// Use backslash to escape special characters:
    /// `\*`, `\|`, `\(`, `\)`, `\\`, `\n`, `\r`, `\t`.
    pub fn from_regex(reg: &str) -> Result<Self, RegexSyntaxError> {
        let tokens = regex_tokenizer(reg)?;
        Self::from_regex_tokens(reg, &tokens)
    }
    pub fn epsilon_closure(&self, state: impl Borrow<BTreeSet<usize>>) -> BTreeSet<usize> {
        let state: &BTreeSet<_> = state.borrow();
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
    pub fn to_dfa(&self) -> (Dfa, String) {
        let (_, nfa) = self.re_index(0);

        let mut state_sets = vec![nfa.epsilon_closure(BTreeSet::from([nfa.start]))];
        let mut current = 0;
        let dfa_start = 0;
        let mut dfa_transitions = vec![];
        let mut markdown = "# NFA to DFA\n".to_string();
        markdown.push_str("\n## NFA\n");
        markdown.push_str(&nfa.to_inline_mermaid());
        markdown.push_str("\n## Process\n");
        markdown.push_str(&format!(
            "\n- $T_0 = \\{{ {} \\}}$\n",
            set2s(&state_sets[0])
        ));
        let mut r = Numberer::new();
        r.i(set2s(&state_sets[0]));
        let mut dfa_accept = BTreeSet::new();
        while current < state_sets.len() {
            let state_set = &state_sets[current];
            if state_set.contains(&nfa.accept) {
                dfa_accept.insert(current);
            }
            let mut transitions: BTreeMap<char, BTreeSet<usize>> = BTreeMap::new();
            for state in state_set {
                for (c, next_set) in nfa.transitions.get(state).unwrap_or(&Transition::new()) {
                    if let Some(c) = c {
                        transitions
                            .entry(*c)
                            .or_insert_with(BTreeSet::new)
                            .extend(nfa.epsilon_closure(next_set));
                    }
                }
            }
            let mut sorted_transitions = transitions.into_iter().collect::<Vec<_>>();
            sorted_transitions.sort_unstable_by_key(|(c, _)| *c);
            for (c, next_set) in sorted_transitions {
                let next = r.i(set2s(&next_set));
                markdown.push_str(&format!(
                    "\n- $\\varepsilon \\text{{-}} closure(move(T_{{{}}}, {})) = \\{{{}\\}} = T_{{{}}}$\n",
                    current,
                    katex_escape(c),
                    set2s(&next_set),
                    next
                ));
                dfa_transitions.push((current, c, next));
                if next == state_sets.len() {
                    state_sets.push(next_set);
                }
            }
            current += 1;
        }
        let dfa_json = DfaJson {
            start: dfa_start,
            accept: dfa_accept,
            transitions: dfa_transitions,
        };
        let dfa = Dfa::from(dfa_json);
        markdown.push_str("\n## DFA\n");
        markdown.push_str(&dfa.to_inline_mermaid());
        (dfa, markdown)
    }
    pub fn test(&self, s: &str) -> bool {
        let mut current = self.epsilon_closure(BTreeSet::from([self.start]));
        for c in s.chars() {
            let mut next = BTreeSet::new();
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
impl From<Token> for Nfa {
    fn from(c: Token) -> Self {
        if c.is_some() {
            Nfa {
                start: 0,
                accept: 1,
                transitions: [(0, [(c, [1].into())].into())].into(),
            }
        } else {
            Nfa {
                start: 0,
                accept: 0,
                transitions: [].into(),
            }
        }
    }
}
impl<T: Borrow<NfaJson>> From<T> for Nfa {
    fn from(nfa_json: T) -> Self {
        let json: &NfaJson = nfa_json.borrow();
        let mut nfa = Nfa {
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
impl<T: Borrow<Nfa>> From<T> for NfaJson {
    fn from(nfa: T) -> Self {
        let nfa: &Nfa = nfa.borrow();
        let mut transitions = vec![];
        for (state, map) in nfa.transitions.iter() {
            for (c, set) in map {
                for next in set {
                    transitions.push((*state, *c, *next));
                }
            }
        }
        transitions.sort_unstable();
        NfaJson {
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
        let nfa = Nfa::from_regex("a(b|c)*d").unwrap();
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
        let nfa = Nfa::from_regex("a(b|c)*d").unwrap();
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
        let nfa = Nfa::from_regex("_|((a|b)*|(c|d)*)").unwrap();
        assert_eq!(nfa.test("_"), true);
        assert_eq!(nfa.test("abbab"), true);
        assert_eq!(nfa.test("cdcd"), true);
        assert_eq!(nfa.test("abcd"), false);
        assert_eq!(nfa.test("_a"), false);
        assert_eq!(nfa.test("_abcd"), false);
    }

    #[test]
    fn priority_test() {
        let nfa_a = Nfa::from_regex("a*|b*").unwrap();
        let nfa_b = Nfa::from_regex("(a|b)*").unwrap();
        let nfa_c = Nfa::from_regex("a*b*").unwrap();
        let test_all = |s: &str| (nfa_a.test(s), nfa_b.test(s), nfa_c.test(s));
        assert_eq!(test_all("aaa"), (true, true, true));
        assert_eq!(test_all("bbb"), (true, true, true));
        assert_eq!(test_all("abb"), (false, true, true));
        assert_eq!(test_all("aba"), (false, true, false));
    }

    #[test]
    fn syntax_error_test() {
        // Unmatched '('
        let nfa = Nfa::from_regex("a(b|c*d");
        assert_eq!(
            nfa.unwrap_err().to_string(),
            "Unmatched Parentheses: '(' at 1 in a(b|c*d"
        );
        // Unmatched '('
        let nfa = Nfa::from_regex("a(b|c)*d)");
        assert_eq!(
            nfa.unwrap_err().to_string(),
            "Unmatched Parentheses: ')' at 8 in a(b|c)*d)"
        );
        // No element to star
        let nfa = Nfa::from_regex("a(*b|c)d");
        assert_eq!(
            nfa.unwrap_err().to_string(),
            "No Element to Star: '*' at 2 in a(*b|c)d"
        );

        let nfa = Nfa::from_regex("a|*c");
        assert_eq!(
            nfa.unwrap_err().to_string(),
            "No Element to Star: '*' at 2 in a|*c"
        );
    }

    #[test]
    fn json_test() {
        let nfa = Nfa::from_regex("a(b|c)*d").unwrap();
        let json = nfa.to_json();
        let nfa2 = Nfa::from_json(&json).unwrap();
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
        let nfa = Nfa::from_regex("a(b|c)*d").unwrap();
        let json = nfa.to_json();
        let nfa2 = Nfa::from_json(&json).unwrap();
        assert_eq!(nfa.to_json(), nfa2.to_json());
    }

    #[test]
    fn empty_test() {
        let nfa = Nfa::from_regex("").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("a"), false);

        let nfa = Nfa::from_regex("(|b)|").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("b"), true);
        assert_eq!(nfa.test("a"), false);
        assert_eq!(nfa.test("bb"), false);

        let nfa = Nfa::from_regex("|(|)").unwrap();
        assert_eq!(nfa.test(""), true);
        assert!(NfaJson::from(&nfa).transitions.is_empty());
    }

    #[test]
    fn star_test() {
        let nfa = Nfa::from_regex("(a*b)*").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("a"), false);
        assert_eq!(nfa.test("b"), true);
        assert_eq!(nfa.test("abbaab"), true);
        assert_eq!(nfa.test("ababa"), false);

        let nfa = Nfa::from_regex("(ab*)*").unwrap();
        assert_eq!(nfa.test(""), true);
        assert_eq!(nfa.test("a"), true);
        assert_eq!(nfa.test("b"), false);
        assert_eq!(nfa.test("abbaab"), true);
        assert_eq!(nfa.test("baa"), false);
    }

    #[test]
    fn escape_test() {
        let nfa = Nfa::from_regex(r"\*\|\(\)\n\r\t").unwrap();
        assert_eq!(nfa.test("*|()\n\r\t"), true);
        assert_eq!(nfa.test(r"\*\|\(\)\n\r\t"), false);
    }
}
