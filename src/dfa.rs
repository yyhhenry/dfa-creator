use crate::{
    nfa::{NFAJson, NFA},
    numberer::{set2s, DisjointSet, Numberer},
};
use serde::{Deserialize, Serialize};
use std::{
    borrow::Borrow,
    collections::{BTreeMap, BTreeSet},
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum FromJsonError {
    #[error("From Json Error: {0}")]
    SyntaxError(#[from] serde_json::error::Error),
}

type Token = char;
type Transition = BTreeMap<Token, usize>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DFAJson {
    pub start: usize,
    pub accept: BTreeSet<usize>,
    pub transitions: Vec<(usize, Token, usize)>,
}
impl DFAJson {
    /// Re-index the DFAJson to start from `index`.
    /// Returns the new size of the DFAJson and the re-indexed DFAJson.
    pub fn re_index(&self, index: usize) -> (usize, Self) {
        let mut r = Numberer::from(index);
        let mut states: Vec<_> = self
            .transitions
            .iter()
            .flat_map(|(s, _, n)| [*s, *n])
            .chain([self.start])
            .chain(self.accept.iter().cloned())
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
        serde_json::to_string(self).unwrap()
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
        format!("\n```mermaid\n{}\n```\n", mermaid)
    }
    pub fn to_markdown(&self, title: &str, description: &str) -> String {
        let mermaid = self.to_inline_mermaid();
        format!("# {}\n\n{}\n{}", title, description, mermaid)
    }
}

#[derive(Debug, Clone)]
pub struct DFA {
    /// The start state of the DFA.
    start: usize,
    /// The set of accept states in the DFA.
    accept: BTreeSet<usize>,
    /// The transition function of the DFA.
    /// state -> (token -> state)
    transitions: BTreeMap<usize, Transition>,
}
impl DFA {
    /// Re-index the DFA to start from `index`.
    /// Returns the new size of the DFA and the re-indexed DFA.
    pub fn re_index(&self, index: usize) -> (usize, DFA) {
        let dfa_json: DFAJson = self.into();
        let (size, dfa_json) = dfa_json.re_index(index);
        (size, Self::from(dfa_json))
    }
    /// Merge the states by the disjoint set.
    /// You should ensure that the disjoint set is generated from the same DFA.
    /// In other words, the DFA should be re-indexed from 0 before merging.
    pub fn merge_by(&self, m: DisjointSet) -> Self {
        let dfa_json: DFAJson = self.into();
        let dfa_json = dfa_json.merge_by(m);
        Self::from(dfa_json)
    }
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
            .or_insert_with(BTreeMap::new)
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
    /// Remove the unreachable states in the DFA.
    /// Returns the new DFA without unreachable states.
    pub fn remove_unreachable(&self) -> Self {
        let mut stack = vec![self.start];
        let mut reachable = BTreeSet::from([self.start]);
        while let Some(state) = stack.pop() {
            if let Some(transition) = self.transitions.get(&state) {
                for &to in transition.values() {
                    if reachable.insert(to) {
                        stack.push(to);
                    }
                }
            }
        }
        let mut dfa_json: DFAJson = self.into();
        dfa_json.accept = dfa_json.accept.intersection(&reachable).cloned().collect();
        dfa_json.transitions = dfa_json
            .transitions
            .into_iter()
            .filter(|(s, _, n)| reachable.contains(s) && reachable.contains(n))
            .collect();
        Self::from(dfa_json)
    }
    /// Minimize the DFA.
    /// Returns the minimized DFA and the description of the minimization process.
    /// The description is a markdown string.
    pub fn minimize(&self) -> (Self, String) {
        let (size, dfa) = self.remove_unreachable().re_index(0);
        let mut markdown = "# Minimization of DFA\n".to_string();
        markdown.push_str("\n## Initial DFA\n");
        markdown.push_str(&dfa.to_inline_mermaid());

        let mut groups = vec![BTreeSet::new(), BTreeSet::new()];
        for i in 0..size {
            let group = dfa.accept.contains(&i) as usize;
            groups[group].insert(i);
        }
        fn get_groups_of(groups: &Vec<BTreeSet<usize>>) -> BTreeMap<usize, usize> {
            groups
                .iter()
                .enumerate()
                .flat_map(|(i, group)| group.iter().map(move |&s| (s, i)))
                .collect()
        }
        /// Find the (g, c) that group g can be divided by token c.
        fn find_break_point(dfa: &DFA, groups: &Vec<BTreeSet<usize>>) -> Option<(usize, Token)> {
            let group_of = get_groups_of(groups);
            fn find_group_break_point(
                dfa: &DFA,
                group: &BTreeSet<usize>,
                group_of: &BTreeMap<usize, usize>,
            ) -> Option<Token> {
                let mut next_c = BTreeSet::new();
                for &s in group {
                    if let Some(transition) = dfa.transitions.get(&s) {
                        for c in transition.keys() {
                            next_c.insert(*c);
                        }
                    }
                }
                for c in next_c {
                    let mut next_group = BTreeMap::new();
                    for &s in group {
                        let to = dfa
                            .transitions
                            .get(&s)
                            .and_then(|t| t.get(&c))
                            .map(|&to| group_of[&to]);
                        next_group.entry(to).or_insert_with(BTreeSet::new).insert(s);
                    }
                    if next_group.len() > 1 {
                        return Some(c);
                    }
                }
                None
            }
            for (g, group) in groups.iter().enumerate() {
                if let Some(c) = find_group_break_point(dfa, group, &group_of) {
                    return Some((g, c));
                }
            }
            None
        }
        fn groups2s(index: &mut usize, groups: &Vec<BTreeSet<usize>>) -> String {
            let groups: Vec<_> = groups
                .iter()
                .map(|g| format!("\\{{ {} \\}}", set2s(g)))
                .collect();
            let i = *index;
            *index += 1;
            format!("\n$ P_{{{}}} = ({}) $\n", i, groups.join(""))
        }
        markdown.push_str("\n## Minimization Process\n");
        let mut index = 0;
        markdown.push_str(&groups2s(&mut index, &groups));
        while let Some((g, c)) = find_break_point(&dfa, &groups) {
            markdown.push_str(&format!(
                "\n$\\{{{}\\}}$ can be divided by {}\n",
                set2s(&groups[g]),
                c
            ));
            let group_of = get_groups_of(&groups);
            let mut new_groups = BTreeMap::new();
            for &s in &groups[g] {
                let next = dfa.transitions.get(&s).and_then(|t| t.get(&c).cloned());
                if let Some(next) = next {
                    let next_g = group_of[&next];
                    new_groups
                        .entry(Some(next_g))
                        .or_insert_with(BTreeSet::new)
                        .insert(s);
                    markdown.push_str(&format!(
                        "\n{} with {} goes to {} in $\\{{ {} \\}}$\n",
                        s,
                        c,
                        next,
                        set2s(&groups[next_g])
                    ));
                } else {
                    new_groups
                        .entry(None)
                        .or_insert_with(BTreeSet::new)
                        .insert(s);
                    markdown.push_str(&format!("\n{} cannot go with {}\n", s, c));
                }
            }
            groups.remove(g);
            groups.extend(new_groups.into_iter().map(|(_, g)| g));
            groups.sort_unstable_by_key(|g| *g.first().unwrap());
            markdown.push_str(&groups2s(&mut index, &groups));
        }
        markdown.push_str("\n## Minimized DFA\n");
        let mut set = DisjointSet::new(size);
        for group in groups.into_iter() {
            let g: Vec<_> = group.into_iter().collect();
            for i in 1..g.len() {
                set.union(g[0], g[i]);
            }
        }
        let dfa = dfa.merge_by(set);
        markdown.push_str(&dfa.to_inline_mermaid());
        (dfa, markdown)
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
            transitions: BTreeMap::new(),
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
        transitions.sort_unstable();
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
    fn basic_test() {
        let nfa = NFA::from_regex("a(b|c)*d").unwrap();
        let (dfa, _) = nfa.to_dfa();
        let nfa_1 = dfa.to_nfa();
        let test_all = |s: &str| {
            let ans = nfa.test(s);
            assert_eq!(dfa.test(s), ans);
            assert_eq!(nfa_1.test(s), ans);
        };
        let tests = [
            "ad",
            "abd",
            "acd",
            "abbd",
            "abccccbcd",
            "a",
            "aabcccd",
            "abccc",
            "_",
        ];
        for s in tests {
            test_all(s);
        }
    }

    #[test]
    fn remove_unreachable_test() {
        let dfa_json = DFAJson {
            start: 0,
            accept: [1, 2].into(),
            transitions: vec![(0, 'a', 1), (0, 'b', 1), (2, 'a', 1)],
        };
        let dfa = DFA::from(&dfa_json).remove_unreachable();
        let result_json = DFAJson {
            start: 0,
            accept: [1].into(),
            transitions: vec![(0, 'a', 1), (0, 'b', 1)],
        };
        assert_eq!(dfa.to_json(), result_json.to_json());
    }

    #[test]
    fn minimize_test() {
        let dfa_json = DFAJson {
            start: 0,
            accept: [5].into(),
            transitions: vec![
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 3),
                (1, 'b', 4),
                (2, 'a', 4),
                (2, 'b', 3),
                (3, 'a', 5),
                (3, 'b', 5),
                (4, 'a', 5),
                (4, 'b', 5),
            ],
        };
        let dfa = DFA::from(&dfa_json).minimize().0;
        let result_json = DFAJson {
            start: 0,
            accept: [3].into(),
            transitions: vec![
                (0, 'a', 1),
                (0, 'b', 1),
                (1, 'a', 2),
                (1, 'b', 2),
                (2, 'a', 3),
                (2, 'b', 3),
            ],
        };
        assert_eq!(dfa.to_json(), result_json.to_json());
    }
}
