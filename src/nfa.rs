use std::{
    collections::{HashMap, HashSet},
    ops::{Add, BitOr, Mul, Range},
};
type NFAToken = Option<char>;
type NFATransition = HashMap<NFAToken, HashSet<usize>>;
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct NFA {
    /// States of the NFA.
    pub states: Range<usize>,
    /// The start state of the NFA.
    pub start: usize,
    /// The accept state of the NFA.
    /// If multiple accept states are needed, add a new state and transition to it from the original accept state.
    pub accept: usize,
    /// Transitions of the NFA.
    /// state -> (character -> states)
    /// The key None represents epsilon transitions.
    pub transitions: HashMap<usize, NFATransition>,
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
        let mut transitions = self
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
    pub fn or(&self, rhs: impl AsRef<Self>) -> NFA {
        let rhs = rhs.as_ref().re_index(self.states.end);
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
    pub fn concat(&self, rhs: impl AsRef<Self>) -> NFA {
        let rhs = rhs.as_ref().re_index(self.states.end);
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
}
impl<T: AsRef<NFA>> BitOr<T> for NFA {
    type Output = Self;
    fn bitor(self, rhs: T) -> Self {
        self.or(rhs)
    }
}
impl<T: AsRef<NFA>> Add<T> for NFA {
    type Output = Self;
    fn add(self, rhs: T) -> Self {
        self.concat(rhs)
    }
}
impl<T: AsRef<NFA>> Mul<T> for NFA {
    type Output = Self;
    fn mul(self, rhs: T) -> Self {
        self.concat(rhs)
    }
}
impl From<NFAToken> for NFA {
    fn from(c: NFAToken) -> Self {
        let mut transitions = HashMap::new();
        transitions.insert(0, NFATransition::from([(c, HashSet::from([1]))]));
        NFA {
            states: 0..2,
            start: 0,
            accept: 1,
            transitions,
        }
    }
}
impl From<char> for NFA {
    fn from(c: char) -> Self {
        Some(c).into()
    }
}
