use std::{
    collections::HashMap,
    ops::{BitOr, Range},
};

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
    pub transitions: HashMap<usize, HashMap<Option<char>, Vec<usize>>>,
}
impl NFA {
    pub fn re_index(&self, offset: usize) -> Self {
        let mut transitions = HashMap::new();
        for (state, map) in &self.transitions {
            let mut new_map = HashMap::new();
            for (c, states) in map {
                let new_states = states.iter().map(|&s| s + offset).collect();
                new_map.insert(*c, new_states);
            }
            transitions.insert(state + offset, new_map);
        }
        NFA {
            states: offset..offset + self.states.len(),
            start: self.start + offset,
            accept: self.accept + offset,
            transitions,
        }
    }
    pub fn star(&self) -> NFA {
        unimplemented!()
    }
}
impl<T: AsRef<NFA>> BitOr<T> for NFA {
    type Output = Self;
    fn bitor(self, rhs: T) -> Self {
        let rhs = rhs.as_ref().re_index(self.states.end);
        let mut transitions = self.transitions;
        for (state, map) in rhs.transitions {
            transitions.insert(state, map);
        }
        transitions.insert(self.accept, HashMap::from([(None, vec![rhs.start])]));
        NFA {
            states: self.states.start..rhs.states.end,
            start: self.start,
            accept: rhs.accept,
            transitions,
        }
    }
}
