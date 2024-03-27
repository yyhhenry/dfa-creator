use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Numberer<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    index: usize,
    map: HashMap<T, usize>,
}
impl<T> Numberer<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    pub fn new() -> Self {
        Self {
            index: 0,
            map: HashMap::new(),
        }
    }
    pub fn len(&self) -> usize {
        self.map.len()
    }
    pub fn end(self) -> usize {
        self.index
    }
    pub fn i(&mut self, item: T) -> usize {
        self.map
            .entry(item)
            .or_insert_with(|| {
                let index = self.index;
                self.index += 1;
                index
            })
            .clone()
    }
}
impl<T> From<usize> for Numberer<T>
where
    T: Clone + Eq + std::hash::Hash,
{
    fn from(index: usize) -> Self {
        Self {
            index,
            map: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DisjointSet {
    fa: Vec<usize>,
}
impl DisjointSet {
    pub fn new(n: usize) -> Self {
        Self {
            fa: (0..n).collect(),
        }
    }
    pub fn len(&self) -> usize {
        self.fa.len()
    }
    pub fn find(&mut self, x: usize) -> usize {
        if self.fa[x] != x {
            self.fa[x] = self.find(self.fa[x]);
        }
        self.fa[x]
    }
    pub fn union(&mut self, x: usize, y: usize) {
        let x = self.find(x);
        let y = self.find(y);
        if x != y {
            self.fa[x] = y;
        }
    }
    pub fn same(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
    /// Returns a map from the original index to the new index.
    /// The new index is indexed from 0.
    pub fn to_map(mut self) -> HashMap<usize, usize> {
        let mut r = Numberer::new();
        (0..self.len()).map(|i| (i, r.i(self.find(i)))).collect()
    }
}
