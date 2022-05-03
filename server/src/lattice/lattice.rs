pub trait AbstractProperty {
    fn bottom() -> Self;
    fn lub(&self, y: &Self) -> Self;
    // An abstract property also has leq, but this is not used
}

pub trait Lattice: AbstractProperty {
    fn top() -> Self;
    fn leq(&self, y: &Self) -> bool;
    fn meet(&self, y: &Self) -> bool;
    fn join(&self, y: &Self) -> bool;
    // leq, meet required for the mathematical definition of a lattice
    // but not used in the library
}
