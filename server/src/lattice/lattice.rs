pub trait AbstractProperty {
    fn bottom() -> Self;
    fn lub(&self, y: &Self) -> Self;
    // An abstract property also has leq, but this is not used
}

pub trait Lattice: AbstractProperty {
    fn top() -> Self;
    // leq, meet required for the mathematical definition of a lattice
    // but not used in the library
}
