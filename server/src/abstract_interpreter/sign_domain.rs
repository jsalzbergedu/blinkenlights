use std::{collections::{HashSet, BTreeMap}, cmp::Ordering, ops::{Sub, Add}};

use crate::lattice::AbstractProperty;

use super::{ExpressionReachability, CartesianValue};

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum SignPropertyElement {
    Bottom = 0,                  // bot
    StrictlyLessThanZero = 1,    // <00
    Zero = 2,                    // =00
    StrictlyGreaterThanZero = 3, // >00
    LessThanZero = 4,            // <=0
    NotZero = 5,                 // !=0
    GreaterThanZero = 6,         // >=0
    Top = 7,                     // top
}

impl From<i64> for SignPropertyElement {
    fn from(i: i64) -> Self {
        if i == 0 {
            SignPropertyElement::Zero
        } else if i > 0 {
            SignPropertyElement::StrictlyGreaterThanZero
        } else {
            SignPropertyElement::StrictlyLessThanZero
        }
    }
}

// An instantiation of the "focus" abstract domain
impl From<SignPropertyElement> for HashSet<SignPropertyElement> {
    fn from(elt: SignPropertyElement) -> Self {
        match elt {
            SignPropertyElement::Bottom => HashSet::from([SignPropertyElement::Bottom]),
            SignPropertyElement::StrictlyLessThanZero => HashSet::from([SignPropertyElement::StrictlyLessThanZero]),
            SignPropertyElement::Zero => HashSet::from([SignPropertyElement::Zero]),
            SignPropertyElement::StrictlyGreaterThanZero => HashSet::from([SignPropertyElement::StrictlyGreaterThanZero]),
            SignPropertyElement::GreaterThanZero => HashSet::from([SignPropertyElement::StrictlyGreaterThanZero, SignPropertyElement::Zero, SignPropertyElement::GreaterThanZero]),
            SignPropertyElement::NotZero => HashSet::from([SignPropertyElement::StrictlyLessThanZero, SignPropertyElement::StrictlyGreaterThanZero, SignPropertyElement::NotZero]),
            SignPropertyElement::LessThanZero => HashSet::from([SignPropertyElement::StrictlyLessThanZero, SignPropertyElement::Zero, SignPropertyElement::LessThanZero]),
            SignPropertyElement::Top => HashSet::from([SignPropertyElement::StrictlyLessThanZero, SignPropertyElement::Zero, SignPropertyElement::StrictlyGreaterThanZero, SignPropertyElement::Top]),
        }
    }
}

const MINUS_TABLE: [[SignPropertyElement; 8]; 8] = {
    let bot = SignPropertyElement::Bottom;
    let sl0 = SignPropertyElement::StrictlyLessThanZero;
    let zro = SignPropertyElement::Zero;
    let sg0 = SignPropertyElement::StrictlyGreaterThanZero;
    let lt0 = SignPropertyElement::LessThanZero;
    let nzr = SignPropertyElement::NotZero;
    let gt0 = SignPropertyElement::GreaterThanZero;
    let top = SignPropertyElement::Top;
    [   //         bot  <00  =00  >00  <=0  !=0  >=0  top
        /* bot */ [bot, bot, bot, bot, bot, bot, bot, bot],
        /* <00 */ [bot, top, sl0, sl0, top, top, sl0, top],
        /* =00 */ [bot, sg0, zro, sl0, gt0, nzr, lt0, top],
        /* >00 */ [bot, sg0, gt0, top, gt0, top, top, top],
        /* <=0 */ [bot, top, lt0, sl0, top, top, lt0, top],
        /* !=0 */ [bot, top, nzr, top, top, top, top, top],
        /* >=0 */ [bot, gt0, gt0, top, gt0, top, top, top],
        /* top */ [bot, top, top, top, top, top, top, top],
    ]
};

const ORD_TABLE: [[Option<Ordering>; 8]; 8] = {
    let les = Some(Ordering::Less);
    let eql = Some(Ordering::Equal);
    let gtr = Some(Ordering::Greater);
    let non = None;
    [   //         bot  <00  =00  >00  <=0  !=0  >=0  top
        /* bot */ [eql, les, les, les, les, les, les, les],
        /* <00 */ [gtr, eql, non, non, les, les, non, les],
        /* =00 */ [gtr, non, eql, non, les, non, les, les],
        /* >00 */ [gtr, non, non, eql, non, les, les, les],
        /* <=0 */ [gtr, gtr, gtr, non, eql, non, non, les],
        /* !=0 */ [gtr, gtr, non, gtr, non, eql, non, les],
        /* >=0 */ [gtr, non, gtr, gtr, non, non, eql, les],
        /* top */ [gtr, gtr, gtr, gtr, gtr, gtr, gtr, eql],
    ]
};


impl PartialOrd for SignPropertyElement {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        ORD_TABLE[*self as usize][*other as usize]
    }
}


impl Sub for SignPropertyElement {
    type Output = SignPropertyElement;

    fn sub(self, rhs: Self) -> Self::Output {
        MINUS_TABLE[self as usize][rhs as usize]
    }
}

impl Add for SignPropertyElement {
    type Output = SignPropertyElement;

    fn add(self, rhs: Self) -> Self::Output {
        self - (SignPropertyElement::Zero - rhs)
    }
}

const LUB_TABLE: [[SignPropertyElement; 8]; 8] = {
    let bot = SignPropertyElement::Bottom;
    let sl0 = SignPropertyElement::StrictlyLessThanZero;
    let zro = SignPropertyElement::Zero;
    let sg0 = SignPropertyElement::StrictlyGreaterThanZero;
    let lt0 = SignPropertyElement::LessThanZero;
    let nzr = SignPropertyElement::NotZero;
    let gt0 = SignPropertyElement::GreaterThanZero;
    let top = SignPropertyElement::Top;
    [   //         bot  <00  =00  >00  <=0  !=0  >=0  top
        /* bot */ [bot, sl0, zro, sg0, lt0, nzr, gt0, top],
        /* <00 */ [sl0, sl0, lt0, nzr, lt0, lt0, top, top],
        /* =00 */ [zro, lt0, zro, gt0, lt0, top, gt0, top],
        /* >00 */ [sg0, nzr, gt0, sg0, top, nzr, gt0, top],
        /* <=0 */ [lt0, lt0, lt0, top, lt0, top, top, top],
        /* !=0 */ [nzr, nzr, top, nzr, top, nzr, top, top],
        /* >=0 */ [gt0, top, gt0, gt0, top, top, gt0, top],
        /* top */ [top, top, top, top, top, top, top, top],
    ]
};

const GLB_TABLE: [[SignPropertyElement; 8]; 8] = {
    let bot = SignPropertyElement::Bottom;
    let sl0 = SignPropertyElement::StrictlyLessThanZero;
    let zro = SignPropertyElement::Zero;
    let sg0 = SignPropertyElement::StrictlyGreaterThanZero;
    let lt0 = SignPropertyElement::LessThanZero;
    let nzr = SignPropertyElement::NotZero;
    let gt0 = SignPropertyElement::GreaterThanZero;
    let top = SignPropertyElement::Top;
    [   //         bot  <00  =00  >00  <=0  !=0  >=0  top
        /* bot */ [bot, bot, bot, bot, bot, bot, bot, bot],
        /* <00 */ [bot, sl0, bot, bot, sl0, sl0, bot, sl0],
        /* =00 */ [bot, bot, zro, bot, zro, bot, zro, zro],
        /* >00 */ [bot, bot, bot, sg0, bot, sg0, sg0, sg0],
        /* <=0 */ [bot, sl0, zro, bot, lt0, sl0, zro, lt0],
        /* !=0 */ [bot, sl0, bot, sg0, sl0, nzr, sg0, nzr],
        /* >=0 */ [bot, bot, zro, sg0, zro, sg0, gt0, gt0],
        /* top */ [bot, sl0, zro, sg0, lt0, nzr, gt0, top],
    ]
};

impl AbstractProperty for SignPropertyElement {
    fn bottom() -> Self {
        SignPropertyElement::Bottom
    }

    fn lub(&self, y: &Self) -> Self {
        LUB_TABLE[*self as usize][*y as usize]
    }
}

impl From<bool> for SignPropertyElement {
    fn from(b: bool) -> Self {
        match b {
            true => Self::Top,
            false => Self::Zero,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SignProperty(BTreeMap<String, SignPropertyElement>);

// TODO FIX:
// Change to String -> a set of Sign Property Elements
// Then reimplement +, <=, >=, etc. as part of the focus adomain
// Then add a way to go back into (w/ lub)
// Does that actually make ANY sense? Hold on...
// Yes, you do _all of your ops_ in this "expanded" domain
// Then you only lub at the end :-)
// (Come back to this later!!)
impl From<&SignProperty> for HashSet<BTreeMap<String, SignPropertyElement>> {
    fn from(SignProperty(map): &SignProperty) -> Self {
        let mut environments = [
            BTreeMap::new(), // SignPropertyElement::Bottom,
            BTreeMap::new(), // SignPropertyElement::StrictlyLessThanZero,
            BTreeMap::new(), // SignPropertyElement::Zero,
            BTreeMap::new(), // SignPropertyElement::StrictlyGreaterThanZero,
            BTreeMap::new(), // SignPropertyElement::GreaterThanZero,
            BTreeMap::new(), // SignPropertyElement::NotZero,
            BTreeMap::new(), // SignPropertyElement::LessThanZero,
            BTreeMap::new(), // SignPropertyElement::Top,
        ];
        for (k, v) in map.into_iter().map(|(k, v)| (k, HashSet::<SignPropertyElement>::from(*v))) {
            for elt in v {
                environments[elt as usize].insert(k.to_owned(), elt);
            }
        }
        HashSet::from(environments)
    }
}

pub struct SignSemantics();

impl AbstractProperty for SignProperty {
    fn bottom() -> Self {
        SignProperty(BTreeMap::new())
    }

    fn lub(&self, y: &Self) -> Self {
        let SignProperty(x) = self;
        let SignProperty(y) = y.clone();
        let mut out = BTreeMap::new();
        for (key, value) in x.into_iter() {
            out.insert(key.to_string(), value.lub(y.get(key).unwrap_or(&SignPropertyElement::Bottom)));
        }
        for (key, value) in y.into_iter() {
            out.insert(key.to_string(), value.lub(x.get(&key).unwrap_or(&SignPropertyElement::Bottom)));
        }
        SignProperty(out)
    }
}

// Empirical design of the inverse operation

fn expand(s: SignPropertyElement) -> HashSet<i64> {
    match s {
        SignPropertyElement::Bottom => HashSet::new(),
        SignPropertyElement::StrictlyLessThanZero => HashSet::from([-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]),
        SignPropertyElement::Zero => HashSet::from([0]),
        SignPropertyElement::StrictlyGreaterThanZero => HashSet::from([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        SignPropertyElement::LessThanZero => HashSet::from([0, -1, -2, -3, -4, -5, -6, -7, -8, -9, -10]),
        SignPropertyElement::NotZero => HashSet::from([-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        SignPropertyElement::GreaterThanZero => HashSet::from([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
        SignPropertyElement::Top => HashSet::from([-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
    }
}

fn inv_op<F: Fn(i64, i64) -> i64>(target: SignPropertyElement, lhs: SignPropertyElement, rhs: SignPropertyElement, f: F) -> (SignPropertyElement, SignPropertyElement) {
    let lhs_possibilities = expand(lhs);
    let rhs_possibilities = expand(rhs);
    let target = expand(target);
    let mut lhs_restricted = HashSet::new();
    let mut rhs_restricted = HashSet::new();
    for x in &lhs_possibilities {
        for y in &rhs_possibilities {
            if target.contains(&f(*x, *y)) {
                lhs_restricted.insert(x);
                rhs_restricted.insert(y);
            }
        }
    }
    (lhs_restricted.into_iter().fold(SignPropertyElement::Bottom, |x, y| x.lub(&SignPropertyElement::from(*y))), rhs_restricted.into_iter().fold(SignPropertyElement::Bottom, |x, y| x.lub(&SignPropertyElement::from(*y))))
}

impl ExpressionReachability for SignPropertyElement {
    fn inv_eq(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        // Overapproximate target = 1 with target = StrictlyGreaterthanZero
        // This is because in the concrete, in C, booleans map to either 0 or 1
        if target >= Self::StrictlyGreaterThanZero {
            (GLB_TABLE[lhs as usize][rhs as usize], GLB_TABLE[lhs as usize][rhs as usize])
        } else if target == Self::Zero {
            Self::inv_neq(Self::Zero, lhs, rhs)
        } else {
            (Self::Bottom, Self::Bottom)
        }
    }

    fn inv_neq(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        if target >= Self::StrictlyGreaterThanZero {
            // Here you're restricting the lhs and the rhs to the possible values
            // where lhs != rhs.
            // The only case where you KNOW there are no values where lhs != rhs
            // is when both are zero.
            // Otherwise since they are all sets containing values including zero and other elements,
            // the zero could != the other elements, or the other elements could != each other.
            match (lhs, rhs) {
                (Self::Bottom, _) => (Self::Bottom, rhs),
                (_, Self::Bottom) => (lhs, Self::Bottom),
                (Self::Zero, Self::Zero) => (Self::Bottom, Self::Bottom),
                (_, _) => (lhs, rhs)
            }
        } else if target == Self::Zero {
            Self::inv_eq(Self::StrictlyGreaterThanZero, lhs, rhs)
        } else {
            (Self::Bottom, Self::Bottom)
        }
    }

    fn inv_add(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| x + y)
    }

    fn inv_sub(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| x - y)
    }

    fn inv_lt(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| if x < y {1} else {0})
    }

    fn inv_gt(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| if x > y {1} else {0})
    }

    fn inv_le(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| if x <= y {1} else {0})
    }

    fn inv_ge(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| if x >= y {1} else {0})
    }

    fn inv_nand(target: Self, lhs: Self, rhs: Self) -> (Self, Self) {
        inv_op(target, lhs, rhs, |x, y| if !(x != 0 && y != 0) {1} else {0})
    }
}

impl CartesianValue for SignPropertyElement {
    fn glb(self, other: Self) -> Self {
        GLB_TABLE[self as usize][other as usize]
    }

    fn nzr() -> Self {
        Self::NotZero
    }
}
