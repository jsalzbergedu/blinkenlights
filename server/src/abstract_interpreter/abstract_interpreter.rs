use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::ops::Add;
use std::ops::Sub;

use crate::ast::Statement;
use crate::ast::Program;
use crate::ast::Expr;
use crate::ast::StatementList;
use crate::ast::Labels;
use crate::lattice::AbstractProperty;
use crate::lattice::Lattice;

const MAX_ITERS: i64 = 1024 * 1024;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropertyCacheElement<T> where T: AbstractProperty + Sized + Clone + Eq + Debug {
    at_property: T,
    after_property: T,
    break_to_property: T
}


pub trait AbstractDomain<T> where T: AbstractProperty + Sized + Clone + Eq + Debug {
    fn assign(&self, x: &Expr, expr: &Expr, element: T) -> T;
    fn test(&self, expr: &Expr, element: T) -> T;
    fn not_test(&self, expr: &Expr, element: T) -> T;
    fn interpret_program(&self, program: &Program, labels: &Labels) -> HashMap<i64, PropertyCacheElement<T>> {
        match program {
            Program::Program(_, statement) => self.interpret(labels, &statement, T::bottom()),
        }
    }
    fn interpret(&self, labels: &Labels, statement: &Statement, element: T) -> HashMap<i64, PropertyCacheElement<T>> {
        match statement {
            Statement::Assign(id, x, y) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element.clone(), after_property: self.assign(x, y, element.clone()), break_to_property: T::bottom()});
                map
            },
            Statement::Skip(id) | Statement::Decl(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element.clone(), after_property: element.clone(), break_to_property: T::bottom()});
                map
            },
            Statement::IfThen(id, expr, st) => {
                let mut test = self.interpret(labels, st, self.test(expr, element.clone()));
                let not_test = self.not_test(expr, element.clone());
                test.insert(*id, PropertyCacheElement { at_property: element, after_property: test[&st.id()].after_property.clone().lub(&not_test.clone()), break_to_property: test[&st.id()].break_to_property.clone() } );
                test
            },
            Statement::IfThenElse(id, expr, st, sf) => {
                let mut test = self.interpret(labels, st, self.test(expr, element.clone()));
                let not_test = self.interpret(labels, sf, self.not_test(expr, element.clone()));
                test.insert(*id, PropertyCacheElement { at_property: element.clone(),
                                                        after_property: test[&st.id()].after_property.clone().lub(&not_test[&st.id()].after_property.clone()),
                                                        break_to_property: test[&st.id()].break_to_property.clone().lub(&not_test[&st.id()].break_to_property.clone()) } );
                test
            },
            Statement::While(id, expr, st) => {
                let mut iterate = PropertyCacheElement { at_property: T::bottom(), after_property: T::bottom(), break_to_property: T::bottom() };
                let mut iter = 0;
                let mut map = HashMap::new();
                while iter < MAX_ITERS - 1 {
                    let old_iterate = iterate.clone();
                    let at_interpretation = self.interpret(labels, st, self.test(expr, iterate.at_property.clone().lub(&element.clone())));
                    map.extend(at_interpretation.clone());
                    let at_property = at_interpretation[&st.id()].after_property.clone();
                    iterate = PropertyCacheElement {
                        at_property: at_property.clone(),
                        after_property: self.not_test(expr, at_property.clone()).lub(&self.interpret(labels, st, self.test(expr, at_property.clone()))[&st.id()].break_to_property.clone()),
                        break_to_property: T::bottom(),
                    };
                    if iterate == old_iterate {
                        break;
                    }
                    iter += 1;
                    if iter == MAX_ITERS {
                        panic!("Fixpoint did not converge");
                    }
                }
                map.insert(*id, PropertyCacheElement { at_property: iterate.at_property,
                                                       after_property: iterate.after_property,
                                                       break_to_property: T::bottom() });
                map
            },
            Statement::Break(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element.clone(), after_property: T::bottom(), break_to_property: element.clone()});
                map
            },
            Statement::Compound(id, sl) => {
                let mut sl_map = self.interpret_sl(labels, sl, element.clone());
                sl_map.insert(*id, PropertyCacheElement { at_property: element, after_property: sl_map[&sl.id()].after_property.clone(), break_to_property: sl_map[&sl.id()].break_to_property.clone() } );
                sl_map
            },
        }
    }
    fn interpret_sl(&self, labels: &Labels, sl: &StatementList, element: T) -> HashMap<i64, PropertyCacheElement<T>> {
        match sl {
            StatementList::Empty(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element.clone(), after_property: element, break_to_property: T::bottom()});
                map
            },
            StatementList::StatementList(id, sl, s) => {
                let mut map_sl = self.interpret_sl(labels, sl, element.clone());
                let map_s = self.interpret(labels, s, map_sl[&sl.id()].after_property.clone());
                map_sl.insert(*id, PropertyCacheElement { at_property: element, after_property: map_s[&s.id()].after_property.clone(), break_to_property: map_sl[&sl.id()].break_to_property.lub(&map_s[&s.id()].break_to_property.clone()) });
                map_sl.extend(map_s);
                map_sl
            },
        }
    }
}

// Some basic implementations

// For now, variables are not assoc'd with their environments.
// When they are, replace String with i64
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SetOfEnvironments(HashSet<BTreeMap<String, i64>>);

impl AbstractProperty for SetOfEnvironments {
    fn bottom() -> Self {
        let map = BTreeMap::new();
        SetOfEnvironments(HashSet::from([map]))
    }

    fn lub(&self, y: &Self) -> Self {
        match (self, y) {
            (SetOfEnvironments(x), SetOfEnvironments(y)) => SetOfEnvironments(x.union(&y).cloned().collect())
        }
    }

}

pub struct AssertionalSemantics();

impl AbstractDomain<SetOfEnvironments> for AssertionalSemantics {
    fn assign(&self, x: &Expr, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        match x {
            Expr::Variable(_, s) => {
                match environments {
                    SetOfEnvironments(e) => {
                        let mut output = HashSet::new();
                        for environment in e {
                            let mut output_environment = environment.clone();
                            println!("Setting {:?} to {:?}", s, expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))));
                            output_environment.insert(s.to_string(), expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))));

                            output.insert(output_environment);
                        }
                        SetOfEnvironments(output)
                    }
                }
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }
    fn test(&self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        let SetOfEnvironments(e) = environments;
        let mut output = HashSet::new();
        for environment in e {
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))) != 0.into() {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }

    fn not_test(&self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        let SetOfEnvironments(e) = environments;
        let mut output = HashSet::new();
        for environment in e {
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))) == 0.into() {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }
}

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
        println!("I'm adding! {:?} {:?}", self, rhs);
        println!("Result will be {:?} - {:?} = {:?}", self, (SignPropertyElement::Zero - rhs), self - (SignPropertyElement::Zero - rhs));
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

impl Lattice for SignPropertyElement {
    fn top() -> Self {
        SignPropertyElement::Top
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

impl AbstractDomain<SignProperty> for SignSemantics {
    fn assign(&self, x: &Expr, expr: &Expr, environments: SignProperty) -> SignProperty {
        println!("I'm Assigning! {:?} {:?} {:?}", x, expr, environments);
        match x {
            Expr::Variable(_, s) => {
                HashSet::<BTreeMap<String, SignPropertyElement>>::from(&environments).iter().map(|elt| {
                    let mut out = elt.clone();
                    println!("Assigning {:?} = {:?}", s, expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero)));
                    out.insert(s.to_owned(), expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero)));
                    out
                })
                    .fold(SignProperty::bottom(), |acc, map| {
                    acc.lub(&SignProperty(map))
                })
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }
    fn test(&self, expr: &Expr, environments: SignProperty) -> SignProperty {
        println!("Testing!! {:?} {:?}", expr, environments);
        HashSet::<BTreeMap<String, SignPropertyElement>>::from(&environments).iter().filter(|elt| {
            println!("filter will say: {:?} {:?}", elt, expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero)) != SignPropertyElement::Zero);
            expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero)) != SignPropertyElement::Zero
        }).fold(SignProperty::bottom(), |acc, map| {
            println!("lub will be: {:?}", acc.lub(&SignProperty(map.clone())));
            acc.lub(&SignProperty(map.clone()))
        })
    }

    fn not_test(&self, expr: &Expr, environments: SignProperty) -> SignProperty {
        HashSet::<BTreeMap<String, SignPropertyElement>>::from(&environments).iter().filter(|elt| {
            SignPropertyElement::Zero <= expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero))
        }).fold(SignProperty::bottom(), |acc, map| {
            acc.lub(&SignProperty(map.clone()))
        })
    }
}
