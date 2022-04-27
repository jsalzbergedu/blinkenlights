// Cartesian Domain
// cartesian relationship inverter, will go in the sign domain, -- NO! this guy takes an abstraction of a cartesian relation inverter
// accessiblity eval, test, and not test
// NANDS. (as specd in the book).
// Actually, your elaborate step wouldn't work.
use std::{collections::BTreeMap, ops::{Sub, Add}, fmt::Debug};
use std::hash::Hash;

use crate::{lattice::AbstractProperty, ast::Expr};

use super::AbstractDomain;

/// Collects methods that restrict the input parameters
/// to those that result in the target value under a relation/expression.
/// To give a concrete example,
/// in the concrete, we may have a relation - with the input parameters
/// {1, 2} and {3}. This means there may exist actual executions of the program
/// in which the left hand side of the minus is 1 or 2 and the right hand side of the minus is a 3.
/// Therefore there may be actual executions of this program where the result is -2 or -1, so the
/// resulting set is {-2, -1}.
/// Suppose our target set is {-1}. The only elements of the left hand side and right hand side
/// that result in the target would be 1 and 3 respectively. So in the concrete, we restrict the left
/// hand side and the right hand side to {1} {3}.
///
///
/// Methods of this trait are expected to overapproximate those reachability semantics.
pub trait ExpressionReachability: Sized {
    // These two are the guys you really care about:
    // inv eq and inv neq
    // bc those give you eq 0 and neq 0
    // Which will properly restrict your lhs and rhs sets.
    // Do you even need the rest at all? I don't think so
    fn inv_eq(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_neq(target: Self, lhs: Self, rhs: Self) -> (Self, Self);

    // These are used in defining the arithmetic evaluator
    // for inverse reachability
    fn inv_add(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_sub(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_lt(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_gt(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_le(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_ge(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
    fn inv_nand(target: Self, lhs: Self, rhs: Self) -> (Self, Self);
}

pub trait CartesianValue : AbstractProperty + Clone + PartialEq + Eq + Debug + PartialOrd + Add<Output=Self> + Sub<Output=Self> + From<i64> + From<bool> + Hash + ExpressionReachability {
    fn glb(self, other: Self) -> Self;

    // A peculiarity: we need an overapproximation of nonzero
    // in the abstract for test, because we use nonzero to represent
    // true and zero to represent false.
    // For soundness, nonzero must overapproximate the concrete set
    // of integers with zero removed.
    fn nzr() -> Self;
}

// We'll need to build an eval first, that uses these
// Then after that, we can build an eval

#[derive(PartialOrd, Hash, PartialEq, Eq, Clone, Debug)]
pub struct CartesianProperty<P> where P: CartesianValue {
    map: BTreeMap<String, P>,
}

impl <P> CartesianProperty<P> where P: CartesianValue {
    fn glb(self, other: Self) -> Self {
        let map1 = self.map;
        let map2 = other.map;
        let mut out = BTreeMap::<String, P>::new();
        for k in map1.keys().chain(map2.keys()) {
            out.insert(k.to_owned(), map1.get(k).unwrap_or(&P::from(0)).to_owned().glb(map2.get(k).unwrap_or(&P::from(0)).to_owned()));
        }
        CartesianProperty { map: out }
    }
}

impl <P> AbstractProperty for CartesianProperty<P> where P: CartesianValue {
    fn bottom() -> Self {
        CartesianProperty { map: BTreeMap::new() }
    }

    fn lub(&self, y: &Self) -> Self {
        let x = self.map.clone();
        let y = y.map.clone();
        let mut map = BTreeMap::new();
        for (key, value) in x.clone().into_iter() {
            map.insert(key.to_string(), value.lub(y.get(&key).unwrap_or(&P::bottom())));
        }
        for (key, value) in y.into_iter() {
            map.insert(key.to_string(), value.lub(x.get(&key).unwrap_or(&P::bottom())));
        }
        CartesianProperty { map }
    }
}

fn eval_accesibility<P>(expr: &Expr, target: P, mut environment: CartesianProperty<P>) -> CartesianProperty<P> where P: CartesianValue {
    match expr {
        Expr::Variable(_, s) => {
            environment.map.insert(s.to_owned(), environment.map.get(s).unwrap_or(&P::from(0)).to_owned().glb(target));
            environment
        },
        Expr::Constant(_, c) => {
            if P::from(*c).glb(target) != P::bottom() {
                environment
            } else {
                CartesianProperty::bottom()
            }
        },
        Expr::Addition(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_add(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::Subtraction(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_sub(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::Equal(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_eq(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::NotEqual(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_neq(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::LessThan(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_lt(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::GreaterThan(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_gt(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::LessThanEqual(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_le(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::GreaterThanEqual(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_ge(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
        Expr::Nand(_, e1, e2) => {
            let forward_lhs = e1.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let forward_rhs = e2.eval(&|(_, s)| environment.map.get(s).unwrap_or(&P::from(0)).to_owned());
            let (lhs, rhs) = P::inv_nand(target, forward_lhs, forward_rhs);
            eval_accesibility(e1, lhs, environment.clone()).glb(eval_accesibility(e2, rhs, environment))
        },
    }
}

pub struct CartesianSemantics();

impl <P> AbstractDomain<CartesianProperty<P>> for CartesianSemantics where P: CartesianValue {
    fn assign(&mut self, x: &Expr, expr: &Expr, environments: CartesianProperty<P>) -> CartesianProperty<P> {
        match x {
            Expr::Variable(_, s) => {
                let mut out = environments.map.clone();
                out.insert(s.to_owned(), expr.eval(&|(_, s)| environments.map.get(s).unwrap_or(&P::from(0)).to_owned()));
                CartesianProperty { map: out }
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }

    fn test(&mut self, expr: &Expr, element: CartesianProperty<P>) -> CartesianProperty<P> {
        eval_accesibility(expr, P::nzr(), element)
    }

    fn not_test(&mut self, expr: &Expr, element: CartesianProperty<P>) -> CartesianProperty<P> {
        eval_accesibility(expr, P::from(0), element)
    }
}


