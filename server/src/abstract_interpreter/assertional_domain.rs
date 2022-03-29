use std::collections::{HashSet, BTreeMap};

use crate::{lattice::AbstractProperty, ast::Expr};

use super::AbstractDomain;

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
    fn assign(&mut self, x: &Expr, expr: &Expr
              , environments: SetOfEnvironments) -> SetOfEnvironments {
        match x {
            Expr::Variable(_, s) => {
                match environments {
                    SetOfEnvironments(e) => {
                        let mut output = HashSet::new();
                        for environment in e {
                            let mut output_environment = environment.clone();
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
    fn test(&mut self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        let SetOfEnvironments(e) = environments;
        let mut output = HashSet::new();
        for environment in e {
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))) != 0 {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }

    fn not_test(&mut self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        let SetOfEnvironments(e) = environments;
        let mut output = HashSet::new();
        for environment in e {
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))) == 0 {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }
}

