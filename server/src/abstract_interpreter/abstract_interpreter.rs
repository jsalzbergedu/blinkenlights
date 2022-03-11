use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;

use crate::ast::Statement;
use crate::ast::Program;
use crate::ast::Expr;
use crate::ast::StatementList;
use crate::ast::Labels;

const MAX_ITERS: i64 = i64::MAX;

pub trait AbstractProperty {
    fn bottom() -> Self;
    fn leq(&self, y: &Self) -> bool;
    fn lub(&self, y: Self) -> Self;
}

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
                test.insert(*id, PropertyCacheElement { at_property: element, after_property: test[&st.id()].after_property.clone().lub(not_test.clone()), break_to_property: test[&st.id()].break_to_property.clone() } );
                test
            },
            Statement::IfThenElse(id, expr, st, sf) => {
                let mut test = self.interpret(labels, st, self.test(expr, element.clone()));
                let not_test = self.interpret(labels, sf, self.not_test(expr, element.clone()));
                test.insert(*id, PropertyCacheElement { at_property: element.clone(),
                                                        after_property: test[&st.id()].after_property.clone().lub(not_test[&st.id()].after_property.clone()),
                                                        break_to_property: test[&st.id()].break_to_property.clone().lub(not_test[&st.id()].break_to_property.clone()) } );
                test
            },
            Statement::While(id, expr, st) => {
                let mut iterate = PropertyCacheElement { at_property: T::bottom(), after_property: T::bottom(), break_to_property: T::bottom() };
                let mut iter = 0;
                let mut map = HashMap::new();
                while iter < MAX_ITERS - 1 {
                    let old_iterate = iterate.clone();
                    let at_interpretation = self.interpret(labels, st, self.test(expr, iterate.at_property.clone().lub(element.clone())));
                    map.extend(at_interpretation.clone());
                    let at_property = at_interpretation[&st.id()].after_property.clone();
                    iterate = PropertyCacheElement {
                        at_property: at_property.clone(),
                        after_property: self.not_test(expr, at_property.clone()).lub(self.interpret(labels, st, self.test(expr, at_property.clone()))[&st.id()].break_to_property.clone()),
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
                map_sl.insert(*id, PropertyCacheElement { at_property: element, after_property: map_s[&s.id()].after_property.clone(), break_to_property: map_sl[&sl.id()].break_to_property.lub(map_s[&s.id()].break_to_property.clone()) });
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
        let mut set = HashSet::new();
        set.insert(map);
        SetOfEnvironments(set)
    }

    fn leq(&self, y: &Self) -> bool {
        let SetOfEnvironments(x) = self;
        let SetOfEnvironments(y) = y;
        x.iter().all(|element| y.contains(element))
    }

    fn lub(&self, y: Self) -> Self {
        let SetOfEnvironments(x) = self;
        let SetOfEnvironments(y) = y.clone();
        SetOfEnvironments(x.union(&y).cloned().collect())
    }
}

pub struct AssertionalSemantics();

impl AbstractDomain<SetOfEnvironments> for AssertionalSemantics {
    fn assign(&self, x: &Expr, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        match x {
            Expr::Variable(_, s) => {
                let SetOfEnvironments(e) = environments;
                let mut output = HashSet::new();
                for environment in e {
                    let mut output_environment = environment.clone();
                    output_environment.insert(s.to_string(), expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0))));

                    output.insert(output_environment);
                }
                SetOfEnvironments(output)
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }
    fn test(&self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        let SetOfEnvironments(e) = environments;
        let mut output = HashSet::new();
        for environment in e {
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0))) > 0 {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }

    fn not_test(&self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
        let SetOfEnvironments(e) = environments;
        let mut output = HashSet::new();
        for environment in e {
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0))) == 0 {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }
}
