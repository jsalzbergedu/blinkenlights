use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt::Debug;

use crate::ast::Statement;
use crate::ast::Program;
use crate::ast::Expr;
use crate::ast::StatementList;
use crate::ast::Labels;
use crate::lattice::AbstractProperty;

// TODO fix the terminology. EG semantics, domain, property get mixed up here

/// The maximum number of iterations allowed for computing fixedpoints (i.e., while loops).
const MAX_ITERS: i64 = 1024 * 1024;

/// Collects at, after, and break-to properties.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropertyCacheElement<T> where T: AbstractProperty + Sized + Clone + Eq + Debug {
    pub at_property: T,
    pub after_property: T,
    pub break_to_property: T
}

impl <T> Default for PropertyCacheElement<T> where T: AbstractProperty + Sized + Clone + Eq + Debug {
    fn default() -> Self {
        Self { at_property: T::bottom(), after_property: T::bottom(), break_to_property: T::bottom() }
    }
}

/// The generic abstract interpreter.
/// Test, not_test and assign must over-approximate the assertional semantics of test, not_test
/// and assign for the interpreter to be correct wrt assertional semantics.
pub trait AbstractDomain<T> where T: AbstractProperty + Sized + Clone + Eq + Debug {
    /// Assign x to expr in the abstract element element.
    fn assign(&mut self, x: &Expr, expr: &Expr, element: T) -> T;
    fn test(&mut self, expr: &Expr, element: T) -> T;
    fn not_test(&mut self, expr: &Expr, element: T) -> T;
    fn interpret_program(&mut self, program: &Program, labels: &Labels) -> HashMap<i64, PropertyCacheElement<T>> {
        match program {
            Program::Program(_, statement) => self.interpret(labels, &statement, T::bottom()),
        }
    }
    fn interpret(&mut self, labels: &Labels, statement: &Statement, element: T) -> HashMap<i64, PropertyCacheElement<T>> {
        match statement {
            Statement::Assign(id, x, y) => {
                let mut map = HashMap::new();
                println!("Executing assign: at_property: {:?}, after_property: {:?}, break_to_property: {:?} ", element.clone(), self.assign(x, y, element.clone()), T::bottom());
                map.insert(*id, PropertyCacheElement { at_property: element.clone(), after_property: self.assign(x, y, element.clone()), break_to_property: T::bottom()});
                map
            },
            Statement::Skip(id) | Statement::Decl(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element.clone(), after_property: element.clone(), break_to_property: T::bottom()});
                map
            },
            Statement::IfThen(id, expr, st) => {
                let test_env = self.test(expr, element.clone());
                let mut test = self.interpret(labels, st, test_env);
                let not_test = self.not_test(expr, element.clone());
                test.insert(*id, PropertyCacheElement { at_property: element, after_property: test[&st.id()].after_property.clone().lub(&not_test.clone()), break_to_property: test[&st.id()].break_to_property.clone() } );
                test
            },
            Statement::IfThenElse(id, expr, st, sf) => {
                let test_env = self.test(expr, element.clone());
                let mut test = self.interpret(labels, st, test_env);
                let not_test_env = self.not_test(expr, element.clone());
                let not_test = self.interpret(labels, sf, not_test_env);
                test.insert(*id, PropertyCacheElement { at_property: element.clone(),
                                                        after_property: test[&st.id()].after_property.clone().lub(&not_test[&st.id()].after_property.clone()),
                                                        break_to_property: test[&st.id()].break_to_property.clone().lub(&not_test[&st.id()].break_to_property.clone()) } );
                test
            },
            Statement::While(id, expr, st) => {
                let mut iterate = PropertyCacheElement { at_property: T::bottom(), after_property: T::bottom(), break_to_property: T::bottom() };
                let mut iter = 0;
                let mut map = HashMap::new();
                while iter < MAX_ITERS {
                    let old_iterate = iterate.clone();
                    println!("Testing in while with: {:?}", iterate.at_property.clone().lub(&element.clone()));
                    println!("lhs lub: {:?}", element.clone());
                    println!("rhs lub: {:?}", iterate.at_property.clone());
                    let test_env = self.test(expr, iterate.at_property.clone().lub(&element.clone()));
                    let at_interpretation = self.interpret(labels, st, test_env);
                    map.extend(at_interpretation.clone());
                    let at_property = at_interpretation[&st.id()].after_property.clone();
                    iterate = PropertyCacheElement {
                        at_property: {at_property.clone().lub(&element)},
                        after_property: {self.not_test(expr, at_property.clone()).lub(&at_interpretation[&st.id()].break_to_property)},
                        break_to_property: T::bottom(),
                    };

                    if iterate == old_iterate {
                        break;
                    }
                    iter += 1;
                    if iter == MAX_ITERS {
                        panic!("Fixpoint did not converge {:?}", iterate);
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
    fn interpret_sl(&mut self, labels: &Labels, sl: &StatementList, element: T) -> HashMap<i64, PropertyCacheElement<T>> {
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
