use std::collections::HashMap;

use crate::ast::Statement;
use crate::ast::Expr;
use crate::ast::StatementList;
use crate::ast::Labels;

const MAX_ITERS: i64 = i64::MAX;

pub trait AbstractProperty {
    fn bottom() -> Self;
    fn leq(x: Self, y: Self) -> bool;
    fn lub(x: Self, y: Self) -> Self;
}

pub trait AbstractDomain<T> where T: AbstractProperty + Sized + Copy + Clone + Eq {
    fn bottom(&self) -> T;
    fn lub(&self, x: T, y: T) -> T;
    fn assign(&self, x: &Expr, expr: &Expr, abstract_element: T) -> T;
    fn test(&self, expr: &Expr, abstract_element: T) -> T;
    fn not_test(&self, expr: &Expr, abstract_element: T) -> T;
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct PropertyCacheElement<T> where T: AbstractProperty + Sized + Copy + Clone + Eq {
    at_property: T,
    after_property: T,
    break_to_property: T
}

impl <T> dyn AbstractDomain<T> where T: AbstractProperty + Sized + PartialOrd + Copy + Clone + Eq {
    pub fn interpret(&self, labels: &Labels, statement: &Statement, element: T) -> HashMap<i64, PropertyCacheElement<T>> {
        match statement {
            Statement::Assign(id, x, y) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element, after_property: self.assign(x, y, element), break_to_property: self.bottom()});
                map
            },
            Statement::Skip(id) | Statement::Decl(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element, after_property: element, break_to_property: self.bottom()});
                map
            },
            Statement::IfThen(id, expr, st) => {
                let mut test = self.interpret(labels, st, self.test(expr, element));
                let not_test = self.not_test(expr, element);
                test.insert(*id, PropertyCacheElement { at_property: element, after_property: self.lub(test[&st.id()].after_property, not_test), break_to_property: test[&st.id()].break_to_property } );
                test
            },
            Statement::IfThenElse(id, expr, st, sf) => {
                let mut test = self.interpret(labels, st, self.test(expr, element));
                let not_test = self.interpret(labels, sf, self.not_test(expr, element));
                test.insert(*id, PropertyCacheElement { at_property: element,
                                                        after_property: self.lub(test[&st.id()].after_property, not_test[&st.id()].after_property),
                                                        break_to_property: self.lub(test[&st.id()].break_to_property, not_test[&st.id()].break_to_property) } );
                test
            },
            Statement::While(id, expr, st) => {
                let mut invariant = PropertyCacheElement { at_property: element, after_property: self.bottom(), break_to_property: self.bottom() };
                let mut iter = 0;
                while iter < MAX_ITERS - 1 {
                    let old_invariant = invariant;
                    invariant.after_property = self.lub(invariant.after_property, self.lub(element, self.interpret(labels, st, self.test(expr, element))[&st.id()].after_property));
                    invariant.break_to_property = self.lub(self.not_test(expr, invariant.after_property), invariant.break_to_property);
                    if invariant == old_invariant {
                        break;
                    }
                    iter += 1;
                    if iter == MAX_ITERS {
                        panic!("Fixpoint did not converge");
                    }
                }
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: invariant.at_property,
                                                       after_property: invariant.after_property,
                                                       break_to_property: invariant.break_to_property });
                map
            },
            Statement::Break(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element, after_property: self.bottom(), break_to_property: element});
                map
            },
            Statement::Compound(id, sl) => {
                let mut sl_map = self.interpret_sl(labels, sl, element);
                sl_map.insert(*id, PropertyCacheElement { at_property: element, after_property: sl_map[&sl.id()].after_property, break_to_property: sl_map[&sl.id()].break_to_property } );
                sl_map
            },
        }
    }

    pub fn interpret_sl(&self, labels: &Labels, sl: &StatementList, element: T) -> HashMap<i64, PropertyCacheElement<T>> {
        match sl {
            StatementList::Empty(id) => {
                let mut map = HashMap::new();
                map.insert(*id, PropertyCacheElement { at_property: element, after_property: self.bottom(), break_to_property: self.bottom()});
                map
            },
            StatementList::StatementList(id, sl, s) => {
                let mut map_sl = self.interpret_sl(labels, sl, element);
                let map_s = self.interpret(labels, s, element);
                map_sl.insert(*id, PropertyCacheElement { at_property: element, after_property: map_s[&s.id()].after_property, break_to_property: map_s[&s.id()].after_property });
                map_sl.extend(map_s);
                map_sl
            },
        }
    }
}
