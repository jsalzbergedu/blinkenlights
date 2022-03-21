use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::hash_map::DefaultHasher;
use std::fmt::Debug;
use std::hash::Hash;
use std::hash::Hasher;
use std::ops::Add;
use std::ops::Sub;
use std::sync::Arc;
use std::sync::Mutex;
use lazy_static::lazy_static;
use rusqlite::Params;
use z3::ast::Ast;
use z3::{Config, Context, Solver};

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
        // println!("interpreting, {:?} {:?}", statement.clone(), element.clone());
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
                while iter < MAX_ITERS {
                    println!("At iteration number: {:?}", iter);
                    // println!("{:?}", iterate);
                    let old_iterate = iterate.clone();
                    let at_interpretation = self.interpret(labels, st, self.test(expr, iterate.at_property.clone().lub(&element.clone())));
                    // println!("at interpretation! {:?}", at_interpretation.clone());
                    map.extend(at_interpretation.clone());
                    let at_property = at_interpretation[&st.id()].after_property.clone();
                    iterate = PropertyCacheElement {
                        at_property: at_property.clone().lub(&element),
                        after_property: self.not_test(expr, at_property.clone()).lub(&self.interpret(labels, st, self.test(expr, at_property.clone()))[&st.id()].break_to_property.clone()),
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
            if expr.eval(&(|(_, s)| *environment.get(s).unwrap_or(&0.into()))) != 0 {
                output.insert(environment);
            }
        }
        SetOfEnvironments(output)
    }

    fn not_test(&self, expr: &Expr, environments: SetOfEnvironments) -> SetOfEnvironments {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    Name(String),
    Literal(i64),
    Addition(Box<Predicate>, Box<Predicate>),
    Subtraction(Box<Predicate>, Box<Predicate>),
    Equal(Box<Predicate>, Box<Predicate>),
    NotEqual(Box<Predicate>, Box<Predicate>),
    LessThan(Box<Predicate>, Box<Predicate>),
    LessThanEqual(Box<Predicate>, Box<Predicate>),
    GreaterThan(Box<Predicate>, Box<Predicate>),
    GreaterThanEqual(Box<Predicate>, Box<Predicate>),
    And(Box<Predicate>, Box<Predicate>),
    Not(Box<Predicate>),
    Implies(Box<Predicate>, Box<Predicate>)
}

impl Predicate {
    fn rename(&self, map: &HashMap<String, String>) -> Self {
        match self {
            Predicate::Name(s) => Predicate::Name(map.get(s).to_owned().unwrap_or(s).clone()),
            Predicate::Literal(i) => Predicate::Literal(*i),
            Predicate::Addition(l, r) => {
                Predicate::Addition(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::Subtraction(l, r) => {
                Predicate::Subtraction(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::Equal(l, r) => {
                Predicate::Equal(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::NotEqual(l, r) => {
                Predicate::NotEqual(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::LessThan(l, r) => {
                Predicate::LessThan(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::LessThanEqual(l, r) => {
                Predicate::LessThanEqual(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::GreaterThan(l, r) => {
                Predicate::GreaterThan(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::GreaterThanEqual(l, r) => {
                Predicate::GreaterThanEqual(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::And(l, r) => {
                Predicate::And(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::Implies(l, r) => {
                Predicate::Implies(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::Not(e) => {
                Predicate::Not(Box::new(e.rename(map)))
            },
        }
    }

    fn into_sat<'a>(&'a self, ctx: &'a Context) -> Z3Repr<'a> {
        match &self {
            Predicate::Literal(i) => {
                Z3Repr::Int(z3::ast::Int::from_i64(ctx, *i))
            },
            Predicate::Name(s) => {
                Z3Repr::Int(z3::ast::Int::new_const(ctx, s.to_owned()))
            },
            Predicate::Addition(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Int(z3::ast::Int::add(ctx, &[&i1, &i2])),
                    _ => panic!("Operation can only occur between integer values")
                }
            },
            Predicate::Subtraction(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Int(z3::ast::Int::sub(ctx, &[&i1, &i2])),
                    _ => panic!("Operation can only occur between integer values")
                }
            },
            Predicate::Equal(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Bool(i1._eq(&i2)),
                    (Z3Repr::Bool(b1), Z3Repr::Bool(b2)) => Z3Repr::Bool(b1._eq(&b2)),
                    _ => panic!("Operation on non-supported values")
                }
            },
            Predicate::NotEqual(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Bool(z3::ast::Bool::not(&i1._eq(&i2))),
                    (Z3Repr::Bool(b1), Z3Repr::Bool(b2)) => Z3Repr::Bool(z3::ast::Bool::not(&b1._eq(&b2))),
                    (l, r) => panic!("Operation can only occur between integer values, not {:?} {:?} {:?} {:?}", l, r, lhs, rhs),
                }
            },
            Predicate::LessThan(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Bool(i1.lt(&i2)),
                    _ => panic!("Operation can only occur between integer values")
                }
            },
            Predicate::LessThanEqual(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Bool(i1.le(&i2)),
                    _ => panic!("Operation can only occur between integer values")
                }
            },
            Predicate::GreaterThan(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Bool(i1.gt(&i2)),
                    _ => panic!("Operation can only occur between integer values")
                }
            },
            Predicate::GreaterThanEqual(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => Z3Repr::Bool(i1.ge(&i2)),
                    _ => panic!("Operation can only occur between integer values")
                }
            },
            Predicate::And(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Bool(i1), Z3Repr::Bool(i2)) => Z3Repr::Bool(z3::ast::Bool::and(ctx, &[&i1, &i2])),
                    _ => panic!("Operation can only occur between boolean values")
                }
            },
            Predicate::Not(e) => {
                match (Self::into_sat(&*e, ctx)) {
                    Z3Repr::Bool(e) => Z3Repr::Bool(z3::ast::Bool::not(&e)),
                    _ => panic!("Operation can only occur between boolean values")
                }
            },
            Predicate::Implies(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Bool(b1), Z3Repr::Bool(b2)) => Z3Repr::Bool(z3::ast::Bool::implies(&b1, &b2)),
                    _ => panic!("Operation can only occur between boolean values")
                }
            },
        }
    }
}

#[derive(Clone, Hash)]
pub struct PredicateExpression {
    invariant: Predicate,
    representative: String,
    named_variables: BTreeMap<String, Predicate>, // Named variables within expr
}

impl Debug for PredicateExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let default = f.debug_struct("PredicateExpression").field("invariant", &self.invariant).field("representative", &self.representative).field("named_variables", &self.named_variables).finish();
        let cfg = Config::new();
        let context = Context::new(&cfg);
        let sat = self.invariant.into_sat(&context);
        match sat {
            Z3Repr::Int(_) => default,
            Z3Repr::Bool(b) => {
                let solver = Solver::new(&context);
                solver.assert(&b);
                match solver.check() {
                    z3::SatResult::Unsat => default,
                    z3::SatResult::Unknown => default,
                    z3::SatResult::Sat => {
                        f.debug_struct("PredicateExpression").field("model", &solver.get_model().unwrap()).field("invariant", &self.invariant).field("representative", &self.representative).field("named_variables", &self.named_variables).finish()

                    },
                }
            },
        }
    }
}

#[derive(Debug)]
enum Z3Repr<'a> {
    Int(z3::ast::Int<'a>),
    Bool(z3::ast::Bool<'a>)
}

impl PredicateExpression {
    fn gensym<F: Fn(&str) -> bool>(&mut self, prefix: &str, excluding: F) -> String {
        let mut state = 0;
        let mut sym = ["__GENSYM__", prefix, "_", &format!("{}", state)].join("");
        while self.named_variables.contains_key(&sym) || excluding(&sym) {
            let mut hasher = DefaultHasher::new();
            sym.hash(&mut hasher);
            state = hasher.finish();
            sym = ["__GENSYM__", prefix, "_", &format!("{}", state)].join("");
        }
        sym
    }

    fn uniquely_rename<F: Fn(&str) -> bool>(&self, excluding: F) -> PredicateExpression {
        let mut new_map = BTreeMap::new();
        let mut renaming = HashMap::new();
        let mut representative = self.representative.clone();
        for k in self.named_variables.keys().clone() {
            if excluding(k) {
                let mut hashed: u64 = 0;
                let mut hashed_string = [k, "_", &format!("{}", hashed)].join("");
                while excluding(&hashed_string.clone()) {
                    let mut hasher = DefaultHasher::new();
                    hashed_string.hash(&mut hasher);
                    hashed = hasher.finish();
                    hashed_string = [k, "_", &format!("{}", hashed)].join("");
                }
                if k.to_owned() == representative {
                    representative = hashed_string.clone();
                }
                renaming.insert(k.to_owned(), hashed_string.clone());
                new_map.insert(hashed_string, self.named_variables[k].clone());
            } else {
                new_map.insert(k.to_string(), self.named_variables[k].clone());
            }
        }
        PredicateExpression { invariant: self.invariant.rename(&renaming), representative, named_variables: new_map }
    }
}

impl AbstractProperty for PredicateExpression {
    fn bottom() -> Self {
        let mut named_variables = BTreeMap::new();
        let tt = Predicate::Equal(Box::new(Predicate::Name("__TT__".to_owned())), Box::new(Predicate::Literal(1)));
        let ff = Predicate::Equal(Box::new(Predicate::Name("__FF__".to_owned())), Box::new(Predicate::Literal(0)));
        let basic_predicates = Predicate::And(Box::new(tt.clone()), Box::new(ff.clone()));
        named_variables.insert("__TT__".to_owned(), Predicate::Name("__TT__".to_owned()));
        named_variables.insert("__FF__".to_owned(), Predicate::Name("__FF__".to_owned()));
        PredicateExpression { invariant: basic_predicates,
                              representative: "__TT__".to_owned(),
                              named_variables: named_variables }
    }

    fn lub(&self, y: &Self) -> Self {
        let mut y = y.uniquely_rename(|s| self.named_variables.contains_key(s));
        let x0 = y.gensym("lub", |s| self.named_variables.contains_key(s));
        // New representative:
        // x0 where
        // self.representative != 0 && y.representative != 0 => x0 = 1
        // otherwise => x0 = 0
        // Which is an AND operation
        let true_case = Box::new(Predicate::Equal(Box::new(Predicate::Name(x0.clone())), Box::new(Predicate::Literal(1))));
        let false_case = Box::new(Predicate::Equal(Box::new(Predicate::Name(x0.clone())), Box::new(Predicate::Literal(0))));
        let lhs_repr = Box::new(y.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0)).clone());
        let rhs_repr = Box::new(y.named_variables.get(&y.representative).unwrap_or(&Predicate::Literal(0)).clone());
        let lhs_istrue = Box::new(Predicate::NotEqual(lhs_repr, Box::new(Predicate::Literal(0))));
        let rhs_istrue = Box::new(Predicate::NotEqual(rhs_repr, Box::new(Predicate::Literal(0))));
        let both_true = Box::new(Predicate::And(lhs_istrue, rhs_istrue));
        let one_untrue = Box::new(Predicate::Not(both_true.clone()));
        let final_predicate = Predicate::And(Box::new(Predicate::Implies(both_true, true_case)), Box::new(Predicate::Implies(one_untrue, false_case)));

        let invariant = Predicate::And(Box::new(Predicate::And(Box::new(self.invariant.clone()), Box::new(y.invariant.clone()))), Box::new(final_predicate));
        let mut new_variables = BTreeMap::new();
        new_variables.extend(self.named_variables.clone());
        new_variables.extend(y.named_variables.clone());
        new_variables.insert(x0.clone(), Predicate::Name(x0.clone()));

        PredicateExpression { invariant: invariant, representative: x0, named_variables: new_variables }
    }
}

impl Add for PredicateExpression {
    type Output = PredicateExpression;

    fn add(self, rhs: Self) -> Self::Output {
        let mut rhs = rhs.uniquely_rename(|s| self.named_variables.contains_key(s));
        let x0 = rhs.gensym("add", |s| self.named_variables.contains_key(s));

        let lhs_repr = Box::new(self.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0)).clone());
        let rhs_repr = Box::new(self.named_variables.get(&rhs.representative).unwrap_or(&Predicate::Literal(0)).clone());
        let final_predicate = Predicate::Equal(Box::new(Predicate::Name(x0.clone())), Box::new(Predicate::Addition(lhs_repr, rhs_repr)));

        let invariant = Predicate::And(Box::new(Predicate::And(Box::new(self.invariant.clone()), Box::new(rhs.invariant.clone()))), Box::new(final_predicate));
        let mut new_variables = BTreeMap::new();
        new_variables.extend(self.named_variables.clone());
        new_variables.extend(rhs.named_variables.clone());
        new_variables.insert(x0.clone(), Predicate::Name(x0.clone()));

        PredicateExpression { invariant: invariant, representative: x0, named_variables: new_variables }
    }
}

impl Sub for PredicateExpression {
    type Output = PredicateExpression;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut rhs = rhs.uniquely_rename(|s| self.named_variables.contains_key(s));
        let x0 = rhs.gensym("sub", |s| self.named_variables.contains_key(s));

        let lhs_repr = Box::new(self.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0)).clone());
        let rhs_repr = Box::new(self.named_variables.get(&rhs.representative).unwrap_or(&Predicate::Literal(0)).clone());
        let final_predicate = Predicate::Equal(Box::new(Predicate::Name(x0.clone())), Box::new(Predicate::Subtraction(lhs_repr, rhs_repr)));

        let invariant = Predicate::And(Box::new(Predicate::And(Box::new(self.invariant.clone()), Box::new(rhs.invariant.clone()))), Box::new(final_predicate));
        let mut new_variables = BTreeMap::new();
        new_variables.extend(self.named_variables.clone());
        new_variables.extend(rhs.named_variables.clone());
        new_variables.insert(x0.clone(), Predicate::Name(x0.clone()));

        PredicateExpression { invariant: invariant, representative: x0, named_variables: new_variables }
    }
}

impl From<i64> for PredicateExpression {
    fn from(i: i64) -> Self {
        let mut named_variables = BTreeMap::new();
        let tt = Predicate::Equal(Box::new(Predicate::Name("__TT__".to_owned())), Box::new(Predicate::Literal(1)));
        let ff = Predicate::Equal(Box::new(Predicate::Name("__FF__".to_owned())), Box::new(Predicate::Literal(0)));
        let c = Predicate::Equal(Box::new(Predicate::Name("c".to_owned())), Box::new(Predicate::Literal(i)));
        let basic_predicates = Predicate::And(Box::new(Predicate::And(Box::new(tt.clone()), Box::new(ff.clone()))), Box::new(c.clone()));
        named_variables.insert("__TT__".to_owned(), Predicate::Name("__TT__".to_owned()));
        named_variables.insert("__FF__".to_owned(), Predicate::Name("__FF__".to_owned()));
        named_variables.insert("c".to_owned(), Predicate::Name("c".to_owned()));
        PredicateExpression { invariant: basic_predicates,
                              representative: "c".to_owned(),
                              named_variables }
    }
}

impl From<bool> for PredicateExpression {
    fn from(b: bool) -> Self {
        let mut named_variables = BTreeMap::new();
        let tt = Predicate::Equal(Box::new(Predicate::Name("__TT__".to_owned())), Box::new(Predicate::Literal(1)));
        let ff = Predicate::Equal(Box::new(Predicate::Name("__FF__".to_owned())), Box::new(Predicate::Literal(0)));
        let basic_predicates = Predicate::And(Box::new(tt.clone()), Box::new(ff.clone()));
        named_variables.insert("__TT__".to_owned(), Predicate::Name("__TT__".to_owned()));
        named_variables.insert("__FF__".to_owned(), Predicate::Name("__FF__".to_owned()));
        PredicateExpression { invariant: basic_predicates,
                              representative: if b {"__TT__".to_owned()} else {"__FF__".to_owned()},
                              named_variables: named_variables }
    }
}

impl PartialEq for PredicateExpression {
    // True iff self and other are equivalent boolean formulas
    fn eq(&self, other: &Self) -> bool {
        // let new_invariant = AbstractProperty::lub(self, other);

        let other = other.uniquely_rename(|s| self.named_variables.contains_key(s));
        // let invariant = Predicate::And(Box::new(self.invariant.clone()), Box::new(other.invariant.clone()));
        let config = Config::new();
        let context = Context::new(&config);
        let lhs_invariant = self.invariant.into_sat(&context);
        match lhs_invariant {
            Z3Repr::Int(_) => panic!("Invariants must be Boolean Expressions"),
            Z3Repr::Bool(il) => {
                let rhs_invariant = other.invariant.into_sat(&context);
                match rhs_invariant {
                    Z3Repr::Int(_) => panic!("Invariants must be Boolean Expressions"),
                    Z3Repr::Bool(ir) => {
                        let to_check = Predicate::Not(Box::new(Predicate::Equal(Box::new(other.named_variables.get(&self.representative).unwrap_or(self.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0))).clone()),
                                                                                Box::new(other.named_variables.get(&other.representative).unwrap_or(&Predicate::Literal(0)).clone()))));
                        let to_check = to_check.into_sat(&context);
                        match to_check {
                            Z3Repr::Int(_) => panic!("Invariants must be Boolean Expressions"),
                            Z3Repr::Bool(tc) => {
                                let solver = Solver::new(&context);
                                solver.assert(&ir);
                                solver.assert(&il);
                                solver.assert(&tc);
                                match solver.check() {
                                    z3::SatResult::Unsat => true,
                                    z3::SatResult::Unknown => panic!("Sat solver timeout"),
                                    z3::SatResult::Sat => false,
                                }
                            }
                        }
                    },
                }
            },
        }
        // let to_check = Predicate::Not(Box::new(Predicate::Equal(Box::new(other.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0)).clone()),
        //                                                         Box::new(other.named_variables.get(&other.representative).unwrap_or(&Predicate::Literal(0)).clone()))));
        // let to_check_and_inv = Predicate::And(Box::new(invariant), Box::new(to_check));

        // let config = Config::new();
        // let context = Context::new(&config);
        // let sat_formula = to_check_and_inv.into_sat(&context);
        // let stsfbl;
        // match sat_formula {
        //     Z3Repr::Int(_) => panic!("Invariant must be a boolean expression"),
        //     Z3Repr::Bool(e) => {
        //         let solver = Solver::new(&context);
        //         solver.assert(&e);
        //         match solver.check() {
        //             z3::SatResult::Unsat => {stsfbl = false;},
        //             z3::SatResult::Unknown => panic!("Sat solver timeout"),
        //             z3::SatResult::Sat => {stsfbl = true;},
        //         }
        //     },
        // }
        // !stsfbl
    }
}

impl PartialOrd for PredicateExpression {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let lt;
        {
            let other = other.uniquely_rename(|s| self.named_variables.contains_key(s));
            let invariant = Predicate::And(Box::new(self.invariant.clone()), Box::new(other.invariant.clone()));
            let to_check = Predicate::Not(Box::new(Predicate::LessThan(Box::new(other.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0)).clone()),
                                                                       Box::new(other.named_variables.get(&other.representative).unwrap_or(&Predicate::Literal(0)).clone()))));
            let to_check_and_inv = Predicate::And(Box::new(invariant), Box::new(to_check));

            let config = Config::new();
            let context = Context::new(&config);
            let sat_formula = to_check_and_inv.into_sat(&context);
            match sat_formula {
                Z3Repr::Int(_) => panic!("Invariant must be a boolean expression"),
                Z3Repr::Bool(e) => {
                    let solver = Solver::new(&context);
                    solver.assert(&e);
                    match solver.check() {
                        z3::SatResult::Unsat => {lt = true;},
                        z3::SatResult::Unknown => panic!("Sat solver timeout"),
                        z3::SatResult::Sat => {lt = false;},
                    }
                },
            }
        }
        let eq = self.eq(other);

        let gt;
        {
            let other = other.uniquely_rename(|s| self.named_variables.contains_key(s));
            let invariant = Predicate::And(Box::new(self.invariant.clone()), Box::new(other.invariant.clone()));
            let to_check = Predicate::Not(Box::new(Predicate::GreaterThan(Box::new(other.named_variables.get(&self.representative).unwrap_or(&Predicate::Literal(0)).clone()),
                                                                          Box::new(other.named_variables.get(&other.representative).unwrap_or(&Predicate::Literal(0)).clone()))));
            let to_check_and_inv = Predicate::And(Box::new(invariant), Box::new(to_check));

            let config = Config::new();
            let context = Context::new(&config);
            let sat_formula = to_check_and_inv.into_sat(&context);
            match sat_formula {
                Z3Repr::Int(_) => panic!("Invariant must be a boolean expression"),
                Z3Repr::Bool(e) => {
                    let solver = Solver::new(&context);
                    solver.assert(&e);
                    match solver.check() {
                        z3::SatResult::Unsat => {gt = true;},
                        z3::SatResult::Unknown => panic!("Sat solver timeout"),
                        z3::SatResult::Sat => {gt = false;},
                    }
                },
            }
        }
        // This looks suspect from an overapproximation standpoint
        match (lt, eq, gt) {
            (true, false, false) => Some(Ordering::Less),
            (false, true, false) => Some(Ordering::Equal),
            (false, false, true) => Some(Ordering::Greater),
            _ => None
        }
    }
}

impl Eq for PredicateExpression {}

pub struct PredicateSemantics();

impl AbstractDomain<PredicateExpression> for PredicateSemantics {
    fn assign(&self, x: &Expr, expr: &Expr, environments: PredicateExpression) -> PredicateExpression {
        match x {
            Expr::Variable(_, s) => {
                let expr = expr.eval(&|(_, s)| PredicateExpression { invariant: environments.invariant.clone(), representative: s.to_string(), named_variables: environments.named_variables.clone() });
                let mut renamed = expr.uniquely_rename(|t| s == t);
                let final_predicate = Predicate::Equal(Box::new(Predicate::Name(s.clone())), Box::new(Predicate::Name(renamed.representative.clone())));
                let invariant = Predicate::And(Box::new(renamed.invariant), Box::new(final_predicate));
                renamed.named_variables.insert(s.clone(), Predicate::Name(s.to_string()));
                // println!("predicate will look like: {:?}", PredicateExpression { invariant: invariant.clone(), representative: s.clone(), named_variables: renamed.named_variables.clone() });
                PredicateExpression { invariant, representative: s.clone(), named_variables: renamed.named_variables }
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }

    fn test(&self, expr: &Expr, element: PredicateExpression) -> PredicateExpression {
        let printexpr = expr.clone();
        let expr = expr.eval(&|(_, s)| PredicateExpression { invariant: element.invariant.clone(), representative: s.to_string(), named_variables: element.named_variables.clone() });
        let invariant = expr.invariant;
        let to_check = Predicate::NotEqual(Box::new(Predicate::Name(expr.representative)), Box::new(Predicate::Name("__FF__".to_string())));
        let to_check_and_inv = Predicate::And(Box::new(invariant), Box::new(to_check));
        let config = Config::new();
        let context = Context::new(&config);
        let sat_formula = to_check_and_inv.into_sat(&context);
        let allow;
        match sat_formula {
            Z3Repr::Int(_) => panic!("Invariant must be a boolean expression"),
            Z3Repr::Bool(e) => {
                let solver = Solver::new(&context);
                solver.assert(&e);
                match solver.check() {
                    z3::SatResult::Unsat => {allow = false;},
                    z3::SatResult::Unknown => panic!("Sat solver timeout"),
                    z3::SatResult::Sat => {allow = true;},
                }
            },
        }
        if allow {
            element
        } else {
            PredicateExpression::bottom()
        }
    }

    fn not_test(&self, expr: &Expr, element: PredicateExpression) -> PredicateExpression {
        let expr = expr.eval(&|(_, s)| PredicateExpression { invariant: element.invariant.clone(), representative: s.to_string(), named_variables: element.named_variables.clone() });
        let invariant = expr.invariant;
        let to_check = Predicate::Equal(Box::new(Predicate::Name(expr.representative)), Box::new(Predicate::Name("__TT__".to_string())));
        let to_check_and_inv = Predicate::And(Box::new(invariant), Box::new(to_check));

        let config = Config::new();
        let context = Context::new(&config);
        let sat_formula = to_check_and_inv.into_sat(&context);
        let allow;
        match sat_formula {
            Z3Repr::Int(_) => panic!("Invariant must be a boolean expression"),
            Z3Repr::Bool(e) => {
                let solver = Solver::new(&context);
                solver.assert(&e);
                match solver.check() {
                    z3::SatResult::Unsat => {allow = false;},
                    z3::SatResult::Unknown => panic!("Sat solver timeout"),
                    z3::SatResult::Sat => {allow = true;},
                }
            },
        }
        if allow {
            element
        } else {
            PredicateExpression::bottom()
        }
    }
}

// #[derive(Clone, Debug, PartialEq, Eq)]
// pub struct PredicateProperty {
//     assignments: HashMap<String, Predicate>,
//     invariant: Predicate,
//     counter: i64,
// }

// impl AbstractProperty for PredicateProperty {
//     fn bottom() -> Self {
//         PredicateProperty { assignments: HashMap::new(), invariant: Predicate::Literal(1), counter: 0 }
//     }

//     fn lub(&self, y: &Self) -> Self {
//         let mut union = HashMap::new();
//         union.extend(self.assignments.clone());
//         union.extend(y.assignments.clone());
//         PredicateProperty{
//             assignments: union,
//             invariant: Predicate::And(Box::new(self.invariant.clone()), Box::new(y.invariant.clone())),
//             counter: i64::max(self.counter, y.counter)
//         }
//     }
// }

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
        match x {
            Expr::Variable(_, s) => {
                HashSet::<BTreeMap<String, SignPropertyElement>>::from(&environments).iter().map(|elt| {
                    let mut out = elt.clone();
                    out.insert(s.to_owned(), expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero)));
                    out
                }).fold(SignProperty::bottom(), |acc, map| {
                    // Legal as alpha preserves lub
                    acc.lub(&SignProperty(map))
                })
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }

    fn test(&self, expr: &Expr, environments: SignProperty) -> SignProperty {
        HashSet::<BTreeMap<String, SignPropertyElement>>::from(&environments).iter().filter(|elt| {
            expr.eval(&|(_, s)| *elt.get(s).unwrap_or(&SignPropertyElement::Zero)) != SignPropertyElement::Zero
        }).fold(SignProperty::bottom(), |acc, map| {
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
