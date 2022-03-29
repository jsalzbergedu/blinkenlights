use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::fmt::Debug;
use std::hash::Hash;
use std::hash::Hasher;
use std::ops::Add;
use std::ops::Sub;
use z3::ast::Ast;
use z3::{Config, Context, Solver};

use crate::ast::Statement;
use crate::ast::Program;
use crate::ast::Expr;
use crate::ast::StatementList;
use crate::ast::Labels;
use crate::db::DB;
use crate::lattice::AbstractProperty;

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

// Some basic implementations

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Predicate {
    IntegerName(String),
    IntegerLiteral(i64),
    BooleanName(String),
    BooleanLiteral(bool),
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
    Implies(Box<Predicate>, Box<Predicate>),
    Or(Box<Predicate>, Box<Predicate>)
}

impl Default for Predicate {
    fn default() -> Self {
        Predicate::BooleanLiteral(true)
    }
}

pub struct PredicateBuilder {
    predicate: Vec<Predicate>,
}

impl PredicateBuilder {
    pub fn new() -> PredicateBuilder {
        PredicateBuilder { predicate: vec![] }
    }

    pub fn pred(mut self, p: Predicate) -> Self {
        self.predicate.push(p);
        self
    }

    pub fn name(mut self, s: String) -> Self {
        self.predicate.push(Predicate::IntegerName(s));
        self
    }

    pub fn literal(mut self, i: i64) -> Self {
        self.predicate.push(Predicate::IntegerLiteral(i));
        self
    }

    pub fn bool(mut self, b: bool) -> Self {
        self.predicate.push(Predicate::BooleanLiteral(b));
        self
    }

    pub fn dup(mut self) -> Self {
        let p = self.predicate.pop().expect("no predicate on predicate builder stack");
        self.predicate.push(p.clone());
        self.predicate.push(p);
        self
    }

    pub fn swap(mut self) -> Self {
        let p = self.predicate.pop().expect("no predicate on predicate builder stack");
        let q = self.predicate.pop().expect("no predicate on predicate builder stack");
        self.predicate.push(p);
        self.predicate.push(q);
        self
    }

    pub fn not(mut self) -> Self {
        let p = self.predicate.pop().expect("no predicate on predicate builder stack");
        self.predicate.push(Predicate::Not(Box::new(p)));
        self
    }

    fn binop<F: FnOnce(Box<Predicate>, Box<Predicate>) -> Predicate>(mut self, f: F) -> Self {
        let rhs = self.predicate.pop().expect("no rhs on predicate builder stack");
        let lhs = self.predicate.pop().expect("no lhs on predicate builder stack");
        self.predicate.push(f(Box::new(lhs), Box::new(rhs)));
        self
    }

    pub fn add(self) -> Self {
        self.binop(Predicate::Addition)
    }
    pub fn sub(self) -> Self {
        self.binop(Predicate::Subtraction)
    }
    pub fn _eq(self) -> Self {
        self.binop(Predicate::Equal)
    }
    pub fn ne(self) -> Self {
        self.binop(Predicate::NotEqual)
    }
    pub fn lt(self) -> Self {
        self.binop(Predicate::LessThan)
    }
    pub fn le(self) -> Self {
        self.binop(Predicate::LessThanEqual)
    }
    pub fn gt(self) -> Self {
        self.binop(Predicate::GreaterThan)
    }
    pub fn ge(self) -> Self {
        self.binop(Predicate::GreaterThanEqual)
    }
    pub fn and(self) -> Self {
        self.binop(Predicate::And)
    }
    pub fn or(self) -> Self {
        self.binop(Predicate::Or)
    }
    pub fn imp(self) -> Self {
        self.binop(Predicate::Implies)
    }

    pub fn finish(mut self) -> Predicate {
        self.predicate.pop().expect("Predicate finalized but predicate stack empty")
    }

}

impl Predicate {
    fn rename(&self, map: &HashMap<String, String>) -> Self {
        match self {
            Predicate::IntegerName(s) => Predicate::IntegerName(map.get(s).to_owned().unwrap_or(s).clone()),
            Predicate::BooleanName(s) => Predicate::BooleanName(map.get(s).to_owned().unwrap_or(s).clone()),
            Predicate::IntegerLiteral(_) | Predicate::BooleanLiteral(_) => self.clone(),
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
            Predicate::Or(l, r) => {
                Predicate::Or(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::Implies(l, r) => {
                Predicate::Implies(Box::new(l.rename(map)), Box::new(r.rename(map)))
            },
            Predicate::Not(e) => {
                Predicate::Not(Box::new(e.rename(map)))
            },
        }
    }

    fn names<'a>(&'a self, names: &'a mut BTreeMap<String, Predicate>) {
        match self {
            Predicate::IntegerName(s) => {names.insert(s.to_owned(), Predicate::IntegerName(s.to_owned()));},
            Predicate::BooleanName(s) => {names.insert(s.to_owned(), Predicate::BooleanName(s.to_owned()));},
            Predicate::IntegerLiteral(_) => {},
            Predicate::BooleanLiteral(_) => {},
            Predicate::Addition(l, r) |
            Predicate::Subtraction(l, r) |
            Predicate::Equal(l, r) |
            Predicate::NotEqual(l, r) |
            Predicate::LessThan(l, r) |
            Predicate::LessThanEqual(l, r)  |
            Predicate::GreaterThan(l, r) |
            Predicate::GreaterThanEqual(l, r) |
            Predicate::And(l, r) |
            Predicate::Or(l, r) |
            Predicate::Implies(l, r) => {
                l.names(names);
                r.names(names);
            },
            Predicate::Not(e) => {
                e.names(names);
            },
        }
    }

    pub fn into_sat<'a>(&'a self, ctx: &'a Context) -> Z3Repr<'a> {
        match &self {
            Predicate::IntegerLiteral(i) => {
                Z3Repr::Int(z3::ast::Int::from_i64(ctx, *i))
            },
            Predicate::BooleanLiteral(b) => {
                Z3Repr::Bool(z3::ast::Bool::from_bool(ctx, *b))
            },
            Predicate::IntegerName(s) => {
                Z3Repr::Int(z3::ast::Int::new_const(ctx, s.clone()))
            },
            Predicate::BooleanName(s) => {
                Z3Repr::Bool(z3::ast::Bool::new_const(ctx, s.to_owned()))
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
                    (_, _) => Z3Repr::Bool(z3::ast::Bool::from_bool(ctx, false))
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
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => (Z3Repr::Bool(z3::ast::Bool::and(ctx, &[&i1.lt(&i2), &(z3::ast::Bool::not(&i1._eq(&i2)))]))),
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
                    (Z3Repr::Int(i1), Z3Repr::Int(i2)) => (Z3Repr::Bool(z3::ast::Bool::and(ctx, &[&i1.gt(&i2), &(z3::ast::Bool::not(&i1._eq(&i2)))]))),
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
                    _ => panic!("Operation can only occur between boolean values, not {:?} {:?}", lhs, rhs)
                }
            },
            Predicate::Or(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Bool(i1), Z3Repr::Bool(i2)) => Z3Repr::Bool(z3::ast::Bool::or(ctx, &[&i1, &i2])),
                    _ => panic!("Operation can only occur between boolean values")
                }
            },
            Predicate::Not(e) => {
                match Self::into_sat(&*e, ctx) {
                    Z3Repr::Bool(e) => Z3Repr::Bool(z3::ast::Bool::not(&e)),
                    _ => panic!("Operation can only occur between boolean values")
                }
            },
            Predicate::Implies(lhs, rhs) => {
                match (Self::into_sat(&*lhs, ctx), Self::into_sat(&*rhs, ctx)) {
                    (Z3Repr::Bool(b1), Z3Repr::Bool(b2)) => Z3Repr::Bool(z3::ast::Bool::implies(&b1, &b2)),
                    _ => panic!("Operation can only occur between boolean values, {:?} {:?}", lhs, rhs)
                }
            },
        }
    }
}

#[derive(Clone, Hash, Default, PartialEq, Eq)]
pub struct PredicateEnvironment {
    pub invariant: Predicate,
    named_variables: BTreeMap<String, Predicate>, // Named variables within expr
    // This keeps track of the renaming.
}

impl PredicateEnvironment {
    fn rename_all(&self, s: &str) -> (PredicateEnvironment, HashMap<String, String>) {
        let mut renaming = HashMap::new();
        let mut hashed: u64 = 0;
        let mut hashed_string = [s, "_", &format!("{}", hashed)].join("");
        if self.named_variables.contains_key(s) {
            renaming.insert(s.to_owned(), hashed_string.clone());
        }
        while self.named_variables.contains_key(&hashed_string) {
            let old_name = hashed_string.clone();
            let mut hasher = DefaultHasher::new();
            hashed_string.hash(&mut hasher);
            hashed = hasher.finish();
            hashed_string = [s, "_", &format!("{}", hashed)].join("");
            renaming.insert(old_name, hashed_string.clone());
        }
        let mut new_variables = self.named_variables.clone();
        new_variables.remove(s);
        for (_, v) in renaming.clone() {
            new_variables.insert(v.clone(), Predicate::IntegerName(v));
        }
        (
            PredicateEnvironment {
                invariant: self.invariant.rename(&renaming),
                named_variables: new_variables,
            },
            renaming
        )
    }

    fn rename(&self, map: &HashMap<String, String>) -> Self {
        let mut named_variables = BTreeMap::new();
        for (k, v) in &self.named_variables {
            named_variables.insert(map.get(k).unwrap_or(k).to_owned(), v.to_owned());
        }
        PredicateEnvironment {
            invariant: self.invariant.rename(map),
            named_variables,
        }
    }


    pub fn model<'a>(&'a self, map: &'a mut HashMap<String, String>) {
        let mut cfg = Config::new();
        cfg.set_timeout_msec(1000);
        let context = Context::new(&cfg);
        let sat = self.invariant.into_sat(&context);
        match sat {
            Z3Repr::Int(_) => {},
            Z3Repr::Bool(b) => {
                let solver = Solver::new(&context);
                solver.assert(&b);
                match solver.check() {
                    z3::SatResult::Unsat => {},
                    z3::SatResult::Unknown => {},
                    z3::SatResult::Sat => {
                        let model = &solver.get_model().unwrap();
                        for (k, v) in &self.named_variables {
                            let sat = v.into_sat(&context);
                            match sat {
                                Z3Repr::Int(i) => map.insert(k.to_string(), format!("{}", model.eval(&i, true).unwrap())),
                                Z3Repr::Bool(b) => map.insert(k.to_string(), format!("{}", model.eval(&b, true).unwrap())),
                            };
                        }

                    },
                }
            },
        }
    }

}

#[derive(Default, Clone)]
pub struct PredicateEnvironmentBuilder {
    environment: Vec<PredicateEnvironment>
}

impl PredicateEnvironmentBuilder {
    pub fn new() -> PredicateEnvironmentBuilder {
        Default::default()
    }

    pub fn env(mut self, environment: PredicateEnvironment) -> Self {
        self.environment.push(environment);
        self
    }

    pub fn and(mut self) -> PredicateEnvironmentBuilder {
        let rhs = self.environment.pop().expect("Predicate environment stack empty but rhs requested");
        let lhs = self.environment.pop().expect("Predicate environment stack empty but lhs requested");
        let mut named_variables = rhs.named_variables;
        named_variables.extend(lhs.named_variables);
        self.environment.push(PredicateEnvironment { invariant: PredicateBuilder::new().pred(lhs.invariant).pred(rhs.invariant).and().finish(), named_variables  });
        self
    }

    pub fn imp(mut self) -> PredicateEnvironmentBuilder {
        let rhs = self.environment.pop().expect("Predicate environment stack empty but rhs requested");
        let lhs = self.environment.pop().expect("Predicate environment stack empty but lhs requested");
        let mut named_variables = rhs.named_variables;
        named_variables.extend(lhs.named_variables);
        self.environment.push(PredicateEnvironment { invariant: PredicateBuilder::new().pred(lhs.invariant).pred(rhs.invariant).imp().finish(), named_variables  });
        self
    }

    pub fn finish(mut self) -> PredicateEnvironment {
        self.environment.pop().expect("Predicate environment stack empty but finish requested")
    }
}

impl AbstractProperty for PredicateEnvironment {
    fn bottom() -> Self {
        Default::default()
    }

    fn lub(&self, y: &Self) -> Self {
        PredicateEnvironmentBuilder::new().env(self.clone()).env(y.clone()).and().finish()
    }
}

#[derive(Clone, Hash, Debug)]
pub enum PredicateValue {
    Variable(String),
    IntegerLiteral(i64),
}

#[derive(Clone, Hash, Debug)]
pub struct PredicateExpression {
    value: PredicateValue,
    environment: PredicateEnvironment
}

impl Debug for PredicateEnvironment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut default = || f.debug_struct("PredicateExpression").field("invariant", &self.invariant).field("named_variables", &self.named_variables).finish();
        let mut cfg = Config::new();
        cfg.set_timeout_msec(1000);
        let context = Context::new(&cfg);
        let sat = self.invariant.into_sat(&context);
        match sat {
            Z3Repr::Int(_) => default(),
            Z3Repr::Bool(b) => {
                let solver = Solver::new(&context);
                solver.assert(&b);
                match solver.check() {
                    z3::SatResult::Unsat => {default()},
                    z3::SatResult::Unknown => {default()},
                    z3::SatResult::Sat => {
                        let model = &solver.get_model().unwrap();
                        let mut map = HashMap::new();
                        for (k, v) in &self.named_variables {
                            let sat = v.into_sat(&context);
                            match sat {
                                Z3Repr::Int(i) => map.insert(k, format!("{}", model.eval(&i, true).unwrap())),
                                Z3Repr::Bool(b) => map.insert(k, format!("{}", model.eval(&b, true).unwrap())),
                            };
                        }
                        f.debug_struct("PredicateExpression").field("model", &map).field("invariant", &self.invariant).field("named_variables", &self.named_variables).finish()

                    },
                }
            },
        }
    }
}

#[derive(Debug)]
pub enum Z3Repr<'a> {
    Int(z3::ast::Int<'a>),
    Bool(z3::ast::Bool<'a>)
}

impl PredicateExpression {
    fn gensym<F: Fn(&str) -> bool>(&self, prefix: &str, excluding: F) -> String {
        let mut state = 0;
        let mut sym = ["__GENSYM__", prefix, "_", &format!("{}", state)].join("");
        while self.environment.named_variables.contains_key(&sym) || excluding(&sym) {
            let mut hasher = DefaultHasher::new();
            sym.hash(&mut hasher);
            state = hasher.finish();
            sym = ["__GENSYM__", prefix, "_", &format!("{}", state)].join("");
        }
        sym
    }

    fn uniquely_rename<F: Fn(&str) -> bool>(&self, excluding: F) -> (PredicateExpression, HashMap<String, String>) {
        let mut new_map = BTreeMap::new();
        let mut renaming = HashMap::new();
        let mut value = self.value.clone();
        for k in self.environment.named_variables.keys().clone() {
            if excluding(k) && &*k != "__TT__" && &*k != "__FF__" && &*k != "__TT__bool__" && &*k != "__FF__bool__"{
                let mut hashed: u64 = 0;
                let mut hashed_string = [k, "_", &format!("{}", hashed)].join("");
                while excluding(&hashed_string.clone()) {
                    let mut hasher = DefaultHasher::new();
                    hashed_string.hash(&mut hasher);
                    hashed = hasher.finish();
                    hashed_string = [k, "_", &format!("{}", hashed)].join("");
                }
                match &value {
                    PredicateValue::Variable(r) => {
                        if k == r {
                            value = PredicateValue::Variable(hashed_string.clone());
                        }
                    },
                    _ => {},
                };
                renaming.insert(k.to_owned(), hashed_string.clone());
                new_map.insert(hashed_string.clone(), Predicate::IntegerName(hashed_string.clone()));
            } else {
                new_map.insert(k.to_string(), self.environment.named_variables[k].clone());
            }
        }
        (PredicateExpression { environment: PredicateEnvironment{ invariant: self.environment.invariant.rename(&renaming), named_variables: new_map }, value }, renaming)
    }

    fn repr(&self) -> Predicate {
        match &self.value {
            PredicateValue::Variable(s) => {
                self.environment.named_variables.get(s).map(|x| x.to_owned()).unwrap_or_default()
            },
            PredicateValue::IntegerLiteral(i) => {
                Predicate::IntegerLiteral(*i)
            },
        }
    }
}

#[derive(Default)]
pub struct PredicateExpressionBuilder {
    expression: Vec<PredicateExpression>
}

impl PredicateExpressionBuilder {
    pub fn new() -> Self {
        PredicateExpressionBuilder::default()
    }

    pub fn expr(mut self, expr: PredicateExpression) -> Self {
        self.expression.push(expr);
        self
    }

    pub fn dup(mut self) -> Self {
        let duplicated = self.expression.pop().expect("Predicate expression stack empty but rhs requested");
        self.expression.push(duplicated.clone());
        self.expression.push(duplicated);
        self
    }

    fn not(mut self) -> Self {
        let mut negated = self.expression.pop().expect("Predicate expression stack empty but rhs requested");
        let value = negated.gensym("not", |s| negated.environment.named_variables.contains_key(s));
        negated.environment.named_variables.insert(value.clone(), Predicate::IntegerName(value.clone()));
        let invariant = PredicateBuilder::new().pred(negated.environment.invariant.clone()).dup().name(value.clone()).literal(0)._eq().imp()
            .swap().not()
            .name(value.clone()).literal(1)._eq().imp()
            .and().finish();

        self.expression.push(PredicateExpression {environment: PredicateEnvironment {invariant, named_variables: negated.environment.named_variables}, value: PredicateValue::Variable(value)});
        self
    }

    fn arith_binop<F: Fn(Predicate, Predicate, String) -> Predicate>(mut self, sym: &str, f: F) -> Self {
        let mut rhs = self.expression.pop().expect("Predicate expression stack empty but rhs requested");
        let lhs = self.expression.pop().expect("Predicate expression stack empty but lhs requested");
        let (mut rhs, _) = rhs.uniquely_rename(|s| lhs.environment.named_variables.contains_key(s) || rhs.environment.named_variables.contains_key(s));
        let value = rhs.gensym(sym, |s| lhs.environment.named_variables.contains_key(s) || rhs.environment.named_variables.contains_key(s));
        rhs.environment.named_variables.insert(value.clone(), Predicate::IntegerName(value.clone()));
        rhs.environment.named_variables.extend(lhs.environment.named_variables.clone());
        let named_variables = rhs.environment.named_variables.clone();
        let arithmetic_predicate = f(lhs.repr().clone(), rhs.repr().clone(), value.clone());
        let invariant = PredicateBuilder::new().pred(arithmetic_predicate).pred(lhs.environment.invariant).pred(rhs.environment.invariant).and().and().finish();
        self.expression.push(PredicateExpression {environment: PredicateEnvironment {invariant, named_variables}, value: PredicateValue::Variable(value)});
        self
    }

    pub fn add(self) -> Self {
        self.arith_binop("add", |lhs, rhs, x0| {
            let invariant_builder = PredicateBuilder::new();
            invariant_builder.name(x0.clone()).pred(lhs).pred(rhs).add()._eq().finish()
        })
    }

    pub fn sub(self) -> Self {
        self.arith_binop("add", |lhs, rhs, x0| {
            let invariant_builder = PredicateBuilder::new();
            invariant_builder.name(x0.clone()).pred(lhs).pred(rhs).sub()._eq().finish()
        })
    }

    fn bool_binop<F: Fn(PredicateBuilder) -> PredicateBuilder>(self, sym: &str, true_case: F) -> Self where
    {
        self.arith_binop(sym, |lhs, rhs, x0| {

            let pb = PredicateBuilder::new();
            true_case(pb.pred(lhs).pred(rhs)).dup()
                .name(x0.clone()).literal(1)._eq().imp()
                .swap().not()
                .name(x0.clone()).literal(0)._eq().imp()
                .and().finish()
        })
    }

    pub fn _eq(self) -> Self {
        self.bool_binop("eq", |pb| pb._eq())
    }
    pub fn ne(self) -> Self {
        self.bool_binop("ne", |pb| pb.ne())
    }
    pub fn lt(self) -> Self {
        self.bool_binop("lt", |pb| pb.lt())
    }
    pub fn gt(self) -> Self {
        self.bool_binop("gt", |pb| pb.gt())
    }
    pub fn le(self) -> Self {
        self.bool_binop("le", |pb| pb.le())
    }
    pub fn ge(self) -> Self {
        self.bool_binop("ge", |pb| pb.ge())
    }
    pub fn and(self) -> Self {
        self.bool_binop("and", |pb| pb.and())
    }
    pub fn or(self) -> Self {
        self.bool_binop("or", |pb| pb.or())
    }
    pub fn nand(self) -> Self {
        self.bool_binop("nand", |pb| pb.literal(0)._eq())
    }

    pub fn finish(mut self) -> PredicateExpression {
        self.expression.pop().expect("Predicate expression finalized but predicate expression stack empty")
    }
}

impl Add for PredicateExpression {
    type Output = PredicateExpression;

    fn add(self, rhs: Self) -> Self::Output {
        PredicateExpressionBuilder::new().expr(self).expr(rhs).add().finish()
    }
}

impl Sub for PredicateExpression {
    type Output = PredicateExpression;

    fn sub(self, rhs: Self) -> Self::Output {
        PredicateExpressionBuilder::new().expr(self).expr(rhs).add().finish()
    }
}

impl From<i64> for PredicateExpression {
    fn from(i: i64) -> Self {
        PredicateExpression { value: PredicateValue::IntegerLiteral(i), environment: PredicateEnvironment { invariant: Predicate::BooleanLiteral(true), named_variables: BTreeMap::new() } }
    }
}

impl From<bool> for PredicateExpression {
    fn from(b: bool) -> Self {
        if b {1.into()} else {0.into()}
    }
}

pub struct PredicateSemantics {
    pub invariants: HashMap<i64, PredicateEnvironment>,
}

impl From<Predicate> for PredicateEnvironment {
    fn from(p: Predicate) -> Self {
        let mut map = BTreeMap::new();
        p.names(&mut map);
        PredicateEnvironment { invariant: p, named_variables: map }
    }
}

lazy_static! {
    static ref TRUE_PREDICATE_ENVIRONMENT: PredicateEnvironment = {
        PredicateEnvironment::bottom()
    };
}

impl PredicateSemantics {
    fn invariant<'a>(&'a self, label: i64) -> &'a PredicateEnvironment {
        self.invariants.get(&label).unwrap_or(&TRUE_PREDICATE_ENVIRONMENT)
    }

    pub fn new(p: HashMap<i64, Predicate>) -> Self {
        let mut map = HashMap::new();
        for (k, v) in p.into_iter() {
            map.insert(k, v.into());
        }
        PredicateSemantics { invariants: map }
    }

    pub fn from_db(db: &DB, labels: &Labels) -> Result<Self, String> {
        let mut map = HashMap::new();
        for assertion in &*db.assertion {
            let expr = Expr::from_db(db, assertion.expr)?;
            let mut expr = process_expression(&expr, |b, s| {
                let environment = PredicateBuilder::new().name(s.clone()).name(s.clone())._eq().finish().into();
                b.expr(PredicateExpression { value: PredicateValue::Variable(s.to_string()),
                                             environment }.into())
            });
            let expr_istrue = PredicateBuilder::new()
                .pred(expr.repr())
                .literal(0).ne()
                .pred(expr.environment.invariant)
                .and()
                .finish();
            expr.environment.invariant = expr_istrue;
            for (i, label) in &labels.labels {
                if label.after == assertion.node {
                    map.insert(labels.labels[i].after, expr.environment.clone());
                }
            }
            map.insert(labels.labels[&assertion.node].after, expr.environment.clone());
        }
        Ok(PredicateSemantics { invariants: map })
    }
}

enum ExprStack<'a> {
    Expr(&'a Expr),
    Add,
    Sub,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Nand
}

impl <'a> From<&'a Expr> for ExprStack<'a> {
    fn from(e: &'a Expr) -> Self {
        match e {
            Expr::Variable(_, _) => Self::Expr(e),
            Expr::Constant(_, _) => Self::Expr(e),
            Expr::Addition(_, _, _) => Self::Add,
            Expr::Subtraction(_, _, _) => Self::Sub,
            Expr::Equal(_, _, _) => Self::Eq,
            Expr::NotEqual(_, _, _) => Self::Ne,
            Expr::LessThan(_, _, _) => Self::Lt,
            Expr::GreaterThan(_, _, _) => Self::Gt,
            Expr::LessThanEqual(_, _, _) => Self::Le,
            Expr::GreaterThanEqual(_, _, _) => Self::Ge,
            Expr::Nand(_, _, _) => Self::Nand,
        }
    }
}

fn process_expression<F: Fn(PredicateExpressionBuilder, &String) -> PredicateExpressionBuilder>(expr: &Expr, f: F) -> PredicateExpression {
    let mut b = PredicateExpressionBuilder::new();
    let mut unprocessed = vec![ExprStack::Expr(expr)];
    while unprocessed.len() > 0 {
        match unprocessed.pop().unwrap() {
            ExprStack::Expr(e) => {
                match e {
                    Expr::Variable(_, s) => {
                        b = f(b, s);
                    },
                    Expr::Constant(_, c) => {
                        b = b.expr(PredicateExpression::from(*c))
                    },
                    Expr::Addition(_, lhs, rhs) |
                    Expr::Subtraction(_, lhs, rhs) |
                    Expr::Equal(_, lhs, rhs) |
                    Expr::NotEqual(_, lhs, rhs) |
                    Expr::LessThan(_, lhs, rhs) |
                    Expr::GreaterThan(_, lhs, rhs) |
                    Expr::LessThanEqual(_, lhs, rhs) |
                    Expr::GreaterThanEqual(_, lhs, rhs) |
                    Expr::Nand(_, lhs, rhs)  => {
                        unprocessed.push(expr.into());
                        unprocessed.push(ExprStack::Expr(rhs));
                        unprocessed.push(ExprStack::Expr(lhs));
                    },
                }
            },
            ExprStack::Add => {b = b.add()},
            ExprStack::Sub => {b = b.sub()},
            ExprStack::Eq => {b = b._eq()},
            ExprStack::Ne => {b = b.ne()},
            ExprStack::Lt => {b = b.lt()},
            ExprStack::Gt => {b = b.gt()},
            ExprStack::Le => {b = b.le()},
            ExprStack::Ge => {b = b.ge()},
            ExprStack::Nand => {b = b.nand()},
        }
    }
    b.finish()
}

impl PredicateSemantics {
    fn assign_expression(&mut self, x: &Expr, expr: &Expr, environment: PredicateEnvironment) -> (PredicateEnvironment, PredicateEnvironment, HashMap<String, String>) {
        match x {
            Expr::Variable(_, s) => {
                let mut expr = process_expression(expr, |b, s| {
                    let mut invariant_builder = PredicateBuilder::new().pred(environment.invariant.clone());
                    let mut named_variables = environment.named_variables.clone();
                    if !environment.named_variables.contains_key(s) {
                        invariant_builder = invariant_builder.name(s.to_owned()).literal(0)._eq().and();
                        named_variables.insert(s.to_owned(), Predicate::IntegerName(s.to_owned()));
                    } else {
                    }
                    let env = PredicateEnvironment {
                        invariant: invariant_builder.finish(),
                        named_variables,
                    };
                    b.expr(PredicateExpression { value: PredicateValue::Variable(s.to_owned()), environment: env })
                });
                let fst: PredicateEnvironment = PredicateBuilder::new().pred(environment.invariant).pred(expr.environment.invariant).and().finish().into();
                let (fst, map) = fst.rename_all(s);
                let snd = match expr.value {
                    PredicateValue::Variable(t) => PredicateEnvironment {
                        invariant: PredicateBuilder::new().name(s.to_string()).name(map.get(&t).unwrap_or(&t).to_owned())._eq().finish(),
                        named_variables: fst.named_variables.clone(),
                    },
                    PredicateValue::IntegerLiteral(i) => PredicateEnvironment {
                        invariant: PredicateBuilder::new().name(s.to_string()).literal(i)._eq().finish(),
                        named_variables: fst.named_variables.clone(),
                    },
                };
                (fst, snd, map)
            },
            _ => panic!("Non variable lvalues not yet handled"),
        }
    }
}

impl AbstractDomain<PredicateEnvironment> for PredicateSemantics {

    fn test(&mut self, expr: &Expr, element: PredicateEnvironment) -> PredicateEnvironment {
        let expr = process_expression(expr, |b, s| {
            let mut invariant_builder = PredicateBuilder::new().pred(element.invariant.clone());
            let mut named_variables = element.named_variables.clone();
            if !element.named_variables.contains_key(s) {
                invariant_builder = invariant_builder.name(s.to_string()).literal(0)._eq().and();
                named_variables.insert(s.to_string(), Predicate::IntegerName(s.to_string()));
            }
            let env = PredicateEnvironment {
                invariant: invariant_builder.finish(),
                named_variables,
            };
            b.expr(PredicateExpression { value: PredicateValue::Variable(s.to_string()), environment: env })
        });
        match expr.value {
            PredicateValue::Variable(s) => PredicateEnvironment {
                invariant: PredicateBuilder::new().pred(expr.environment.invariant).name(s.to_string()).literal(0).ne().and().finish(),
                named_variables: expr.environment.named_variables,

            },
            PredicateValue::IntegerLiteral(i) => PredicateEnvironment {
                invariant: PredicateBuilder::new().pred(expr.environment.invariant).literal(i).literal(0).ne().and().finish(),
                named_variables: expr.environment.named_variables,
            },
        }
    }

    fn not_test(&mut self, expr: &Expr, element: PredicateEnvironment) -> PredicateEnvironment {
        let expr = process_expression(expr, |b, s| {
            let mut invariant_builder = PredicateBuilder::new().pred(element.invariant.clone());
            let mut named_variables = element.named_variables.clone();
            if !element.named_variables.contains_key(s) {
                invariant_builder = invariant_builder.name(s.to_string()).literal(0)._eq().and();
                named_variables.insert(s.to_string(), Predicate::IntegerName(s.to_string()));
            }
            let env = PredicateEnvironment {
                invariant: invariant_builder.finish(),
                named_variables,
            };
            b.expr(PredicateExpression { value: PredicateValue::Variable(s.to_string()), environment: env })
        });
        match expr.value {
            PredicateValue::Variable(s) => PredicateEnvironment {
                invariant: PredicateBuilder::new().pred(expr.environment.invariant).name(s.to_string()).literal(0)._eq().and().finish(),
                named_variables: expr.environment.named_variables,

            },
            PredicateValue::IntegerLiteral(i) => PredicateEnvironment {
                invariant: PredicateBuilder::new().pred(expr.environment.invariant).literal(i).literal(0)._eq().and().finish(),
                named_variables: expr.environment.named_variables,
            },
        }
    }

    fn interpret(&mut self, labels: &Labels, statement: &Statement, element: PredicateEnvironment) -> HashMap<i64, PropertyCacheElement<PredicateEnvironment>> {
        let at = statement.id();
        let after = labels.labels[&statement.id()].after;
        let break_to = labels.labels[&statement.id()].break_to;
        let at_invariant = self.invariant(at).clone();
        let after_invariant = self.invariant(after).clone();
        let break_to_invariant = self.invariant(break_to).clone();

        let mut at_property_b = PredicateEnvironmentBuilder::new();
        at_property_b = at_property_b.env(element.clone()).env(at_invariant.clone()).imp().env(at_invariant.clone()).and();

        let mut map = HashMap::new();
        match statement {
            Statement::Assign(_, x, expr) => {
                // println!("At invariant: {:?}", at_invariant);
                // {
                //     println!("Assign: {:?}", self.assign_expression(x, expr, at_invariant.clone()));
                //     let cfg = Config::new();
                //     let context = Context::new(&cfg);
                //     println!("assign again {:?}", self.assign_epxression(x, expr, at_invariant.clone()).invariant.into_sat(&context));
                // }
                let (environment, predicate, renaming) = self.assign_expression(x, expr, at_invariant.clone());
                println!("At: {:?} => {:?}", environment, at_invariant);
                println!("Predicate: {:?} => {:?}", predicate, after_invariant);
                let at_property = PredicateEnvironmentBuilder::new().env(environment.clone()).env(at_invariant.rename(&renaming)).imp()
                    .env(predicate).env(environment).and().env(after_invariant.clone()).imp()
                    .and()
                    .env(after_invariant).and().finish();
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
                {
                    let cfg = Config::new();
                    let context = Context::new(&cfg);
                    // println!("{:?}", map[&at].at_property.invariant.into_sat(&context));
                }
            },
            Statement::Skip(_) | Statement::Decl(_) => {
                let at_property = at_property_b.env(at_invariant).env(after_invariant).imp().and().finish();
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
            },
            Statement::IfThen(_, b, st) | Statement::While(_, b, st) => {
                let st_interpretation = self.interpret(labels, st, at_invariant.clone());
                let not_test = self.not_test(b, at_invariant.clone());
                let at_property = at_property_b.env(st_interpretation[&st.id()].at_property.clone()).and().env(not_test).env(after_invariant).imp().and().finish();
                map.extend(st_interpretation);
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
            },
            Statement::IfThenElse(_, b, st, sf) => {
                let st_interpretation = self.interpret(labels, st, at_invariant.clone());
                let sf_interpretation = self.interpret(labels, st, at_invariant.clone());
                let at_property = at_property_b.env(st_interpretation[&st.id()].at_property.clone()).and().env(sf_interpretation[&sf.id()].at_property.clone()).and().finish();
                map.extend(st_interpretation);
                map.extend(sf_interpretation);
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
            },
            Statement::Break(_) => {
                let at_property = at_property_b.env(at_invariant).env(break_to_invariant).imp().and().finish();
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
            },
            Statement::Compound(_, sl) => {
                let at_property = self.interpret_sl(labels, sl, element);
                map.insert(at, PropertyCacheElement { at_property: at_property[&sl.id()].at_property.clone(), ..Default::default() });
                map.extend(at_property);
            },
        }
        map
    }

    fn interpret_sl(&mut self, labels: &Labels, sl: &StatementList, element: PredicateEnvironment) -> HashMap<i64, PropertyCacheElement<PredicateEnvironment>> {
        let at = sl.id();
        let after = labels.labels[&sl.id()].after;
        let at_invariant = self.invariant(at).clone();
        let after_invariant = self.invariant(after).clone();

        let mut at_property_b = PredicateEnvironmentBuilder::new();
        // at_property_b = at_property_b.env(element.clone()).env(at_invariant.clone()).imp();
        let mut map = HashMap::new();
        match sl {
            StatementList::Empty(_) => {
                let at_property = at_property_b.env(at_invariant).env(after_invariant).imp().finish();
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
            },
            StatementList::StatementList(_, sl, s) => {
                let sl_interpretation = self.interpret_sl(labels, sl, element.clone());
                // Propegate invariant
                let s_interpretation = self.interpret(labels, s, self.invariant(labels.labels[&sl.id()].after).clone());
                let at_property = at_property_b.env(sl_interpretation[&sl.id()].at_property.clone()).env(s_interpretation[&s.id()].at_property.clone()).and().finish();
                map.insert(at, PropertyCacheElement { at_property, ..Default::default() });
                map.extend(s_interpretation);
                map.extend(sl_interpretation);
            },
        }
        map
    }

    fn interpret_program(&mut self, program: &Program, labels: &Labels) -> HashMap<i64, PropertyCacheElement<PredicateEnvironment>> {
        match program {
            Program::Program(_, statement) => {
                // let mut names = Vec::new();
                // statement.names(&mut names);
                // let mut b = PredicateBuilder::new().bool(true);
                // for name in names {
                //     b = b.name(name).literal(0)._eq().and();
                // }
                // let env = b.finish().into();
                self.interpret(labels, &statement, PredicateEnvironment::bottom())
            },
        }
    }

    fn assign(&mut self, x: &Expr, expr: &Expr, element: PredicateEnvironment) -> PredicateEnvironment {
        panic!("Assign with this signature could not be used for predicate environment")
    }
}
