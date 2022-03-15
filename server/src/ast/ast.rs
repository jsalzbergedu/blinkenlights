use std::{borrow::Borrow, collections::{HashMap, HashSet}, ops::{Add, Sub}};
use std::convert::Into;

use crate::{db, lattice::Lattice};

type AstId = i64;

#[derive(Debug, Eq, PartialEq)]
pub enum Statement {
    Assign(AstId, Box<Expr>, Box<Expr>),
    Skip(AstId),
    IfThen(AstId, Box<Expr>, Box<Statement>),
    IfThenElse(AstId, Box<Expr>, Box<Statement>, Box<Statement>),
    While(AstId, Box<Expr>, Box<Statement>),
    Break(AstId),
    Compound(AstId, Box<StatementList>),
    Decl(AstId),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Expr {
    Variable(AstId, String),
    Constant(AstId, i64),
    Addition(AstId, Box<Expr>, Box<Expr>),
    Subtraction(AstId, Box<Expr>, Box<Expr>),
    Equal(AstId, Box<Expr>, Box<Expr>),
    NotEqual(AstId, Box<Expr>, Box<Expr>),
    LessThan(AstId, Box<Expr>, Box<Expr>),
    GreaterThan(AstId, Box<Expr>, Box<Expr>),
    LessThanEqual(AstId, Box<Expr>, Box<Expr>),
    GreaterThanEqual(AstId, Box<Expr>, Box<Expr>),
    Nand(AstId, Box<Expr>, Box<Expr>),
}

#[derive(Debug, Eq, PartialEq)]
pub enum StatementList {
    Empty(AstId),
    StatementList(AstId, Box<StatementList>, Box<Statement>)
}

#[derive(Debug, Eq, PartialEq)]
pub enum Program {
    Program(AstId, Box<Statement>)
}

impl StatementList {
    pub fn from_db(db: &db::DB, slno: i64) -> Result<Self, String> {
        let sl = db::get_by_id(&db.node, slno)?;
        match sl.kind.borrow() {
            "empty" => Ok(StatementList::Empty(slno)),
            "sl" => {
                let left_id = db::get(&db.children, |x| (x.node == slno) && (x.idx == 0) )?.child;
                let right_id = db::get(&db.children, |x| (x.node == slno) && (x.idx == 1) )?.child;
                let left_sl = Box::new(StatementList::from_db(&db, left_id)?);
                let right_sl = Box::new(Statement::from_db(&db, right_id)?);
                Ok(StatementList::StatementList(slno, left_sl, right_sl))
            }
            _ => Err(format!("statment list: {} not handled", sl.kind))
        }
    }

    pub fn id(&self) -> i64 {
        match self {
            StatementList::Empty(i) => *i,
            StatementList::StatementList(i, _, _) => *i,
        }
    }
}

impl Into<i64> for StatementList {
    fn into(self) -> i64 {
        self.id()
    }
}

impl Expr {
    pub fn from_db(db: &db::DB, exprno: i64) -> Result<Self, String> {
        let expr = db::get_by_id(&db.expr, exprno)?;
        match expr.kind.borrow() {
            "constant" => {
                let constant_id = db::get(&db.expr_children, |x| x.expr == exprno)?.child;
                let constant = db::get_by_id(&db.constant, constant_id)?;
                Ok(Expr::Constant(constant.id, constant.constant))
            },
            "variable" => {
                let variable_id = db::get(&db.expr_children, |x| x.expr == exprno)?.child;
                let variable = db::get_by_id(&db.variable, variable_id)?;
                Ok(Expr::Variable(variable.id, variable.name.clone()))
            },
            "+" | "-" | "lt" | "gt" | "le" | "ge" | "eq" | "neq" | "nand" => {
                let left_id = db::get(&db.expr_children, |x| (x.expr == exprno) && (x.idx == 0) )?.child;
                let right_id = db::get(&db.expr_children, |x| (x.expr == exprno) && (x.idx == 1) )?.child;
                let left_expr = Box::new(Expr::from_db(&db, left_id)?);
                let right_expr = Box::new(Expr::from_db(&db, right_id)?);
                match expr.kind.borrow() {
                    "+" => Ok(Expr::Addition(exprno, left_expr, right_expr)),
                    "-" => Ok(Expr::Subtraction(exprno, left_expr, right_expr)),
                    "lt" => Ok(Expr::LessThan(exprno, left_expr, right_expr)),
                    "gt" => Ok(Expr::GreaterThan(exprno, left_expr, right_expr)),
                    "le" => Ok(Expr::LessThanEqual(exprno, left_expr, right_expr)),
                    "ge" => Ok(Expr::GreaterThanEqual(exprno, left_expr, right_expr)),
                    "eq" => Ok(Expr::Equal(exprno, left_expr, right_expr)),
                    "neq" => Ok(Expr::NotEqual(exprno, left_expr, right_expr)),
                    "nand" => Ok(Expr::Nand(exprno, left_expr, right_expr)),
                    _ => panic!("impossible"),
                }
            },
            _ => Err(format!("expr: {} not handled", expr.kind)),
        }
    }

    pub fn id(&self) -> i64 {
        match self {
            Expr::Variable(i, _) => *i,
            Expr::Constant(i, _) => *i,
            Expr::Addition(i, _, _) => *i,
            Expr::Subtraction(i, _, _) => *i,
            Expr::Equal(i, _, _) => *i,
            Expr::NotEqual(i, _, _) => *i,
            Expr::LessThan(i, _, _) => *i,
            Expr::GreaterThan(i, _, _) => *i,
            Expr::LessThanEqual(i, _, _) => *i,
            Expr::GreaterThanEqual(i, _, _) => *i,
            Expr::Nand(i, _, _) => *i,
        }
    }

    // For now, variables are not associated with their environments.
    // Once they are, replace (i64, String) with  i64
    pub fn eval<T: PartialOrd + Eq + Add<Output = T> + Sub<Output = T> + From<i64> + From<bool>, E: Fn((i64, &str)) -> T>(&self, environment: &E) -> T {
        match self {
            Expr::Variable(id, s) => environment((*id, s)),
            Expr::Constant(_, value) => T::from(*value),
            Expr::Addition(_, left, right) => left.eval(environment) + right.eval(environment),
            Expr::Subtraction(_, left, right) => left.eval(environment) - right.eval(environment),
            Expr::Equal(_, left, right) => if left.eval(environment) == right.eval(environment) {T::from(true)} else {T::from(false)},
            Expr::NotEqual(_, left, right) => if left.eval(environment) != right.eval(environment) {T::from(true)} else {T::from(false)},
            Expr::LessThan(_, left, right) => T::from((right.eval(environment) - left.eval(environment)) > T::from(0)),
            Expr::GreaterThan(_, left, right) => T::from((left.eval(environment) - right.eval(environment)) > T::from(0)),
            Expr::LessThanEqual(_, left, right) => T::from((right.eval(environment) - left.eval(environment)) >= T::from(0)),
            Expr::GreaterThanEqual(_, left, right) => T::from((left.eval(environment) - right.eval(environment)) >= T::from(0)),
            Expr::Nand(_, left, right) => if left.eval(environment) <= T::from(false) || right.eval(environment) <= T::from(false) {T::from(true)} else {T::from(true)},
        }
    }
}

impl Into<i64> for Expr {
    fn into(self) -> i64 {
        self.id()
    }
}

impl Statement {
    pub fn from_db(db: &db::DB, stmtno: i64) -> Result<Self, String> {
        let node = db::get_by_id(&db.node, stmtno)?;
        match node.kind.borrow() {
            "skip" => Ok(Statement::Skip(stmtno)),
            "break" => Ok(Statement::Break(stmtno)),
            "decl" => Ok(Statement::Decl(stmtno)),
            "assign" => Ok(Statement::Assign(stmtno,
                                             Box::new(Expr::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 0))?.child)?),
                                             Box::new(Expr::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 1))?.child)?))),
            "ifthen" => Ok(Statement::IfThen(stmtno,
                                             Box::new(Expr::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 0))?.child)?),
                                             Box::new(Statement::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 1))?.child)?))),
            "ifthenelse" => Ok(Statement::IfThenElse(stmtno,
                                                     Box::new(Expr::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 0))?.child)?),
                                                     Box::new(Statement::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 1))?.child)?),
                                                     Box::new(Statement::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 2))?.child)?))),
            "while" => Ok(Statement::While(stmtno,
                                           Box::new(Expr::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 0))?.child)?),
                                           Box::new(Statement::from_db(db, db::get(&db.children, |x| (x.node == stmtno) && (x.idx == 1))?.child)?))),
            "compound" => Ok(Statement::Compound(stmtno, Box::new(StatementList::from_db(db, db::get(&db.children, |x| (x.node == stmtno))?.child)?))),
            _ => Err(format!("statement: {} not handled", node.kind)),
        }
    }

    pub fn id(&self) -> i64 {
        match self {
            Statement::Assign(i, _, _) => *i,
            Statement::Skip(i) => *i,
            Statement::IfThen(i, _, _) => *i,
            Statement::IfThenElse(i, _, _, _) => *i,
            Statement::While(i, _, _) => *i,
            Statement::Break(i) => *i,
            Statement::Compound(i, _) => *i,
            Statement::Decl(i) => *i,
        }
    }
}

impl Into<i64> for Statement {
    fn into(self) -> i64 {
        self.id()
    }
}

impl Program {
    pub fn from_db(db: &db::DB, pgmno: i64) -> Result<Self, String> {
        Ok(Program::Program(pgmno, Box::new(Statement::from_db(db, db::get(&db.children, |x| x.node == pgmno)?.child)?)))
    }

    pub fn id(&self) -> i64 {
        match &self {
            Program::Program(i, _) => *i,
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Labelling {
    pub at: i64,
    pub after: i64,
    pub escape: bool,
    pub break_to: i64,
    pub breaks_of: HashSet<i64>,
    pub inside: HashSet<i64>,
    pub labs: HashSet<i64>,
    pub labx: HashSet<i64>
}

impl Default for Labelling {
    fn default() -> Self {
        Self { at: -1, after: -1, escape: false, break_to: -1, breaks_of: HashSet::new(), inside: HashSet::new(), labs: HashSet::new(), labx: HashSet::new() }
    }
}

impl Labelling {
    pub fn set_at(mut s: Self, id: i64) -> Self {
        s.at = id;
        s
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct Labels {
    pub labels: HashMap<i64, Labelling>
}


impl Labels {
    pub fn from_statement_list(s: &StatementList) -> Labels {
        match s {
            StatementList::Empty(_) => {
                let labelling = Labelling::set_at(Labelling::default(), s.id());
                let mut map = HashMap::new();
                map.insert(s.id(), labelling);
                Labels { labels: map }
            },
            StatementList::StatementList(_, sl, stmt) => {
                let labelling = Labelling::set_at(Labelling::default(), stmt.id());
                let mut labels_left = Labels::from_statement_list(&sl);
                let labels_right = Labels::from_statement(stmt);
                labels_left.labels.extend(labels_right.labels.into_iter());
                labels_left.labels.insert(s.id(), labelling);
                labels_left
            },
        }
    }

    pub fn from_statement(s: &Statement) -> Labels {
        match s {
            Statement::Skip(_) | Statement::Break(_) | Statement::Decl(_) | Statement::Assign(_, _, _) => {
                let labelling = Labelling::set_at(Labelling::default(), s.id());
                let mut map = HashMap::new();
                map.insert(s.id(), labelling);
                Labels { labels: map }
            },
            Statement::IfThen(_, _, stmt) | Statement::While(_, _, stmt) => {
                let labelling = Labelling::set_at(Labelling::default(), s.id());
                let mut labels = Labels::from_statement(&stmt);
                labels.labels.insert(s.id(), labelling );
                labels
            },
            Statement::IfThenElse(_, _, statement_then, statement_else) => {
                let labelling = Labelling::set_at(Labelling::default(), s.id());
                let mut labels_left = Labels::from_statement(&statement_then);
                let labels_right = Labels::from_statement(&statement_else);
                labels_left.labels.extend(labels_right.labels.into_iter());
                labels_left.labels.insert(s.id(), labelling);
                labels_left
            },
            Statement::Compound(_, stmtlist) => {
                let labelling = Labelling::set_at(Labelling::default(), s.id());
                let mut labels = Labels::from_statement_list(&stmtlist);
                labels.labels.insert(s.id(), labelling);
                labels
            },
        }
    }

    pub fn from_program(p: &Program) -> Labels {
        match p {
            Program::Program(i, stmt) => {
                let labelling = Labelling::set_at(Labelling::default(), *i);
                let mut labels = Labels::from_statement(&stmt);
                labels.labels.insert(p.id(), labelling);
                labels
            },
        }
    }

    pub fn set_labelling_tree<'a>(s: &Statement, after: i64, break_to: i64, labels: &'a mut Labels) {
        match s {
            Statement::Assign(id, _, _)  | Statement::Skip(id) | Statement::Decl(id) => {
                let mut l = labels.labels.get_mut(id).unwrap();
                l.after = after;
                l.break_to = -1;
                l.escape = false;
            },
            Statement::IfThen(id, _, stmt) | Statement::While(id, _, stmt) => {
                let escape;
                {
                    Labels::set_labelling_tree(stmt, after, break_to, labels);
                    let l_stmt = labels.labels.get_mut(&stmt.id()).unwrap();
                    escape = l_stmt.escape;
                }
                let mut l = labels.labels.get_mut(id).unwrap();
                l.after = after;
                l.escape = escape;
                if escape {
                    l.break_to = break_to;
                }
            },
            Statement::IfThenElse(id, _, stmt_true, stmt_false) => {
                let mut escape;
                {
                    Labels::set_labelling_tree(stmt_true, after, break_to, labels);
                    let l_stmt_true = labels.labels.get_mut(&stmt_true.id()).unwrap();
                    escape = l_stmt_true.escape;
                }
                {
                    Labels::set_labelling_tree(stmt_false, after, break_to, labels);
                    let l_stmt_true = labels.labels.get_mut(&stmt_true.id()).unwrap();
                    escape |= l_stmt_true.escape;
                }
                let mut l = labels.labels.get_mut(id).unwrap();
                l.after = after;
                l.escape = escape;
                if escape {
                    l.break_to = break_to;
                }
            },
            Statement::Break(id) => {
                let mut l = labels.labels.get_mut(id).unwrap();
                l.after = after;
                l.break_to = break_to;
                l.escape = true;
            },
            Statement::Compound(id, stmt) => {
                let escape;
                {
                    escape = Labels::set_labelling_tree_list(stmt, after, break_to, labels);
                }
                let mut l = labels.labels.get_mut(id).unwrap();
                l.after = after;
                l.escape = escape;
                if escape {
                    l.break_to = break_to;
                }
            }
        }
    }
    pub fn set_labelling_tree_list<'a>(s: &StatementList, after: i64, break_to: i64, labels: &'a mut Labels) -> bool {
        match s {
            StatementList::Empty(_) => false,
            StatementList::StatementList(_, sl, stmt) => {
                let mut escape;
                {
                    escape = Labels::set_labelling_tree_list(sl, stmt.id(), break_to, labels);
                }
                {
                    Labels::set_labelling_tree(stmt, after, break_to, labels);
                    let l_stmt = labels.labels.get_mut(&stmt.id()).unwrap();
                    escape |= l_stmt.escape;
                }
                escape
            },
        }
    }

    pub fn set_labelling_tree_program<'a>(p: &Program, labels: &'a mut Labels) -> Result<(), String> {
        match p {
            Program::Program(id, stmt)  => {
                let escape;
                {
                    Labels::set_labelling_tree(stmt, *id, *id, labels);
                    let l_stmt = labels.labels.get_mut(&stmt.id()).unwrap();
                    escape = l_stmt.escape;
                }
                match escape {
                    true => Ok(()),
                    false => Err("No escape allowed outside of while loop".to_string()),
                }
            },
        }
    }

    pub fn set_collections<'a>(s: &Statement, labels: &'a mut Labels) {
        let mut inside = HashSet::new();
        inside.insert(s.id());
        let mut breaks_of = HashSet::<i64>::new();
        {
            match s {
                Statement::Assign(_, _, _)  | Statement::Skip(_) | Statement::Decl(_) | Statement::Break(_) => {
                },
                Statement::IfThen(_, _, stmt) | Statement::While(_, _, stmt) => {
                    Labels::set_collections(stmt, labels);
                    breaks_of.extend(labels.labels[&stmt.id()].inside.iter());
                    inside.extend(labels.labels[&stmt.id()].inside.iter());
                },
                Statement::IfThenElse(_, _, stmt_true, stmt_false) => {
                    Labels::set_collections(stmt_true, labels);
                    Labels::set_collections(stmt_false, labels);
                    breaks_of.extend(labels.labels[&stmt_true.id()].inside.iter());
                    inside.extend(labels.labels[&stmt_true.id()].inside.iter());
                    breaks_of.extend(labels.labels[&stmt_false.id()].inside.iter());
                    inside.extend(labels.labels[&stmt_false.id()].inside.iter());
                },
                Statement::Compound(_, stmt) => {
                    Labels::set_collections_list(stmt, labels);
                    breaks_of.extend(labels.labels[&stmt.id()].inside.iter());
                    inside.extend(labels.labels[&stmt.id()].inside.iter());
                }
            }
        }

        let mut labs = HashSet::new();
        {
            labs.extend(inside.clone().iter());
            labs.insert(labels.labels[&s.id()].after);
        }

        let mut labx = HashSet::new();
        {
            let escape = &labels.labels[&s.id()].escape;
            labx.extend(labs.clone().iter());
            if *escape {
                labx.insert(labels.labels[&s.id()].break_to);
            }
        }
        {
            let labelling : &mut Labelling = labels.labels.get_mut(&s.id()).unwrap();
            labelling.breaks_of.extend(breaks_of);
            labelling.inside.extend(inside);
            labelling.labs.extend(labs);
            labelling.labx.extend(labx);
        }
    }

    pub fn set_collections_list<'a>(s: &StatementList, labels: &'a mut Labels) {
        let mut inside = HashSet::<i64>::new();
        let mut breaks_of = HashSet::<i64>::new();
        match s {
            StatementList::Empty(_) => {},
            StatementList::StatementList(_, sl, stmt) => {
                Labels::set_collections_list(sl, labels);
                Labels::set_collections(stmt, labels);
                breaks_of.extend(labels.labels[&sl.id()].inside.iter());
                inside.extend(labels.labels[&sl.id()].inside.iter());
                breaks_of.extend(labels.labels[&stmt.id()].inside.iter());
                inside.extend(labels.labels[&stmt.id()].inside.iter());
            },
        }

        {
            let labelling : &mut Labelling = labels.labels.get_mut(&s.id()).unwrap();
            labelling.breaks_of.extend(breaks_of);
            labelling.inside.extend(inside);
        }
    }

    pub fn set_collections_program<'a>(p: &Program, labels: &'a mut Labels) {
        let mut inside = HashSet::new();
        inside.insert(p.id());
        let mut breaks_of = HashSet::<i64>::new();
        {
            match p {
                Program::Program(_, stmt) => {
                    Labels::set_collections(stmt, labels);
                    breaks_of.extend(labels.labels[&stmt.id()].inside.iter());
                    inside.extend(labels.labels[&stmt.id()].inside.iter());
                },
            }
        }
    }
}
