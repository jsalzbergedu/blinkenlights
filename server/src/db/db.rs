use std::path::Path;

use serde::{Serialize, Deserialize};
use serde_rusqlite::from_rows;
use rusqlite::Connection;
use std::io::{Error, ErrorKind};

pub trait FromDB: Sized {
    fn table_name<'a>() -> &'a str;
    fn from_db(con: &mut Connection) -> Vec<Self> where for<'de> Self: Deserialize<'de> {
        let mut statement = con.prepare(&format!("SELECT * FROM {}", Self::table_name())).unwrap();
        from_rows::<Self>(statement.query([]).unwrap()).map(|item| item.unwrap()).collect()
    }
}

pub trait Identifiable {
    fn id(&self) -> i64;
}

pub fn get<'a, T, F: Fn(&T) -> bool>(collection: &'a Vec<T>,  f: F) -> Result<&'a T, String> {
    match collection.iter().filter(|element| f(element)).collect::<Vec<&T>>().get(0) {
        Some(element) => Ok(element),
        None => Err("no matching element in collection".to_string()),
    }
}

// pub fn get_by_field<'a, T, F: Fn(&T) -> i64>(collection: &'a Vec<T>,  f: F, id: i64) -> Result<&'a T, String> {
//     get(collection, |elt| )
//     // match collection.iter().filter(|element| f(element) == id).collect::<Vec<&T>>().get(0) {
//     //     Some(element) => Ok(element),
//     //     None => Err(format!("{} not in collection", id)),
//     // }
// }

pub fn get_by_id<'a, T: Identifiable>(collection: &'a Vec<T>, id: i64) -> Result<&'a T, String> {
    get(collection, |elt| elt.id() == id)
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Node {
    pub kind: String,
    pub id: i64,
}

impl FromDB for Node {
    fn table_name<'a>() -> &'a str {
        return "node";
    }
}

impl Identifiable for Node {
    fn id(&self) -> i64 {
        self.id
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct FileInfo {
    pub id: i64,
    pub filename: String,
    pub column: String,
    pub line: String,
    pub node: i64,
}

impl FromDB for FileInfo {
    fn table_name<'a>() -> &'a str {
        return "fileinfo";
    }
}

impl Identifiable for FileInfo {
    fn id(&self) -> i64 {
        self.id
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Children {
    pub id: i64,
    pub node: i64,
    pub idx: i64,
    pub child: i64,
}

impl FromDB for Children {
    fn table_name<'a>() -> &'a str {
        return "children";
    }
}

impl Identifiable for Children {
    fn id(&self) -> i64 {
        self.id
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Expr {
    pub kind: String,
    pub id: i64,
}

impl Identifiable for Expr {
    fn id(&self) -> i64 {
        self.id
    }
}

impl FromDB for Expr {
    fn table_name<'a>() -> &'a str {
        return "expr";
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct ExprChildren {
    pub id: i64,
    pub expr: i64,
    pub idx: i64,
    pub child: i64,
}

impl FromDB for ExprChildren {
    fn table_name<'a>() -> &'a str {
        return "expr_children";
    }
}

impl Identifiable for ExprChildren {
    fn id(&self) -> i64 {
        self.id
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Variable {
    pub id: i64,
    pub name: String,
}

impl FromDB for Variable {
    fn table_name<'a>() -> &'a str {
        return "variable";
    }
}

impl Identifiable for Variable {
    fn id(&self) -> i64 {
        self.id
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Constant {
    pub id: i64,
    pub constant: i64,
}

impl FromDB for Constant {
    fn table_name<'a>() -> &'a str {
        return "constant";
    }
}

impl Identifiable for Constant {
    fn id(&self) -> i64 {
        self.id
    }
}

pub struct DB {
    pub node: Vec<Node>,
    pub fileinfo: Vec<FileInfo>,
    pub children: Vec<Children>,
    pub expr: Vec<Expr>,
    pub expr_children: Vec<ExprChildren>,
    pub variable: Vec<Variable>,
    pub constant: Vec<Constant>
}

impl DB {
    pub fn from_db(con: &mut Connection) -> Self {
        DB {
            node: Node::from_db(con),
            fileinfo: FileInfo::from_db(con),
            children: Children::from_db(con),
            expr: Expr::from_db(con),
            expr_children: ExprChildren::from_db(con),
            variable: Variable::from_db(con),
            constant: Constant::from_db(con)
        }
    }

    pub fn from_path<P: AsRef<Path>>(p: P) -> Result<Self, Error> {
        let mut con = Connection::open(p).map_err(|_| Error::new(ErrorKind::Other, "Failed to connect to db"))?;
        Ok(DB::from_db(&mut con))
    }
}
