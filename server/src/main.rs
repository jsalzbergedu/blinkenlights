#[allow(unused_imports)]
use actix_web::{get, post, web, App, HttpResponse, HttpServer, Responder, http::header::HttpDate, HttpRequest};

use serde::{Serialize, Deserialize};
use std::{collections::HashMap, io::{BufWriter, Write, ErrorKind, BufReader, BufRead}};
use mktemp::Temp;
use std::process::{ Command, Stdio };

use server::db::*;
use server::ast::*;

#[get("/api")]
async fn hello() -> impl Responder {
    HttpResponse::Ok().body("Hello world!")
}

#[post("/api/echo")]
async fn echo(req_body: String) -> impl Responder {
    HttpResponse::Ok().body(req_body)
}

#[derive(Serialize, Deserialize)]
struct NodeResponse {
    node: i64,
}

#[derive(Serialize, Deserialize)]
struct AnalyzeRequest {
    document: String,
}

fn write_tmp_file(s: &str) -> std::io::Result<i64> {
    let path = Temp::new_file()?;
    {
        let f = std::fs::File::create(&path)?;
        let mut f = BufWriter::new(&f);
        f.write_all(s.as_bytes())?;
        match f.flush() {
            Ok(it) => it,
            Err(err) => {
                println!("{:?}", err);
                return Err(err)
            },
        };
    }
    let cmd = Command::new("timeout")
        .arg("10s")
        .arg("python3")
        .arg("../parser/blinkenlights/blinkenlights.py")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
     match cmd.stdin {
         Some(mut stdin) => stdin.write(format!(r#"{{"command": "parse", "filename": "{}"}}"#,
                                                &path.as_path()
                                                .as_os_str()
                                                .to_owned()
                                                .into_string()
                                                .map_err(|_| std::io::Error::new(ErrorKind::Other, "bad path string"))?).as_bytes()).map(|_| ()),
        None => Err(std::io::Error::new(ErrorKind::Other, "No stdin")),
    }?;
     match cmd.stdout {
         Some(stdout) => {
             let mut buf = String::new();
             let mut reader = BufReader::new(stdout);
             reader.read_line(&mut buf)?;
             let node_response : NodeResponse  = serde_json::from_str(&buf)?;
             Ok(node_response.node)
         }
        None => Err(std::io::Error::new(ErrorKind::Other, "No stdout")),
    }
}

#[post("/api/analyze")]
async fn analyze(body: String) -> Result<impl Responder, std::io::Error> {
    let mut map = HashMap::new();
    let mut dummy_property = Vec::new();
    let analyze_request : AnalyzeRequest = serde_json::from_str(&body)?;
    dummy_property.push((0, "dummyword".to_string(), "dummyprop".to_string()));
    map.insert(9, dummy_property);
    let pgm_idt = write_tmp_file(&analyze_request.document)?;
    let db = DB::from_path("analysis.db")?;
    match Program::from_db(&db, pgm_idt) {
        Ok(p) => {
            let mut labels = Labels::from_program(&p);
            match Labels::set_labelling_tree_program(&p, &mut labels) {
                Err(err) => return Err(std::io::Error::new(std::io::ErrorKind::Other, err)),
                _ => {},
            };
            Labels::set_collections_program(&p, &mut labels);
            println!("Labels: {:?}",  labels);
        },
        Err(str) => {println!("{}", str); return Err(std::io::Error::new(std::io::ErrorKind::Other, str));},
    };
    Ok(HttpResponse::Ok().json(map))
}

#[actix_web::main]
async fn main() -> Result<(), std::io::Error> {
    println!("hello?");
    HttpServer::new(|| {
        App::new().service(hello).service(echo).service(analyze)
    }).bind(("127.0.0.1", 8000))?.run().await
}
