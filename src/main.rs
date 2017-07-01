extern crate itertools;
extern crate rand;

use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result};
use std::iter::Peekable;
use std::str::Chars;
use std::env;
use std::fs::File;
use std::path::Path;
use std::io::Read;
use itertools::join;
use Term::*;

////////////////////////////////////////////////////////////////////////////////
// DATA

/// Prolog term:
///   variable: every identifier that starts with uppercase letter
///   atom: term without arguments
///   predicate: term with arguments ( <name>(<arg1>,...,<argN>) )
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Term {
    Var(String),
    Atom(String),
    Pred(String, Vec<Term>)
}

/// Prolog clause:
///   <term> [ :- <term> (, <term>)* ].
#[derive(Debug, Clone, PartialEq, Eq)]
struct Clause {
    head: Term,
    body: Option<Vec<Term>>
}

/// Environment
type Bindings = HashMap<Term, Term>;
type OptBindings = Option<Bindings>;

/// Database of facts
type FactDB = HashMap<String, Vec<Clause>>;

/// Result of a prove:
///   [] -> unsatisfiable
///   vec -> vector of assigments
type ProveResult = Vec<Bindings>;

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> Result {
        match self {
            &Var(ref x) if x.ends_with("__") && x.starts_with("__") => write!(f, "_"),
            &Var(ref x) | &Atom(ref x) => write!(f, "{}", x),
            &Pred(ref x, ref xs) =>
                write!(f, "{}({})", x, join(xs.iter().map(|x| x.to_string()), ", "))
        }
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if let Some(ref body) = self.body {
            write!(f, "{} :- {}.", self.head,
                   join(body.iter().map(|x| x.to_string()), ", "))
        } else {
            write!(f, "{}.", self.head)
        }
    }
}

/// Extract term variables
fn vars(x: &Term) -> Vec<&Term> {
    match x {
        &Var(_) => vec![x],
        &Atom(_) => vec![],
        &Pred(_, ref xs) => xs.iter().flat_map(vars).collect()
    }
}

/// Get the name of a term
fn term_name(term: &Term) -> &String {
    match term {
        &Atom(ref s) => s,
        &Pred(ref s, _) => s,
        &Var(ref s) => s
    }
}

////////////////////////////////////////////////////////////////////////////////
// UNIFICATION

/// Unify two terms in the current enviroment.
fn unify(x: &Term, y: &Term, env: OptBindings) -> OptBindings {
    if let None = env {
        return None
    }

    match (x, y) {
        (&Var(ref x), &Var(ref y)) if x == y => env,
        (&Var(_), y) => unify_variable(x, y, env),
        (x, &Var(_)) => unify_variable(y, x, env),
        (&Atom(ref a), &Atom(ref b)) if a == b => env,
        (&Pred(ref a, ref xs), &Pred(ref b, ref ys)) if a == b && xs.len() == ys.len() => {
            let mut nenv = env;
            for i in 0 .. xs.len() {
                nenv = unify(&xs[i], &ys[i], nenv);
            }
            nenv
        }
        _ => None
    }
}

/// Unify a variable and a term in the current environment
fn unify_variable(var: &Term, x: &Term, env: OptBindings) -> OptBindings {
    let mut binds = env.unwrap();

    if binds.contains_key(var) {
        let val = binds.get(var).unwrap().clone();
        return unify(&val, x, Some(binds))
    } else if binds.contains_key(x) {
        let val = binds.get(x).unwrap().clone();
        return unify(var, &val, Some(binds))
    } // no occurs check
    binds.insert(var.clone(), x.clone());
    Some(binds)
}

///////////////////////////////////////////////////////////////////////////////
// PARSER

/// Parse a string until it satisfies the predicate `f'
fn take_while<F>(f: F, iter: &mut Peekable<Chars>) -> Option<String>
    where F: Fn(char) -> bool {

    let mut s = String::new();
    loop {
        match iter.peek() {
            Some(c) if f(*c) => s.push(*c),
            _ => break
        }
        iter.next();
    }
    Some(s)
}

/// Parse the string s with spaces before and after it
fn parse_symbol(s: &str, iter: &mut Peekable<Chars>) -> Option<()> {
    take_while(|c| c.is_whitespace(), iter);
    for ch in s.chars() {
        match iter.peek() {
            Some(c) if *c == ch => (),
            _ => return None
        }
        iter.next();
    }
    take_while(|c| c.is_whitespace(), iter);
    Some(())
}

/// Run the parser "p >> s" multiple times
fn sep_by1<R,O,P,S>(p: P, s: S, iter: &mut Peekable<Chars>) -> Option<Vec<R>>
    where P: Fn(&mut Peekable<Chars>) -> Option<R>,
          S: Fn(&mut Peekable<Chars>) -> Option<O> {

    let mut vec = Vec::new();
    loop {
        match p(iter) {
            None => return None,
            Some(t) => vec.push(t)
        }
        if let Some(_) = s(iter) { continue }
        break
    }
    Some(vec)
}

/// Run the parser `p' between `o' and `c'
fn between<R,S,T,O,P,C>(o: O, c: C, p: P, iter: &mut Peekable<Chars>) -> Option<R>
    where P: Fn(&mut Peekable<Chars>) -> Option<R>,
          O: Fn(&mut Peekable<Chars>) -> Option<S>,
          C: Fn(&mut Peekable<Chars>) -> Option<T> {
    o(iter).and_then(|_| p(iter).and_then(|r| c(iter).map(|_|r)))
}

/// Parse a prolog clause
fn parse_clause(iter:  &mut Peekable<Chars>) -> Option<Clause> {
    parse_term(iter).and_then(|head|{
        let body = parse_symbol(":-", iter).and_then(|_|
                   sep_by1(parse_term, |i| parse_symbol(",",i), iter));
        Some(Clause { head: head, body: body })
    })
}

/// Parse a prolog term
fn parse_term(iter: &mut Peekable<Chars>) -> Option<Term> {

    fn parse_name(iter: &mut Peekable<Chars>) -> Option<String> {
        match take_while(|c| c.is_alphanumeric() || c == '_', iter) {
            Some(ref s) if !s.is_empty() => Some(s.clone()),
            _ => None
        }
    }

    fn parse_arglist(iter: &mut Peekable<Chars>) -> Option<Vec<Term>> {
        between(|i| parse_symbol("(", i),
                |i| parse_symbol(")", i),
                |i| sep_by1(parse_term, |it| parse_symbol(",",it), i),
                iter)
    }

    parse_name(iter).and_then(|name|
        Some(match parse_arglist(iter) {
            Some(args) => Pred(name, args),
            _ => if name.chars().next().unwrap().is_uppercase() { Var(name) }
            else if name == "_" { Var(gen_sym(&name)) }
            else { Atom(name) }
        }))
}

////////////////////////////////////////////////////////////////////////////////
// PROVE

/// Prova a goal in the environment using a fact database
fn prove(goal: &Term, env: OptBindings, facts: &FactDB) -> ProveResult {
    let mut results: Vec<Bindings> = vec![];

    if let &Var(_) = goal {
        return results
    }

    let predicate = term_name(goal);

    if let Some(clauses) = facts.get(predicate) {
        for clause in clauses {
            let nclause = rename_vars(clause);
            let nenv = unify(goal, &nclause.head, env.clone());
            match nclause.body {
                Some(ref body) => {
                    let mut res = prove_all(&body, nenv, facts);
                    results.append(&mut res)
                }
                _ => if let Some(e) = nenv { results.push(e) }
            }
        }

    }
    results
}

/// Prove all the goals
fn prove_all(goals: &[Term], env: OptBindings, facts: &FactDB) -> ProveResult {
    let mut results: Vec<Bindings> = vec![];

    if let None = env {
        return results
    }

    if goals.is_empty() && env.is_some() {
        results.push(env.unwrap());
        return results
    }

    let res = prove(&goals[0], env, facts);
    for nenv in res {
        let mut v = prove_all(&goals[1..], Some(nenv), facts);
        results.append(&mut v)
    }
    results
}

////////////////////////////////////////////////////////////////////////////////
// UTILS

/// Generate unique symbol
fn gen_sym(s: &str) -> String {
    if s == "_" {
        format!("__{}__", rand::random::<u32>())
    } else {
        format!("{}_{}", s, rand::random::<u32>())
    }
}

/// Get variable binding recursively if exists
fn get_result(var: &Term, binds: &Bindings) -> Option<Term>{
    match var {
        &Var(_) => binds.get(var).and_then(|x| get_result(x, binds)),
        _ => Some(var.clone())
    }
}

/// Display prove result
fn show_result(r: ProveResult, vars: Vec<&Term>) -> String {
    if r.is_empty() {
        format!("no.")
    } else if vars.is_empty() {
        format!("yes.")
    } else {
        let lines = r.iter().map(|b| join(vars.iter().map(|v| match v {
            &&Var(ref s) => format!("{} = {}", s, get_result(v, b).unwrap()),
            _ => panic!("`{}' is NOT a variable!")
        }), ", "));
        join(lines, ";\n") + "."
    }
}

/// Rename variables inside a clause
fn rename_vars(x: &Clause) -> Clause {
    let mut vars = HashMap::new();
    let &Clause{ref head, ref body} = x;

    fn rename_term_vars(x: &Term, vars: &mut HashMap<String, Term>) -> Term {
        match x {
            &Var(ref s) if vars.contains_key(s) => vars.get(s).unwrap().clone(),
            &Var(ref s) => {
                let new = Var(gen_sym(s));
                if s != "_" {
                    vars.insert(s.clone(), new.clone());
                }
                new
            }
            &Pred(ref n, ref xs) =>
                Pred(n.clone(),
                     xs.into_iter().map(|x| rename_term_vars(x,vars)).collect()),
            t => t.clone()
        }
    }

    Clause{
        head: rename_term_vars(head, &mut vars),
        body: body.clone().map(|x| x.into_iter()
                               .map(|x| rename_term_vars(&x,&mut vars)).collect())
    }
}

/// Insert a clause in the database
fn insert_clause(clause: Clause, facts:  &mut FactDB) {
    if facts.contains_key(term_name(&clause.head)) {
        let others = facts.get_mut(term_name(&clause.head)).unwrap();
        others.push(clause)
    } else {
        facts.insert(term_name(&clause.head).clone(), vec![clause]);
    }
}

////////////////////////////////////////////////////////////////////////////////
// MAIN

/// Prolog interactive console:
///  every line that ends with "." is a statement and is added to the database
///  every line that ends with "?" is a query
///  "list" shows the contents of the db
///  "quit" quits the interpreter
fn prolog_interact(facts: &mut FactDB) {
    use std::io::*;

    let reader = stdin();
    let mut writer = stdout();
    let mut line = String::new();
    loop {
        print!("?- ");
        writer.flush().unwrap();

        line.clear();
        reader.read_line(&mut line).unwrap();

        if line == "quit\n" || line == "q\n" {
            break
        }

        if line == "list\n" || line == "l\n" {
            for (_, v) in facts.iter() {
                for clause in v {
                    println!("{}", clause);
                }
                println!("")
            }
        }

        if line.ends_with("?\n") {
            let read = parse_term(&mut line.chars().peekable());
             if let Some(query) = read {
                 println!("{}", show_result(
                     prove(&query, Some(HashMap::new()), facts),
                     vars(&query)
                 ))
             }
        }

        if line.ends_with(".\n") {
            let read = parse_clause(&mut line.chars().peekable());
            if let Some(clause) = read {
                insert_clause(clause, facts);
                println!("ok.")
            }
        }
    }
}

// parse file and insert the clauses in the db
fn load_file(filename: &str, facts: &mut FactDB) {
    let path = Path::new(filename);
    let mut file = File::open(&path).unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();

    let mut iterator = contents.chars().peekable();
    loop {
        match parse_clause(&mut iterator) {
            Some(clause) => {
                println!("{}", clause);
                insert_clause(clause, facts);
                parse_symbol(".", &mut iterator);
            }
            _ => break
        }
    }
}

fn main () {
    let mut facts = HashMap::new();

    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        load_file(&args[1], &mut facts)
    }

    prolog_interact(&mut facts);
}
