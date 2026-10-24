use crate::{Lit, LitVec, Var};
use std::{
    fs::{File, read_to_string},
    io::Write,
    path::Path,
};

pub fn from_dimacs_file<P: AsRef<Path>>(file: P) -> Vec<LitVec> {
    let str = read_to_string(file).unwrap();
    from_dimacs_str(&str)
}

pub fn from_dimacs_str(str: &str) -> Vec<LitVec> {
    let mut cnf = Vec::new();
    for line in str.lines() {
        if line.is_empty() || &line[0..1] == "p" || &line[0..1] == "c" {
            continue;
        }
        let mut clause: Vec<i32> = line
            .split_whitespace()
            .map(|s| s.parse::<i32>().unwrap())
            .collect();
        assert!(clause.pop().unwrap() == 0);
        cnf.push(LitVec::from_iter(clause.into_iter().map(|lit| {
            Lit::new(Var::new((lit.unsigned_abs() - 1) as _), lit > 0)
        })));
    }
    cnf
}

pub fn to_dimacs(cnf: &[LitVec]) -> String {
    let mut max_var = 0;
    for cls in cnf.iter() {
        max_var = max_var.max(
            cls.iter()
                .map(|l| Into::<usize>::into(l.var()))
                .max()
                .unwrap(),
        );
    }
    max_var += 1;
    let mut dimacs = Vec::new();
    dimacs.push(format!("p cnf {max_var} {}", cnf.len()));
    for cls in cnf.iter() {
        let mut s = String::new();
        for l in cls.iter().map(|l| {
            let mut res = Into::<usize>::into(l.var()) as i32 + 1;
            if !l.polarity() {
                res = -res;
            }
            res
        }) {
            s.push_str(&format!("{l} "));
        }
        s.push('0');
        dimacs.push(s);
    }
    dimacs.join("\n")
}

pub fn to_dimacs_file<P: AsRef<Path>>(cnf: &[LitVec], file: P) {
    let dimacs = to_dimacs(cnf);
    let mut file = File::create(file).unwrap();
    file.write_all(dimacs.as_bytes()).unwrap();
}
