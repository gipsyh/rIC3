use crate::Btor;
use giputils::{bitvec::BitVec, hash::GHashMap};
use logicrs::fol::{FolOp, Sort, Term, TermSymbol};
use num_bigint::{BigInt, Sign};
use num_traits::Num;

#[derive(Default)]
pub struct Parser {
    sorts: GHashMap<usize, Sort>,
    nodes: GHashMap<usize, Term>,
    input: Vec<Term>,
    latch: Vec<Term>,
    init: GHashMap<Term, Term>,
    next: GHashMap<Term, Term>,
    output: Vec<Term>,
    bad: Vec<Term>,
    constraint: Vec<Term>,
    symbols: TermSymbol,
    prop_labels: Vec<String>,
}

impl Parser {
    #[inline]
    fn get_node(&self, nid: isize) -> Term {
        let abs: usize = nid.unsigned_abs();
        let mut res = self.nodes.get(&abs).unwrap().clone();
        if nid < 0 {
            res = !res;
        }
        res
    }

    fn parse_sort<'a>(&self, mut split: impl Iterator<Item = &'a str>) -> Sort {
        match split.next().unwrap() {
            "bitvec" => {
                let w = split.next().unwrap().parse::<usize>().unwrap();
                Sort::Bv(w)
            }
            "array" => {
                let index = parse_id(&mut split);
                let element = parse_id(&mut split);
                let index = self.sorts.get(&index).unwrap();
                let element = self.sorts.get(&element).unwrap();
                if element.is_array() {
                    panic!("currently arrays of arrays are not supported");
                }
                Sort::Array(index.bv(), element.bv())
            }
            _ => panic!(),
        }
    }

    fn parse_symbol<'a>(&mut self, t: &Term, mut split: impl Iterator<Item = &'a str>) {
        // BTOR2 allows an optional symbol token, followed by an optional inline comment
        // starting with ';'. Only the first symbol token is significant; any following
        // whitespace-separated tokens are comments/ignored text.
        let Some(symbol) = split.next() else {
            return;
        };
        if symbol.starts_with(';') {
            return;
        }
        for symbol in symbol.split(',').filter(|symbol| !symbol.is_empty()) {
            self.symbols.add_symbol(t, symbol.to_string());
        }
    }

    pub fn parse(mut self, s: &str) -> Btor {
        for line in s.lines() {
            if line.starts_with(';') {
                continue;
            }
            let mut split = line.split_whitespace();
            let Some(id) = split.next() else {
                continue;
            };
            let id = id.parse().unwrap();
            let second = split.next().unwrap();
            match second {
                "sort" => {
                    let sort = self.parse_sort(split);
                    assert!(self.sorts.insert(id, sort).is_none());
                }
                "input" => {
                    let sort = *self.sorts.get(&parse_id(&mut split)).unwrap();
                    let v = Term::new_var(sort);
                    self.input.push(v.clone());
                    self.parse_symbol(&v, split);
                    assert!(self.nodes.insert(id, v).is_none());
                }
                "state" => {
                    let sort = *self.sorts.get(&parse_id(&mut split)).unwrap();
                    let v = Term::new_var(sort);
                    self.latch.push(v.clone());
                    self.parse_symbol(&v, split);
                    assert!(self.nodes.insert(id, v).is_none());
                }
                "init" => {
                    let _sort = self.sorts.get(&parse_id(&mut split)).unwrap();
                    let state = self.get_node(parse_signed_id(&mut split));
                    let value = self.get_node(parse_signed_id(&mut split));
                    self.init.insert(state, value);
                }
                "next" => {
                    let sort = self.sorts.get(&parse_id(&mut split)).unwrap();
                    let state = self.get_node(parse_signed_id(&mut split));
                    let value = self.get_node(parse_signed_id(&mut split));
                    assert!(state.sort().eq(sort));
                    assert!(value.sort().eq(sort));
                    self.next.insert(state, value);
                }
                "output" => {
                    let o = self.get_node(parse_signed_id(&mut split));
                    self.output.push(o.clone());
                    self.parse_symbol(&o, split);
                    assert!(self.nodes.insert(id, o).is_none());
                }
                "bad" => {
                    let b = self.get_node(parse_signed_id(&mut split));
                    if let Some(symbol) = split.next()
                        && !symbol.starts_with(';')
                    {
                        self.prop_labels.push(symbol.to_string());
                    } else {
                        self.prop_labels.push(String::new());
                    }
                    self.bad.push(b);
                }
                "constraint" => {
                    let c = self.get_node(parse_signed_id(&mut split));
                    self.parse_symbol(&c, split);
                    self.constraint.push(c);
                }
                "const" | "constd" | "consth" => {
                    let ty = ConstType::try_from(second).unwrap();
                    let sort = *self.sorts.get(&parse_id(&mut split)).unwrap();
                    let Sort::Bv(w) = sort else { todo!() };
                    let c = split.next().unwrap();
                    let radix = match ty {
                        ConstType::Const => 2,
                        ConstType::Constd => 10,
                        ConstType::Consth => 16,
                    };
                    let c = BigInt::from_str_radix(c, radix).unwrap();
                    let (s, c) = c.to_radix_le(2);
                    let mut c: Vec<bool> = c.into_iter().map(|x| x == 1).collect();
                    assert!(c.len() <= w);
                    while c.len() < w {
                        c.push(false);
                    }
                    if let Sign::Minus = s {
                        c = c.into_iter().map(|x| !x).collect();
                        let mut carry = true;
                        for i in c.iter_mut() {
                            if !carry {
                                break;
                            }
                            let ni = *i ^ carry;
                            carry = *i && carry;
                            *i = ni;
                        }
                    }
                    let v = Term::bv_const(BitVec::from(&c));
                    self.parse_symbol(&v, split);
                    assert!(self.nodes.insert(id, v).is_none());
                }
                "zero" => {
                    let sort = *self.sorts.get(&parse_id(&mut split)).unwrap();
                    let v = Term::bv_const(BitVec::zero(sort.bv()));
                    self.parse_symbol(&v, split);
                    assert!(self.nodes.insert(id, v).is_none());
                }
                "one" => {
                    let sort = *self.sorts.get(&parse_id(&mut split)).unwrap();
                    let v = Term::bv_const(BitVec::one(sort.bv()));
                    self.parse_symbol(&v, split);
                    assert!(self.nodes.insert(id, v).is_none());
                }
                "ones" => {
                    let sort = *self.sorts.get(&parse_id(&mut split)).unwrap();
                    let v = Term::bv_const(BitVec::ones(sort.bv()));
                    self.parse_symbol(&v, split);
                    assert!(self.nodes.insert(id, v).is_none());
                }
                _ => {
                    let term = self.parse_op(second, split);
                    assert!(self.nodes.insert(id, term).is_none());
                }
            }
        }
        Btor {
            input: self.input,
            latch: self.latch,
            init: self.init,
            next: self.next,
            bad: self.bad,
            output: self.output,
            constraint: self.constraint,
            symbols: self.symbols,
            prop_label: self.prop_labels,
        }
    }

    fn parse_op<'a>(&mut self, second: &str, mut split: impl Iterator<Item = &'a str>) -> Term {
        let op = FolOp::from(second);
        let sort = self.sorts.get(&parse_id(&mut split)).unwrap();
        let mut operand = Vec::new();
        if op == FolOp::Uext || op == FolOp::Sext {
            let opa = self.get_node(parse_signed_id(&mut split));
            let ext_len: usize = split.next().unwrap().parse().unwrap();
            if ext_len == 0 {
                self.parse_symbol(&opa, split);
                return opa;
            } else {
                let ext_len = Term::bv_const(BitVec::zero(ext_len));
                operand.push(opa);
                operand.push(ext_len);
            }
        } else if op == FolOp::Slice {
            let opa = self.get_node(parse_signed_id(&mut split));
            let high: usize = split.next().unwrap().parse().unwrap();
            let low: usize = split.next().unwrap().parse().unwrap();
            operand.push(opa);
            operand.push(Term::bv_const(BitVec::zero(high)));
            operand.push(Term::bv_const(BitVec::zero(low)));
        } else {
            for _ in 0..op.num_operand() {
                operand.push(self.get_node(parse_signed_id(&mut split)));
            }
        }
        let res = Term::new_op(op, &operand);
        assert!(res.sort().eq(sort));
        self.parse_symbol(&res, split);
        res
    }
}

#[derive(Debug, Clone, strum::EnumString, strum::Display)]
#[strum(serialize_all = "lowercase")]
pub enum ConstType {
    Const = 2,
    Constd = 10,
    Consth = 16,
}

#[inline]
fn parse_id<'a>(split: &mut impl Iterator<Item = &'a str>) -> usize {
    split.next().unwrap().parse().unwrap()
}

#[inline]
fn parse_signed_id<'a>(split: &mut impl Iterator<Item = &'a str>) -> isize {
    split.next().unwrap().parse().unwrap()
}
