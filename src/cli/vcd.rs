use enum_as_inner::EnumAsInner;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::fol::{Sort, Term};
use rIC3::wltransys::certify::WlWitness;
use std::io::{self, Write};
use vcd::{TimescaleUnit, Value, VarType};

#[derive(EnumAsInner)]
enum Scope {
    Node(GHashMap<String, Scope>),
    Var(Term),
}

impl Default for Scope {
    fn default() -> Self {
        Self::Node(Default::default())
    }
}

impl Scope {
    fn insert(&mut self, path: &[&str], term: Term) {
        if path.is_empty() {
            *self = Self::Var(term)
        } else {
            let map = self.as_node_mut().unwrap();
            map.entry(path[0].to_string())
                .or_default()
                .insert(&path[1..], term);
        }
    }

    fn define_scope_rec(
        &self,
        writer: &mut vcd::Writer<impl Write>,
        term_ids: &mut GHashMap<Term, vcd::IdCode>,
    ) -> io::Result<()> {
        match self {
            Scope::Node(node) => {
                for (name, child) in node.iter() {
                    match child {
                        Scope::Node(_) => {
                            writer.add_module(name)?;
                            child.define_scope_rec(writer, term_ids)?;
                            writer.upscope()?;
                        }
                        Scope::Var(t) => {
                            let id =
                                writer.add_var(VarType::Wire, t.sort().bv() as _, name, None)?;
                            term_ids.insert(t.clone(), id);
                        }
                    }
                }
            }
            Scope::Var(_) => unreachable!(),
        }
        Ok(())
    }

    fn define_scope(
        &self,
        writer: &mut vcd::Writer<impl Write>,
        term_ids: &mut GHashMap<Term, vcd::IdCode>,
    ) -> io::Result<()> {
        let node = self.as_node().unwrap();
        if node.values().any(|s| s.is_var()) {
            writer.add_module("top")?;
            self.define_scope_rec(writer, term_ids)?;
            writer.upscope()?;
        } else {
            self.define_scope_rec(writer, term_ids)?;
        }
        Ok(())
    }
}

pub fn wlwitness_vcd(
    wit: &WlWitness,
    sym: &GHashMap<Term, String>,
    out: impl Write,
) -> io::Result<()> {
    let mut writer = vcd::Writer::new(out);
    writer.timescale(1, TimescaleUnit::NS)?;

    let mut present_terms = GHashSet::default();
    for frame in &wit.input {
        for tv in frame {
            present_terms.insert(tv.t().clone());
        }
    }
    for frame in &wit.state {
        for tv in frame {
            present_terms.insert(tv.t().clone());
        }
    }
    let mut root = Scope::default();
    for (term, name) in sym.iter() {
        if !present_terms.contains(term) {
            continue;
        }
        let parts: Vec<&str> = name.split('.').collect();
        if !parts.is_empty() {
            root.insert(&parts, term.clone());
        }
    }
    let mut term_ids = GHashMap::default();
    root.define_scope(&mut writer, &mut term_ids)?;
    writer.enddefinitions()?;

    for t in 0..wit.len() {
        writer.timestamp(t as u64)?;

        let mut frame_values = GHashMap::default();

        for tv in &wit.input[t] {
            frame_values.insert(tv.t().clone(), tv.v().clone());
        }
        for tv in &wit.state[t] {
            if let Sort::Bv(_) = tv.t().sort() {
                let bv_tv = tv.into_bv();
                frame_values.insert(bv_tv.t().clone(), bv_tv.v().clone());
            }
        }

        for (term, id) in term_ids.iter() {
            if let Some(val) = frame_values.get(term) {
                let len = val.len();
                let vcd_val: Vec<Value> = (0..len)
                    .rev()
                    .map(|i| {
                        let is_valid = val.mask().get(i);
                        let is_true = val.v().get(i);
                        if !is_valid {
                            Value::X
                        } else if is_true {
                            Value::V1
                        } else {
                            Value::V0
                        }
                    })
                    .collect();
                writer.change_vector(*id, vcd_val)?;
            }
        }
    }
    writer.timestamp(wit.len() as u64)?;

    Ok(())
}
