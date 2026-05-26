use enum_as_inner::EnumAsInner;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{
    Lbool, LboolVec,
    fol::{Sort, Term, Value as FolValue},
};
use rIC3::wltransys::{certify::WlCex, symbol::WlTsSymbol};
use std::io::{self, Write};
use vcd::{ReferenceIndex, TimescaleUnit, Value as VcdValue, VarType};

#[derive(Debug)]
struct DumpTarget {
    id: vcd::IdCode,
    array_index: Option<usize>,
}

#[derive(EnumAsInner, Debug)]
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
        term_ids: &mut GHashMap<Term, Vec<DumpTarget>>,
        array_indices: &GHashMap<Term, GHashSet<usize>>,
    ) -> io::Result<()> {
        match self {
            Scope::Node(node) => {
                for (name, child) in node.iter() {
                    match child {
                        Scope::Node(_) => {
                            writer.add_module(name)?;
                            child.define_scope_rec(writer, term_ids, array_indices)?;
                            writer.upscope()?;
                        }
                        Scope::Var(t) => match t.sort() {
                            Sort::Bv(width) => {
                                let id = writer.add_var(VarType::Wire, width as _, name, None)?;
                                term_ids.entry(t.clone()).or_default().push(DumpTarget {
                                    id,
                                    array_index: None,
                                });
                            }
                            Sort::Array(_, element_width) => {
                                if let Some(indices) = array_indices.get(t) {
                                    let mut indices: Vec<_> = indices.iter().copied().collect();
                                    indices.sort_unstable();
                                    for index in indices {
                                        let id = writer.add_var(
                                            VarType::Wire,
                                            element_width as _,
                                            name,
                                            Some(ReferenceIndex::BitSelect(index as i32)),
                                        )?;
                                        term_ids.entry(t.clone()).or_default().push(DumpTarget {
                                            id,
                                            array_index: Some(index),
                                        });
                                    }
                                }
                            }
                        },
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
        term_ids: &mut GHashMap<Term, Vec<DumpTarget>>,
        array_indices: &GHashMap<Term, GHashSet<usize>>,
    ) -> io::Result<()> {
        let node = self.as_node().unwrap();
        if node.values().any(|s| s.is_var()) {
            writer.add_module("")?;
            self.define_scope_rec(writer, term_ids, array_indices)?;
            writer.upscope()?;
        } else {
            self.define_scope_rec(writer, term_ids, array_indices)?;
        }
        Ok(())
    }
}

fn lbool_vec_to_vcd(val: &LboolVec) -> Vec<VcdValue> {
    (0..val.len())
        .rev()
        .map(|i| match val.get(i) {
            Lbool::TRUE => VcdValue::V1,
            Lbool::FALSE => VcdValue::V0,
            _ => VcdValue::X,
        })
        .collect()
}

pub fn wlwitness_vcd(
    cex: &WlCex,
    sym: &WlTsSymbol,
    out: impl Write,
    filter: &str,
) -> io::Result<()> {
    let mut writer = vcd::Writer::new(out);
    writer.timescale(1, TimescaleUnit::NS)?;

    let mut present_terms = GHashSet::default();
    let mut array_indices = GHashMap::<Term, GHashSet<usize>>::default();
    for frame in &cex.input {
        for tv in frame {
            present_terms.insert(tv.t().clone());
        }
    }
    for frame in &cex.state {
        for tv in frame {
            present_terms.insert(tv.t().clone());
            if let FolValue::Array(array) = tv.v() {
                for (index, value) in array.iter() {
                    if !value.all_x() {
                        array_indices
                            .entry(tv.t().clone())
                            .or_default()
                            .insert(*index);
                    }
                }
            }
        }
    }
    let mut root = Scope::default();
    // Strip the parent of `filter` so the dumped hierarchy starts at `filter`.
    // Example: filter="a.b.c" => parent="a.b" => signal "a.b.c.d" becomes "c.d".
    let filter_parent = filter.rsplit_once('.').map(|(p, _)| p).unwrap_or("");
    for (term, name) in sym.iter() {
        if !present_terms.contains(term) {
            continue;
        }
        for name in name.iter() {
            if !name.starts_with(filter) {
                continue;
            }
            let relative = if filter_parent.is_empty() {
                name.as_str()
            } else {
                name.strip_prefix(filter_parent)
                    .unwrap()
                    .trim_start_matches('.')
            };
            if name.starts_with("_witness_.") {
                continue;
            }

            let parts: Vec<&str> = relative.split('.').filter(|s| !s.is_empty()).collect();
            if !parts.is_empty() {
                root.insert(&parts, term.clone());
            }
        }
    }
    let mut term_ids = GHashMap::default();
    root.define_scope(&mut writer, &mut term_ids, &array_indices)?;
    writer.enddefinitions()?;

    for t in 0..cex.len() {
        writer.timestamp(t as u64)?;

        let mut frame_values = GHashMap::default();

        for tv in &cex.input[t] {
            frame_values.insert(tv.t().clone(), FolValue::Bv(tv.v().clone()));
        }
        for tv in &cex.state[t] {
            frame_values.insert(tv.t().clone(), tv.v().clone());
        }
        for (term, targets) in term_ids.iter() {
            if let Some(val) = frame_values.get(term) {
                for target in targets {
                    let vcd_val = match (val, target.array_index) {
                        (FolValue::Bv(val), None) => lbool_vec_to_vcd(val),
                        (FolValue::Array(array), Some(index)) => {
                            let Some(val) = array.get(&index) else {
                                continue;
                            };
                            if val.all_x() {
                                continue;
                            }
                            lbool_vec_to_vcd(val)
                        }
                        _ => continue,
                    };
                    writer.change_vector(target.id, vcd_val)?;
                }
            }
        }
    }
    writer.timestamp(cex.len() as u64)?;

    Ok(())
}
