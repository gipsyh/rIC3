use crate::cli::{Ric3Config, cache::Ric3Proj, yosys::Yosys};
use giputils::file::{recreate_dir, remove_if_exists};
use serde::Deserialize;
use std::{collections::BTreeMap, fs, path::PathBuf};
use std::{collections::HashMap, path::Path};

#[derive(Debug, Clone)]
struct BtorNode {
    op: String,
    rest: String,
}

#[derive(Debug, Default)]
struct BtorText {
    nodes: BTreeMap<usize, BtorNode>,
    symbols: HashMap<String, usize>,
    node_symbols: HashMap<usize, String>,
    sorts: HashMap<usize, String>,
    max_id: usize,
}

#[derive(Debug, Deserialize)]
struct LinkMap {
    ports: HashMap<String, LinkEntry>,
}

#[derive(Debug, Deserialize)]
struct LinkEntry {
    path: String,
    memory: bool,
    indices: Vec<isize>,
}

fn parse_btor(path: &Path) -> anyhow::Result<BtorText> {
    let mut btor = BtorText::default();
    for raw in fs::read_to_string(path)?.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with(';') {
            continue;
        }
        let mut parts = line.splitn(3, char::is_whitespace);
        let Some(id) = parts.next() else {
            continue;
        };
        let Ok(node_id) = id.parse::<usize>() else {
            continue;
        };
        let Some(op) = parts.next() else {
            continue;
        };
        let rest = parts.next().unwrap_or("").trim().to_string();
        btor.max_id = btor.max_id.max(node_id);
        btor.nodes.insert(
            node_id,
            BtorNode {
                op: op.to_string(),
                rest: rest.clone(),
            },
        );

        let tokens = rest.split_whitespace().collect::<Vec<_>>();
        if op == "sort" {
            btor.sorts.insert(node_id, rest);
        } else if matches!(op, "input" | "state") && tokens.len() >= 2 {
            let sym = tokens[1];
            if !sym.starts_with(';') {
                btor.symbols.insert(sym.to_string(), node_id);
                btor.node_symbols.insert(node_id, sym.to_string());
            }
        } else if !matches!(op, "sort" | "init" | "next" | "bad" | "constraint")
            && !tokens.is_empty()
            && let Some(semi) = tokens.iter().position(|tok| *tok == ";")
            && semi > 0
        {
            let sym = tokens[semi - 1];
            if !sym.starts_with(';') {
                btor.symbols.insert(sym.to_string(), node_id);
                btor.node_symbols.insert(node_id, sym.to_string());
            }
        }
    }
    Ok(btor)
}

fn bitvec_width(sort_desc: &str) -> Option<usize> {
    let mut parts = sort_desc.split_whitespace();
    if parts.next()? != "bitvec" {
        return None;
    }
    parts.next()?.parse().ok()
}

fn rewrite_signed_ref(tok: &str, repl: &HashMap<String, usize>) -> String {
    let (neg, key) = tok
        .strip_prefix('-')
        .map_or((false, tok), |stripped| (true, stripped));
    if let Some(val) = repl.get(key) {
        if neg {
            format!("-{val}")
        } else {
            val.to_string()
        }
    } else {
        tok.to_string()
    }
}

struct BtorLinker {
    core: BtorText,
    monitor: BtorText,
    link_map: HashMap<String, LinkEntry>,
    core_sort_by_desc: HashMap<String, usize>,
    repl: HashMap<String, usize>,
    append: Vec<String>,
    added_sorts: HashMap<String, usize>,
    notes: Vec<String>,
    next_id: usize,
}

impl BtorLinker {
    fn new(core: BtorText, monitor: BtorText, link_map: LinkMap) -> Self {
        let core_sort_by_desc = core
            .sorts
            .iter()
            .map(|(node_id, desc)| (desc.clone(), *node_id))
            .collect();
        let next_id = core.max_id;
        Self {
            core,
            monitor,
            link_map: link_map.ports,
            core_sort_by_desc,
            repl: HashMap::new(),
            append: Vec::new(),
            added_sorts: HashMap::new(),
            notes: Vec::new(),
            next_id,
        }
    }

    fn alloc(&mut self, op: &str, rest: String) -> usize {
        self.next_id += 1;
        self.append
            .push(format!("{} {} {}", self.next_id, op, rest));
        self.next_id
    }

    fn get_sort(&mut self, desc: &str) -> usize {
        if let Some(node_id) = self.core_sort_by_desc.get(desc) {
            return *node_id;
        }
        if let Some(node_id) = self.added_sorts.get(desc) {
            return *node_id;
        }
        let node_id = self.alloc("sort", desc.to_string());
        self.added_sorts.insert(desc.to_string(), node_id);
        node_id
    }

    fn build_memory_concat(
        &mut self,
        prefix: &str,
        sort_desc: &str,
        indices: &[isize],
    ) -> Option<(usize, usize, usize)> {
        let target_width = bitvec_width(sort_desc)?;
        let mut elems = Vec::new();
        for idx in indices {
            let sym = format!("{prefix}[{idx}]");
            elems.push(*self.core.symbols.get(&sym)?);
        }
        if elems.is_empty() {
            return None;
        }

        let first = self.core.nodes.get(&elems[0])?;
        if !matches!(first.op.as_str(), "state" | "input") {
            return None;
        }
        let first_sort = first
            .rest
            .split_whitespace()
            .next()?
            .parse::<usize>()
            .ok()?;
        let elem_width = bitvec_width(self.core.sorts.get(&first_sort)?)?;
        if elem_width * elems.len() != target_width {
            return None;
        }

        let mut cur = elems[0];
        let mut cur_width = elem_width;
        for elem in elems.into_iter().skip(1) {
            cur_width += elem_width;
            let sort_id = self.get_sort(&format!("bitvec {cur_width}"));
            cur = self.alloc("concat", format!("{sort_id} {cur} {elem}"));
        }
        Some((cur, indices.len(), elem_width))
    }

    fn replacement_for_symbol(
        &mut self,
        sym: &str,
        sort_desc: Option<&str>,
    ) -> Option<(usize, String)> {
        let fallback;
        let entry = if let Some(entry) = self.link_map.get(sym) {
            entry
        } else if self.core.symbols.contains_key(sym) {
            fallback = LinkEntry {
                path: sym.to_string(),
                memory: false,
                indices: Vec::new(),
            };
            &fallback
        } else {
            return None;
        };
        let target = entry.path.clone();
        let memory = entry.memory;
        let indices = entry.indices.clone();

        if let Some(node_id) = self.core.symbols.get(&target) {
            return Some((*node_id, format!("{sym} -> {target} (core node {node_id})")));
        }
        if memory
            && let Some(sort_desc) = sort_desc
            && let Some((node_id, depth, elem_width)) =
                self.build_memory_concat(&target, sort_desc, &indices)
        {
            return Some((
                node_id,
                format!(
                    "{sym} -> concat core {target}[{}:{}] ({depth} x {elem_width}-bit)",
                    indices.first()?,
                    indices.last()?
                ),
            ));
        }
        None
    }

    fn sort_desc_for_monitor_node(&self, rest: &str) -> Option<String> {
        let sort_tok = rest
            .split_whitespace()
            .next()
            .map(|tok| rewrite_signed_ref(tok, &self.repl))?;
        let sort_id = sort_tok.trim_start_matches('-').parse::<usize>().ok()?;
        self.monitor
            .sorts
            .get(&sort_id)
            .or_else(|| self.core.sorts.get(&sort_id))
            .cloned()
    }

    fn rewrite_tokens(&self, rest: &str) -> String {
        rest.split_whitespace()
            .map(|tok| rewrite_signed_ref(tok, &self.repl))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn run(mut self, core_path: &Path, linked: &Path) -> anyhow::Result<Vec<String>> {
        for (node_id, node) in self.monitor.nodes.clone() {
            if node.op == "sort" {
                let sort_id = self.get_sort(&node.rest);
                self.repl.insert(node_id.to_string(), sort_id);
                continue;
            }

            if let Some(sym) = self.monitor.node_symbols.get(&node_id).cloned() {
                let sort_desc = self.sort_desc_for_monitor_node(&node.rest);
                if let Some((replacement, note)) =
                    self.replacement_for_symbol(&sym, sort_desc.as_deref())
                {
                    self.repl.insert(node_id.to_string(), replacement);
                    self.notes.push(note);
                    continue;
                }
            }

            if node.op == "input" {
                self.link_input(node_id, &node.rest);
                continue;
            }
            if node.op == "output" {
                continue;
            }
            if node.op == "bad" {
                self.alloc("bad", self.rewrite_tokens(&node.rest));
                continue;
            }

            let rewritten = self.rewrite_tokens(&node.rest);
            let new_id = self.alloc(&node.op, rewritten);
            self.repl.insert(node_id.to_string(), new_id);
        }

        let mut core_lines = fs::read_to_string(core_path)?
            .lines()
            .filter(|line| !line.trim().starts_with("; end of yosys output"))
            .map(str::to_string)
            .collect::<Vec<_>>();
        core_lines.extend(self.append);
        core_lines.push("; end of shadow link output".to_string());
        fs::write(linked, format!("{}\n", core_lines.join("\n")))?;
        Ok(self.notes)
    }

    fn link_input(&mut self, node_id: usize, rest: &str) {
        let toks = rest.split_whitespace().collect::<Vec<_>>();
        let sym = toks.get(1).copied().unwrap_or("");
        let fallback;
        let entry = if let Some(entry) = self.link_map.get(sym) {
            entry
        } else {
            fallback = LinkEntry {
                path: sym.to_string(),
                memory: false,
                indices: Vec::new(),
            };
            &fallback
        };
        let target = entry.path.clone();
        let memory = entry.memory;
        let indices = entry.indices.clone();

        if memory && toks.len() >= 2 {
            let aggregate = toks
                .first()
                .and_then(|sort_id| sort_id.parse::<usize>().ok())
                .and_then(|sort_id| self.monitor.sorts.get(&sort_id).cloned())
                .and_then(|sort_desc| self.build_memory_concat(&target, &sort_desc, &indices));
            if let Some((node, depth, elem_width)) = aggregate {
                self.repl.insert(node_id.to_string(), node);
                self.notes.push(format!(
                    "{sym} -> concat core {target}[{}:{}] ({depth} x {elem_width}-bit)",
                    indices.first().unwrap(),
                    indices.last().unwrap()
                ));
            } else {
                let new_id = self.alloc("input", self.rewrite_tokens(rest));
                self.repl.insert(node_id.to_string(), new_id);
                self.notes.push(format!(
                    "{sym} -> fresh monitor input (missing core memory {target})"
                ));
            }
        } else if let Some(node) = self.core.symbols.get(sym) {
            self.repl.insert(node_id.to_string(), *node);
            self.notes
                .push(format!("{sym} -> {sym} (core node {node})"));
        } else {
            let new_id = self.alloc("input", self.rewrite_tokens(rest));
            self.repl.insert(node_id.to_string(), new_id);
            self.notes.push(format!("{sym} -> fresh monitor input"));
        }
    }
}

fn link_btor(core: &Path, monitor: &Path, link_map: &Path, linked: &Path) -> anyhow::Result<()> {
    let core_btor = parse_btor(core)?;
    let monitor_btor = parse_btor(monitor)?;
    let link_map = toml::from_str::<LinkMap>(&fs::read_to_string(link_map)?)?;
    let notes = BtorLinker::new(core_btor, monitor_btor, link_map).run(core, linked)?;
    println!("\nLinked monitor signals:");
    for note in notes {
        println!("  {note}");
    }
    Ok(())
}

pub fn link(rcfg: Ric3Config, rp: Ric3Proj, invariants: PathBuf) -> anyhow::Result<()> {
    if !rcfg.dut.defines.is_empty() {
        anyhow::bail!("`ric3 cill link` does not support dut.defines");
    }
    if !invariants.exists() {
        anyhow::bail!("invariants file not found: {}", invariants.display());
    }
    let dut_dir = rp.path("dut");
    let cill_dir = rp.path("cill");
    let shadow = cill_dir.join("shadow.sv");
    let link_map = cill_dir.join("link_map.toml");
    let core = dut_dir.join("dut.btor");
    for path in [&shadow, &link_map, &core] {
        if !path.exists() {
            anyhow::bail!(
                "missing prepared DUT artifact: {}. Run `ric3 cill prepare` first.",
                path.display()
            );
        }
    }

    let candinv_dir = rp.path("cill/candinv");
    recreate_dir(&candinv_dir)?;
    remove_if_exists(candinv_dir.join("linked.btor"))?;
    Yosys::generate_btor_with_files(&rcfg, &[shadow, invariants], &candinv_dir, "monitor")?;
    link_btor(
        &core,
        &candinv_dir.join("monitor.btor"),
        &link_map,
        &candinv_dir.join("linked.btor"),
    )?;
    println!(
        "CIll helper artifacts generated in {}.",
        candinv_dir.display()
    );
    Ok(())
}
