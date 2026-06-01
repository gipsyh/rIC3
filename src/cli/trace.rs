use anyhow::Context;
use clap::Subcommand;
use enum_as_inner::EnumAsInner;
use giputils::hash::{GHashMap, GHashSet};
use logicrs::{
    Lbool, LboolVec,
    fol::{self, Sort, Term, Value as FolValue},
};
use rIC3::wltransys::{cert::WlCex, symbol::WlTsSymbol};
use regex::Regex;
use rmcp::{
    ServerHandler, ServiceExt, handler::server::wrapper::Parameters, schemars, tool, tool_handler,
    tool_router,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value as JsonValue, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
};
use vcd::{ReferenceIndex, TimescaleUnit, Value as VcdValue, VarType};

const SIGNAL_IRRELEVANT: &str = "<IRRELEVANT>";
const SIGNAL_NOT_FOUND: &str = "<NOT FOUND>";

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

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WlSymbolTrace {
    trace: GHashMap<String, Vec<fol::Value>>,
}

impl WlSymbolTrace {
    pub fn new(cex: &WlCex, sym: &WlTsSymbol) -> Self {
        let mut term_trace = GHashMap::<Term, Vec<fol::Value>>::default();
        for t in sym.keys() {
            term_trace.insert(
                t.clone(),
                vec![fol::Value::default_from(t.sort()); cex.len()],
            );
        }

        for k in 0..cex.len() {
            for tv in &cex.input[k] {
                if let Some(trace) = term_trace.get_mut(tv.t()) {
                    trace[k] = fol::Value::Bv(tv.v().clone());
                }
            }
            for tv in &cex.state[k] {
                if let Some(trace) = term_trace.get_mut(tv.t()) {
                    trace[k] = tv.v().clone();
                }
            }
        }

        let mut trace = GHashMap::default();
        for (term, names) in sym.iter() {
            let values = term_trace.remove(term).unwrap();
            for name in names {
                assert!(trace.insert(name.clone(), values.clone()).is_none());
            }
        }
        Self { trace }
    }

    pub fn load(path: impl AsRef<Path>) -> anyhow::Result<Self> {
        let path = path.as_ref();
        let content = fs::read_to_string(path)
            .with_context(|| format!("failed to read trace file: {}", path.display()))?;
        ron::from_str(&content)
            .with_context(|| format!("failed to parse trace file as RON: {}", path.display()))
    }

    fn signal_targets(&self) -> BTreeMap<String, SignalTarget> {
        let mut targets = BTreeMap::new();
        for (name, values) in self.trace.iter() {
            let mut is_array = false;
            let mut indices = BTreeSet::new();
            for value in values {
                if let FolValue::Array(array) = value {
                    is_array = true;
                    indices.extend(array.keys().copied());
                }
            }

            if is_array {
                if indices.is_empty() {
                    targets.insert(name.clone(), SignalTarget::ArrayBase { name: name.clone() });
                } else {
                    for index in indices {
                        let indexed_name = format!("{name}[{index}]");
                        targets.insert(
                            indexed_name.clone(),
                            SignalTarget::ArrayIndex {
                                base: name.clone(),
                                index,
                            },
                        );
                    }
                }
            } else {
                targets.insert(name.clone(), SignalTarget::Bv { name: name.clone() });
            }
        }
        targets
    }

    pub fn signal_names(&self) -> Vec<String> {
        self.signal_targets().into_keys().collect()
    }

    pub fn search_signals(&self, pattern: &str) -> anyhow::Result<Vec<String>> {
        let regex = Regex::new(pattern)?;
        let targets = self.signal_targets();
        let matched: Vec<_> = self
            .signal_names()
            .into_iter()
            .filter(|signal| regex.is_match(signal))
            .filter(|signal| {
                targets
                    .get(signal)
                    .is_some_and(|target| self.target_has_relevant_value(target))
            })
            .collect();

        if matched.len() > 50 {
            let mut out = vec![format!(
                "Too many signals matched ({}), only showing first 50.",
                matched.len()
            )];
            out.extend(matched.into_iter().take(50));
            Ok(out)
        } else {
            Ok(matched)
        }
    }

    fn target_has_relevant_value(&self, target: &SignalTarget) -> bool {
        match target {
            SignalTarget::Bv { name } => self
                .trace
                .get(name)
                .is_some_and(|values| values.iter().any(|value| !value.all_x())),
            SignalTarget::ArrayIndex { base, index } => {
                self.trace.get(base).is_some_and(|values| {
                    values.iter().any(|value| match value {
                        FolValue::Array(array) => {
                            array.get(index).is_some_and(|value| !value.all_x())
                        }
                        FolValue::Bv(_) => false,
                    })
                })
            }
            SignalTarget::ArrayBase { name } => self
                .trace
                .get(name)
                .is_some_and(|values| values.iter().any(|value| !value.all_x())),
        }
    }

    pub fn signal_values(&self, signals: &[String]) -> anyhow::Result<BTreeMap<String, JsonValue>> {
        anyhow::ensure!(!signals.is_empty(), "signals must be a non-empty list");

        let targets = self.signal_targets();
        let available: Vec<_> = targets.keys().cloned().collect();
        let (resolved, not_found) = expand_signal_names(&available, signals);

        let mut result = BTreeMap::new();
        for signal in resolved {
            let target = targets
                .get(&signal)
                .with_context(|| format!("internal error: resolved unknown signal {signal}"))?;
            result.insert(signal, self.target_values(target)?);
        }

        for signal in not_found {
            result.insert(signal, json!(SIGNAL_NOT_FOUND));
        }

        Ok(result)
    }

    fn target_values(&self, target: &SignalTarget) -> anyhow::Result<JsonValue> {
        match target {
            SignalTarget::Bv { name } => {
                let values = self
                    .trace
                    .get(name)
                    .with_context(|| format!("Signal not found: {name}"))?;
                values_to_json(values, |value| match value {
                    FolValue::Bv(value) => Ok(Some(value)),
                    FolValue::Array(_) => anyhow::bail!(
                        "Signal {name} is an array; request indexed signals such as {name}[0]"
                    ),
                })
            }
            SignalTarget::ArrayIndex { base, index } => {
                let values = self
                    .trace
                    .get(base)
                    .with_context(|| format!("Signal not found: {base}"))?;
                values_to_json(values, |value| match value {
                    FolValue::Array(array) => Ok(array.get(index)),
                    FolValue::Bv(_) => anyhow::bail!("Signal {base} is not an array"),
                })
            }
            SignalTarget::ArrayBase { name } => {
                let values = self
                    .trace
                    .get(name)
                    .with_context(|| format!("Signal not found: {name}"))?;
                if values.iter().all(FolValue::all_x) {
                    Ok(json!(SIGNAL_IRRELEVANT))
                } else {
                    anyhow::bail!("Signal {name} is an array; request indexed signals")
                }
            }
        }
    }
}

#[derive(Clone, Debug)]
enum SignalTarget {
    Bv { name: String },
    ArrayIndex { base: String, index: usize },
    ArrayBase { name: String },
}

fn values_to_json<'a>(
    values: &'a [fol::Value],
    mut get_bv: impl FnMut(&'a fol::Value) -> anyhow::Result<Option<&'a LboolVec>>,
) -> anyhow::Result<JsonValue> {
    let mut out = Vec::with_capacity(values.len());
    let mut all_x = true;

    for value in values {
        let bv = get_bv(value)?;
        let is_x = bv.is_none_or(LboolVec::all_x);
        if !is_x {
            all_x = false;
        }
        out.push(match bv {
            Some(value) => format_lbool_vec(value),
            None => "X".to_string(),
        });
    }

    if all_x {
        Ok(json!(SIGNAL_IRRELEVANT))
    } else {
        Ok(json!(out))
    }
}

fn format_lbool_vec(value: &LboolVec) -> String {
    if value.all_x() {
        return "X".to_string();
    }

    if value.any_x() {
        return format!("0b_{value}");
    }

    let hex = format!("{:x}", value.v());
    let hex = hex.strip_prefix("0x").unwrap_or(&hex);
    format!("0x_{hex}")
}

fn expand_signal_names(available: &[String], requested: &[String]) -> (Vec<String>, Vec<String>) {
    let mut resolved = Vec::new();
    let mut not_found = Vec::new();

    for name in requested {
        if let Some(signal) = resolve_exact_signal_name(available, name) {
            resolved.push(signal);
            continue;
        }

        let mut matches: Vec<_> = available
            .iter()
            .filter(|signal| signal_matches_request(signal, name))
            .cloned()
            .collect();
        if matches.is_empty() {
            not_found.push(name.clone());
            continue;
        }

        matches.sort();
        resolved.extend(matches);
    }

    let mut seen = BTreeSet::new();
    resolved.retain(|signal| seen.insert(signal.clone()));
    (resolved, not_found)
}

fn resolve_exact_signal_name(available: &[String], name: &str) -> Option<String> {
    let mut candidates = vec![name.to_string()];
    if let Some(stripped) = name.strip_prefix('/') {
        candidates.push(stripped.to_string());
    } else {
        candidates.push(format!("/{name}"));
    }

    for candidate in &candidates {
        if let Some(signal) = available.iter().find(|signal| *signal == candidate) {
            return Some(signal.clone());
        }
    }

    for candidate in &candidates {
        if let Some(signal) = available
            .iter()
            .find(|signal| signal.eq_ignore_ascii_case(candidate))
        {
            return Some(signal.clone());
        }
    }

    None
}

fn signal_matches_request(signal: &str, request: &str) -> bool {
    let request = request.strip_prefix('/').unwrap_or(request);
    if signal.ends_with(&format!(".{request}")) || signal.ends_with(&format!("/{request}")) {
        return true;
    }

    let base = array_base_name(signal).unwrap_or(signal);
    base == request
        || base.ends_with(&format!(".{request}"))
        || base.ends_with(&format!("/{request}"))
}

fn array_base_name(name: &str) -> Option<&str> {
    let without_bracket = name.strip_suffix(']')?;
    let (base, index) = without_bracket.rsplit_once('[')?;
    index.parse::<usize>().ok()?;
    Some(base)
}

pub fn search_signals_file(path: impl AsRef<Path>, pattern: &str) -> anyhow::Result<Vec<String>> {
    WlSymbolTrace::load(path)?.search_signals(pattern)
}

pub fn signal_values_file(
    path: impl AsRef<Path>,
    signals: &[String],
) -> anyhow::Result<BTreeMap<String, JsonValue>> {
    WlSymbolTrace::load(path)?.signal_values(signals)
}

#[derive(Subcommand, Debug, Clone)]
pub enum TraceCommands {
    /// Search signals in a .strace file by regex and print matches.
    Search {
        /// Path to the .strace file.
        path: PathBuf,

        /// Regex used to match signal names.
        pattern: String,
    },

    /// Print selected signal values from a .strace file as JSON.
    Value {
        /// Path to the .strace file.
        path: PathBuf,

        /// Signal names to print. Suffix matches are supported.
        #[arg(required = true)]
        signals: Vec<String>,
    },

    /// Run the trace tools as an MCP stdio server.
    Mcp,
}

pub fn trace(cmd: TraceCommands) -> anyhow::Result<()> {
    match cmd {
        TraceCommands::Search { path, pattern } => {
            for signal in search_signals_file(path, &pattern)? {
                println!("{signal}");
            }
            Ok(())
        }
        TraceCommands::Value { path, signals } => {
            let values = signal_values_file(path, &signals)?;
            println!("{}", toml::to_string_pretty(&values)?);
            Ok(())
        }
        TraceCommands::Mcp => run_mcp_server(),
    }
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
struct SearchSignalsArgs {
    #[schemars(description = "Absolute path to the .strace file.")]
    path: String,

    #[schemars(description = "Regex pattern to search for.")]
    pattern: String,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
struct SignalValuesArgs {
    #[schemars(description = "Absolute path to the .strace file.")]
    path: String,

    #[schemars(description = "Signal names to read.")]
    signals: Vec<String>,
}

#[derive(Debug, Serialize, schemars::JsonSchema)]
struct SearchSignalsOutput {
    signals: Vec<String>,
}

#[derive(Debug, Serialize, schemars::JsonSchema)]
struct SignalValuesOutput {
    values: BTreeMap<String, JsonValue>,
}

#[derive(Clone)]
struct TraceMcpServer;

#[tool_router]
impl TraceMcpServer {
    #[tool(
        description = "Search signals in a .strace file by regex pattern. Returns matching signal names. The path argument is kept for compatibility and should point to the .strace file. If more than 50 signals match, only the first 50 are returned."
    )]
    fn search_signals(
        &self,
        Parameters(SearchSignalsArgs { path, pattern }): Parameters<SearchSignalsArgs>,
    ) -> Result<rmcp::Json<SearchSignalsOutput>, String> {
        search_signals_file(path, &pattern)
            .map(|signals| rmcp::Json(SearchSignalsOutput { signals }))
            .map_err(|err| err.to_string())
    }

    #[tool(
        description = "Returns the values of selected signals as a JSON object. Keys are signal names, and values are arrays representing the signal state at each step. The path argument is kept for compatibility and should point to the .strace file."
    )]
    fn signal_values(
        &self,
        Parameters(SignalValuesArgs { path, signals }): Parameters<SignalValuesArgs>,
    ) -> Result<rmcp::Json<SignalValuesOutput>, String> {
        signal_values_file(path, &signals)
            .map(|values| rmcp::Json(SignalValuesOutput { values }))
            .map_err(|err| err.to_string())
    }
}

#[tool_handler(
    name = "ric3-trace-tools",
    instructions = "Tools for inspecting .strace files."
)]
impl ServerHandler for TraceMcpServer {}

fn run_mcp_server() -> anyhow::Result<()> {
    let runtime = tokio::runtime::Runtime::new()?;
    runtime.block_on(async {
        TraceMcpServer
            .serve(rmcp::transport::stdio())
            .await?
            .waiting()
            .await?;
        anyhow::Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbol_trace(
        entries: impl IntoIterator<Item = (&'static str, Vec<fol::Value>)>,
    ) -> WlSymbolTrace {
        WlSymbolTrace {
            trace: entries
                .into_iter()
                .map(|(name, values)| (name.to_string(), values))
                .collect(),
        }
    }

    #[test]
    fn all_x_signal_is_irrelevant_and_missing_signal_is_reported() {
        let trace = symbol_trace([(
            "top.sig",
            vec![
                FolValue::Bv(LboolVec::from("xx")),
                FolValue::Bv(LboolVec::from("xx")),
            ],
        )]);

        let values = trace
            .signal_values(&["sig".to_string(), "absent".to_string()])
            .unwrap();

        assert_eq!(values.get("top.sig"), Some(&json!(SIGNAL_IRRELEVANT)));
        assert_eq!(values.get("absent"), Some(&json!(SIGNAL_NOT_FOUND)));
    }

    #[test]
    fn search_signals_omits_all_x_signals() {
        let trace = symbol_trace([
            (
                "top.all_x",
                vec![
                    FolValue::Bv(LboolVec::from("xx")),
                    FolValue::Bv(LboolVec::from("xx")),
                ],
            ),
            (
                "top.relevant",
                vec![
                    FolValue::Bv(LboolVec::from("xx")),
                    FolValue::Bv(LboolVec::from("01")),
                ],
            ),
        ]);

        let matches = trace.search_signals("top\\.").unwrap();

        assert_eq!(matches, vec!["top.relevant"]);
    }

    #[test]
    fn values_use_hex_unless_some_bits_are_x() {
        let trace = symbol_trace([(
            "sig",
            vec![
                FolValue::Bv(LboolVec::from("1010")),
                FolValue::Bv(LboolVec::from("1x0")),
                FolValue::Bv(LboolVec::from("xxx")),
            ],
        )]);

        let values = trace.signal_values(&["sig".to_string()]).unwrap();

        assert_eq!(values.get("sig"), Some(&json!(["0x_a", "0b_1x0", "X"])));
    }

    #[test]
    fn array_signals_are_exposed_by_observed_indices() {
        let mut frame0 = fol::ArrayValue::default_from(Sort::Array(2, 2));
        frame0.insert(1, LboolVec::from("01"));
        let frame1 = fol::ArrayValue::default_from(Sort::Array(2, 2));
        let trace = symbol_trace([(
            "mem",
            vec![FolValue::Array(frame0), FolValue::Array(frame1)],
        )]);

        assert_eq!(trace.signal_names(), vec!["mem[1]"]);

        let values = trace.signal_values(&["mem".to_string()]).unwrap();
        assert_eq!(values.get("mem[1]"), Some(&json!(["0x_1", "X"])));
    }
}
