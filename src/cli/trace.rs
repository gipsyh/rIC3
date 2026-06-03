use crate::cli::rproj::Ric3Proj;
use anyhow::Context;
use clap::Subcommand;
use enum_as_inner::EnumAsInner;
use giputils::{
    file::{create_dir_if_not_exists, remove_if_exists},
    hash::{GHashMap, GHashSet},
};
use logicrs::{
    Lbool, LboolVec,
    fol::{self, Sort, Term, Value as FolValue, term_mgr},
};
use rIC3::wltransys::{WlTransys, cert::WlCex, symbol::WlTsSymbol};
use regex::Regex;
use rmcp::{
    ServerHandler, ServiceExt, handler::server::wrapper::Parameters, schemars, tool, tool_handler,
    tool_router,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value as JsonValue, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, read_to_string},
    io::{self, Write},
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

impl Ric3Proj {
    pub fn clear_trace(&self) -> anyhow::Result<()> {
        remove_if_exists(self.path("trace"))?;
        Ok(())
    }

    pub fn save_trace(
        &self,
        wts_path: impl AsRef<str>,
        t: &WlCex,
        name: impl AsRef<str>,
    ) -> anyhow::Result<()> {
        create_dir_if_not_exists(self.path("trace"))?;
        let wts_path = wts_path.as_ref();
        let wtsln_path = self.path("trace/wtsln");
        if wtsln_path.exists() {
            assert!(fs::read(&wtsln_path)? == wts_path.as_bytes());
        } else {
            fs::write(&wtsln_path, wts_path)?;
        }
        self.save_serde_obj(t, format!("trace/{}.rtrc", name.as_ref()))
    }

    pub fn load_trace(&self, name: impl AsRef<str>) -> anyhow::Result<WlCex> {
        self.load_serde_obj(format!("trace/{}.rtrc", name.as_ref()))
    }

    pub fn load_wts_of_trace(&self) -> anyhow::Result<(WlTransys, WlTsSymbol)> {
        let wtsln = read_to_string(self.path("trace/wtsln"))?;
        let res = self.load_wts(wtsln)?;
        term_mgr().enable_id_map();
        Ok(res)
    }
}

#[derive(Clone, Debug)]
enum SignalTarget {
    Bv { term: Term },
    ArrayIndex { term: Term, index: usize },
    ArrayBase { term: Term },
}

#[derive(Clone, Copy)]
enum TraceValue<'a> {
    Bv(&'a LboolVec),
    Array(&'a fol::ArrayValue),
}

impl TraceValue<'_> {
    fn all_x(self) -> bool {
        match self {
            TraceValue::Bv(value) => value.all_x(),
            TraceValue::Array(value) => value.is_empty(),
        }
    }
}

fn signal_targets(cex: &WlCex, sym: &WlTsSymbol) -> BTreeMap<String, SignalTarget> {
    let mut targets = BTreeMap::new();
    for (term, names) in sym.iter() {
        let mut is_array = false;
        let mut indices = BTreeSet::new();
        for value in term_values(cex, term).into_iter().flatten() {
            if let TraceValue::Array(array) = value {
                is_array = true;
                indices.extend(array.keys().copied());
            }
        }

        for name in names {
            if is_array {
                if indices.is_empty() {
                    targets.insert(name.clone(), SignalTarget::ArrayBase { term: term.clone() });
                } else {
                    for index in &indices {
                        targets.insert(
                            format!("{name}[{index}]"),
                            SignalTarget::ArrayIndex {
                                term: term.clone(),
                                index: *index,
                            },
                        );
                    }
                }
            } else {
                targets.insert(name.clone(), SignalTarget::Bv { term: term.clone() });
            }
        }
    }
    targets
}

fn term_values<'a>(cex: &'a WlCex, term: &Term) -> Vec<Option<TraceValue<'a>>> {
    let mut values = Vec::with_capacity(cex.len());
    for t in 0..cex.len() {
        if let Some(value) = cex.state[t]
            .iter()
            .find(|value| value.t() == term)
            .map(|value| value.v())
        {
            let value = match value {
                FolValue::Bv(value) => TraceValue::Bv(value),
                FolValue::Array(value) => TraceValue::Array(value),
            };
            values.push(Some(value));
        } else if let Some(value) = cex.input[t]
            .iter()
            .find(|value| value.t() == term)
            .map(|value| value.v())
        {
            values.push(Some(TraceValue::Bv(value)));
        } else {
            values.push(None);
        }
    }
    values
}

fn target_has_relevant_value(cex: &WlCex, target: &SignalTarget) -> bool {
    match target {
        SignalTarget::Bv { term } | SignalTarget::ArrayBase { term } => {
            term_values(cex, term)
                .iter()
                .any(|value| value.is_some_and(|value| !value.all_x()))
        }
        SignalTarget::ArrayIndex { term, index } => term_values(cex, term).iter().any(|value| {
            matches!(
                value,
                Some(TraceValue::Array(array)) if array.get(index).is_some_and(|value| !value.all_x())
            )
        }),
    }
}

fn search_signals(cex: &WlCex, sym: &WlTsSymbol, pattern: &str) -> anyhow::Result<Vec<String>> {
    let regex = Regex::new(pattern)?;
    let targets = signal_targets(cex, sym);
    let matched: Vec<_> = targets
        .iter()
        .filter(|(signal, target)| regex.is_match(signal) && target_has_relevant_value(cex, target))
        .map(|(signal, _)| signal.clone())
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

fn signal_values(
    cex: &WlCex,
    sym: &WlTsSymbol,
    signals: &[String],
) -> anyhow::Result<BTreeMap<String, JsonValue>> {
    anyhow::ensure!(!signals.is_empty(), "signals must be a non-empty list");

    let targets = signal_targets(cex, sym);
    let available: Vec<_> = targets.keys().cloned().collect();
    let (resolved, not_found) = expand_signal_names(&available, signals);

    let mut result = BTreeMap::new();
    for signal in resolved {
        let target = targets
            .get(&signal)
            .with_context(|| format!("internal error: resolved unknown signal {signal}"))?;
        result.insert(signal, target_values(cex, target)?);
    }

    for signal in not_found {
        result.insert(signal, json!(SIGNAL_NOT_FOUND));
    }

    Ok(result)
}

fn target_values(cex: &WlCex, target: &SignalTarget) -> anyhow::Result<JsonValue> {
    match target {
        SignalTarget::Bv { term } => values_to_json(term_values(cex, term), |value| match value {
            TraceValue::Bv(value) => Ok(Some(value)),
            TraceValue::Array(_) => anyhow::bail!("Signal is an array; request indexed signals"),
        }),
        SignalTarget::ArrayIndex { term, index } => {
            values_to_json(term_values(cex, term), |value| match value {
                TraceValue::Array(array) => Ok(array.get(index)),
                TraceValue::Bv(_) => anyhow::bail!("Signal is not an array"),
            })
        }
        SignalTarget::ArrayBase { term } => {
            if term_values(cex, term)
                .iter()
                .all(|value| value.is_none_or(|value| value.all_x()))
            {
                Ok(json!(SIGNAL_IRRELEVANT))
            } else {
                anyhow::bail!("Signal is an array; request indexed signals")
            }
        }
    }
}

fn values_to_json<'a>(
    values: Vec<Option<TraceValue<'a>>>,
    mut get_bv: impl FnMut(TraceValue<'a>) -> anyhow::Result<Option<&'a LboolVec>>,
) -> anyhow::Result<JsonValue> {
    let mut out = Vec::with_capacity(values.len());
    let mut all_x = true;

    for value in &values {
        let bv = value.map_or(Ok(None), &mut get_bv)?;
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
        return format!("{}'b{value}", value.len());
    }

    let hex = format!("{:x}", value.v());
    let hex = hex.strip_prefix("0x").unwrap_or(&hex);
    format!("{}'h{hex}", value.len())
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

pub fn search_signals_file(
    property: impl AsRef<str>,
    pattern: &str,
) -> anyhow::Result<Vec<String>> {
    let rp = Ric3Proj::new()?;
    let (_, wsym) = rp.load_wts_of_trace()?;
    let trace: WlCex = rp.load_trace(property)?;
    search_signals(&trace, &wsym, pattern)
}

pub fn signal_values_file(
    property: impl AsRef<str>,
    signals: &[String],
) -> anyhow::Result<BTreeMap<String, JsonValue>> {
    let rp = Ric3Proj::new()?;
    let (_, wsym) = rp.load_wts_of_trace()?;
    let trace: WlCex = rp.load_trace(property)?;
    signal_values(&trace, &wsym, signals)
}

#[derive(Subcommand, Debug, Clone)]
pub enum TraceCommands {
    /// Search signals in a property's trace by regex and print matches.
    Search {
        /// Property name whose trace should be inspected.
        property: String,

        /// Regex used to match signal names.
        pattern: String,
    },

    /// Print selected signal values from a property's trace as JSON.
    Value {
        /// Property name whose trace should be inspected.
        property: String,

        /// Signal names to print. Suffix matches are supported.
        #[arg(required = true)]
        signals: Vec<String>,
    },

    /// Run the trace tools as an MCP stdio server.
    Mcp,
}

pub fn trace(cmd: TraceCommands) -> anyhow::Result<()> {
    match cmd {
        TraceCommands::Search { property, pattern } => {
            for signal in search_signals_file(property, &pattern)? {
                println!("{signal}");
            }
            Ok(())
        }
        TraceCommands::Value { property, signals } => {
            let values = signal_values_file(property, &signals)?;
            println!("{}", toml::to_string(&values)?);
            Ok(())
        }
        TraceCommands::Mcp => run_mcp_server(),
    }
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
struct SearchSignalsArgs {
    #[schemars(description = "Property name whose trace should be inspected.")]
    property: String,

    #[schemars(description = "Regex pattern to search for.")]
    pattern: String,
}

#[derive(Debug, Deserialize, schemars::JsonSchema)]
struct SignalValuesArgs {
    #[schemars(description = "Property name whose trace should be inspected.")]
    property: String,

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
        description = "Search signals in a property's trace by regex pattern. Returns matching signal names. If more than 50 signals match, only the first 50 are returned."
    )]
    fn search_signals(
        &self,
        Parameters(SearchSignalsArgs { property, pattern }): Parameters<SearchSignalsArgs>,
    ) -> Result<rmcp::Json<SearchSignalsOutput>, String> {
        search_signals_file(property, &pattern)
            .map(|signals| rmcp::Json(SearchSignalsOutput { signals }))
            .map_err(|err| err.to_string())
    }

    #[tool(
        description = "Returns the values of selected signals from a property's trace as a JSON object. Keys are signal names, and values are arrays representing the signal state at each step."
    )]
    fn signal_values(
        &self,
        Parameters(SignalValuesArgs { property, signals }): Parameters<SignalValuesArgs>,
    ) -> Result<rmcp::Json<SignalValuesOutput>, String> {
        signal_values_file(property, &signals)
            .map(|values| rmcp::Json(SignalValuesOutput { values }))
            .map_err(|err| err.to_string())
    }
}

#[tool_handler(
    name = "ric3-trace-tools",
    instructions = "Tools for inspecting saved property traces."
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
    use logicrs::fol::TermValue;

    fn witness_trace(
        entries: impl IntoIterator<Item = (&'static str, Vec<fol::Value>)>,
    ) -> (WlCex, WlTsSymbol) {
        let mut cex = WlCex::new();
        let mut sym = WlTsSymbol {
            signal: Default::default(),
            prop: Vec::new(),
        };
        for (name, values) in entries {
            if cex.len() == 0 {
                cex.resize(values.len());
            } else {
                assert_eq!(cex.len(), values.len());
            }
            let sort = match &values[0] {
                FolValue::Bv(value) => Sort::Bv(value.len()),
                FolValue::Array(value) => value.sort(),
            };
            let term = Term::new_var(sort);
            sym.signal.insert(term.clone(), vec![name.to_string()]);
            for (frame, value) in values.into_iter().enumerate() {
                cex.state[frame].push(TermValue::new(term.clone(), value));
            }
        }
        (cex, sym)
    }

    #[test]
    fn all_x_signal_is_irrelevant_and_missing_signal_is_reported() {
        let (trace, sym) = witness_trace([(
            "top.sig",
            vec![
                FolValue::Bv(LboolVec::from("xx")),
                FolValue::Bv(LboolVec::from("xx")),
            ],
        )]);

        let values =
            signal_values(&trace, &sym, &["sig".to_string(), "absent".to_string()]).unwrap();

        assert_eq!(values.get("top.sig"), Some(&json!(SIGNAL_IRRELEVANT)));
        assert_eq!(values.get("absent"), Some(&json!(SIGNAL_NOT_FOUND)));
    }

    #[test]
    fn search_signals_omits_all_x_signals() {
        let (trace, sym) = witness_trace([
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

        let matches = search_signals(&trace, &sym, "top\\.").unwrap();

        assert_eq!(matches, vec!["top.relevant"]);
    }

    #[test]
    fn values_include_hardware_literal_widths() {
        let (trace, sym) = witness_trace([(
            "sig",
            vec![
                FolValue::Bv(LboolVec::from("1010")),
                FolValue::Bv(LboolVec::from("1x0")),
                FolValue::Bv(LboolVec::from("xxx")),
            ],
        )]);

        let values = signal_values(&trace, &sym, &["sig".to_string()]).unwrap();

        assert_eq!(values.get("sig"), Some(&json!(["4'ha", "3'b1x0", "X"])));
    }

    #[test]
    fn array_signals_are_exposed_by_observed_indices() {
        let mut frame0 = fol::ArrayValue::default_from(Sort::Array(2, 2));
        frame0.insert(1, LboolVec::from("01"));
        let frame1 = fol::ArrayValue::default_from(Sort::Array(2, 2));
        let (trace, sym) = witness_trace([(
            "mem",
            vec![FolValue::Array(frame0), FolValue::Array(frame1)],
        )]);

        assert_eq!(
            signal_targets(&trace, &sym).into_keys().collect::<Vec<_>>(),
            vec!["mem[1]"]
        );

        let values = signal_values(&trace, &sym, &["mem".to_string()]).unwrap();
        assert_eq!(values.get("mem[1]"), Some(&json!(["2'h1", "X"])));
    }
}
