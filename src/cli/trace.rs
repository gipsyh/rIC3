use crate::cli::{
    Ric3Config,
    rproj::Ric3Proj,
    verilog::{SvModule, sv_type},
    yosys::Yosys,
};
use anyhow::Context;
use btor::Btor;
use clap::Subcommand;
use giputils::{
    file::{create_dir_if_not_exists, recreate_dir, remove_if_exists},
    hash::GHashSet,
};
use logicrs::{
    LboolVec,
    fol::{self, Term, TermSymbol, Value as FolValue, term_mgr},
};
use rIC3::{
    frontend::{Frontend, btor::BtorFrontend},
    wltransys::{
        WlTransys,
        cert::WlCex,
        symbol::{WlTsSymbol, link_wts_by_symbol},
    },
};
use regex::Regex;
use rmcp::{
    ErrorData, ServerHandler, ServiceExt, handler::server::wrapper::Parameters, schemars, tool,
    tool_handler, tool_router,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value as JsonValue, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, read_to_string},
    path::Path,
};

const SIGNAL_IRRELEVANT: &str = "<IRRELEVANT>";
const SIGNAL_NOT_FOUND: &str = "<NOT FOUND>";
const TRACE_EXPR_MODULE: &str = "__ric3_trace_expr";
const TRACE_EXPR_PREFIX: &str = "__ric3_trace_expr_";

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
        let name = name.as_ref();
        let path = format!("trace/{name}.rtrc");
        let full_path = self.path(&path);
        term_mgr().enable_id_map();
        if !full_path.exists() {
            anyhow::bail!(
                "trace not found for property: {name} (expected file: {})",
                full_path.display()
            );
        }
        let res = self.load_serde_obj(path)?;
        term_mgr().disable_id_map();
        Ok(res)
    }

    pub fn load_wts_of_trace(&self) -> anyhow::Result<(WlTransys, WlTsSymbol)> {
        let wtsln = read_to_string(self.path("trace/wtsln"))?;
        let res = self.load_wts(wtsln)?;
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

fn resolved_signal_values(
    cex: &WlCex,
    sym: &WlTsSymbol,
    signals: &[String],
) -> anyhow::Result<(BTreeMap<String, JsonValue>, Vec<String>)> {
    anyhow::ensure!(!signals.is_empty(), "signals must be a non-empty list");

    let targets = signal_targets(cex, sym);
    let available: Vec<_> = targets.keys().cloned().collect();
    let (resolved, unresolved) = resolve_signal_names(&available, signals);

    let mut result = BTreeMap::new();
    for signal in resolved {
        let target = targets
            .get(&signal)
            .with_context(|| format!("internal error: resolved unknown signal {signal}"))?;
        result.insert(signal, target_values(cex, target)?);
    }

    Ok((result, unresolved))
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

fn resolve_signal_names(available: &[String], requested: &[String]) -> (Vec<String>, Vec<String>) {
    let mut resolved = Vec::new();
    let mut not_found = Vec::new();

    for name in requested {
        if let Some(signal) = available.iter().find(|signal| signal.as_str() == name) {
            resolved.push(signal.clone());
        } else {
            not_found.push(name.clone());
        }
    }

    let mut seen = BTreeSet::new();
    resolved.retain(|signal| seen.insert(signal.clone()));
    (resolved, not_found)
}

fn write_trace_observer(
    rcfg: &Ric3Config,
    tsym: &TermSymbol,
    expressions: &[String],
    out_path: impl AsRef<Path>,
    body_dclr: &mut Vec<String>,
) -> anyhow::Result<Vec<String>> {
    let mut module = SvModule::new("__ric3_trace_expr");
    for (t, s) in tsym.iter() {
        let sort = t.sort();
        for s in s.iter() {
            if !s.contains(".") {
                if sort.is_array() {
                    module.add_ext_body(format!("{};", sv_type(sort, s)));
                    body_dclr.push(s.clone());
                } else {
                    module.add_input(s, sort);
                }
            }
        }
    }

    let mut observer_symbols = Vec::new();
    for (idx, expr) in expressions.iter().enumerate() {
        let name = format!("{TRACE_EXPR_PREFIX}{idx}");
        observer_symbols.push(format!("{TRACE_EXPR_MODULE}.{TRACE_EXPR_PREFIX}{idx}"));
        module.add_ext_body(format!("(* keep *) wire type({}) {};", expr, &name));
        module.add_ext_body(format!("assign {} = ({});", &name, expr));
    }
    module.outside.push(format!(
        "bind {} {} {} (.*);\n",
        &rcfg.dut.top, TRACE_EXPR_MODULE, TRACE_EXPR_MODULE
    ));
    let content = format!("{}", module);
    fs::write(out_path.as_ref(), content)?;
    Ok(observer_symbols)
}

fn synthesize_trace_observer(
    rcfg: &Ric3Config,
    rp: &Ric3Proj,
    core_wts: &WlTransys,
    core_wsym: &WlTsSymbol,
    expressions: &[String],
) -> anyhow::Result<(WlTsSymbol, Vec<String>)> {
    let expr_dir = rp.path("trace/expr");
    recreate_dir(&expr_dir)?;
    let observer_path = expr_dir.join("observer.sv");
    let mut body_dclr = Vec::new();
    let observer_symbols =
        write_trace_observer(rcfg, core_wsym, expressions, &observer_path, &mut body_dclr)?;
    generate_observer_btor(
        rcfg,
        &[rp.path("cill/shadow.sv"), observer_path.clone()],
        &expr_dir,
    )?;

    let mut observer_bf = BtorFrontend::new(Btor::from_file(expr_dir.join("observer.btor")));
    let (observer_wts, mut observer_wsym) = observer_bf.wts();
    for s in body_dclr {
        observer_wsym.replace_sym(format!("{TRACE_EXPR_MODULE}.{s}"), s);
    }

    let expr_prefix = format!("{TRACE_EXPR_MODULE}.{TRACE_EXPR_PREFIX}");

    let (_, linked_wsym, mut unlinked_symbols) =
        link_wts_by_symbol(core_wts, core_wsym, observer_wts, observer_wsym)?;
    unlinked_symbols.retain(|symbol| !symbol.starts_with(&expr_prefix));
    anyhow::ensure!(
        unlinked_symbols.is_empty(),
        "trace expression references symbols that could not be linked to the saved trace: {}",
        unlinked_symbols.join(",")
    );

    Ok((linked_wsym, observer_symbols))
}

fn generate_observer_btor(
    cfg: &Ric3Config,
    input_files: &[std::path::PathBuf],
    p: impl AsRef<std::path::Path>,
) -> anyhow::Result<()> {
    let src_dir = p.as_ref().join("src");
    recreate_dir(&src_dir)?;
    let mut files = Vec::new();
    for f in input_files {
        let file_name = f.file_name().unwrap();
        let dest = src_dir.join(file_name);
        fs::copy(f, &dest)?;
        files.push(file_name.to_owned());
    }

    let mut yosys = Yosys::new();
    let mut read = format!(
        "read_slang -Wnone -D FORMAL -D YOSYS_SLANG --allow-hierarchical-const -top {}",
        cfg.dut.top
    );
    for file in &files {
        read.push_str(&format!(" {}", file.display()));
    }
    yosys.add_command(&read);
    yosys.add_command("setundef -undriven -anyseq");
    yosys.add_command("opt_clean");
    yosys.add_command("memory_nordff");
    yosys.add_command("chformal -cover -remove");
    yosys.add_command("chformal -early");
    yosys.add_command("async2sync");
    yosys.add_command("formalff -clk2ff -ff2anyinit -hierarchy -assume");
    yosys.add_command("dffunmap");
    yosys.add_command("opt -fast");
    yosys.add_command("check");
    yosys.add_command(&format!(
        "write_btor {}",
        std::path::PathBuf::from("..")
            .join("observer.btor")
            .display()
    ));
    yosys.execute(Some(&src_dir), vec!["slang".to_string()])
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
    let (wts, wsym) = rp.load_wts_of_trace()?;
    let mut trace: WlCex = rp.load_trace(property)?;
    let (mut values, expressions) = resolved_signal_values(&trace, &wsym, signals)?;
    if expressions.is_empty() {
        return Ok(values);
    }

    let rcfg = Ric3Config::from_file("ric3.toml")?;
    let (expr_wsym, observer_symbols) =
        synthesize_trace_observer(&rcfg, &rp, &wts, &wsym, &expressions)?;
    let observe: GHashSet<Term> = observer_symbols
        .iter()
        .filter_map(|name| expr_wsym.term_of_sym(name))
        .collect();
    anyhow::ensure!(
        observe.len() == observer_symbols.len(),
        "failed to find synthesized trace expression symbols"
    );
    trace.enrich(&observe);

    for (expression, observer_symbol) in expressions.into_iter().zip(observer_symbols) {
        if let Some(term) = expr_wsym.term_of_sym(&observer_symbol) {
            values.insert(
                expression,
                target_values(&trace, &SignalTarget::Bv { term }).with_context(|| {
                    format!("failed to read synthesized trace expression {observer_symbol}")
                })?,
            );
        } else {
            values.insert(expression, json!(SIGNAL_NOT_FOUND));
        }
    }
    Ok(values)
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

    /// Print selected signal or Verilog expression values from a property's trace as JSON.
    Value {
        /// Property name whose trace should be inspected.
        property: String,

        /// Signal names or Verilog expressions to print.
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

    #[schemars(description = "Signal names or Verilog expressions to read.")]
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
    ) -> Result<rmcp::Json<SearchSignalsOutput>, ErrorData> {
        search_signals_file(property, &pattern)
            .map(|signals| rmcp::Json(SearchSignalsOutput { signals }))
            .map_err(|err| ErrorData::invalid_params(err.to_string(), None))
    }

    #[tool(
        description = "Returns the values of selected signal names or Verilog expressions from a property's trace as a JSON object. Keys are signal expressions, and values are arrays representing the state at each step."
    )]
    fn signal_values(
        &self,
        Parameters(SignalValuesArgs { property, signals }): Parameters<SignalValuesArgs>,
    ) -> Result<rmcp::Json<SignalValuesOutput>, ErrorData> {
        signal_values_file(property, &signals)
            .map(|values| rmcp::Json(SignalValuesOutput { values }))
            .map_err(|err| ErrorData::invalid_params(err.to_string(), None))
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
    use logicrs::fol::{BvTermValue, Sort, TermValue};

    fn signal_values(
        cex: &WlCex,
        sym: &WlTsSymbol,
        signals: &[String],
    ) -> anyhow::Result<BTreeMap<String, JsonValue>> {
        let (mut result, not_found) = resolved_signal_values(cex, sym, signals)?;
        for signal in not_found {
            result.insert(signal, json!(SIGNAL_NOT_FOUND));
        }
        Ok(result)
    }

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
            sym.add_symbol(&term, name.to_string());
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
            signal_values(&trace, &sym, &["top.sig".to_string(), "absent".to_string()]).unwrap();

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

        let values = signal_values(&trace, &sym, &["mem[1]".to_string()]).unwrap();
        assert_eq!(values.get("mem[1]"), Some(&json!(["2'h1", "X"])));
    }

    #[test]
    fn unresolved_requests_are_returned_as_trace_expressions() {
        let (trace, sym) = witness_trace([(
            "top.sig",
            vec![
                FolValue::Bv(LboolVec::from("1")),
                FolValue::Bv(LboolVec::from("0")),
            ],
        )]);

        let (values, expressions) = resolved_signal_values(
            &trace,
            &sym,
            &["sig".to_string(), "a[3] & b[2]".to_string()],
        )
        .unwrap();

        assert!(values.is_empty());
        assert_eq!(expressions, vec!["sig", "a[3] & b[2]"]);
    }

    #[test]
    fn slang_observer_uses_expression_type_without_bits() {
        let tmp = tempfile::tempdir().unwrap();
        let rcfg = Ric3Config {
            dut: super::super::Dut {
                reset: None,
                top: "top".to_string(),
                files: Vec::new(),
                include_files: None,
                defines: Default::default(),
            },
            modeling: None,
            formal: None,
        };
        let sym = WlTsSymbol {
            signal: Default::default(),
            prop: Vec::new(),
        };

        let observer_path = tmp.path().join("observer.sv");
        write_trace_observer(
            &rcfg,
            &sym,
            &["a + b".to_string()],
            &observer_path,
            &mut vec![],
        )
        .unwrap();
        let observer = std::fs::read_to_string(observer_path).unwrap();

        assert!(observer.contains("wire type(a + b) __ric3_trace_expr_0;"));
        assert!(!observer.contains("$bits"));
    }

    #[test]
    fn linked_observer_expression_enriches_saved_trace() {
        let a = Term::new_var(Sort::Bv(1));
        let b = Term::new_var(Sort::Bv(1));
        let core_wts = WlTransys {
            input: vec![a.clone(), b.clone()],
            ..Default::default()
        };
        let mut core_wsym = WlTsSymbol {
            signal: Default::default(),
            prop: Vec::new(),
        };
        core_wsym.add_symbol(&a, "a".to_string());
        core_wsym.add_symbol(&b, "b".to_string());

        let observer_a = Term::new_var(Sort::Bv(1));
        let observer_b = Term::new_var(Sort::Bv(1));
        let observer_expr = &observer_a & &observer_b;
        let observer_wts = WlTransys {
            input: vec![observer_a.clone(), observer_b.clone()],
            output: vec![observer_expr.clone()],
            ..Default::default()
        };
        let observer_symbol = format!("{TRACE_EXPR_MODULE}.{TRACE_EXPR_PREFIX}0");
        let mut observer_wsym = WlTsSymbol {
            signal: Default::default(),
            prop: Vec::new(),
        };
        observer_wsym.add_symbol(&observer_a, "a".to_string());
        observer_wsym.add_symbol(&observer_b, "b".to_string());
        observer_wsym.add_symbol(&observer_expr, observer_symbol.clone());

        let (_, linked_wsym, unlinked_symbols) =
            link_wts_by_symbol(&core_wts, &core_wsym, observer_wts, observer_wsym).unwrap();
        assert_eq!(unlinked_symbols, vec![observer_symbol.clone()]);
        let expr_term = linked_wsym.term_of_sym(&observer_symbol).unwrap();

        let mut trace = WlCex::new();
        trace.resize(2);
        trace.input[0].push(BvTermValue::new(a.clone(), LboolVec::from("1")));
        trace.input[0].push(BvTermValue::new(b.clone(), LboolVec::from("0")));
        trace.input[1].push(BvTermValue::new(a, LboolVec::from("1")));
        trace.input[1].push(BvTermValue::new(b, LboolVec::from("1")));
        trace.enrich(&GHashSet::from_iter([expr_term.clone()]));

        let values = target_values(&trace, &SignalTarget::Bv { term: expr_term }).unwrap();

        assert_eq!(values, json!(["1'h0", "1'h1"]));
    }
}
