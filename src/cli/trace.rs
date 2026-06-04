use crate::cli::{
    Ric3Config,
    rproj::Ric3Proj,
    verilog::{SvModule, sv_type},
    yosys::Yosys,
};
use anyhow::bail;
use btor::Btor;
use clap::Subcommand;
use giputils::file::{create_dir_if_not_exists, recreate_dir, remove_if_exists};
use logicrs::{
    LboolVec,
    fol::{TermSymbol, term_mgr},
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
    collections::BTreeMap,
    fs::{self, read_to_string},
    path::Path,
};

const SIGNAL_IRRELEVANT: &str = "<IRRELEVANT>";
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

fn search_signals(_cex: &WlCex, sym: &WlTsSymbol, pattern: &str) -> anyhow::Result<Vec<String>> {
    let regex = Regex::new(pattern)?;
    let mut targets: Vec<_> = sym.symbols().cloned().collect();
    targets.retain(|signal| regex.is_match(signal));

    if targets.len() > 50 {
        let mut out = vec![format!(
            "Too many signals matched ({}), only showing first 50.",
            targets.len()
        )];
        out.extend(targets.into_iter().take(50));
        Ok(out)
    } else {
        Ok(targets)
    }
}

fn resolved_signal_values(
    cex: &WlCex,
    sym: &WlTsSymbol,
    signals: &[String],
    values: &mut BTreeMap<String, Vec<LboolVec>>,
) -> anyhow::Result<Vec<String>> {
    let mut found = Vec::new();
    let mut not_found = Vec::new();
    for s in signals.into_iter() {
        if let Some(t) = sym.term_of_sym(s) {
            if t.sort().is_array() {
                bail!("cannot inspect array signal `{s}` directly; specify an array index");
            }
            found.push((s.clone(), t));
        } else {
            not_found.push(s.clone());
        }
    }

    for (s, t) in found {
        let target = cex.term_values(&t);
        let target = target.into_iter().map(|t| t.into_bv().unwrap()).collect();
        values.insert(s, target);
    }

    Ok(not_found)
}

fn values_to_json(values: &[LboolVec]) -> JsonValue {
    let mut out = Vec::with_capacity(values.len());
    let mut all_x = true;

    for value in values {
        if !value.all_x() {
            all_x = false;
            out.push(format_lbool_vec(value));
        } else {
            out.push("X".to_string());
        }
    }

    if all_x {
        json!(SIGNAL_IRRELEVANT)
    } else {
        json!(out)
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

    anyhow::ensure!(
        observer_symbols
            .iter()
            .all(|name| linked_wsym.term_of_sym(name).is_some()),
        "failed to find synthesized trace expression symbols"
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
) -> anyhow::Result<BTreeMap<String, Vec<LboolVec>>> {
    anyhow::ensure!(!signals.is_empty(), "signals must be a non-empty list");

    let rp = Ric3Proj::new()?;
    let (wts, wsym) = rp.load_wts_of_trace()?;
    let mut trace: WlCex = rp.load_trace(property)?;
    trace.enrich(&wsym.keys().cloned().collect());
    let mut values = BTreeMap::new();
    let expressions = resolved_signal_values(&trace, &wsym, signals, &mut values)?;
    if expressions.is_empty() {
        return Ok(values);
    }

    let rcfg = Ric3Config::from_file("ric3.toml")?;
    let (expr_wsym, observer_symbols) =
        synthesize_trace_observer(&rcfg, &rp, &wts, &wsym, &expressions)?;

    trace.enrich(&expr_wsym.keys().cloned().collect());
    assert!(resolved_signal_values(&trace, &wsym, &observer_symbols, &mut values)?.is_empty());

    for (expression, observer_symbol) in expressions.into_iter().zip(observer_symbols) {
        let res = values.remove(&observer_symbol).unwrap();
        values.insert(expression, res);
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
            let values = values
                .into_iter()
                .map(|(k, v)| (k, values_to_json(&v)))
                .collect::<BTreeMap<String, JsonValue>>();
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
            .map(|values| {
                values
                    .into_iter()
                    .map(|(k, v)| (k, values_to_json(&v)))
                    .collect::<BTreeMap<String, JsonValue>>()
            })
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
