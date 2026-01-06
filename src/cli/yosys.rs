use super::Ric3Config;
use crate::cli::VcdConfig;
use giputils::file::recreate_dir;
use giputils::hash::GHashMap;
use log::info;
use std::{
    fs,
    io::{BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    process::{Command, Output},
};
use vcd::IdCode;

fn format_output_for_error(output: &Output) -> String {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    format!(
        "status: {}\nstdout:\n{}\nstderr:\n{}",
        output.status, stdout, stderr
    )
}

#[derive(Default)]
pub struct Yosys {
    commands: Vec<String>,
}

impl Yosys {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_command(&mut self, cmd: &str) {
        self.commands.push(cmd.to_string());
    }

    pub fn execute(&mut self, cwd: Option<&Path>) -> anyhow::Result<()> {
        let cmds = self.commands.join(" ; ");
        let mut cmd = Command::new("yosys");
        cmd.args(["-m", "slang"]);
        if let Some(cwd) = cwd {
            cmd.current_dir(cwd);
        }
        let output = cmd.arg("-p").arg(&cmds).output()?;
        if !output.status.success() {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            info!("{}", stdout);
            info!("{}", stderr);
            anyhow::bail!("Yosys execution failed.\n{}\n{}", stdout, stderr)
        }
        Ok(())
    }

    pub fn generate_btor(cfg: &Ric3Config, p: impl AsRef<Path>) -> anyhow::Result<()> {
        info!("Yosys: parsing the DUT and generating BTOR.");
        recreate_dir(p.as_ref())?;
        let src_dir = p.as_ref().join("src");
        recreate_dir(&src_dir)?;
        let mut files = Vec::new();
        for f in cfg.dut.files.iter() {
            let file_name = f.file_name().unwrap();
            let dest = src_dir.join(file_name);
            fs::copy(f, &dest)?;
            files.push(file_name);
        }
        for f in cfg.dut.include_files.iter().flatten() {
            let dest = src_dir.join(f.file_name().unwrap());
            fs::copy(f, &dest)?;
        }
        let mut yosys = Self::new();
        let mut read = "read_slang -D FORMAL -D YOSYS_SLANG".to_string();
        for file in files.iter() {
            read.push_str(&format!(" {}", file.display()));
        }
        yosys.add_command(&read);
        yosys.add_command(&format!("prep -flatten -top {}", cfg.dut.top));
        yosys.add_command("hierarchy -smtcheck -nokeep_prints");
        yosys.add_command("scc -select; simplemap; select -clear");
        yosys.add_command("memory_nordff");
        if let Some(reset) = &cfg.dut.reset {
            yosys.add_command(&format!("fminit -seq {} 1,0", reset));
        }
        yosys.add_command("chformal -cover -remove");
        yosys.add_command("chformal -early");
        yosys.add_command("async2sync");
        yosys.add_command("formalff -clk2ff -ff2anyinit -hierarchy -assume");
        yosys.add_command("memory_map -formal");
        yosys.add_command("dffunmap");
        yosys.add_command("setundef -undriven -anyseq");
        yosys.add_command("opt -fast");
        yosys.add_command("opt_clean");
        yosys.add_command("delete -output");
        yosys.add_command("rename -witness");
        yosys.add_command("check");
        let dp = PathBuf::from("..");
        yosys.add_command(&format!("write_rtlil {}", dp.join("dut.il").display()));
        yosys.add_command(&format!(
            "write_btor -ywmap {} -i {} {}",
            dp.join("dut.ywb").display(),
            dp.join("dut.info").display(),
            dp.join("dut.btor").display(),
        ));
        yosys.execute(Some(&src_dir))
    }

    pub fn btor_wit_to_vcd(
        dut: impl AsRef<Path>,
        witness: impl AsRef<Path>,
        vcd: impl AsRef<Path>,
        cex_check: bool,
        vcd_cfg: Option<&VcdConfig>,
    ) -> anyhow::Result<()> {
        let mut btorvcd = if cex_check {
            Command::new("btorsim")
        } else {
            Command::new("btorvcd")
        };
        btorvcd.args(["-c", "--vcd"]);
        btorvcd.arg(vcd.as_ref());
        btorvcd.args(["--hierarchical-symbols", "--info"]);
        btorvcd.arg(dut.as_ref().join("dut.info"));
        btorvcd.arg(dut.as_ref().join("dut.btor"));
        btorvcd.arg(witness.as_ref());
        let output = btorvcd.output()?;
        if !output.status.success() {
            info!("{}", String::from_utf8_lossy(&output.stdout));
            info!("{}", String::from_utf8_lossy(&output.stderr));
            anyhow::bail!(
                "btorvcd/btorsim execution failed.\n{}",
                format_output_for_error(&output)
            )
        }
        let vcd_file = fs::File::open(&vcd)?;
        let mut filtered = Vec::new();
        let top = vcd_cfg.and_then(|c| c.top.as_deref());
        Self::filter_vcd(vcd_file, &mut filtered, top, Some(|i| i % 2 == 1))?;
        fs::write(vcd.as_ref(), &filtered)?;

        Ok(())
    }

    fn filter_scope_item(
        item: &vcd::ScopeItem,
        writer: &mut vcd::Writer<impl std::io::Write>,
        target_path: &[&str],
        kept_ids: &mut GHashMap<IdCode, IdCode>,
    ) -> anyhow::Result<()> {
        if target_path.is_empty() {
            match item {
                vcd::ScopeItem::Scope(scope) => {
                    writer.add_module(&scope.identifier)?;
                    for child in &scope.items {
                        Self::filter_scope_item(child, writer, &[], kept_ids)?;
                    }
                    writer.upscope()?;
                }
                vcd::ScopeItem::Var(var) => {
                    let new_id =
                        writer.add_var(var.var_type, var.size, &var.reference, var.index)?;
                    kept_ids.insert(var.code, new_id);
                }
                _ => {}
            }
        } else {
            // We are searching for the target scope.
            if let vcd::ScopeItem::Scope(scope) = item
                && scope.identifier == target_path[0]
            {
                let next_path = &target_path[1..];
                if next_path.is_empty() {
                    // Found the target scope. Keep it to ensure variables are in a scope.
                    writer.add_module(&scope.identifier)?;
                    for child in &scope.items {
                        Self::filter_scope_item(child, writer, &[], kept_ids)?;
                    }
                    writer.upscope()?;
                } else {
                    // Keep searching
                    for child in &scope.items {
                        Self::filter_scope_item(child, writer, next_path, kept_ids)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn filter_vcd(
        vcd: impl Read,
        out: impl Write,
        top: Option<&str>,
        skip_timestamp: Option<impl Fn(usize) -> bool>,
    ) -> anyhow::Result<()> {
        let mut parser = vcd::Parser::new(BufReader::new(vcd));
        let mut writer = vcd::Writer::new(BufWriter::new(out));

        let mut kept_ids = GHashMap::new();

        let header = parser.parse_header()?;

        if let Some(version) = &header.version {
            writer.version(version)?;
        }
        if let Some(date) = &header.date {
            writer.date(date)?;
        }
        if let Some(ts) = header.timescale {
            writer.timescale(ts.0, ts.1)?;
        }

        let target_path: Vec<&str> = match top {
            Some(t) if !t.is_empty() => t.split('.').collect(),
            _ => Vec::new(),
        };

        for item in &header.items {
            Self::filter_scope_item(item, &mut writer, &target_path, &mut kept_ids)?;
        }

        writer.enddefinitions()?;

        let mut timestamp_index = 0usize;
        let mut skip_current = false;

        for cmd in parser {
            let cmd = cmd?;
            match cmd {
                vcd::Command::Timestamp(t) => {
                    skip_current = skip_timestamp.as_ref().is_some_and(|f| f(timestamp_index));
                    if !skip_current {
                        writer.timestamp(t)?;
                    }
                    timestamp_index += 1;
                }
                vcd::Command::ChangeScalar(id, v) => {
                    if !skip_current {
                        if let Some(&new_id) = kept_ids.get(&id) {
                            writer.change_scalar(new_id, v)?;
                        } else if kept_ids.is_empty() {
                            writer.change_scalar(id, v)?;
                        }
                    }
                }
                vcd::Command::ChangeVector(id, v) => {
                    if !skip_current {
                        if let Some(&new_id) = kept_ids.get(&id) {
                            writer.change_vector(new_id, &v)?;
                        } else if kept_ids.is_empty() {
                            writer.change_vector(id, &v)?;
                        }
                    }
                }
                vcd::Command::ChangeReal(id, v) => {
                    if !skip_current {
                        if let Some(&new_id) = kept_ids.get(&id) {
                            writer.change_real(new_id, v)?;
                        } else if kept_ids.is_empty() {
                            writer.change_real(id, v)?;
                        }
                    }
                }
                vcd::Command::ChangeString(id, v) => {
                    if !skip_current {
                        if let Some(&new_id) = kept_ids.get(&id) {
                            writer.change_string(new_id, &v)?;
                        } else if kept_ids.is_empty() {
                            writer.change_string(id, &v)?;
                        }
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }
}
