use super::Ric3Config;
use crate::cli::VcdConfig;
use giputils::file::recreate_dir;
use giputils::hash::GHashMap;
use log::info;
use std::{
    fs,
    io::{BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    process::Command,
};
use vcd::IdCode;

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
        if let Some(cwd) = cwd {
            cmd.current_dir(cwd);
        }
        let output = cmd.arg("-p").arg(&cmds).output()?;
        if !output.status.success() {
            info!("{}", String::from_utf8_lossy(&output.stdout));
            info!("{}", String::from_utf8_lossy(&output.stderr));
            anyhow::bail!("Yosys execution failed")
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
        for file in files.iter() {
            yosys.add_command(&format!("read_verilog -formal -sv {}", file.display()));
        }
        yosys.add_command(&format!("prep -flatten -top {}", cfg.dut.top));
        yosys.add_command("hierarchy -smtcheck -nokeep_prints");
        yosys.add_command("scc -select; simplemap; select -clear");
        yosys.add_command("memory_nordff");
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
            anyhow::bail!("Yosys execution failed")
        }
        if let Some(VcdConfig { top: Some(top) }) = vcd_cfg {
            let mut filter = Vec::new();
            let vcd_file = fs::File::open(&vcd)?;
            Self::filter_vcd(vcd_file, &mut filter, top)?;
            fs::write(vcd.as_ref(), filter)?;
        }
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

    fn filter_vcd(vcd: impl Read, out: impl Write, top: &str) -> anyhow::Result<()> {
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

        let target_path: Vec<&str> = if top.is_empty() {
            Vec::new()
        } else {
            top.split('.').collect()
        };

        for item in &header.items {
            Self::filter_scope_item(item, &mut writer, &target_path, &mut kept_ids)?;
        }

        writer.enddefinitions()?;

        for cmd in parser {
            let cmd = cmd?;
            match cmd {
                vcd::Command::Timestamp(t) => writer.timestamp(t)?,
                vcd::Command::ChangeScalar(id, v) => {
                    if let Some(&new_id) = kept_ids.get(&id) {
                        writer.change_scalar(new_id, v)?;
                    }
                }
                vcd::Command::ChangeVector(id, v) => {
                    if let Some(&new_id) = kept_ids.get(&id) {
                        writer.change_vector(new_id, &v)?;
                    }
                }
                vcd::Command::ChangeReal(id, v) => {
                    if let Some(&new_id) = kept_ids.get(&id) {
                        writer.change_real(new_id, v)?;
                    }
                }
                vcd::Command::ChangeString(id, v) => {
                    if let Some(&new_id) = kept_ids.get(&id) {
                        writer.change_string(new_id, &v)?;
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }
}
