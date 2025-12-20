use crate::cli::VcdConfig;

use super::Ric3Config;
use giputils::file::recreate_dir;
use giputils::hash::GHashMap;
use log::info;
use std::{
    fs,
    io::{BufReader, BufWriter},
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
            println!("{}", String::from_utf8_lossy(&output.stdout));
            println!("{}", String::from_utf8_lossy(&output.stderr));
            anyhow::bail!("Yosys execution failed")
        }
        Ok(())
    }

    pub fn generate_btor(cfg: &Ric3Config, p: impl AsRef<Path>) -> anyhow::Result<()> {
        info!("Yosys: parsing the DUT and generating BTOR.");
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
            "write_btor -ywmap {} {}",
            dp.join("dut.ywb").display(),
            dp.join("dut.btor").display(),
        ));
        yosys.execute(Some(&src_dir))
    }

    pub fn btor_wit_to_yosys_wit(
        btor_wit: impl AsRef<Path>,
        ywb_file: impl AsRef<Path>,
        yosys_wit: impl AsRef<Path>,
    ) -> anyhow::Result<()> {
        let output = Command::new("yosys-witness")
            .arg("wit2yw")
            .arg(btor_wit.as_ref())
            .arg(ywb_file.as_ref())
            .arg(yosys_wit.as_ref())
            .output()?;
        if !output.status.success() {
            println!("{}", String::from_utf8_lossy(&output.stdout));
            println!("{}", String::from_utf8_lossy(&output.stderr));
            anyhow::bail!("yosys-witness execution failed")
        }
        Ok(())
    }

    pub fn yosys_wit_to_vcd(
        rtlil: impl AsRef<Path>,
        yw: impl AsRef<Path>,
        vcd: impl AsRef<Path>,
    ) -> anyhow::Result<()> {
        let mut yosys = Self::new();
        yosys.add_command(&format!("read_rtlil {}", rtlil.as_ref().display()));
        yosys.add_command(&format!(
            "sim -r {} -vcd {} -hdlname",
            yw.as_ref().display(),
            vcd.as_ref().display()
        ));
        yosys.execute(None)?;
        Ok(())
    }

    pub fn btor_wit_to_vcd(
        dut: impl AsRef<Path>,
        btor_wit: impl AsRef<Path>,
        vcd: impl AsRef<Path>,
        vcd_cfg: Option<&VcdConfig>,
    ) -> anyhow::Result<()> {
        let dut = dut.as_ref();
        let yw = tempfile::NamedTempFile::with_suffix(".yw")?;
        Self::btor_wit_to_yosys_wit(&btor_wit, dut.join("dut.ywb"), &yw)?;
        if let Some(VcdConfig { top: Some(top) }) = vcd_cfg {
            let temp_vcd = tempfile::NamedTempFile::with_suffix(".vcd")?;
            Self::yosys_wit_to_vcd(dut.join("dut.il"), &yw, &temp_vcd)?;
            Self::filter_vcd(temp_vcd.path(), vcd.as_ref(), top)?;
            return Ok(());
        }
        Self::yosys_wit_to_vcd(dut.join("dut.il"), &yw, vcd)?;
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

    fn filter_vcd(input: &Path, output: &Path, top: &str) -> anyhow::Result<()> {
        let file = fs::File::open(input)?;
        let mut parser = vcd::Parser::new(BufReader::new(file));

        let out_file = fs::File::create(output)?;
        let mut writer = vcd::Writer::new(BufWriter::new(out_file));

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
