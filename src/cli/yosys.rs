use super::Ric3Config;
use giputils::file::recreate_dir;
use log::info;
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

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

    pub fn execute(&mut self, cwd: Option<impl AsRef<Path>>) -> anyhow::Result<()> {
        let cmds = self.commands.join(" ; ");
        let mut cmd = Command::new("yosys");
        if let Some(cwd) = cwd {
            cmd.current_dir(cwd.as_ref());
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
        yosys.add_command("rename -witness");
        yosys.add_command("scc -select; simplemap; select -clear");
        yosys.add_command("memory_nordff");
        yosys.add_command("chformal -cover -remove");
        yosys.add_command("chformal -early");
        yosys.add_command("chformal -lower");
        yosys.add_command("opt_clean");
        yosys.add_command("formalff -clk2ff -hierarchy -assume"); // -ff2anyinit
        yosys.add_command("check");
        yosys.add_command("setundef -undriven -anyseq");
        yosys.add_command("opt -fast");
        yosys.add_command("rename -witness");
        yosys.add_command("opt_clean");
        yosys.add_command("memory_map -formal");
        yosys.add_command("opt -fast");
        yosys.add_command("delete -output");
        yosys.add_command("dffunmap");
        let dp = PathBuf::from("..");
        yosys.add_command(&format!(
            "write_btor -i {} -ywmap {} {}",
            dp.join("dut.info").display(),
            dp.join("dut.ywb").display(),
            dp.join("dut.btor").display(),
        ));
        yosys.execute(Some(src_dir))
    }
}
