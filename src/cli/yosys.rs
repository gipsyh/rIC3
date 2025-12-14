use super::Ric3Config;
use std::{path::Path, process::Command};

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

    pub fn execute(&mut self) {
        let cmds = self.commands.join(" ; ");
        let status = Command::new("yosys")
            .arg("-p")
            .arg(&cmds)
            .status()
            .expect("Failed to execute yosys");
        if !status.success() {
            panic!("Yosys failed");
        }
    }

    pub fn generate_btor(cfg: &Ric3Config, p: impl AsRef<Path>) {
        let mut yosys = Self::new();
        for file in &cfg.dut.files {
            yosys.add_command(&format!("read_verilog -sv {}", file.display()));
        }
        yosys.add_command(&format!("prep -top {}", cfg.dut.top));
        yosys.add_command("hierarchy -smtcheck");
        yosys.add_command("rename -witness");
        yosys.add_command("scc -select; simplemap; select -clear");
        yosys.add_command("memory_nordff");
        yosys.add_command("async2sync");
        yosys.add_command("chformal -assume -early");
        yosys.add_command("opt_clean");
        yosys.add_command("formalff -setundef -clk2ff -ff2anyinit -hierarchy");
        yosys.add_command("chformal -live -fair -cover -remove");
        yosys.add_command("opt_clean");
        yosys.add_command("check");
        yosys.add_command("setundef -undriven -anyseq");
        yosys.add_command("opt -fast");
        yosys.add_command("rename -witness");
        yosys.add_command("opt_clean");
        yosys.add_command("hierarchy -simcheck");
        yosys.add_command("delete */t:$print");
        yosys.add_command("formalff -assume");
        yosys.add_command("memory_map -formal");
        yosys.add_command("formalff -setundef -clk2ff -ff2anyinit");
        yosys.add_command("flatten");
        yosys.add_command("setundef -undriven -anyseq");
        yosys.add_command("opt -fast");
        yosys.add_command("delete -output");
        yosys.add_command("dffunmap");
        let dp = p.as_ref();
        yosys.add_command(&format!(
            "write_btor -i {} -ywmap {} {}",
            dp.join("dut.info").display(),
            dp.join("dut.ywb").display(),
            dp.join("dut.btor").display(),
        ));
        yosys.execute();
    }
}
