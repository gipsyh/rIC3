use super::Ric3Config;
use crate::cli::Parse;
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

    pub fn execute(
        &mut self,
        cwd: Option<&Path>,
        plugin: impl IntoIterator<Item = String>,
    ) -> anyhow::Result<()> {
        let cmds = self.commands.join(" ; ");
        let mut cmd = Command::new("yosys");
        for p in plugin {
            cmd.args(["-m", &p]);
        }
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
        Self::generate_btor_with_files(cfg, &cfg.dut.files, p, "dut")
    }

    pub fn generate_btor_with_files(
        cfg: &Ric3Config,
        input_files: &[PathBuf],
        p: impl AsRef<Path>,
        stem: &str,
    ) -> anyhow::Result<()> {
        info!("Yosys: parsing SystemVerilog and generating BTOR.");
        let slang = cfg
            .modeling
            .as_ref()
            .is_none_or(|m| matches!(m.parser, Parse::yosys_slang));
        recreate_dir(p.as_ref())?;
        let src_dir = p.as_ref().join("src");
        recreate_dir(&src_dir)?;
        let mut files = Vec::new();
        for f in input_files {
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
        let mut read = if slang {
            "read_slang -Wnone -D FORMAL -D YOSYS_SLANG"
        } else {
            "read_verilog -formal -sv"
        }
        .to_string();
        for define in define_args(&cfg.dut.defines) {
            read.push_str(&format!(" {define}"));
        }
        for file in files.iter() {
            read.push_str(&format!(" {}", file.display()));
        }
        yosys.add_command(&read);
        yosys.add_command(&format!("prep -flatten -top {}", cfg.dut.top));
        yosys.add_command("hierarchy -smtcheck -nokeep_prints");
        yosys.add_command("memory_nordff");
        if let Some(reset) = &cfg.dut.reset {
            if reset.starts_with("!") {
                let reset = reset.strip_prefix("!").unwrap();
                yosys.add_command(&format!("fminit -seq {} 0,1", reset));
            } else {
                yosys.add_command(&format!("fminit -seq {} 1,0", reset));
            }
        }
        yosys.add_command("chformal -cover -remove");
        yosys.add_command("async2sync");
        yosys.add_command("formalff -clk2ff -ff2anyinit -hierarchy -assume");
        yosys.add_command("memory_map -formal");
        yosys.add_command("dffunmap");
        yosys.add_command("setundef -undriven -anyseq");
        yosys.add_command("opt -fast");
        yosys.add_command("opt_clean");
        yosys.add_command("rename -witness");
        yosys.add_command("check");
        let dp = PathBuf::from("..");
        yosys.add_command(&format!(
            "write_rtlil {}",
            dp.join(format!("{stem}.il")).display()
        ));
        yosys.add_command(&format!(
            "write_btor -ywmap {} -i {} {}",
            dp.join(format!("{stem}.ywb")).display(),
            dp.join(format!("{stem}.info")).display(),
            dp.join(format!("{stem}.btor")).display(),
        ));
        let plugin = if slang {
            vec!["slang".to_string()]
        } else {
            vec![]
        };
        yosys.execute(Some(&src_dir), plugin)
    }
}

fn define_args(defines: &giputils::hash::GHashMap<String, String>) -> Vec<String> {
    let mut defines = defines.iter().collect::<Vec<_>>();
    defines.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));
    defines
        .into_iter()
        .map(|(name, value)| {
            if value.is_empty() {
                format!("-D {name}")
            } else {
                format!("-D {name}={value}")
            }
        })
        .collect()
}
