use crate::cli::{VcdConfig, cache::Ric3Proj, cill::CIll, vcd::wlwitness_vcd};
use chrono::{DateTime, Duration, Local};
use rIC3::{McWitness, frontend::Frontend, transys::certify::BlWitness};
use ratatui::crossterm::style::Stylize;
use serde::{Deserialize, Serialize};
use std::{
    fmt,
    fs::{self, File},
    io::BufWriter,
    path::Path,
};
use tabled::{
    Table, Tabled,
    settings::{Format, Modify, Style, object::Rows},
};

impl CIll {
    pub fn save_witness(
        &mut self,
        wit: &BlWitness,
        p: impl AsRef<Path>,
        vcd: Option<impl AsRef<Path>>,
    ) -> anyhow::Result<()> {
        let wit = self.ts_rst.restore_witness(wit);
        let mut wit = self.bb_map.restore_witness(&wit);
        let bwit = self.btorfe.unsafe_certificate(McWitness::Wl(wit.clone()));
        fs::write(&p, format!("{}", bwit))?;
        let Some(vcd) = vcd else {
            return Ok(());
        };
        let vcd_file = BufWriter::new(File::create(&vcd)?);
        let filter = if let Some(VcdConfig { top: Some(t) }) = &self.rcfg.trace {
            t.as_str()
                .strip_prefix(&self.rcfg.dut.top)
                .map(|s| s.strip_prefix('.').unwrap_or(s))
                .unwrap()
        } else {
            ""
        };
        wit.enrich(&self.wsym.keys().cloned().collect());
        wlwitness_vcd(&wit, &self.wsym, vcd_file, filter)?;
        // crate::cli::yosys::Yosys::btor_wit_to_vcd(
        //     self.rp.path("dut"),
        //     &cti_file,
        //     &vcd,
        //     false,
        //     self.rcfg.trace.as_ref(),
        // )?;
        Ok(())
    }
}

#[derive(Tabled)]
struct InductiveResult {
    #[tabled(rename = "ID")]
    id: usize,
    #[tabled(rename = "Property")]
    property: String,
    #[tabled(rename = "Result")]
    result: String,
}

impl CIll {
    pub fn print_ind_res(&mut self) -> anyhow::Result<()> {
        let mut results = Vec::new();
        for (i, &res) in self.res.iter().enumerate() {
            let name = &self.wsym.prop[i];
            let status = if res {
                "Inductive".green().to_string()
            } else {
                "Not Inductive".red().to_string()
            };
            results.push(InductiveResult {
                id: i,
                property: name.to_string(),
                result: status,
            });
        }

        let mut table = Table::new(&results);
        table.with(Style::empty()).with(
            Modify::new(Rows::first()).with(Format::content(|s| s.yellow().bold().to_string())),
        );

        println!("{}", table);

        Ok(())

        // loop {
        //     print!("Please enter the ID of the property to generate CTI (or 'q' to quit): ");
        //     io::stdout().flush()?;
        //     let mut input = String::new();
        //     io::stdin().read_line(&mut input)?;
        //     let input = input.trim();

        //     if input == "q" {
        //         return Ok(None);
        //     }

        //     match input.parse::<usize>() {
        //         Ok(id) => {
        //             if id < self.res.len() {
        //                 if self.res[id] {
        //                     println!(
        //                         "{} is inductive, cannot generate CTI.",
        //                         results[id].property
        //                     );
        //                 } else {
        //                     println!("{} is selected for CTI generation.", results[id].property);
        //                     return Ok(Some(id));
        //                 }
        //             } else {
        //                 println!("Invalid ID.");
        //             }
        //         }
        //         Err(_) => {
        //             println!("Invalid input.");
        //         }
        //     }
        // }
    }
}

#[derive(Serialize, Deserialize)]
pub struct CIllStat {
    pub start: DateTime<Local>,
    pub bmc_time: Duration,
    pub ind_time: Duration,
}

impl Default for CIllStat {
    fn default() -> Self {
        Self {
            start: Local::now(),
            bmc_time: Duration::zero(),
            ind_time: Duration::zero(),
        }
    }
}

impl CIllStat {
    pub fn init(rp: &Ric3Proj) -> anyhow::Result<()> {
        if rp.path("cill/statistic.ron").exists() {
            return Ok(());
        }
        let stat = Self::default();
        stat.save(rp)
    }

    pub fn load(rp: &Ric3Proj) -> anyhow::Result<Self> {
        let content = fs::read_to_string(rp.path("cill/statistic.ron"))?;
        Ok(ron::from_str(&content)?)
    }

    pub fn save(&self, rp: &Ric3Proj) -> anyhow::Result<()> {
        fs::write(rp.path("cill/statistic.ron"), ron::to_string(self)?)?;
        Ok(())
    }
}

impl fmt::Display for CIllStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let elapsed = Local::now().signed_duration_since(self.start);
        write!(
            f,
            "Total time: {}s, Correctness check: {}s, Inductiveness check: {}s",
            elapsed.num_seconds(),
            self.bmc_time.num_seconds(),
            self.ind_time.num_seconds()
        )
    }
}
