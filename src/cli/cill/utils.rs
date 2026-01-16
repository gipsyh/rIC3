use crate::cli::{VcdConfig, cill::CIll, vcd::wlwitness_vcd};
use rIC3::{McWitness, frontend::Frontend, transys::certify::BlWitness};
use ratatui::crossterm::style::Stylize;
use std::{
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
