use super::Ctilg;
use ratatui::crossterm::style::Stylize;
use std::io::{self, Write};
use tabled::{
    Table, Tabled,
    settings::{Format, Modify, Style, object::Rows},
};

#[derive(Tabled)]
struct InductiveResult {
    #[tabled(rename = "ID")]
    id: usize,
    #[tabled(rename = "Property")]
    property: String,
    #[tabled(rename = "Result")]
    result: String,
}

impl Ctilg {
    pub fn tui_run(&mut self) -> anyhow::Result<Option<usize>> {
        let mut results = Vec::new();
        for (i, &res) in self.res.iter().enumerate() {
            let name = if let Some(term) = self.uts.ts.bad.get(i) {
                self.symbol
                    .get(term)
                    .map(|s| s.as_str())
                    .unwrap_or("Unknown")
            } else {
                "Unknown"
            };
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

        let mut table = Table::new(results);
        table.with(Style::empty()).with(
            Modify::new(Rows::first()).with(Format::content(|s| s.yellow().bold().to_string())),
        );

        println!("{}", table);

        loop {
            print!("Please enter the ID of the property to generate CTI (or 'q' to quit): ");
            io::stdout().flush()?;
            let mut input = String::new();
            io::stdin().read_line(&mut input)?;
            let input = input.trim();

            if input == "q" {
                return Ok(None);
            }

            match input.parse::<usize>() {
                Ok(id) => {
                    if id < self.res.len() {
                        if self.res[id] {
                            println!("Property {} is inductive, cannot generate CTI.", id);
                        } else {
                            return Ok(Some(id));
                        }
                    } else {
                        println!("Invalid ID.");
                    }
                }
                Err(_) => {
                    println!("Invalid input.");
                }
            }
        }
    }
}
