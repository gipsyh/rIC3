#![feature(ptr_metadata)]

mod cli;

use crate::cli::cli_main;
use std::{fs, io::Write};

fn main() -> anyhow::Result<()> {
    fs::create_dir_all("/tmp/rIC3")?;
    cli_main()
}

fn logger_init() {
    env_logger::Builder::from_default_env()
        .format(|buf, record| {
            let now = time::OffsetDateTime::now_utc();
            let ts = now
                .format(time::macros::format_description!(
                    "[hour repr:24]:[minute]:[second]"
                ))
                .unwrap();

            let meta_style = env_logger::fmt::style::Style::new().dimmed();
            let level_style = buf.default_level_style(record.level());
            writeln!(
                buf,
                "{meta_style}[{ts} {meta_style:#}{level_style}{}{level_style:#}{meta_style}]{meta_style:#} {}",
                record.level(),
                record.args()
            )
        })
        .format_target(false)
        .init();
}
