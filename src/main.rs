mod cli;

use crate::cli::cli_main;
use env_logger::Target;
use log::{Level, error};
use std::{env, io::Write, panic};

fn main() -> anyhow::Result<()> {
    cli_main()
}

fn logger_init(level: Option<Level>) {
    let mut builder = env_logger::Builder::new();
    if let Some(level) = level {
        builder.filter_level(level.to_level_filter());
    } else {
        builder.parse_filters(&env::var("RUST_LOG").unwrap_or_else(|_| "info".to_owned()));
    }
    builder
        .parse_write_style(&env::var("RUST_LOG_STYLE").unwrap_or_default())
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
        .target(Target::Stdout)
        .init();

    let default_hook = panic::take_hook();
    panic::set_hook(Box::new(move |info| {
        error!("{info}");
        default_hook(info);
    }));
}
