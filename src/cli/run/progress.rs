use crate::cli::run::{McStatus, PropMcState, Run};
use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};
use rIC3::McResult;
use ratatui::crossterm::{style::Stylize, terminal};
use std::{thread::sleep, time::Duration};

const ID_WIDTH: usize = 6;
const STATE_WIDTH: usize = 10;
const BOUND_WIDTH: usize = 10;
const TIME_WIDTH: usize = 10;
const COLUMN_GAPS: usize = 4;
const MIN_PROPERTY_WIDTH: usize = 1;
const DEFAULT_PROGRESS_WIDTH: usize = 78;
const DEFAULT_PLAIN_WIDTH: usize = 80;
const PROGRESS_PREFIX_WIDTH: usize = 2;

impl PropMcState {
    fn status_columns(&self) -> (String, String) {
        match self.prop.res {
            McResult::UNSAT => (
                format!("{:<STATE_WIDTH$}", "Proved")
                    .green()
                    .bold()
                    .to_string(),
                format!("{:<BOUND_WIDTH$}", "-").to_string(),
            ),
            McResult::SAT(b) => (
                format!("{:<STATE_WIDTH$}", "Violated")
                    .red()
                    .bold()
                    .to_string(),
                format!("{:<BOUND_WIDTH$}", b).to_string(),
            ),
            McResult::Unknown(Some(b)) => match self.state {
                McStatus::Solving => (
                    format!("{:<STATE_WIDTH$}", "Solving").yellow().to_string(),
                    format!("{:<BOUND_WIDTH$}", b).cyan().bold().to_string(),
                ),
                McStatus::Wait => (
                    format!("{:<STATE_WIDTH$}", "Waiting")
                        .dark_grey()
                        .to_string(),
                    format!("{:<BOUND_WIDTH$}", b).blue().to_string(),
                ),
                McStatus::Pause => (
                    format!("{:<STATE_WIDTH$}", "Paused")
                        .dark_grey()
                        .to_string(),
                    format!("{:<BOUND_WIDTH$}", b).blue().to_string(),
                ),
            },
            McResult::Unknown(None) => match self.state {
                McStatus::Solving => (
                    format!("{:<STATE_WIDTH$}", "Solving").yellow().to_string(),
                    format!("{:<BOUND_WIDTH$}", "-").to_string(),
                ),
                McStatus::Wait => (
                    format!("{:<STATE_WIDTH$}", "Waiting")
                        .dark_grey()
                        .to_string(),
                    format!("{:<BOUND_WIDTH$}", "-").to_string(),
                ),
                McStatus::Pause => (
                    format!("{:<STATE_WIDTH$}", "Paused")
                        .dark_grey()
                        .to_string(),
                    format!("{:<BOUND_WIDTH$}", "-").to_string(),
                ),
            },
        }
    }

    fn message(&self, line_width: usize) -> String {
        let (state, bound) = self.status_columns();
        let total_time = self.time + self.start_time.map_or(Duration::ZERO, |t| t.elapsed());
        let property_width = property_width(line_width);
        let property = truncate(&self.prop.name, property_width);
        format!(
            "{} {} {} {} {}",
            format!("{:<ID_WIDTH$}", format!("p{}", self.prop.id))
                .magenta()
                .bold(),
            format!("{property:<property_width$}").white(),
            state,
            bound,
            format!("{:<TIME_WIDTH$}", format_time(total_time))
        )
    }

    fn progress_message(&self, line_width: usize) -> String {
        self.message(line_width)
    }

    fn plain_message(&self, line_width: usize) -> String {
        self.message(line_width)
    }
}

fn format_time(duration: Duration) -> String {
    let secs = duration.as_secs();
    if duration.is_zero() {
        "0s".to_string()
    } else if secs < 60 {
        format!("{}s", secs)
    } else if secs < 3600 {
        format!("{}m {}s", secs / 60, secs % 60)
    } else {
        format!("{}h {}m", secs / 3600, (secs % 3600) / 60)
    }
}

impl Run {
    pub(crate) fn run_progress(&mut self) -> anyhow::Result<()> {
        let mut line_width = progress_line_width();
        println!("  {}", header_message(line_width));
        let mp = MultiProgress::with_draw_target(ProgressDrawTarget::stdout_with_hz(10));
        mp.set_move_cursor(true);
        let style = ProgressStyle::with_template("{spinner:.cyan.bold} {wide_msg}")?
            .tick_strings(&["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏", "✔"]);
        let bars: Vec<_> = self
            .mc
            .iter()
            .map(|prop| {
                let bar = mp.add(ProgressBar::new_spinner());
                bar.set_style(style.clone());
                bar.set_message(prop.progress_message(line_width));
                bar.enable_steady_tick(Duration::from_millis(100));
                bar
            })
            .collect();

        for (id, prop) in self.mc.iter().enumerate() {
            finish_bar(&bars[id], prop, line_width);
        }

        loop {
            let current_line_width = progress_line_width();
            if current_line_width != line_width {
                line_width = current_line_width;
                for (id, prop) in self.mc.iter().enumerate() {
                    update_bar(&bars[id], prop, line_width);
                }
            }

            if self.nexus_task.is_none() {
                self.launch_nexus();
                for (id, prop) in self.mc.iter().enumerate() {
                    update_bar(&bars[id], prop, line_width);
                }
            }

            let updates = self.process_updates()?;
            for id in updates.state {
                update_bar(&bars[id], &self.mc[id], line_width);
            }

            // Always update bars occasionally to keep time moving smoothly if solving
            for (id, prop) in self.mc.iter().enumerate() {
                if prop.state == McStatus::Solving {
                    bar_update_time_only(&bars[id], prop, line_width);
                }
            }

            if self.all_done() || self.is_idle() {
                for (id, prop) in self.mc.iter().enumerate() {
                    finish_bar(&bars[id], prop, line_width);
                }
                return Ok(());
            }

            sleep(Duration::from_millis(100));
        }
    }

    pub(crate) fn run_plain(&mut self) -> anyhow::Result<()> {
        let line_width = plain_line_width();
        println!("{}", header_message(line_width));
        for prop in &self.mc {
            println!("{}", prop.plain_message(line_width));
        }

        loop {
            if self.nexus_task.is_none() {
                self.launch_nexus();
                for prop in &self.mc {
                    if prop.state == McStatus::Solving {
                        println!("{}", prop.plain_message(line_width));
                    }
                }
            }

            let updates = self.process_updates()?;
            for id in updates.state {
                println!("{}", self.mc[id].plain_message(line_width));
            }

            if self.all_done() || self.is_idle() {
                return Ok(());
            }

            sleep(Duration::from_millis(100));
        }
    }
}

fn bar_update_time_only(bar: &ProgressBar, prop: &PropMcState, line_width: usize) {
    if !bar.is_finished() {
        bar.set_message(prop.progress_message(line_width));
    }
}

fn update_bar(bar: &ProgressBar, prop: &PropMcState, line_width: usize) {
    bar.set_message(prop.progress_message(line_width));
    if !matches!(prop.prop.res, McResult::Unknown(_)) || prop.state == McStatus::Pause {
        finish_bar(bar, prop, line_width);
    } else {
        bar.tick();
    }
}

fn finish_bar(bar: &ProgressBar, prop: &PropMcState, line_width: usize) {
    if bar.is_finished() {
        return;
    }

    match prop.prop.res {
        McResult::UNSAT => {
            bar.set_style(ProgressStyle::with_template("{prefix:.green.bold} {wide_msg}").unwrap());
            bar.finish_with_message(prop.progress_message(line_width));
            bar.set_prefix("✔");
        }
        McResult::SAT(_) => {
            bar.set_style(ProgressStyle::with_template("{prefix:.red.bold} {wide_msg}").unwrap());
            bar.finish_with_message(prop.progress_message(line_width));
            bar.set_prefix("✘");
        }
        McResult::Unknown(_) if prop.state == McStatus::Pause => {
            bar.set_style(
                ProgressStyle::with_template("{prefix:.yellow.bold} {wide_msg}").unwrap(),
            );
            bar.finish_with_message(prop.progress_message(line_width));
            bar.set_prefix("⏹");
        }
        _ => {}
    }
}

fn header_message(line_width: usize) -> String {
    let property_width = property_width(line_width);
    let property = truncate("Property", property_width);
    format!(
        "{} {} {} {} {}",
        format!("{:<ID_WIDTH$}", "ID").bold(),
        format!("{property:<property_width$}").bold(),
        format!("{:<STATE_WIDTH$}", "State").bold(),
        format!("{:<BOUND_WIDTH$}", "Bound").bold(),
        format!("{:<TIME_WIDTH$}", "Time").bold(),
    )
}

fn property_width(line_width: usize) -> usize {
    line_width
        .saturating_sub(ID_WIDTH + STATE_WIDTH + BOUND_WIDTH + TIME_WIDTH + COLUMN_GAPS)
        .max(MIN_PROPERTY_WIDTH)
}

fn progress_line_width() -> usize {
    terminal::size()
        .map(|(width, _)| usize::from(width).saturating_sub(PROGRESS_PREFIX_WIDTH))
        .unwrap_or(DEFAULT_PROGRESS_WIDTH)
}

fn plain_line_width() -> usize {
    terminal::size()
        .map(|(width, _)| usize::from(width))
        .unwrap_or(DEFAULT_PLAIN_WIDTH)
}

fn truncate(s: &str, max_chars: usize) -> String {
    let char_count = s.chars().count();
    if char_count <= max_chars {
        s.to_string()
    } else if max_chars <= 3 {
        ".".repeat(max_chars)
    } else {
        let truncated: String = s.chars().take(max_chars - 3).collect();
        format!("{truncated}...")
    }
}
