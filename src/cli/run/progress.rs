use crate::cli::run::{McStatus, PropMcState, Run};
use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};
use rIC3::McResult;
use ratatui::crossterm::style::Stylize;
use std::{thread::sleep, time::Duration};

impl PropMcState {
    fn status_columns(&self) -> (String, String) {
        match self.prop.res {
            McResult::UNSAT => (
                format!("{:<10}", "Proved").green().bold().to_string(),
                format!("{:<10}", "-").to_string(),
            ),
            McResult::SAT(b) => (
                format!("{:<10}", "Violated").red().bold().to_string(),
                format!("{:<10}", b).to_string(),
            ),
            McResult::Unknown(Some(b)) => match self.state {
                McStatus::Solving => (
                    format!("{:<10}", "Solving").yellow().to_string(),
                    format!("{:<10}", b).cyan().bold().to_string(),
                ),
                McStatus::Wait => (
                    format!("{:<10}", "Waiting").dark_grey().to_string(),
                    format!("{:<10}", b).blue().to_string(),
                ),
                McStatus::Pause => (
                    format!("{:<10}", "Paused").dark_grey().to_string(),
                    format!("{:<10}", b).blue().to_string(),
                ),
            },
            McResult::Unknown(None) => match self.state {
                McStatus::Solving => (
                    format!("{:<10}", "Solving").yellow().to_string(),
                    format!("{:<10}", "-").to_string(),
                ),
                McStatus::Wait => (
                    format!("{:<10}", "Waiting").dark_grey().to_string(),
                    format!("{:<10}", "-").to_string(),
                ),
                McStatus::Pause => (
                    format!("{:<10}", "Paused").dark_grey().to_string(),
                    format!("{:<10}", "-").to_string(),
                ),
            },
        }
    }

    fn message(&self) -> String {
        let (state, bound) = self.status_columns();
        let total_time = self.time + self.start_time.map_or(Duration::ZERO, |t| t.elapsed());
        format!(
            "{} {} {} {} {}",
            format!("{:<6}", format!("p{}", self.prop.id))
                .magenta()
                .bold(),
            format!("{:<32}", truncate(&self.prop.name, 32)).white(),
            state,
            bound,
            format!("{:<10}", format_time(total_time))
        )
    }

    fn progress_message(&self) -> String {
        self.message()
    }

    fn plain_message(&self) -> String {
        self.message()
    }
}

fn format_time(duration: Duration) -> String {
    let secs = duration.as_secs();
    if secs == 0 {
        "<1s".to_string()
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
        println!(
            "  {} {} {} {} {}",
            format!("{:<6}", "ID").bold(),
            format!("{:<32}", "Property").bold(),
            format!("{:<10}", "State").bold(),
            format!("{:<10}", "Bound").bold(),
            format!("{:<10}", "Time").bold(),
        );
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
                bar.set_message(prop.progress_message());
                bar.enable_steady_tick(Duration::from_millis(100));
                bar
            })
            .collect();

        for (id, prop) in self.mc.iter().enumerate() {
            finish_bar(&bars[id], prop);
        }

        loop {
            if self.nexus_task.is_none() {
                self.launch_nexus();
                for (id, prop) in self.mc.iter().enumerate() {
                    update_bar(&bars[id], prop);
                }
            }

            let updates = self.process_updates()?;
            for id in updates.state {
                update_bar(&bars[id], &self.mc[id]);
            }

            // Always update bars occasionally to keep time moving smoothly if solving
            for (id, prop) in self.mc.iter().enumerate() {
                if prop.state == McStatus::Solving {
                    bar_update_time_only(&bars[id], prop);
                }
            }

            if self.all_done() || self.is_idle() {
                for (id, prop) in self.mc.iter().enumerate() {
                    finish_bar(&bars[id], prop);
                }
                return Ok(());
            }

            sleep(Duration::from_millis(100));
        }
    }

    pub(crate) fn run_plain(&mut self) -> anyhow::Result<()> {
        println!(
            "{} {} {} {} {}",
            format!("{:<6}", "ID").bold(),
            format!("{:<32}", "Property").bold(),
            format!("{:<10}", "State").bold(),
            format!("{:<10}", "Bound").bold(),
            format!("{:<10}", "Time").bold(),
        );
        for prop in &self.mc {
            println!("{}", prop.plain_message());
        }

        loop {
            if self.nexus_task.is_none() {
                self.launch_nexus();
                for prop in &self.mc {
                    if prop.state == McStatus::Solving {
                        println!("{}", prop.plain_message());
                    }
                }
            }

            let updates = self.process_updates()?;
            for id in updates.state {
                println!("{}", self.mc[id].plain_message());
            }

            if self.all_done() || self.is_idle() {
                return Ok(());
            }

            sleep(Duration::from_millis(100));
        }
    }
}

fn bar_update_time_only(bar: &ProgressBar, prop: &PropMcState) {
    if !bar.is_finished() {
        bar.set_message(prop.progress_message());
    }
}

fn update_bar(bar: &ProgressBar, prop: &PropMcState) {
    bar.set_message(prop.progress_message());
    if !matches!(prop.prop.res, McResult::Unknown(_)) || prop.state == McStatus::Pause {
        finish_bar(bar, prop);
    } else {
        bar.tick();
    }
}

fn finish_bar(bar: &ProgressBar, prop: &PropMcState) {
    if bar.is_finished() {
        return;
    }

    match prop.prop.res {
        McResult::UNSAT => {
            bar.set_style(ProgressStyle::with_template("{prefix:.green.bold} {wide_msg}").unwrap());
            bar.finish_with_message(prop.progress_message());
            bar.set_prefix("✔");
        }
        McResult::SAT(_) => {
            bar.set_style(ProgressStyle::with_template("{prefix:.red.bold} {wide_msg}").unwrap());
            bar.finish_with_message(prop.progress_message());
            bar.set_prefix("✘");
        }
        McResult::Unknown(_) if prop.state == McStatus::Pause => {
            bar.set_style(
                ProgressStyle::with_template("{prefix:.yellow.bold} {wide_msg}").unwrap(),
            );
            bar.finish_with_message(prop.progress_message());
            bar.set_prefix("⏹");
        }
        _ => {}
    }
}

fn truncate(s: &str, max_chars: usize) -> String {
    let mut chars = s.chars();
    let truncated: String = chars.by_ref().take(max_chars).collect();
    if chars.next().is_some() {
        format!("{truncated}...")
    } else {
        truncated
    }
}
