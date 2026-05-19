use crate::cli::run::{McStatus, PropMcState, Run};
use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};
use rIC3::McResult;
use std::{thread::sleep, time::Duration};

impl PropMcState {
    fn status_text(&self) -> String {
        match self.prop.res {
            McResult::UNSAT => "Proved".to_string(),
            McResult::SAT(bound) => format!("Violated at bound {bound}"),
            McResult::Unknown(Some(bound)) => match self.state {
                McStatus::Solving => format!("Solving bound {bound}"),
                McStatus::Wait => format!("Waiting bound {bound}"),
                McStatus::Pause => format!("Paused bound {bound}"),
            },
            McResult::Unknown(None) => match self.state {
                McStatus::Solving => "Solving".to_string(),
                McStatus::Wait => "Waiting".to_string(),
                McStatus::Pause => "Paused".to_string(),
            },
        }
    }

    fn progress_message(&self) -> String {
        format!(
            "p{:<3} {:<32} {}",
            self.prop.id,
            truncate(&self.prop.name, 32),
            self.status_text()
        )
    }

    fn plain_message(&self) -> String {
        format!(
            "p{} {}: {}",
            self.prop.id,
            self.prop.name,
            self.status_text()
        )
    }
}

impl Run {
    pub(crate) fn run_progress(&mut self) -> anyhow::Result<()> {
        let mp = MultiProgress::with_draw_target(ProgressDrawTarget::stdout_with_hz(10));
        mp.set_move_cursor(true);
        let style = ProgressStyle::with_template("{spinner:.cyan} {wide_msg}")?
            .tick_strings(&["-", "\\", "|", "/"]);
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

            if self.all_done() || self.is_idle() {
                for (id, prop) in self.mc.iter().enumerate() {
                    finish_bar(&bars[id], prop);
                }
                mp.clear()?;
                for prop in &self.mc {
                    println!("{}", prop.plain_message());
                }
                return Ok(());
            }

            sleep(Duration::from_millis(100));
        }
    }

    pub(crate) fn run_plain(&mut self) -> anyhow::Result<()> {
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
        McResult::UNSAT => bar.finish_with_message(format!("[OK] {}", prop.progress_message())),
        McResult::SAT(_) => bar.finish_with_message(format!("[FAIL] {}", prop.progress_message())),
        McResult::Unknown(_) if prop.state == McStatus::Pause => {
            bar.finish_with_message(format!("[STOP] {}", prop.progress_message()))
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
