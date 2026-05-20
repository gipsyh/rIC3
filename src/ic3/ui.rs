use super::IC3;
use crate::McResult;
use indicatif::{MultiProgress, ProgressBar, ProgressDrawTarget, ProgressStyle};
use ratatui::crossterm::{style::Stylize, terminal};
use std::fmt::Write;
use std::io::IsTerminal;
use std::time::Duration;

/// Template prefix width for the frame bar ("  ").
const FRAME_PREFIX_WIDTH: usize = 2;

pub struct IC3Progress {
    _mp: MultiProgress,
    status_bar: ProgressBar,
    frame_bar: ProgressBar,
}

impl IC3Progress {
    pub fn new() -> Option<Self> {
        if !std::io::stderr().is_terminal() {
            return None;
        }

        let mp = MultiProgress::with_draw_target(ProgressDrawTarget::stderr_with_hz(10));
        mp.set_move_cursor(true);

        let spinner_style = ProgressStyle::with_template("{spinner:.cyan.bold} {wide_msg}")
            .unwrap()
            .tick_strings(&["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏", "✔"]);
        let plain_style = ProgressStyle::with_template("  {wide_msg}").unwrap();

        let status_bar = mp.add(ProgressBar::new_spinner());
        status_bar.set_style(spinner_style);
        status_bar.set_message(format!(
            "{}  {}  {}",
            "rIC3".magenta().bold(),
            "────".dark_grey(),
            "Initializing…".dark_grey(),
        ));
        status_bar.enable_steady_tick(Duration::from_millis(100));

        let frame_bar = mp.add(ProgressBar::new_spinner());
        frame_bar.set_style(plain_style);
        frame_bar.set_message(format!("{} {}", "Frames".green().bold(), "—".dark_grey(),));
        frame_bar.enable_steady_tick(Duration::from_millis(100));

        Some(Self {
            _mp: mp,
            status_bar,
            frame_bar,
        })
    }
}

fn term_width() -> usize {
    terminal::size().map(|(w, _)| usize::from(w)).unwrap_or(80)
}

impl IC3 {
    /// Render the live progress UI (no-op if terminal is not detected).
    pub(super) fn render_progress(&self) {
        let Some(progress) = &self.progress else {
            return;
        };
        if self.solvers.is_empty() {
            return;
        }

        let level = self.level();
        let time = self.statistic.time.time();
        let tw = term_width();

        // ── Status line ──────────────────────────────────────────────
        progress.status_bar.set_message(format!(
            "{}  {}  {}  {}  {} {}",
            "rIC3".magenta().bold(),
            "────".dark_grey(),
            format!("Level {level}").cyan().bold(),
            "────".dark_grey(),
            "⏱".white(),
            format_duration(time).white().bold(),
        ));

        // ── Frames line (width-aware) ────────────────────────────────
        progress.frame_bar.set_message(format_frame_line(self, tw));
    }

    /// Finish the progress UI with result-specific styling.
    pub(super) fn finish_progress(&self, result: McResult) {
        let Some(progress) = &self.progress else {
            return;
        };
        if !self.solvers.is_empty() {
            self.render_progress();
        }

        let (style, icon, label) = match result {
            McResult::UNSAT => (
                ProgressStyle::with_template("{prefix:.green.bold} {wide_msg}").unwrap(),
                "✔",
                "UNSAT".green().bold().to_string(),
            ),
            McResult::SAT(d) => (
                ProgressStyle::with_template("{prefix:.red.bold} {wide_msg}").unwrap(),
                "✘",
                format!("SAT({d})").red().bold().to_string(),
            ),
            McResult::Unknown(_) => (
                ProgressStyle::with_template("{prefix:.yellow.bold} {wide_msg}").unwrap(),
                "⚠",
                "UNKNOWN".yellow().bold().to_string(),
            ),
        };

        let level = if self.solvers.is_empty() {
            0
        } else {
            self.level()
        };
        let time = self.statistic.time.time();

        // Status bar: icon + result
        progress.status_bar.set_style(style);
        progress.status_bar.set_prefix(icon);
        progress.status_bar.finish_with_message(format!(
            "{}  {}  {}  {}  {} {}  {}  {}",
            "rIC3".magenta().bold(),
            "────".dark_grey(),
            format!("Level {level}").cyan().bold(),
            "────".dark_grey(),
            "⏱".white(),
            format_duration(time).white().bold(),
            "────".dark_grey(),
            label,
        ));

        // Frame bar: just finish, keep content, no icon
        progress.frame_bar.finish();
    }
}

/// Build the frame line message, truncating from the left to fit `tw`.
///
/// When all frames fit:
///   `Frames [8]  12 45 23 67 34 89 12 45 ∞ 156`
///
/// When truncated:
///   `Frames [80]  …+62 34 89 12 45 23 67 ∞ 156`
fn format_frame_line(ic3: &IC3, tw: usize) -> String {
    let num_frames = ic3.frame.len();
    let total = num_frames + 1;
    let inf_count = ic3.frame.inf.len();

    // Visual widths of the fixed parts (char count, not bytes).
    let prefix_text = format!("Frames [{}]  ", total);
    let prefix_vw = prefix_text.chars().count();
    // "∞ N" — "∞" is 1 column wide.
    let suffix_vw = 2 + inf_count.to_string().len(); // "∞ " + digits

    let budget = tw
        .saturating_sub(FRAME_PREFIX_WIDTH)
        .saturating_sub(prefix_vw)
        .saturating_sub(suffix_vw);

    // Greedily fit frame numbers from the end.
    // At each step, if frame[i] is included then frames 0..i are hidden,
    // so we account for the indicator "…+{hidden} " in the width check.
    let mut start = num_frames;
    let mut used = 0usize;
    for i in (0..num_frames).rev() {
        let fw = ic3.frame[i].len().to_string().len() + 1; // "N "
        let hidden = i; // frames 0..i would be hidden
        let indicator_w = if hidden > 0 {
            // "…+N " visual width
            2 + hidden.to_string().len() + 1
        } else {
            0
        };
        if used + fw + indicator_w > budget {
            break;
        }
        used += fw;
        start = i;
    }
    let hidden = start;

    // ── Assemble the styled message ──────────────────────────────────
    let mut msg = format!(
        "{} {}  ",
        "Frames".green().bold(),
        format!("[{total}]").green(),
    );

    if hidden > 0 {
        write!(msg, "{} ", format!("…+{hidden}").dark_grey()).unwrap();
    }
    for i in start..num_frames {
        let count = ic3.frame[i].len();
        write!(msg, "{} ", count.to_string().white()).unwrap();
    }
    write!(
        msg,
        "{} {}",
        "∞".cyan().bold(),
        inf_count.to_string().cyan().bold(),
    )
    .unwrap();

    msg
}

fn format_duration(d: Duration) -> String {
    let secs = d.as_secs();
    if d.is_zero() {
        "0s".to_string()
    } else if secs < 60 {
        format!("{}.{}s", secs, d.subsec_millis() / 100)
    } else if secs < 3600 {
        format!("{}m {}s", secs / 60, secs % 60)
    } else {
        format!("{}h {}m", secs / 3600, (secs % 3600) / 60)
    }
}
