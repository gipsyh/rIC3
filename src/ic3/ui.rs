use super::IC3;
use crate::McResult;
use ratatui::crossterm::terminal;
use ratatui::{
    Terminal, TerminalOptions, Viewport,
    backend::CrosstermBackend,
    layout::{Constraint, Direction, Layout},
    style::Stylize,
    text::{Line, Span},
    widgets::Paragraph,
};
use std::io::IsTerminal;
use std::time::{Duration, Instant};

/// Template prefix width for the frame bar ("  ").
const FRAME_PREFIX_WIDTH: usize = 2;

pub struct IC3Progress {
    terminal: Terminal<CrosstermBackend<std::io::Stderr>>,
    spinner_tick: usize,
    last_update: Instant,
}

impl IC3Progress {
    pub fn new() -> Option<Self> {
        if !std::io::stderr().is_terminal() {
            return None;
        }

        let backend = CrosstermBackend::new(std::io::stderr());
        let mut terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(2),
            },
        )
        .ok()?;

        // Hide cursor initially so it doesn't flicker/show in the inline area
        let _ = terminal.hide_cursor();

        Some(Self {
            terminal,
            spinner_tick: 0,
            last_update: Instant::now(),
        })
    }
}

fn term_width() -> usize {
    terminal::size().map(|(w, _)| usize::from(w)).unwrap_or(80)
}

impl IC3 {
    /// Render the live progress UI (no-op if terminal is not detected).
    pub(super) fn render_progress(&mut self) {
        if self.progress.is_none() {
            return;
        }
        if self.solvers.is_empty() {
            return;
        }

        let level = self.level();
        let time = self.statistic.time.time();
        let tw = term_width();
        let frame_line = format_frame_line(self, tw);

        let progress = self.progress.as_mut().unwrap();
        let now = Instant::now();
        if now.duration_since(progress.last_update) >= Duration::from_millis(80) {
            progress.spinner_tick = progress.spinner_tick.wrapping_add(1);
            progress.last_update = now;
        }
        let spinners = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"];
        let spinner = spinners[progress.spinner_tick % spinners.len()];

        let _ = progress.terminal.draw(|f| {
            let area = f.area();
            let chunks = Layout::default()
                .direction(Direction::Vertical)
                .constraints([Constraint::Length(1), Constraint::Length(1)])
                .split(area);

            // Row 1: Status line
            let status_line = Line::from(vec![
                Span::raw(format!("{} ", spinner)).cyan().bold(),
                Span::raw("rIC3").magenta().bold(),
                Span::raw("  ────  ").dark_gray(),
                Span::raw(format!("Level {}", level)).cyan().bold(),
                Span::raw("  ────  ").dark_gray(),
                Span::raw("⏱ ").white(),
                Span::raw(format_duration(time)).white().bold(),
            ]);
            f.render_widget(Paragraph::new(status_line), chunks[0]);

            // Row 2: Frames line
            f.render_widget(Paragraph::new(frame_line), chunks[1]);
        });
    }

    /// Finish the progress UI with result-specific styling.
    pub(super) fn finish_progress(&mut self, result: McResult) {
        if self.progress.is_none() {
            return;
        }

        let level = if self.solvers.is_empty() {
            0
        } else {
            self.level()
        };
        let time = self.statistic.time.time();
        let tw = term_width();
        let frame_line = format_frame_line(self, tw);

        let (icon, label_span) = match result {
            McResult::UNSAT => (
                Span::raw("✔ ").green().bold(),
                Span::raw("UNSAT").green().bold(),
            ),
            McResult::SAT(d) => (
                Span::raw("✘ ").red().bold(),
                Span::raw(format!("SAT({d})")).red().bold(),
            ),
            McResult::Unknown(_) => (
                Span::raw("⚠ ").yellow().bold(),
                Span::raw("UNKNOWN").yellow().bold(),
            ),
        };

        let progress = self.progress.as_mut().unwrap();

        let _ = progress.terminal.draw(|f| {
            let area = f.area();
            let chunks = Layout::default()
                .direction(Direction::Vertical)
                .constraints([Constraint::Length(1), Constraint::Length(1)])
                .split(area);

            // Row 1: Finished Status
            let status_line = Line::from(vec![
                icon,
                Span::raw("rIC3").magenta().bold(),
                Span::raw("  ────  ").dark_gray(),
                Span::raw(format!("Level {}", level)).cyan().bold(),
                Span::raw("  ────  ").dark_gray(),
                Span::raw("⏱ ").white(),
                Span::raw(format_duration(time)).white().bold(),
                Span::raw("  ────  ").dark_gray(),
                label_span,
            ]);
            f.render_widget(Paragraph::new(status_line), chunks[0]);

            // Row 2: Frames
            f.render_widget(Paragraph::new(frame_line), chunks[1]);
        });

        // Restore terminal state: show cursor and print a newline so the shell prompt won't overwrite the final output
        let _ = progress.terminal.show_cursor();
        eprintln!();
    }
}

/// Build the frame line message, truncating from the left to fit `tw`.
///
/// When all frames fit:
///   `Frames [8]  12 45 23 67 34 89 12 45 ∞ 156`
///
/// When truncated:
///   `Frames [80]  …+62 34 89 12 45 23 67 ∞ 156`
fn format_frame_line(ic3: &IC3, tw: usize) -> Line<'static> {
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
    let mut spans = vec![
        Span::raw("  "),
        Span::raw("Frames").green().bold(),
        Span::raw(" "),
        Span::raw(format!("[{total}]")).green(),
        Span::raw("  "),
    ];

    if hidden > 0 {
        spans.push(Span::raw(format!("…+{} ", hidden)).dark_gray());
    }
    for i in start..num_frames {
        let count = ic3.frame[i].len();
        spans.push(Span::raw(format!("{} ", count)).white());
    }
    spans.push(Span::raw("∞ ").cyan().bold());
    spans.push(Span::raw(inf_count.to_string()).cyan().bold());

    Line::from(spans)
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
