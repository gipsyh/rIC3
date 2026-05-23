use super::IC3;
use crate::McResult;
use ratatui::crossterm::terminal;
use ratatui::{
    style::Stylize,
    text::{Line, Span},
};

/// Template prefix width for the frame bar ("  ").
const FRAME_PREFIX_WIDTH: usize = 2;

fn term_width() -> usize {
    terminal::size().map(|(w, _)| usize::from(w)).unwrap_or(80)
}

impl IC3 {
    #[inline]
    pub(super) fn format_frame_line(&self) -> Line<'static> {
        let tw = term_width();
        format_frame_line(self, tw)
    }

    #[inline]
    pub(super) fn render_progress(&mut self) {
        if let Some(ref renderer) = self.renderer {
            renderer.render(vec![self.format_frame_line(); 2]);
        }
    }

    #[inline]
    pub(super) fn finish_progress(&mut self, result: McResult) {
        self.tracer.trace_state(None, result);
        if result.is_unknown()
            && let Some(renderer) = &self.renderer
        {
            renderer.finish(result);
        }
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
