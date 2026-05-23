use crate::{
    McResult,
    tracer::{StateTracerIf, TracerIf},
};
use ratatui::{
    Terminal, TerminalOptions, Viewport,
    backend::CrosstermBackend,
    crossterm::{
        ExecutableCommand, cursor,
        style::{ResetColor, SetAttribute},
    },
    layout::{Constraint, Direction, Layout},
    style::{Color, Style, Stylize},
    text::{Line, Span},
    widgets::{Paragraph, Wrap},
};
use std::io::{IsTerminal, Write};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

pub struct UiRendererInner {
    terminal: Terminal<CrosstermBackend<std::io::Stderr>>,
    cursor_hidden: bool,
    spinner_tick: usize,
    last_update: Instant,
    start_time: Instant,
    name: String,
    level: usize,
    custom_line: Option<Line<'static>>,
    finished: bool,
}

impl UiRendererInner {
    fn cleanup_terminal(&mut self) {
        if self.cursor_hidden {
            let _ = self.terminal.show_cursor();
            self.cursor_hidden = false;
        }
        restore_terminal_direct();
    }

    fn draw(&mut self, finish: bool, result: McResult) {
        let level = self.level;
        let elapsed = self.start_time.elapsed();
        let running_icon = if finish {
            None
        } else {
            let now = Instant::now();
            if now.duration_since(self.last_update) >= Duration::from_millis(80) {
                self.spinner_tick = self.spinner_tick.wrapping_add(1);
                self.last_update = now;
            }
            let spinners = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"];
            Some(spinners[self.spinner_tick % spinners.len()])
        };

        let frame_line = self.custom_line.clone();

        let _ = self.terminal.draw(|f| {
            let area = f.area();
            let status_line = format_status_line(
                &self.name,
                level,
                elapsed,
                finish,
                result,
                running_icon,
                area.width,
            );
            let chunks = Layout::default()
                .direction(Direction::Vertical)
                .constraints([Constraint::Length(1); 3])
                .split(area);
            f.render_widget(
                Paragraph::new(status_line).wrap(Wrap { trim: true }),
                chunks[0],
            );
            let mut output_idx = 1;
            if let Some(frame_line) = frame_line {
                output_idx += 1;
                f.render_widget(Paragraph::new(frame_line), chunks[1]);
            }
            f.render_widget(Paragraph::new(""), chunks[output_idx]);
            if finish {
                f.set_cursor_position((chunks[output_idx].x, chunks[output_idx].y));
            }
        });

        if finish {
            self.cleanup_terminal();
        }
    }
}

fn format_status_line(
    name: &str,
    level: usize,
    elapsed: Duration,
    finish: bool,
    result: McResult,
    running_icon: Option<&'static str>,
    width: u16,
) -> Line<'static> {
    let result_label = match result {
        McResult::UNSAT => "UNSAT".to_string(),
        McResult::SAT(d) => format!("SAT({d})"),
        McResult::Unknown(_) => "UNKNOWN".to_string(),
    };
    let result_color = match result {
        McResult::UNSAT => Color::Green,
        McResult::SAT(_) => Color::Red,
        McResult::Unknown(_) => Color::Yellow,
    };
    let result_style = Style::default().fg(result_color).bold();
    let icon = if finish {
        match result {
            McResult::UNSAT => "✔",
            McResult::SAT(_) => "✘",
            McResult::Unknown(_) => "⚠",
        }
    } else {
        running_icon.unwrap_or("•")
    };
    let time = format_duration(elapsed);

    let w = usize::from(width);
    let icon_span = Span::raw(format!("{icon} ")).style(status_icon_style(finish, result_color));
    let result_span = Span::raw(result_label).style(result_style);
    let level_full = vec![
        Span::raw("Level ").dark_gray(),
        Span::raw(level.to_string()).cyan().bold(),
    ];
    let level_compact = vec![Span::raw(format!("L{level}")).cyan().bold()];
    let time_full = vec![
        Span::raw("time ").dark_gray(),
        Span::raw(time.clone()).white().bold(),
    ];
    let time_compact = vec![Span::raw(time).white().bold()];

    let make_name_group = |name_width| {
        vec![
            icon_span.clone(),
            Span::raw(compact_name(name, name_width)).magenta().bold(),
        ]
    };

    if w >= 68 {
        let groups = fit_status_groups(
            w,
            vec![
                make_name_group(name.chars().count()),
                level_full.clone(),
                time_full,
                vec![result_span.clone()],
            ],
            0,
        );
        if let Some(groups) = groups {
            return spaced_status_line(groups, w);
        }
    }

    if w >= 42 {
        let groups = fit_status_groups(
            w,
            vec![
                make_name_group(name.chars().count()),
                level_compact.clone(),
                time_compact,
                vec![result_span.clone()],
            ],
            0,
        );
        if let Some(groups) = groups {
            return spaced_status_line(groups, w);
        }
    }

    let fixed_width = icon_span.width() + level_compact.iter().map(Span::width).sum::<usize>();
    let result_width = result_span.width();
    let min_gap_width = 2;
    let name_width = w.saturating_sub(fixed_width + result_width + min_gap_width);
    let groups = vec![
        make_name_group(name_width),
        level_compact,
        vec![result_span.clone()],
    ];
    if status_groups_width(&groups) + 2 > w && result_width <= w {
        return spaced_status_line(vec![vec![result_span]], w);
    }
    spaced_status_line(groups, w)
}

fn fit_status_groups(
    width: usize,
    mut groups: Vec<Vec<Span<'static>>>,
    name_group_idx: usize,
) -> Option<Vec<Vec<Span<'static>>>> {
    if groups.is_empty() {
        return Some(groups);
    }

    let gaps = groups.len().saturating_sub(1);
    let content_width = status_groups_width(&groups);
    if content_width + gaps <= width {
        return Some(groups);
    }

    let overflow = content_width + gaps - width;
    let name_span = groups.get_mut(name_group_idx)?.get_mut(1)?;
    let name_width = name_span.width();
    if overflow >= name_width {
        return None;
    }
    let next_name_width = name_width - overflow;
    let style = name_span.style;
    name_span.content = compact_name(&name_span.content, next_name_width).into();
    name_span.style = style;

    Some(groups)
}

fn spaced_status_line(mut groups: Vec<Vec<Span<'static>>>, width: usize) -> Line<'static> {
    if groups.is_empty() {
        return Line::default();
    }

    let content_width = status_groups_width(&groups);
    let gaps = groups.len().saturating_sub(1);
    if gaps == 0 {
        let mut spans = Vec::new();
        if content_width < width {
            spans.push(Span::raw(" ".repeat(width - content_width)).dark_gray());
        }
        spans.extend(groups.remove(0));
        return Line::from(spans);
    }

    let gap_widths = if content_width + gaps <= width && gaps > 0 {
        distribute_spaces(width - content_width, gaps)
    } else {
        vec![1; gaps]
    };

    let mut spans = Vec::new();
    for (idx, group) in groups.drain(..).enumerate() {
        spans.extend(group);
        if let Some(gap_width) = gap_widths.get(idx) {
            spans.push(Span::raw(" ".repeat(*gap_width)).dark_gray());
        }
    }

    Line::from(spans)
}

fn status_groups_width(groups: &[Vec<Span<'static>>]) -> usize {
    groups.iter().flatten().map(Span::width).sum()
}

fn distribute_spaces(total: usize, gaps: usize) -> Vec<usize> {
    let base = total / gaps;
    let extra = total % gaps;
    (0..gaps)
        .map(|idx| base + usize::from(idx < extra))
        .collect()
}

fn status_icon_style(finish: bool, result_color: Color) -> Style {
    if finish {
        Style::default().fg(result_color).bold()
    } else {
        Style::default().fg(Color::Cyan).bold()
    }
}

fn compact_name(name: &str, max_chars: usize) -> String {
    if max_chars == 0 {
        return String::new();
    }
    let len = name.chars().count();
    if len <= max_chars {
        name.to_string()
    } else if max_chars <= 1 {
        "…".to_string()
    } else {
        let keep = max_chars - 1;
        format!("{}…", name.chars().take(keep).collect::<String>())
    }
}

impl Drop for UiRendererInner {
    fn drop(&mut self) {
        self.cleanup_terminal();
    }
}

#[derive(Clone)]
pub struct UiRenderer {
    inner: Arc<Mutex<UiRendererInner>>,
}

impl UiRenderer {
    pub fn new(name: &str) -> Option<Self> {
        if !std::io::stderr().is_terminal() {
            return None;
        }

        let backend = CrosstermBackend::new(std::io::stderr());
        let mut terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(3),
            },
        )
        .ok()?;

        // Hide cursor initially so it doesn't flicker/show in the inline area
        let cursor_hidden = terminal.hide_cursor().is_ok();

        let renderer = Self {
            inner: Arc::new(Mutex::new(UiRendererInner {
                terminal,
                cursor_hidden,
                spinner_tick: 0,
                last_update: Instant::now(),
                start_time: Instant::now(),
                name: name.to_string(),
                level: 0,
                custom_line: None,
                finished: false,
            })),
        };

        Some(renderer)
    }

    #[inline]
    pub fn render(&self, line: Line<'static>) {
        let mut inner = self.inner.lock().unwrap();
        if inner.finished {
            return;
        }
        inner.custom_line = Some(line);
        let level = inner.level;
        inner.draw(false, McResult::Unknown(Some(level)));
    }

    pub fn shutdown(&self) {
        match self.inner.lock() {
            Ok(mut inner) => {
                inner.finished = true;
                inner.cleanup_terminal();
            }
            Err(_) => restore_terminal_direct(),
        }
    }

    pub fn finish(&self, result: McResult) {
        match self.inner.lock() {
            Ok(mut inner) => {
                if inner.finished {
                    return;
                }
                if let McResult::Unknown(Some(k)) = result {
                    inner.level = k;
                }
                inner.draw(true, result);
                inner.finished = true;
            }
            Err(_) => restore_terminal_direct(),
        }
    }
}

impl TracerIf for UiRenderer {}

#[intertrait::cast_to]
impl StateTracerIf for UiRenderer {
    #[inline]
    fn trace_state(&mut self, _prop: Option<usize>, res: McResult) {
        let mut inner = self.inner.lock().unwrap();
        if inner.finished {
            return;
        }
        match res {
            McResult::Unknown(Some(k)) => {
                inner.level = k;
                inner.draw(false, res);
            }
            McResult::UNSAT | McResult::SAT(_) | McResult::Unknown(None) => {
                inner.draw(true, res);
                inner.finished = true;
            }
        }
    }
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

fn restore_terminal_direct() {
    let mut stderr = std::io::stderr();
    let _ = stderr.execute(cursor::Show);
    let _ = stderr.execute(SetAttribute(ratatui::crossterm::style::Attribute::Reset));
    let _ = stderr.execute(ResetColor);
    let _ = stderr.flush();
}

pub fn restore_terminal() {
    restore_terminal_direct();
}
