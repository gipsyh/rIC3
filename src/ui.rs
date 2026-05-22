use crate::{
    McResult,
    tracer::{StateTracerIf, TracerIf},
};
use ratatui::{
    Terminal, TerminalOptions, Viewport,
    backend::CrosstermBackend,
    crossterm::{
        ExecutableCommand, cursor,
        event::{self, Event, KeyCode, KeyModifiers},
        terminal::{disable_raw_mode, enable_raw_mode},
    },
    layout::{Constraint, Direction, Layout},
    style::Stylize,
    text::{Line, Span},
    widgets::Paragraph,
};
use std::io::{IsTerminal, Write};
use std::sync::{
    Arc, Mutex, Weak,
    atomic::{AtomicBool, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

pub struct UiRendererInner {
    terminal: Terminal<CrosstermBackend<std::io::Stderr>>,
    raw_mode: bool,
    cursor_hidden: bool,
    interrupt_watcher: Arc<AtomicBool>,
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
        self.interrupt_watcher.store(false, Ordering::Relaxed);
        if self.cursor_hidden {
            let _ = self.terminal.show_cursor();
            self.cursor_hidden = false;
        }
        if self.raw_mode {
            let _ = disable_raw_mode();
            self.raw_mode = false;
        }
    }

    fn draw(&mut self, finish: bool, result: McResult) {
        let level = self.level;
        let elapsed = self.start_time.elapsed();

        let (icon, name_span, suffix) = if finish {
            let (icon, label_span) = match result {
                McResult::UNSAT => (
                    Span::raw("✔ ").green().bold(),
                    Span::raw("UNSAT").green().bold(),
                ),
                McResult::SAT(d) => (
                    Span::raw("✘ ").red().bold(),
                    Span::raw(format!("SAT({d})")).red().bold(),
                ),
                _ => (
                    Span::raw("⚠ ").yellow().bold(),
                    Span::raw("UNKNOWN").yellow().bold(),
                ),
            };
            (
                icon,
                Span::raw(&self.name).magenta().bold(),
                Some(label_span),
            )
        } else {
            let now = Instant::now();
            if now.duration_since(self.last_update) >= Duration::from_millis(80) {
                self.spinner_tick = self.spinner_tick.wrapping_add(1);
                self.last_update = now;
            }
            let spinners = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"];
            let spinner = spinners[self.spinner_tick % spinners.len()];
            (
                Span::raw(format!("{} ", spinner)).cyan().bold(),
                Span::raw(&self.name).magenta().bold(),
                None,
            )
        };

        let mut status_spans = vec![
            icon,
            name_span,
            Span::raw("  ────  ").dark_gray(),
            Span::raw(format!("Level {}", level)).cyan().bold(),
            Span::raw("  ────  ").dark_gray(),
            Span::raw("⏱ ").white(),
            Span::raw(format_duration(elapsed)).white().bold(),
        ];
        if let Some(suf) = suffix {
            status_spans.push(Span::raw("  ────  ").dark_gray());
            status_spans.push(suf);
        }
        let status_line = Line::from(status_spans);

        let frame_line = self
            .custom_line
            .clone()
            .unwrap_or_else(|| Line::from(vec![]));

        let _ = self.terminal.draw(|f| {
            let area = f.area();
            let chunks = Layout::default()
                .direction(Direction::Vertical)
                .constraints([Constraint::Length(1), Constraint::Length(1)])
                .split(area);

            f.render_widget(Paragraph::new(status_line), chunks[0]);
            f.render_widget(Paragraph::new(frame_line), chunks[1]);
        });

        if finish {
            self.cleanup_terminal();
            eprintln!();
        }
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

        let raw_mode = std::io::stdin().is_terminal() && enable_raw_mode().is_ok();
        let backend = CrosstermBackend::new(std::io::stderr());
        let mut terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(2),
            },
        )
        .ok()?;

        // Hide cursor initially so it doesn't flicker/show in the inline area
        let cursor_hidden = terminal.hide_cursor().is_ok();

        let interrupt_watcher = Arc::new(AtomicBool::new(raw_mode));
        let renderer = Self {
            inner: Arc::new(Mutex::new(UiRendererInner {
                terminal,
                raw_mode,
                cursor_hidden,
                interrupt_watcher: interrupt_watcher.clone(),
                spinner_tick: 0,
                last_update: Instant::now(),
                start_time: Instant::now(),
                name: name.to_string(),
                level: 0,
                custom_line: None,
                finished: false,
            })),
        };

        if raw_mode {
            spawn_interrupt_watcher(interrupt_watcher, Arc::downgrade(&renderer.inner));
        }

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

fn spawn_interrupt_watcher(active: Arc<AtomicBool>, inner: Weak<Mutex<UiRendererInner>>) {
    thread::spawn(move || {
        while active.load(Ordering::Relaxed) {
            match event::poll(Duration::from_millis(100)) {
                Ok(true) => match event::read() {
                    Ok(Event::Key(key))
                        if key.modifiers.contains(KeyModifiers::CONTROL)
                            && matches!(key.code, KeyCode::Char('c') | KeyCode::Char('C')) =>
                    {
                        if let Some(inner) = inner.upgrade() {
                            match inner.lock() {
                                Ok(mut inner) => {
                                    inner.cleanup_terminal();
                                    eprintln!();
                                }
                                Err(_) => restore_terminal_direct(),
                            }
                        } else {
                            restore_terminal_direct();
                        }
                        std::process::exit(130);
                    }
                    Ok(_) => {}
                    Err(_) => break,
                },
                Ok(false) => {}
                Err(_) => break,
            }
        }
    });
}

fn restore_terminal_direct() {
    let mut stderr = std::io::stderr();
    let _ = stderr.execute(cursor::Show);
    let _ = stderr.flush();
    let _ = disable_raw_mode();
}
