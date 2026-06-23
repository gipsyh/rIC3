use crate::{
    McResult,
    tracer::{StateTracerIf, TracerIf},
};
use nix::sys::termios::{self, FlushArg, LocalFlags, SetArg, Termios};
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
use std::io::{self, IsTerminal, Write};
use std::os::fd::AsFd;
use std::sync::{
    Arc, Condvar, LazyLock, Mutex, Weak,
    atomic::{AtomicUsize, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

const UI_REFRESH_INTERVAL: Duration = Duration::from_millis(250);

pub struct UiRendererInner {
    terminal: Terminal<CrosstermBackend<std::io::Stderr>>,
    input_mode: TerminalInputGuard,
    cursor_hidden: bool,
    height: usize,
    spinner_tick: usize,
    last_update: Instant,
    start_time: Instant,
    name: String,
    level: usize,
    custom_lines: Vec<Line<'static>>,
    finished: bool,
    /// Set by `finish` and consumed by the render thread to draw the final frame.
    pending_finish: Option<McResult>,
}

impl UiRendererInner {
    fn terminal(height: usize) -> Option<Terminal<CrosstermBackend<std::io::Stderr>>> {
        let backend = CrosstermBackend::new(std::io::stderr());
        Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(height as u16),
            },
        )
        .ok()
    }

    fn resize_height_if_needed(&mut self, height: usize) {
        if height == self.height {
            return;
        }
        let old_area = self.terminal.get_frame().area();
        let _ = self.terminal.show_cursor();
        let _ = self.terminal.clear();
        let _ = self.terminal.set_cursor_position((old_area.x, old_area.y));
        restore_terminal_writers();
        if let Some(mut terminal) = Self::terminal(height) {
            self.cursor_hidden = terminal.hide_cursor().is_ok();
            self.terminal = terminal;
            self.height = height;
        }
    }

    fn cleanup_terminal(&mut self) {
        self.input_mode.discard_input();
        self.input_mode.restore();
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

        let custom_lines = self.custom_lines.clone();
        let custom_line_count = custom_lines.len();
        let cursor_line = custom_line_count + 1;
        let height = cursor_line + 1;
        self.resize_height_if_needed(height);
        self.input_mode.discard_input();

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
                .constraints(vec![Constraint::Length(1); height])
                .split(area);
            f.render_widget(
                Paragraph::new(status_line).wrap(Wrap { trim: true }),
                chunks[0],
            );
            for (idx, line) in custom_lines.into_iter().enumerate() {
                f.render_widget(Paragraph::new(line), chunks[idx + 1]);
            }
            if finish {
                let cursor_area = chunks[cursor_line];
                f.set_cursor_position((cursor_area.x, cursor_area.y));
            }
        });

        if finish {
            self.cleanup_terminal();
            let _ = writeln!(std::io::stderr());
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
        Span::raw("Time ").dark_gray(),
        Span::raw(time.clone()).white().bold(),
    ];
    let time_compact = vec![Span::raw(time).white().bold()];
    let memory_groups = memory_stats().map(memory_status_groups);

    let make_name_group = |name_width| {
        vec![
            icon_span.clone(),
            Span::raw(compact_name(name, name_width)).magenta().bold(),
        ]
    };

    if let Some((memory_full, memory_compact)) = memory_groups {
        if w >= 68 {
            let groups = fit_status_groups(
                w,
                vec![
                    make_name_group(name.chars().count()),
                    level_full.clone(),
                    time_full.clone(),
                    memory_full,
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
                    time_compact.clone(),
                    memory_compact,
                    vec![result_span.clone()],
                ],
                0,
            );
            if let Some(groups) = groups {
                return spaced_status_line(groups, w);
            }
        }
    }

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

#[derive(Clone, Copy)]
struct MemoryStats {
    rss_kib: u64,
}

fn memory_stats() -> Option<MemoryStats> {
    #[cfg(target_os = "linux")]
    {
        let status = std::fs::read_to_string("/proc/self/status").ok()?;
        let mut rss_kib = None;

        for line in status.lines() {
            if let Some(value) = line.strip_prefix("VmRSS:") {
                rss_kib = parse_status_kib(value);
            }
        }

        let rss_kib = rss_kib?;
        Some(MemoryStats { rss_kib })
    }

    #[cfg(not(target_os = "linux"))]
    {
        None
    }
}

fn parse_status_kib(value: &str) -> Option<u64> {
    value.split_whitespace().next()?.parse().ok()
}

fn memory_status_groups(stats: MemoryStats) -> (Vec<Span<'static>>, Vec<Span<'static>>) {
    let rss = format_kib(stats.rss_kib);
    (
        vec![
            Span::raw("Mem ").dark_gray(),
            Span::raw(rss.clone()).white().bold(),
        ],
        vec![Span::raw(format!("M {rss}")).white().bold()],
    )
}

fn format_kib(kib: u64) -> String {
    const KIB_PER_MIB: u64 = 1024;
    const KIB_PER_GIB: u64 = 1024 * 1024;

    if kib < KIB_PER_MIB {
        format!("{kib}KiB")
    } else if kib < KIB_PER_GIB {
        let mib = kib as f64 / KIB_PER_MIB as f64;
        if mib < 10.0 {
            format!("{mib:.1}MiB")
        } else {
            format!("{mib:.0}MiB")
        }
    } else {
        let gib = kib as f64 / KIB_PER_GIB as f64;
        if gib < 10.0 {
            format!("{gib:.2}GiB")
        } else {
            format!("{gib:.1}GiB")
        }
    }
}

#[derive(Default)]
pub struct TerminalInputGuard {
    active: bool,
}

impl TerminalInputGuard {
    pub fn new() -> Self {
        Self {
            active: acquire_input_guard(),
        }
    }

    pub fn discard_input(&self) {
        if self.active {
            discard_terminal_input();
        }
    }

    pub fn restore(&mut self) {
        if self.active {
            release_input_guard();
            self.active = false;
        }
    }
}

impl Drop for TerminalInputGuard {
    fn drop(&mut self) {
        self.restore();
    }
}

struct TerminalInputState {
    stdin: io::Stdin,
    original: Termios,
}

impl TerminalInputState {
    fn new() -> Option<Self> {
        let stdin = io::stdin();
        let original = termios::tcgetattr(stdin.as_fd()).ok()?;
        Some(Self { stdin, original })
    }

    fn apply_quiet_mode(&self) -> bool {
        let mut next = self.original.clone();
        next.local_flags
            .remove(LocalFlags::ECHO | LocalFlags::ICANON);
        termios::tcsetattr(self.stdin.as_fd(), SetArg::TCSANOW, &next).is_ok()
    }

    fn discard_input(&self) {
        let _ = termios::tcflush(self.stdin.as_fd(), FlushArg::TCIFLUSH);
    }

    fn restore(&self) {
        let _ = termios::tcsetattr(self.stdin.as_fd(), SetArg::TCSANOW, &self.original);
    }
}

static INPUT_GUARD_COUNT: AtomicUsize = AtomicUsize::new(0);

static TERMINAL_INPUT_STATE: LazyLock<Mutex<Option<TerminalInputState>>> = LazyLock::new(|| {
    let stdin = io::stdin();
    Mutex::new(stdin.is_terminal().then(TerminalInputState::new).flatten())
});

fn acquire_input_guard() -> bool {
    let Ok(state) = TERMINAL_INPUT_STATE.lock() else {
        return false;
    };
    let Some(state) = state.as_ref() else {
        return false;
    };
    if INPUT_GUARD_COUNT.fetch_add(1, Ordering::SeqCst) == 0 && !state.apply_quiet_mode() {
        INPUT_GUARD_COUNT.fetch_sub(1, Ordering::SeqCst);
        return false;
    }
    true
}

fn release_input_guard() {
    if INPUT_GUARD_COUNT.load(Ordering::SeqCst) == 0 {
        return;
    }
    if INPUT_GUARD_COUNT.fetch_sub(1, Ordering::SeqCst) == 1
        && let Ok(state) = TERMINAL_INPUT_STATE.lock()
        && let Some(state) = state.as_ref()
    {
        state.restore();
    }
}

fn discard_terminal_input() {
    if let Ok(state) = TERMINAL_INPUT_STATE.lock()
        && let Some(state) = state.as_ref()
    {
        state.discard_input();
    }
}

fn restore_terminal_input() {
    INPUT_GUARD_COUNT.store(0, Ordering::SeqCst);
    if let Ok(state) = TERMINAL_INPUT_STATE.lock()
        && let Some(state) = state.as_ref()
    {
        state.restore();
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
    /// Wakes the render thread early for a terminal transition (`finish`/`shutdown`).
    notify: Arc<Condvar>,
    handle: Arc<Mutex<Option<thread::JoinHandle<()>>>>,
}

impl UiRenderer {
    pub fn new(name: &str) -> Option<Self> {
        if !std::io::stderr().is_terminal() {
            return None;
        }

        let height = 2;
        let input_mode = TerminalInputGuard::new();
        let mut terminal = UiRendererInner::terminal(height)?;

        // Hide cursor initially so it doesn't flicker/show in the inline area
        let cursor_hidden = terminal.hide_cursor().is_ok();

        let inner = Arc::new(Mutex::new(UiRendererInner {
            terminal,
            input_mode,
            cursor_hidden,
            height,
            spinner_tick: 0,
            last_update: Instant::now(),
            start_time: Instant::now(),
            name: name.to_string(),
            level: 0,
            custom_lines: Vec::new(),
            finished: false,
            pending_finish: None,
        }));

        let notify = Arc::new(Condvar::new());
        let render_inner = Arc::downgrade(&inner);
        let render_notify = Arc::downgrade(&notify);
        let handle = thread::spawn(move || run_render_loop(render_inner, render_notify));

        Some(Self {
            inner,
            notify,
            handle: Arc::new(Mutex::new(Some(handle))),
        })
    }

    /// Push new lines to be rendered. Only updates shared state; the render
    /// thread picks them up on its next interval tick. No signal is sent —
    /// rendering is purely timer-driven.
    #[inline]
    pub fn render(&self, lines: Vec<Line<'static>>) {
        let mut inner = self.inner.lock().unwrap();
        if inner.finished {
            return;
        }
        inner.custom_lines = lines;
    }

    /// Tear down the terminal without a final draw and stop the render thread.
    pub fn shutdown(&self) {
        {
            let mut inner = self.inner.lock().unwrap();
            if inner.finished {
                return;
            }
            inner.finished = true;
        }
        self.notify.notify_one();
        self.join_render_thread();
    }

    /// Render the final frame for `result` and tear down the terminal. Blocks
    /// until the render thread has drawn the frame, so callers can safely emit
    /// further output afterwards.
    pub fn finish(&self, result: McResult) {
        self.finish_with(result);
    }

    fn finish_with(&self, result: McResult) {
        {
            let mut inner = self.inner.lock().unwrap();
            if inner.finished {
                return;
            }
            inner.pending_finish = Some(result);
        }
        self.notify.notify_one();
        self.join_render_thread();
    }

    fn join_render_thread(&self) {
        let handle = self.handle.lock().unwrap().take();
        if let Some(handle) = handle {
            let _ = handle.join();
        } else {
            // Another clone owns the join; wait for it to finish so the
            // terminal is restored before this caller returns.
            while !self.inner.lock().unwrap().finished {
                thread::sleep(Duration::from_millis(2));
            }
        }
    }
}

/// The render thread owns every `terminal.draw` call. It is purely
/// timer-driven: every `UI_REFRESH_INTERVAL` it redraws the current shared
/// state, so elapsed time, memory usage and the latest `custom_lines` update
/// regardless of engine activity. Engine methods only mutate shared state and
/// never wake the thread; only terminal transitions (`finish`/`shutdown`) wake
/// it early via the condvar.
///
/// The thread holds `Weak` references so it stops on its own once every
/// `UiRenderer` clone is dropped (e.g. without an explicit `finish`).
fn run_render_loop(inner: Weak<Mutex<UiRendererInner>>, notify: Weak<Condvar>) {
    loop {
        let Some(inner_arc) = inner.upgrade() else {
            break;
        };
        let Some(notify_arc) = notify.upgrade() else {
            break;
        };
        let mut inner = inner_arc.lock().unwrap();

        // Terminal transitions take priority over the periodic refresh.
        if let Some(result) = inner.pending_finish.take() {
            if !inner.finished {
                if let McResult::Unknown(Some(k)) = result {
                    inner.level = k;
                }
                inner.draw(true, result);
                inner.finished = true;
            }
            break;
        }
        if inner.finished {
            inner.cleanup_terminal();
            break;
        }

        // Periodic refresh: redraw current state so time/memory/custom lines
        // update every interval independent of engine activity.
        let level = inner.level;
        inner.draw(false, McResult::Unknown(Some(level)));

        // Wait for the next interval, or wake early for a terminal transition.
        // The lock is released while waiting, so the engine can update state.
        let (guard, _) = notify_arc.wait_timeout(inner, UI_REFRESH_INTERVAL).unwrap();
        drop(guard);
    }
}

impl TracerIf for UiRenderer {}

#[intertrait::cast_to]
impl StateTracerIf for UiRenderer {
    #[inline]
    fn trace_state(&mut self, _prop: Option<usize>, res: McResult) {
        match res {
            // Progress update: record the new level. The render thread draws it
            // on its next interval tick — no explicit wake is sent.
            McResult::Unknown(Some(k)) => {
                let mut inner = self.inner.lock().unwrap();
                if inner.finished {
                    return;
                }
                inner.level = k;
            }
            // Terminal result: draw the final frame on the render thread and
            // block until it is done.
            McResult::UNSAT | McResult::SAT(_) | McResult::Unknown(None) => {
                self.finish_with(res);
            }
        }
    }
}

fn format_duration(d: Duration) -> String {
    let secs = d.as_secs();
    if d.is_zero() {
        "0s".to_string()
    } else {
        format!("{}.{}s", secs, d.subsec_millis() / 100)
    }
}

fn restore_terminal_direct() {
    restore_terminal_input();
    restore_terminal_writers();
}

fn restore_terminal_writers() {
    restore_terminal_writer(std::io::stdout());
    restore_terminal_writer(std::io::stderr());
}

fn restore_terminal_writer(mut writer: impl Write) {
    let _ = writer.execute(cursor::Show);
    let _ = writer.execute(SetAttribute(ratatui::crossterm::style::Attribute::Reset));
    let _ = writer.execute(ResetColor);
    let _ = writer.flush();
}

pub fn restore_terminal() {
    restore_terminal_direct();
}
