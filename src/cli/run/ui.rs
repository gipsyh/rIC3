use crate::cli::run::{McStatus, PropMcState, Run};
use rIC3::McResult;
use ratatui::{
    Frame, Terminal, TerminalOptions, Viewport,
    backend::CrosstermBackend,
    crossterm::{style::Stylize, terminal},
    layout::Constraint,
    style::{Color, Style},
    widgets::{Cell, Row, Table},
};
use std::{
    io::{self, IsTerminal},
    os::fd::AsFd,
    thread::sleep,
    time::Duration,
};

#[cfg(unix)]
use nix::sys::termios::{self, FlushArg, LocalFlags, SetArg, Termios};

const ID_WIDTH: usize = 6;
const STATE_WIDTH: usize = 10;
const BOUND_WIDTH: usize = 10;
const TIME_WIDTH: usize = 10;
const COLUMN_GAPS: usize = 4;
const MIN_PROPERTY_WIDTH: usize = 1;
const DEFAULT_PLAIN_WIDTH: usize = 80;

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
    pub(crate) fn run_tui(&mut self) -> anyhow::Result<()> {
        let height = self.mc.len() + 1;
        let mut terminal = RunTerminal::new(height)?;

        let mut tick = 0;

        loop {
            if self.nexus_task.is_none() {
                self.launch_nexus();
            }

            let _updates = self.process_updates()?;

            terminal.discard_input();
            terminal.draw(&self.mc, tick)?;

            if self.all_done() || self.is_idle() {
                break;
            }

            sleep(Duration::from_millis(100));
            tick += 1;
        }

        terminal.discard_input();
        terminal.draw(&self.mc, tick)?;
        println!();
        Ok(())
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

type RunBackend = CrosstermBackend<io::Stdout>;

struct RunTerminal {
    terminal: Terminal<RunBackend>,
    input_mode: InputModeGuard,
}

impl RunTerminal {
    fn new(height: usize) -> anyhow::Result<Self> {
        let input_mode = InputModeGuard::new()?;
        let backend = CrosstermBackend::new(io::stdout());
        let mut terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(height as u16),
            },
        )?;
        terminal.hide_cursor()?;
        Ok(Self {
            terminal,
            input_mode,
        })
    }

    fn draw(&mut self, props: &[PropMcState], tick: usize) -> anyhow::Result<()> {
        self.terminal.draw(|f| draw_run_table(f, props, tick))?;
        Ok(())
    }

    fn discard_input(&self) {
        self.input_mode.discard_input();
    }
}

impl Drop for RunTerminal {
    fn drop(&mut self) {
        let _ = self.terminal.show_cursor();
    }
}

#[cfg(unix)]
struct InputModeGuard {
    stdin: io::Stdin,
    original: Option<Termios>,
}

#[cfg(unix)]
impl InputModeGuard {
    fn new() -> anyhow::Result<Self> {
        let stdin = io::stdin();
        if !stdin.is_terminal() {
            return Ok(Self {
                stdin,
                original: None,
            });
        }

        let original = termios::tcgetattr(stdin.as_fd())?;
        let mut next = original.clone();
        next.local_flags
            .remove(LocalFlags::ECHO | LocalFlags::ICANON);
        termios::tcsetattr(stdin.as_fd(), SetArg::TCSANOW, &next)?;

        Ok(Self {
            stdin,
            original: Some(original),
        })
    }

    fn discard_input(&self) {
        if self.original.is_some() {
            let _ = termios::tcflush(self.stdin.as_fd(), FlushArg::TCIFLUSH);
        }
    }
}

#[cfg(unix)]
impl Drop for InputModeGuard {
    fn drop(&mut self) {
        if let Some(original) = &self.original {
            let _ = termios::tcsetattr(self.stdin.as_fd(), SetArg::TCSANOW, original);
        }
    }
}

#[cfg(not(unix))]
struct InputModeGuard;

#[cfg(not(unix))]
impl InputModeGuard {
    fn new() -> anyhow::Result<Self> {
        Ok(Self)
    }

    fn discard_input(&self) {}
}

fn draw_run_table(f: &mut Frame<'_>, props: &[PropMcState], tick: usize) {
    let size = f.area();
    let term_width = size.width as usize;
    let prop_width = term_width.saturating_sub(42).max(1);

    let header = Row::new(vec![
        Cell::from(""),
        Cell::from("ID"),
        Cell::from(truncate("Property", prop_width)),
        Cell::from("State"),
        Cell::from("Bound"),
        Cell::from("Time"),
    ])
    .style(Style::default().bold());

    let rows = props
        .iter()
        .map(|prop| run_table_row(prop, prop_width, tick));
    let widths = [
        Constraint::Length(1),
        Constraint::Length(6),
        Constraint::Min(1),
        Constraint::Length(10),
        Constraint::Length(10),
        Constraint::Length(10),
    ];
    let table = Table::new(rows, widths).header(header).column_spacing(1);

    f.render_widget(table, size);
}

fn run_table_row(prop: &PropMcState, prop_width: usize, tick: usize) -> Row<'static> {
    let total_time = prop.time + prop.start_time.map_or(Duration::ZERO, |t| t.elapsed());
    Row::new(vec![
        progress_cell(prop, tick),
        Cell::from(format!("p{}", prop.prop.id)).style(Style::default().fg(Color::Magenta).bold()),
        Cell::from(truncate(&prop.prop.name, prop_width)).style(Style::default().fg(Color::White)),
        state_cell(prop),
        bound_cell(prop),
        Cell::from(format_time(total_time)),
    ])
}

fn progress_cell(prop: &PropMcState, tick: usize) -> Cell<'static> {
    match prop.prop.res {
        McResult::UNSAT => Cell::from("✔").style(Style::default().fg(Color::Green).bold()),
        McResult::SAT(_) => Cell::from("✘").style(Style::default().fg(Color::Red).bold()),
        McResult::Unknown(_) if prop.state == McStatus::Pause => {
            Cell::from("⏹").style(Style::default().fg(Color::Yellow).bold())
        }
        McResult::Unknown(_) => {
            const SPINNERS: [&str; 10] = ["⠋", "⠙", "⠹", "⠸", "⠼", "⠴", "⠦", "⠧", "⠇", "⠏"];
            Cell::from(SPINNERS[tick % SPINNERS.len()])
                .style(Style::default().fg(Color::Cyan).bold())
        }
    }
}

fn state_cell(prop: &PropMcState) -> Cell<'static> {
    match prop.prop.res {
        McResult::UNSAT => Cell::from("Proved").style(Style::default().fg(Color::Green).bold()),
        McResult::SAT(_) => Cell::from("Violated").style(Style::default().fg(Color::Red).bold()),
        McResult::Unknown(_) => match prop.state {
            McStatus::Solving => Cell::from("Solving").style(Style::default().fg(Color::Yellow)),
            McStatus::Wait => Cell::from("Waiting").style(Style::default().fg(Color::DarkGray)),
            McStatus::Pause => Cell::from("Paused").style(Style::default().fg(Color::DarkGray)),
        },
    }
}

fn bound_cell(prop: &PropMcState) -> Cell<'static> {
    match prop.prop.res {
        McResult::UNSAT => Cell::from("-"),
        McResult::SAT(b) => Cell::from(b.to_string()),
        McResult::Unknown(Some(b)) => match prop.state {
            McStatus::Solving => {
                Cell::from(b.to_string()).style(Style::default().fg(Color::Cyan).bold())
            }
            McStatus::Wait | McStatus::Pause => {
                Cell::from(b.to_string()).style(Style::default().fg(Color::Blue))
            }
        },
        McResult::Unknown(None) => Cell::from("-"),
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
