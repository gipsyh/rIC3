use super::Ctilg;
use ratatui::{
    TerminalOptions, Viewport,
    crossterm::{
        event::{self, Event, KeyCode, KeyEventKind},
        terminal::{disable_raw_mode, enable_raw_mode},
    },
    prelude::*,
    widgets::{Block, Borders, Cell, Row, Table, TableState},
};
use std::time::{Duration, Instant};

impl Ctilg {
    pub fn tui_run(&mut self) -> anyhow::Result<Option<usize>> {
        enable_raw_mode()?;
        let stdout = std::io::stdout();
        let backend = CrosstermBackend::new(stdout);
        let height = (self.res.len() + 4) as u16;
        let mut terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(height),
            },
        )?;

        let mut table_state = TableState::default();
        table_state.select(Some(0));

        let tick_rate = Duration::from_millis(100);
        let mut last_tick = Instant::now();
        let mut selected = None;
        let mut warning_msg = None;

        loop {
            terminal.draw(|f| self.ui(f, &mut table_state, &warning_msg))?;

            let timeout = tick_rate
                .checked_sub(last_tick.elapsed())
                .unwrap_or_else(|| Duration::from_secs(0));

            if event::poll(timeout)? {
                if let Event::Key(key) = event::read()? {
                    if key.kind == KeyEventKind::Press {
                        match key.code {
                            KeyCode::Char('q') | KeyCode::Esc => break,
                            KeyCode::Down => {
                                warning_msg = None;
                                let i = match table_state.selected() {
                                    Some(i) => {
                                        if i >= self.res.len() - 1 {
                                            0
                                        } else {
                                            i + 1
                                        }
                                    }
                                    None => 0,
                                };
                                table_state.select(Some(i));
                            }
                            KeyCode::Up => {
                                warning_msg = None;
                                let i = match table_state.selected() {
                                    Some(i) => {
                                        if i == 0 {
                                            self.res.len() - 1
                                        } else {
                                            i - 1
                                        }
                                    }
                                    None => 0,
                                };
                                table_state.select(Some(i));
                            }
                            KeyCode::Enter => {
                                if let Some(i) = table_state.selected() {
                                    if self.res[i] {
                                        warning_msg =
                                            Some("Cannot select inductive property!".to_string());
                                    } else {
                                        selected = Some(i);
                                        break;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }

            if last_tick.elapsed() >= tick_rate {
                last_tick = Instant::now();
            }
        }

        disable_raw_mode()?;
        Ok(selected)
    }

    fn ui(&self, frame: &mut Frame, state: &mut TableState, warning: &Option<String>) {
        let area = frame.area();

        let header_style = Style::default()
            .fg(Color::Yellow)
            .add_modifier(Modifier::BOLD);

        let header = ["ID", "Property", "Result"]
            .into_iter()
            .map(Cell::from)
            .collect::<Row>()
            .style(header_style)
            .height(1);

        let rows = self.res.iter().enumerate().map(|(i, &res)| {
            let name = if let Some(term) = self.uts.ts.bad.get(i) {
                self.symbol
                    .get(term)
                    .map(|s| s.as_str())
                    .unwrap_or("Unknown")
            } else {
                "Unknown"
            };

            let status = if res { "Inductive" } else { "Not Inductive" };
            let color = if res { Color::Green } else { Color::Red };

            Row::new(vec![
                Cell::from(i.to_string()),
                Cell::from(name),
                Cell::from(status).fg(color),
            ])
        });

        let title = if let Some(msg) = warning {
            format!(" Error: {} ", msg)
        } else {
            " Inductive Check Results ".to_string()
        };

        let border_style = if warning.is_some() {
            Style::default().fg(Color::Red)
        } else {
            Style::default()
        };

        let t = Table::new(
            rows,
            [
                Constraint::Length(4),
                Constraint::Min(20),
                Constraint::Length(15),
            ],
        )
        .header(header)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title(title)
                .border_style(border_style),
        )
        .highlight_symbol("> ");

        frame.render_stateful_widget(t, area, state);
    }
}
