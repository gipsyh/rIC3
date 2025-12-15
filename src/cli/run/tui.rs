use crate::cli::run::{McStatus, PropMcState, Run};
use btor::Btor;
use clap::Parser;
use rIC3::{McResult, config::EngineConfig, portfolio::Portfolio};
use ratatui::crossterm::{
    event::{self, Event, KeyCode, KeyEventKind},
    execute,
    terminal::{EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode, enable_raw_mode},
};
use ratatui::{
    prelude::*,
    widgets::{Block, Borders, Cell, Row, Table},
};
use std::{
    mem::take,
    thread::spawn,
    time::{Duration, Instant},
};

impl PropMcState {
    fn color(&self) -> Color {
        match self.prop.res {
            rIC3::McResult::Safe => Color::Green,
            rIC3::McResult::Unsafe(_) => Color::Red,
            rIC3::McResult::Unknown(_) => match self.state {
                McStatus::Solving => Color::Yellow,
                McStatus::Wait => Color::DarkGray,
                McStatus::Pause => Color::DarkGray,
            },
        }
    }

    fn as_str(&self) -> &str {
        match self.prop.res {
            rIC3::McResult::Safe => "Safe",
            rIC3::McResult::Unsafe(_) => "Unsafe",
            rIC3::McResult::Unknown(_) => self.state.as_ref(),
        }
    }

    fn cells(&'_ self) -> Vec<Cell<'_>> {
        let bound = match self.prop.res {
            rIC3::McResult::Unsafe(b) => format!("{b}"),
            rIC3::McResult::Unknown(Some(b)) => format!("{b}"),
            _ => "-".to_string(),
        };
        vec![
            Cell::from(self.prop.id.to_string()),
            Cell::from(self.prop.name.clone()),
            Cell::from(self.as_str()).fg(self.color()),
            Cell::from(bound),
            Cell::from("IC3"),
        ]
    }
}

impl Run {
    fn next(&mut self) {
        let i = match self.table.selected() {
            Some(i) => {
                if i >= self.mc.len() - 1 {
                    0
                } else {
                    i + 1
                }
            }
            None => 0,
        };
        self.table.select(Some(i));
    }

    fn previous(&mut self) {
        let i = match self.table.selected() {
            Some(i) => {
                if i == 0 {
                    self.mc.len() - 1
                } else {
                    i - 1
                }
            }
            None => 0,
        };
        self.table.select(Some(i));
    }

    pub fn stop_selected(&mut self) {
        if let Some(i) = self.table.selected()
            && self.mc[i].state == McStatus::Solving
        {
            self.mc[i].state = McStatus::Pause;
        }
    }

    pub fn run(&mut self) -> anyhow::Result<()> {
        enable_raw_mode()?;
        let mut stdout = std::io::stdout();
        execute!(stdout, EnterAlternateScreen)?;
        let backend = CrosstermBackend::new(stdout);
        let mut terminal = Terminal::new(backend)?;

        let tick_rate = Duration::from_millis(100);
        let mut last_tick = Instant::now();

        loop {
            terminal.draw(|f| self.ui(f))?;

            if self.solving.as_ref().is_some_and(|s| s.1.is_finished()) {
                let (id, join) = take(&mut self.solving).unwrap();
                let res = join.join().unwrap();
                self.mc[id].prop.res = match res {
                    Some(true) => McResult::Safe,
                    Some(false) => McResult::Unsafe(0),
                    None => McResult::Unknown(None),
                };
                self.mc[id].state = McStatus::Pause;
            }

            if self.solving.is_none() {
                self.launch_engine();
            }

            let timeout = tick_rate
                .checked_sub(last_tick.elapsed())
                .unwrap_or_else(|| Duration::from_secs(0));

            if ratatui::crossterm::event::poll(timeout)?
                && let Event::Key(key) = event::read()?
                && key.kind == KeyEventKind::Press
            {
                match key.code {
                    KeyCode::Char('q') => self.should_quit = true,
                    KeyCode::Down => self.next(),
                    KeyCode::Up => self.previous(),
                    KeyCode::Char('s') => self.stop_selected(),
                    _ => {}
                }
            }

            if last_tick.elapsed() >= tick_rate {
                last_tick = Instant::now();
            }

            if self.should_quit {
                disable_raw_mode()?;
                execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
                terminal.show_cursor()?;
                return Ok(());
            }
        }
    }

    fn launch_engine(&mut self) {
        let Some(id) = self.queue.pop_front() else {
            return;
        };
        self.mc[id].state = McStatus::Solving;
        let mut wts = self.wts.clone();
        wts.bad = vec![wts.bad[id].clone()];
        let btor_path = self.ric3_proj.path(format!("tmp/p{id}.btor"));
        let btor = Btor::from(&wts);
        btor.to_file(&btor_path);
        let engine_cfg = EngineConfig::parse_from(["", "-e", "portfolio"]);
        let cert_file = self.ric3_proj.path(format!("res/p{id}.cert"));
        let mut engine = Portfolio::new(btor_path, Some(cert_file), engine_cfg);
        let join = spawn(move || engine.check());
        self.solving = Some((id, join));
    }

    fn ui(&mut self, frame: &mut Frame) {
        let rects = Layout::default()
            .constraints([Constraint::Min(0), Constraint::Length(3)])
            .split(frame.area());

        self.render_table(frame, rects[0]);
        self.render_footer(frame, rects[1]);
    }

    fn render_table(&mut self, frame: &mut Frame, area: Rect) {
        let header_style = Style::default()
            .fg(Color::Yellow)
            .add_modifier(Modifier::BOLD);
        let selected_style = Style::default();

        let header = ["ID", "Property", "Status", "Bound", "Engine"]
            .into_iter()
            .map(Cell::from)
            .collect::<Row>()
            .style(header_style)
            .height(1);

        let rows = self.mc.iter().map(|item| Row::new(item.cells()).height(1));

        let t = Table::new(
            rows,
            [
                Constraint::Length(4),  // ID
                Constraint::Min(25),    // Property Name
                Constraint::Length(12), // Status
                Constraint::Length(8),  // Bound
                Constraint::Length(10), // Engine
            ],
        )
        .header(header)
        .block(Block::default().borders(Borders::ALL).title(" rIC3 "))
        .row_highlight_style(selected_style)
        .highlight_symbol(">> ");

        frame.render_stateful_widget(t, area, &mut self.table);
    }

    fn render_footer(&mut self, frame: &mut Frame, area: Rect) {
        let info_style = Style::default().fg(Color::White);
        let keys_style = Style::default()
            .fg(Color::Cyan)
            .add_modifier(Modifier::BOLD);

        let text = Line::from(vec![
            Span::styled(" [↑/↓] ", keys_style),
            Span::styled("Select Row ", info_style),
            Span::styled(" [s] ", keys_style),
            Span::styled("Stop Solving ", info_style),
            Span::styled(" [q] ", keys_style),
            Span::styled("Quit", info_style),
        ]);

        let block = Block::default()
            .borders(Borders::ALL)
            .style(Style::default());

        let paragraph = ratatui::widgets::Paragraph::new(text)
            .block(block)
            .alignment(Alignment::Center);

        frame.render_widget(paragraph, area);
    }
}
