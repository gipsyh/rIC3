use crate::cli::run::{McStatus, NexusTask, PropMcState, Run};
use rIC3::{
    Engine, McResult, MpEngine, MpMcResult,
    frontend::{Frontend, btor::BtorFrontend},
    polynexus::{PolyNexus, PolyNexusConfig},
    tracer::channel_tracer,
};
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
    thread::spawn,
    time::{Duration, Instant},
};

impl PropMcState {
    fn color(&self) -> Color {
        match self.prop.res {
            McResult::Safe => Color::Green,
            McResult::Unsafe(_) => Color::Red,
            McResult::Unknown(_) => match self.state {
                McStatus::Solving => Color::Yellow,
                McStatus::Wait => Color::DarkGray,
                McStatus::Pause => Color::DarkGray,
            },
        }
    }

    fn as_str(&self) -> &str {
        match self.prop.res {
            McResult::Safe => "Safe",
            McResult::Unsafe(_) => "Unsafe",
            McResult::Unknown(_) => self.state.as_ref(),
        }
    }

    fn cells(&'_ self) -> Vec<Cell<'_>> {
        let bound = match self.prop.res {
            McResult::Unsafe(b) => format!("{b}"),
            McResult::Unknown(Some(b)) => format!("{b}"),
            _ => "-".to_string(),
        };
        vec![
            Cell::from(self.prop.id.to_string()),
            Cell::from(self.prop.name.clone()),
            Cell::from(self.as_str()).fg(self.color()),
            Cell::from(bound),
            Cell::from(self.prop.config.as_ref().map(|c| c.as_ref()).unwrap_or("-")),
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

    pub fn stop_solving(&mut self) {
        if let Some(task) = self.nexus_task.take() {
            task.ctrl.terminate();
            let _ = task.join.join();
        }
        // Mark all solving as paused
        for m in self.mc.iter_mut() {
            if m.state == McStatus::Solving {
                m.state = McStatus::Pause;
            }
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

            if self.nexus_task.is_none() {
                self.launch_nexus();
            }

            self.process_updates();

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
                    KeyCode::Char('s') => self.stop_solving(),
                    _ => {}
                }
            }

            if last_tick.elapsed() >= tick_rate {
                last_tick = Instant::now();
            }

            if self.should_quit {
                self.stop_solving();
                disable_raw_mode()?;
                execute!(terminal.backend_mut(), LeaveAlternateScreen)?;
                terminal.show_cursor()?;
                return Ok(());
            }
        }
    }

    fn process_updates(&mut self) {
        if let Some(task) = &self.nexus_task {
            // Process real-time updates from PolyNexus
            while let Ok((prop_id, result)) = task.state_tracer.try_recv() {
                let prop_id = prop_id.unwrap();
                let prop = &mut self.mc[prop_id];
                prop.prop.res = result;
                if let McResult::Unsafe(_) = result {
                    // let witness =
                    // Yosys::btor_wit_to_vcd(
                    //     self.ric3_proj.path("dut"),
                    //     cert_path,
                    //     self.ric3_proj.path(format!("res/p{prop_id}.vcd")),
                    //     true,
                    //     None,
                    // )
                    // .unwrap();
                }
            }
        }
    }

    fn launch_nexus(&mut self) {
        // Get pending property IDs
        let pending: Vec<usize> = self
            .mc
            .iter()
            .filter(|m| matches!(m.prop.res, McResult::Unknown(_)) && m.state == McStatus::Wait)
            .map(|m| m.prop.id)
            .collect();

        if pending.is_empty() {
            return;
        }

        // Create PolyNexus engine
        let mut btorfe = BtorFrontend::new(self.btor.clone());
        let (ts, _) = btorfe.ts();

        let cfg = PolyNexusConfig::default();
        let mp_res: MpMcResult = self.mc.iter().map(|m| m.prop.res).collect();
        let mut engine = PolyNexus::new(cfg, ts, mp_res);

        let (tsx, trx) = channel_tracer();
        engine.add_tracer(Box::new(tsx));

        let ctrl = engine.get_ctrl();

        // Mark pending props as solving
        for &id in &pending {
            self.mc[id].state = McStatus::Solving;
        }

        // Spawn engine in background thread
        let join = spawn(move || MpEngine::check(&mut engine));

        self.nexus_task = Some(NexusTask {
            join,
            state_tracer: trx,
            ctrl,
        });
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
