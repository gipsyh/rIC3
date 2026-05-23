use crate::{McResult, ui::UiRenderer};
use ratatui::{
    style::{Color, Style, Stylize},
    text::{Line, Span},
};

const ID_WIDTH: usize = 4;
const BOUND_WIDTH: usize = 8;
const DEFAULT_WORKER_WIDTH: usize = 24;

pub(super) struct PortfolioUi {
    renderer: UiRenderer,
    workers: Vec<WorkerUiState>,
}

struct WorkerUiState {
    name: String,
    res: McResult,
}

impl PortfolioUi {
    pub(super) fn new(renderer: UiRenderer, names: impl IntoIterator<Item = String>) -> Self {
        let ui = Self {
            renderer,
            workers: names
                .into_iter()
                .map(|name| WorkerUiState {
                    name,
                    res: McResult::Unknown(None),
                })
                .collect(),
        };
        ui.render();
        ui
    }

    pub(super) fn update(&mut self, worker_idx: usize, res: McResult) {
        if let Some(worker) = self.workers.get_mut(worker_idx) {
            worker.res = res;
        }
        self.render();
    }

    pub(super) fn finish(&self, res: McResult) {
        self.renderer.finish(res);
    }

    fn render(&self) {
        let mut lines = Vec::with_capacity(self.workers.len() + 1);
        lines.push(header_line());
        lines.extend(
            self.workers
                .iter()
                .enumerate()
                .map(|(idx, worker)| worker_line(idx, worker)),
        );
        self.renderer.render(lines);
    }
}

fn header_line() -> Line<'static> {
    Line::from(vec![
        Span::raw(format!("{:<ID_WIDTH$}", "ID")).bold(),
        Span::raw(" "),
        Span::raw(format!("{:<DEFAULT_WORKER_WIDTH$}", "Worker")).bold(),
        Span::raw(" "),
        Span::raw(format!("{:<BOUND_WIDTH$}", "Bound")).bold(),
    ])
}

fn worker_line(idx: usize, worker: &WorkerUiState) -> Line<'static> {
    let (bound, bound_style) = bound_column(worker.res);
    Line::from(vec![
        Span::raw(format!("{:<ID_WIDTH$}", idx))
            .style(Style::default().fg(Color::Magenta).bold()),
        Span::raw(" "),
        Span::raw(format!("{:<DEFAULT_WORKER_WIDTH$}", truncate(&worker.name)))
            .style(Style::default().fg(Color::White)),
        Span::raw(" "),
        Span::raw(format!("{bound:<BOUND_WIDTH$}")).style(bound_style),
    ])
}

fn bound_column(res: McResult) -> (String, Style) {
    match res {
        McResult::UNSAT => ("UNSAT".to_string(), Style::default().fg(Color::Green).bold()),
        McResult::SAT(depth) => (depth.to_string(), Style::default().fg(Color::Red).bold()),
        McResult::Unknown(Some(bound)) => {
            (bound.to_string(), Style::default().fg(Color::Cyan).bold())
        }
        McResult::Unknown(None) => ("-".to_string(), Style::default().fg(Color::DarkGray)),
    }
}

fn truncate(name: &str) -> String {
    let len = name.chars().count();
    if len <= DEFAULT_WORKER_WIDTH {
        name.to_string()
    } else {
        format!(
            "{}...",
            name.chars()
                .take(DEFAULT_WORKER_WIDTH.saturating_sub(3))
                .collect::<String>()
        )
    }
}
