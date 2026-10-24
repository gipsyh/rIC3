use log::{Level, LevelFilter, log, max_level, set_max_level};
use std::{
    fmt::Display,
    time::{Duration, Instant},
};

pub struct IntervalLogger {
    last: Instant,
    interval: Duration,
}

impl IntervalLogger {
    #[inline]
    pub fn new(interval: Duration) -> Self {
        Self {
            last: Instant::now(),
            interval,
        }
    }

    #[inline]
    pub fn log<T: Display>(&mut self, level: Level, msg: T) {
        let now = Instant::now();
        if now.duration_since(self.last) >= self.interval {
            log!(level, "{msg}");
            self.last = now;
        }
    }
}

impl Default for IntervalLogger {
    #[inline]
    fn default() -> Self {
        Self::new(Duration::from_secs(10))
    }
}

pub fn with_log_level<F, R>(level: LevelFilter, f: F) -> R
where
    F: FnOnce() -> R,
{
    let prev_level = max_level();
    set_max_level(level);
    let result = f();
    set_max_level(prev_level);
    result
}
