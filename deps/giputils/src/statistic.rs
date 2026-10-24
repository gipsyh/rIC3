use std::{
    fmt::{self, Debug},
    ops::{Add, AddAssign},
    time::{Duration, Instant},
};

#[derive(Default, Clone, Copy)]
pub struct Average {
    sum: f64,
    num: usize,
}

impl Debug for Average {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.6}", self.sum / self.num as f64)
    }
}

impl AddAssign<usize> for Average {
    #[inline]
    fn add_assign(&mut self, rhs: usize) {
        self.sum += rhs as f64;
        self.num += 1;
    }
}

impl AddAssign<f64> for Average {
    #[inline]
    fn add_assign(&mut self, rhs: f64) {
        self.sum += rhs;
        self.num += 1;
    }
}

impl Add<Average> for Average {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Average) -> Self::Output {
        Self {
            sum: self.sum + rhs.sum,
            num: self.num + rhs.num,
        }
    }
}

impl AddAssign<Average> for Average {
    #[inline]
    fn add_assign(&mut self, rhs: Average) {
        self.sum += rhs.sum;
        self.num += rhs.num;
    }
}

#[derive(Default, Clone, Copy)]
pub struct AverageDuration {
    sum: Duration,
    num: usize,
}

impl Debug for AverageDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.num == 0 {
            write!(f, "None")
        } else {
            write!(f, "{:?}", self.sum / self.num as u32)
        }
    }
}

impl AddAssign<Duration> for AverageDuration {
    #[inline]
    fn add_assign(&mut self, rhs: Duration) {
        self.sum += rhs;
        self.num += 1;
    }
}

impl AddAssign<AverageDuration> for AverageDuration {
    #[inline]
    fn add_assign(&mut self, rhs: AverageDuration) {
        self.sum += rhs.sum;
        self.num += rhs.num;
    }
}

#[derive(Default, Clone, Copy)]
pub struct CountedDuration {
    sum: Duration,
    num: usize,
}

impl CountedDuration {
    #[inline]
    pub fn count(&self) -> usize {
        self.num
    }
}

impl Debug for CountedDuration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} times in {:.6?}", self.num, self.sum)
    }
}

impl AddAssign<Duration> for CountedDuration {
    #[inline]
    fn add_assign(&mut self, rhs: Duration) {
        self.sum += rhs;
        self.num += 1;
    }
}

impl AddAssign<CountedDuration> for CountedDuration {
    #[inline]
    fn add_assign(&mut self, rhs: CountedDuration) {
        self.sum += rhs.sum;
        self.num += rhs.num;
    }
}

#[derive(Default, Clone, Copy)]
pub struct SuccessRate {
    succ: usize,
    fail: usize,
}

impl SuccessRate {
    #[inline]
    pub fn success(&mut self) {
        self.succ += 1;
    }

    #[inline]
    pub fn fail(&mut self) {
        self.fail += 1;
    }

    #[inline]
    pub fn statistic(&mut self, success: bool) {
        if success { self.success() } else { self.fail() }
    }
}

impl Add for SuccessRate {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            succ: self.succ + rhs.succ,
            fail: self.fail + rhs.fail,
        }
    }
}

impl AddAssign for SuccessRate {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.succ += rhs.succ;
        self.fail += rhs.fail;
    }
}

impl Debug for SuccessRate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "success: {}, fail: {}, success rate: {:.2}%",
            self.succ,
            self.fail,
            (self.succ as f64 / (self.succ + self.fail) as f64) * 100_f64
        )
    }
}

#[derive(Clone)]
pub struct RunningTime {
    start: Instant,
}

impl RunningTime {
    #[inline]
    pub fn label(&self) -> Duration {
        self.start.elapsed()
    }

    #[inline]
    pub fn from_label(&self, start: Duration) -> Duration {
        self.start.elapsed() - start
    }

    #[inline]
    pub fn time(&self) -> Duration {
        self.start.elapsed()
    }
}

impl Default for RunningTime {
    fn default() -> Self {
        Self {
            start: Instant::now(),
        }
    }
}

impl Debug for RunningTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.2}s", self.start.elapsed().as_secs_f64())
    }
}
