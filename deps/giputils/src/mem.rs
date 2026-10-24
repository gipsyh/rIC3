use std::fmt::{self, Debug, Display, Formatter};

/// A snapshot of the resident memory usage of the current process, in bytes.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct MemUsage {
    /// Resident set size at the time of the sampling.
    pub current: usize,
    /// High water mark of the resident set size since the process started.
    ///
    /// This is a process wide and monotonically non-decreasing value, so it only
    /// ever reports the peak reached so far, not the peak of a single phase. On
    /// Linux it can be lowered by writing `5` to `/proc/self/clear_refs`.
    pub peak: usize,
}

impl MemUsage {
    /// Samples the memory usage of the current process, in bytes.
    ///
    /// # Panics
    ///
    /// Panics if the platform is not supported, or the underlying query failed.
    #[inline]
    pub fn now() -> Self {
        Self::try_now().expect("unsupported memory usage query")
    }

    /// Samples the memory usage of the current process, in bytes.
    ///
    /// Returns `None` if the platform is not supported, or the underlying query
    /// failed.
    #[inline]
    pub fn try_now() -> Option<Self> {
        platform::usage()
    }
}

impl Display for MemUsage {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "current {}, peak {}",
            human_size(self.current),
            human_size(self.peak)
        )
    }
}

impl Debug for MemUsage {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self, f)
    }
}

/// Formats a size in bytes into a human readable string, e.g. `1.00GiB`.
pub fn human_size(bytes: usize) -> String {
    const KIB: usize = 1024;
    const MIB: usize = KIB * 1024;
    const GIB: usize = MIB * 1024;

    if bytes < KIB {
        format!("{bytes}B")
    } else if bytes < MIB {
        format!("{}KiB", bytes / KIB)
    } else if bytes < GIB {
        let mib = bytes as f64 / MIB as f64;
        if mib < 10.0 {
            format!("{mib:.1}MiB")
        } else {
            format!("{mib:.0}MiB")
        }
    } else {
        let gib = bytes as f64 / GIB as f64;
        if gib < 10.0 {
            format!("{gib:.2}GiB")
        } else {
            format!("{gib:.1}GiB")
        }
    }
}

#[cfg(target_os = "macos")]
mod platform {
    use super::MemUsage;
    use std::mem::MaybeUninit;

    /// `mach_task_basic_info` reports both the resident size and its high water
    /// mark, so a single `task_info` call covers the current and the peak.
    pub(super) fn usage() -> Option<MemUsage> {
        let mut info = MaybeUninit::<libc::mach_task_basic_info_data_t>::uninit();
        let mut count = libc::MACH_TASK_BASIC_INFO_COUNT;
        // SAFETY: `info` is valid for writes of `count` natural_t words, which
        // is exactly what `task_info` writes for this flavor.
        let ret = unsafe {
            libc::task_info(
                task_self(),
                libc::MACH_TASK_BASIC_INFO,
                info.as_mut_ptr() as libc::task_info_t,
                &mut count,
            )
        };
        if ret != libc::KERN_SUCCESS {
            return None;
        }
        // SAFETY: `task_info` returned `KERN_SUCCESS`, so `info` is initialized.
        let info = unsafe { info.assume_init() };
        Some(MemUsage {
            current: info.resident_size as usize,
            peak: info.resident_size_max as usize,
        })
    }

    /// `mach_task_self` is deprecated in favour of the `mach2` crate, which is
    /// not worth a dependency for a single port lookup.
    #[allow(deprecated)]
    #[inline]
    fn task_self() -> libc::mach_port_t {
        // SAFETY: `mach_task_self` only reads the task port of the process.
        unsafe { libc::mach_task_self() }
    }
}

#[cfg(target_os = "linux")]
mod platform {
    use super::MemUsage;
    use std::{fs, mem::MaybeUninit};

    /// The resident set size is read from `/proc/self/statm`, and its high water
    /// mark from `getrusage`, which reports the same kernel counter.
    pub(super) fn usage() -> Option<MemUsage> {
        // Fields of statm: size resident shared text lib data dt, all in pages.
        let statm = fs::read_to_string("/proc/self/statm").ok()?;
        let resident = statm.split_whitespace().nth(1)?.parse::<usize>().ok()?;
        Some(MemUsage {
            current: resident.checked_mul(page_size()?)?,
            peak: peak()?,
        })
    }

    fn page_size() -> Option<usize> {
        // SAFETY: `sysconf` only queries the configuration of the process.
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        usize::try_from(size).ok()
    }

    fn peak() -> Option<usize> {
        let mut usage = MaybeUninit::<libc::rusage>::uninit();
        // SAFETY: `usage` is a valid pointer to a `rusage` for `getrusage` to fill.
        if unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) } != 0 {
            return None;
        }
        // SAFETY: `getrusage` succeeded, so `usage` is initialized.
        // `ru_maxrss` is in KiB on Linux.
        let maxrss = unsafe { usage.assume_init() }.ru_maxrss;
        usize::try_from(maxrss).ok()?.checked_mul(1024)
    }
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
mod platform {
    use super::MemUsage;

    #[inline]
    pub(super) fn usage() -> Option<MemUsage> {
        None
    }
}
