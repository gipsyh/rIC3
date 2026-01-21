use crate::cli::run::PropMcInfo;
use giputils::{file::create_dir_if_not_exists, hash::GHashMap};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
struct FileEntry {
    hash: String,
}

#[derive(Serialize, Deserialize, Debug, Default, PartialEq, Eq)]
pub struct SourceCache {
    files: GHashMap<PathBuf, FileEntry>,
}

fn calculate_hash(path: &Path) -> anyhow::Result<String> {
    let mut file = fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buffer = [0; 8192];
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

impl SourceCache {
    fn new(sources: &[PathBuf]) -> anyhow::Result<Self> {
        let mut cache = Self::default();
        for src in sources {
            let abs_src = fs::canonicalize(src)?;
            let hash = calculate_hash(&abs_src)?;
            cache.files.insert(abs_src, FileEntry { hash });
        }
        Ok(cache)
    }
}

#[derive(Debug, Clone)]
pub struct Ric3Proj {
    path: PathBuf,
}

impl Ric3Proj {
    pub fn new() -> anyhow::Result<Self> {
        let path = PathBuf::from("ric3proj");
        create_dir_if_not_exists(&path)?;
        Ok(Self { path })
    }

    pub fn path(&self, join: impl AsRef<Path>) -> PathBuf {
        self.path.join(join.as_ref())
    }

    pub fn clear_entry(&mut self, p: impl AsRef<Path>) -> anyhow::Result<()> {
        for entry in fs::read_dir(p.as_ref())? {
            let entry = entry?;
            let path = entry.path();
            if entry.file_type()?.is_dir() {
                fs::remove_dir_all(&path)?;
            } else {
                fs::remove_file(&path)?;
            }
        }
        Ok(())
    }

    pub fn clear(&mut self) -> anyhow::Result<()> {
        self.clear_entry(self.path.clone())
    }

    /// None: not exists
    /// Some(bool): consistency
    pub fn check_cached_dut(&self, sources: &[PathBuf]) -> anyhow::Result<Option<bool>> {
        let cache_path = self.path("dut/hash.ron");
        if !cache_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&cache_path)?;
        let cache: SourceCache = ron::from_str(&content)?;
        let ncache = SourceCache::new(sources)?;
        Ok(Some(ncache == cache))
    }

    pub fn cache_dut(&self, sources: &[PathBuf]) -> anyhow::Result<()> {
        let content = ron::to_string(&SourceCache::new(sources)?)?;
        fs::write(self.path("dut/hash.ron"), content)?;
        Ok(())
    }

    pub fn check_cached_res(&self) -> anyhow::Result<Option<Vec<PropMcInfo>>> {
        let res_path = self.path("res/res.ron");
        if !res_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&res_path)?;
        let res: Vec<PropMcInfo> = ron::from_str(&content)?;
        Ok(Some(res))
    }

    pub fn cache_res(&self, res: Vec<PropMcInfo>) -> anyhow::Result<()> {
        let cache = ron::to_string(&res)?;
        fs::write(self.path("res/res.ron"), cache)?;
        Ok(())
    }
}
