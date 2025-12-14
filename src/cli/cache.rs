use crate::cli::run::PropMcInfo;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::HashMap,
    fs,
    io::Read,
    path::{Path, PathBuf},
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
struct FileEntry {
    hash: String,
}

#[derive(Serialize, Deserialize, Debug, Default)]
struct SourceCache {
    files: HashMap<PathBuf, FileEntry>,
}

pub struct Ric3Proj {
    path: PathBuf,
}

impl Ric3Proj {
    pub fn new() -> anyhow::Result<Self> {
        let path = PathBuf::from("ric3proj");
        if !Path::new(&path).exists() {
            fs::create_dir(&path)?;
        }
        let mut res = Self { path };
        res.create_subdir()?;
        Ok(res)
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn dut_path(&self) -> PathBuf {
        self.path.join("dut")
    }

    pub fn res_path(&self) -> PathBuf {
        self.path.join("res")
    }

    pub fn ctilg_path(&self) -> PathBuf {
        self.path.join("ctilg")
    }

    pub fn tmp_path(&self) -> PathBuf {
        self.path.join("tmp")
    }

    pub fn new_dir_entry(&mut self, p: impl AsRef<Path>) -> anyhow::Result<PathBuf> {
        let p_ref = p.as_ref();
        if p_ref.exists() {
            if p_ref.is_file() {
                fs::remove_file(p_ref)?;
                fs::create_dir(p_ref)?;
            } else {
                self.clear_entry(p_ref)?;
            }
        } else {
            fs::create_dir(p_ref)?;
        }
        Ok(p.as_ref().into())
    }

    fn create_subdir(&mut self) -> anyhow::Result<()> {
        for p in [
            self.dut_path(),
            self.res_path(),
            self.ctilg_path(),
            self.tmp_path(),
        ] {
            if !Path::new(&p).exists() {
                fs::create_dir(&p)?;
            }
        }
        Ok(())
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
        self.clear_entry(self.path.clone())?;
        self.create_subdir()
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

    /// None: not exists
    /// Some(bool): consistency
    pub fn check_cached_dut(&self, sources: &[PathBuf]) -> anyhow::Result<Option<bool>> {
        let cache_path = self.dut_path().join("hash.ron");
        if !cache_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&cache_path)?;
        let cache: SourceCache = ron::from_str(&content)?;
        if cache.files.len() != sources.len() {
            return Ok(Some(false));
        }
        for src in sources {
            let src = fs::canonicalize(src)?;
            if let Some(entry) = cache.files.get(&src) {
                let current_hash = Self::calculate_hash(&src)?;
                if entry.hash != current_hash {
                    return Ok(Some(false));
                }
            } else {
                return Ok(Some(false));
            }
        }

        Ok(Some(true))
    }

    pub fn cache_dut(&self, sources: &[PathBuf]) -> anyhow::Result<()> {
        let mut cache = SourceCache::default();
        for src in sources {
            let abs_src = fs::canonicalize(src)?;
            let hash = Self::calculate_hash(&abs_src)?;

            cache.files.insert(abs_src, FileEntry { hash });
        }
        let content = ron::to_string(&cache)?;
        fs::write(self.dut_path().join("hash.ron"), content)?;
        Ok(())
    }

    pub fn check_cached_res(&self) -> anyhow::Result<Option<Vec<PropMcInfo>>> {
        let res_path = self.res_path().join("res.ron");
        if !res_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&res_path)?;
        let res: Vec<PropMcInfo> = ron::from_str(&content)?;
        Ok(Some(res))
    }

    pub fn cache_res(&self, res: Vec<PropMcInfo>) -> anyhow::Result<()> {
        let cache = ron::to_string(&res)?;
        fs::write(self.res_path().join("res.ron"), cache)?;
        Ok(())
    }
}
