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
    dut_path: PathBuf,
    res_path: PathBuf,
    tmp_path: PathBuf,
}

impl Ric3Proj {
    pub fn new() -> anyhow::Result<Self> {
        let path = PathBuf::from("ric3proj");
        let dut_path = path.join("dut");
        let res_path = path.join("res");
        let tmp_path = path.join("tmp");
        for p in [
            path.clone(),
            dut_path.clone(),
            res_path.clone(),
            tmp_path.clone(),
        ] {
            if !Path::new(&p).exists() {
                fs::create_dir(&p)?;
            }
        }
        Ok(Self {
            path,
            dut_path,
            res_path,
            tmp_path,
        })
    }

    pub fn clear(&self) -> anyhow::Result<()> {
        if let Ok(entries) = fs::read_dir(&self.path) {
            for entry in entries.flatten() {
                let path = entry.path();
                match entry.file_type() {
                    Ok(ft) if ft.is_dir() => {
                        fs::remove_dir_all(&path)?;
                    }
                    _ => {
                        fs::remove_file(&path)?;
                    }
                }
            }
        }
        fs::create_dir(&self.dut_path)?;
        fs::create_dir(&self.res_path)?;
        fs::create_dir(&self.tmp_path)?;
        Ok(())
    }

    pub fn dut_path(&self) -> &PathBuf {
        &self.dut_path
    }

    pub fn res_path(&self) -> &PathBuf {
        &self.res_path
    }

    pub fn tmp_path(&self) -> &PathBuf {
        &self.tmp_path
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

    pub fn check_cached_src(&self, sources: &[PathBuf]) -> anyhow::Result<bool> {
        let cache_path = self.dut_path.join("hash.ron");
        if !cache_path.exists() {
            return Ok(false);
        }
        let content = fs::read_to_string(&cache_path)?;
        let cache: SourceCache = ron::from_str(&content)?;
        if cache.files.len() != sources.len() {
            return Ok(false);
        }
        for src in sources {
            let src = fs::canonicalize(src)?;
            if let Some(entry) = cache.files.get(&src) {
                let current_hash = Self::calculate_hash(&src)?;
                if entry.hash != current_hash {
                    return Ok(false);
                }
            } else {
                return Ok(false);
            }
        }

        Ok(true)
    }

    pub fn cache_src(&self, sources: &[PathBuf]) -> anyhow::Result<()> {
        if !self.dut_path.exists() {
            fs::create_dir_all(&self.dut_path)?;
        }
        let mut cache = SourceCache::default();
        for src in sources {
            let abs_src = fs::canonicalize(src)?;
            let hash = Self::calculate_hash(&abs_src)?;

            cache.files.insert(abs_src, FileEntry { hash });
        }
        let content = ron::to_string(&cache)?;
        fs::write(self.dut_path.join("hash.ron"), content)?;
        Ok(())
    }

    pub fn check_cached_res(&self) -> anyhow::Result<Option<Vec<PropMcInfo>>> {
        if !self.res_path.exists() {
            fs::create_dir_all(&self.res_path)?;
        }
        let res_path = self.res_path.join("res.ron");
        if !res_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&res_path)?;
        let res: Vec<PropMcInfo> = ron::from_str(&content)?;
        Ok(Some(res))
    }

    pub fn cache_res(&self, res: Vec<PropMcInfo>) -> anyhow::Result<()> {
        if !self.res_path.exists() {
            fs::create_dir_all(&self.res_path)?;
        }
        let cache = ron::to_string(&res)?;
        fs::write(self.res_path.join("res.ron"), cache)?;
        Ok(())
    }
}
