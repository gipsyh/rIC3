use bincode::{Decode, Encode};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    collections::HashMap,
    error::Error,
    fs,
    io::Read,
    path::{Path, PathBuf},
    time::SystemTime,
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Encode, Decode)]
struct FileEntry {
    modified_nanos: u128,
    hash: String,
}

#[derive(Serialize, Deserialize, Debug, Default, Encode, Decode)]
struct SourceCache {
    files: HashMap<PathBuf, FileEntry>,
}

pub struct RiceProj {
    path: PathBuf,
    dut_path: PathBuf,
}

impl RiceProj {
    pub fn new() -> Result<Self, Box<dyn Error>> {
        let path = PathBuf::from("riceproj");
        let mut dut_path = path.clone();
        dut_path.push("dut");
        if !Path::new(&path).exists() {
            fs::create_dir(&path)?;
        }
        if !Path::new(&dut_path).exists() {
            fs::create_dir(&dut_path)?;
        }
        Ok(Self { path, dut_path })
    }

    pub fn clear(&self) -> Result<(), Box<dyn Error>> {
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
        Ok(())
    }

    pub fn dut_path(&self) -> &PathBuf {
        &self.dut_path
    }

    fn calculate_hash(path: &Path) -> Result<String, Box<dyn Error>> {
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

    pub fn check_cached_src(&self, sources: &[PathBuf]) -> Result<bool, Box<dyn Error>> {
        let cache_path = self.dut_path.join("src_cache.bin");
        if !cache_path.exists() {
            return Ok(false);
        }
        let content = fs::read(&cache_path)?;
        let cache: SourceCache =
            bincode::decode_from_slice(&content, bincode::config::standard())?.0;
        if cache.files.len() != sources.len() {
            return Ok(false);
        }
        for src in sources {
            let src = fs::canonicalize(src)?;
            if let Some(entry) = cache.files.get(&src) {
                let metadata = fs::metadata(&src)?;
                let modified = metadata
                    .modified()?
                    .duration_since(SystemTime::UNIX_EPOCH)?;
                if entry.modified_nanos != modified.as_nanos() {
                    return Ok(false);
                }
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

    pub fn cache_src(&self, sources: &[PathBuf]) -> Result<(), Box<dyn Error>> {
        if !self.dut_path.exists() {
            fs::create_dir_all(&self.dut_path)?;
        }
        let mut cache = SourceCache::default();
        for src in sources {
            let abs_src = fs::canonicalize(src)?;
            let metadata = fs::metadata(&abs_src)?;
            let modified = metadata
                .modified()?
                .duration_since(SystemTime::UNIX_EPOCH)?;
            let hash = Self::calculate_hash(&abs_src)?;

            cache.files.insert(
                abs_src,
                FileEntry {
                    modified_nanos: modified.as_nanos(),
                    hash,
                },
            );
        }

        let content = bincode::encode_to_vec(&cache, bincode::config::standard())?;
        fs::write(self.dut_path.join("src_cache.bin"), content)?;
        Ok(())
    }
}
