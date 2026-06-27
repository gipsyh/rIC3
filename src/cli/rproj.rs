use giputils::{
    file::{create_dir_if_not_exists, recreate_dir, remove_if_exists},
    hash::GHashMap,
};
use logicrs::fol::{TermManager, set_term_mgr, term_gc, term_mgr};
use rIC3::{
    McResult,
    config::EngineConfig,
    transys::Transys,
    wltransys::{WlTransys, bitblast::BitblastMap, symbol::WlTsSymbol},
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{ErrorKind, Read},
    path::{Path, PathBuf},
};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
struct FileEntry {
    hash: Vec<u8>,
}

#[derive(Clone, Serialize, Deserialize, Debug, Default, PartialEq, Eq)]
pub struct DutHash {
    files: GHashMap<PathBuf, FileEntry>,
}

fn calculate_hash(path: &Path) -> anyhow::Result<Vec<u8>> {
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
    Ok(hasher.finalize().to_vec())
}

impl DutHash {
    pub fn new(sources: &[PathBuf]) -> anyhow::Result<Self> {
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

    pub fn save_serde_obj(&self, s: &impl Serialize, path: impl AsRef<Path>) -> anyhow::Result<()> {
        remove_if_exists(&path)?;
        fs::write(self.path(path), ron::to_string(s)?)?;
        Ok(())
    }

    pub fn load_serde_obj<D: DeserializeOwned>(&self, path: impl AsRef<Path>) -> anyhow::Result<D> {
        let path = self.path(path);
        let s = fs::read_to_string(&path).map_err(|err| {
            if err.kind() == ErrorKind::NotFound {
                anyhow::anyhow!("project file not found: {}", path.display())
            } else {
                err.into()
            }
        })?;
        let obj: D = ron::from_str(&s)?;
        Ok(obj)
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
    pub fn check_cached_dut(&self, dh: &DutHash) -> anyhow::Result<Option<bool>> {
        let cache_path = self.path("dut/hash.ron");
        if !cache_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&cache_path)?;
        let cache: DutHash = ron::from_str(&content)?;
        Ok(Some(&cache == dh))
    }

    pub fn cache_dut(&self, dh: &DutHash) -> anyhow::Result<()> {
        let content = ron::to_string(dh)?;
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

    // pub fn save_term_mgr(&self, path: impl AsRef<Path>) -> anyhow::Result<()> {
    //     term_gc();
    //     self.save_serde_obj(term_mgr(), self.path(path.as_ref()))
    // }

    // pub fn load_term_mgr(&self, path: impl AsRef<Path>) -> anyhow::Result<()> {
    //     // term_gc();
    //     // self.save_serde_obj(term_mgr(), self.path(path.as_ref()))
    // }

    pub fn save_wts(
        &self,
        wts: &WlTransys,
        wsym: &WlTsSymbol,
        path: impl AsRef<Path>,
    ) -> anyhow::Result<()> {
        recreate_dir(&self.path(path.as_ref()))?;
        term_gc();
        self.save_serde_obj(term_mgr(), path.as_ref().join("term.ron"))?;
        self.save_serde_obj(&wts, path.as_ref().join("wts.ron"))?;
        self.save_serde_obj(wsym, path.as_ref().join("wsym.ron"))?;
        Ok(())
    }

    pub fn load_wts(&self, path: impl AsRef<Path>) -> anyhow::Result<(WlTransys, WlTsSymbol)> {
        term_gc();
        assert!(term_mgr().is_empty());
        let tm: TermManager = self.load_serde_obj(path.as_ref().join("term.ron"))?;
        set_term_mgr(tm);
        term_mgr().enable_id_map();
        let wts: WlTransys = self.load_serde_obj(path.as_ref().join("wts.ron"))?;
        let wsym: WlTsSymbol = self.load_serde_obj(path.as_ref().join("wsym.ron"))?;
        term_mgr().disable_id_map();
        Ok((wts, wsym))
    }

    /// wts: Option<BitblastMap, Path link of wts>
    pub fn save_ts(
        &self,
        ts: &Transys,
        wts: Option<(&BitblastMap, impl AsRef<Path>)>,
        path: impl AsRef<Path>,
    ) -> anyhow::Result<()> {
        let path = path.as_ref();
        recreate_dir(&self.path(path))?;
        self.save_serde_obj(&ts, path.join("ts.ron"))?;
        if let Some((bbmap, wts_path)) = wts {
            let wts_path = wts_path.as_ref();
            let wtsln_path = self.path(path.join("wtsln"));
            fs::write(&wtsln_path, wts_path.to_string_lossy().as_bytes())?;
            self.save_serde_obj(bbmap, path.join("bbmap.ron"))?;
        }
        Ok(())
    }
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct PropMcInfo {
    pub name: String,
    pub res: McResult,
    pub config: Option<EngineConfig>,
}
