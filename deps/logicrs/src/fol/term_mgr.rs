use super::{FolOp, OpTerm, Sort, Term, TermInner, TermType};
use giputils::{
    bitvec::BitVec,
    hash::{GHashMap, GHashSet},
    ptr::Grc,
};
use log::debug;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::{cell::UnsafeCell, ops::Deref};

#[derive(Default, Clone)]
pub struct TermManager {
    avl_vid: usize,
    avl_tid: usize,
    map: GHashMap<TermType, Term>,
    id2term: Option<GHashMap<usize, Term>>,
}

impl TermManager {
    #[inline]
    pub fn new() -> Self {
        Self {
            avl_vid: 0,
            avl_tid: 0,
            map: GHashMap::new(),
            id2term: None,
        }
    }

    #[inline]
    pub fn new_term(&mut self, ty: TermType, sort: Sort) -> Term {
        match self.map.get(&ty) {
            Some(term) => term.clone(),
            None => {
                let id = self.avl_tid;
                self.avl_tid += 1;
                let term = Term {
                    inner: Grc::new(TermInner {
                        id,
                        sort,
                        ty: ty.clone(),
                    }),
                };
                self.map.insert(ty, term.clone());
                if let Some(id2term) = &mut self.id2term {
                    id2term.insert(id, term.clone());
                }
                term
            }
        }
    }

    #[inline]
    pub fn new_var(&mut self, sort: Sort) -> Term {
        let id = self.avl_vid;
        self.avl_vid += 1;
        let term = TermType::Var(id);
        self.new_term(term, sort)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    #[inline]
    pub fn enable_id_map(&mut self) {
        if self.id2term.is_none() {
            let map = self
                .map
                .values()
                .map(|term| (term.id(), term.clone()))
                .collect();
            self.id2term = Some(map);
        }
    }

    #[inline]
    pub fn disable_id_map(&mut self) {
        self.id2term = None;
    }

    #[inline]
    pub fn get_term_by_id(&self, id: usize) -> Option<Term> {
        self.id2term.as_ref()?.get(&id).cloned()
    }

    #[inline]
    fn add_internal_ref(term: &Term, internal_refs: &mut GHashMap<*const TermInner, usize>) {
        *internal_refs.entry(term.inner.as_ptr()).or_insert(0) += 1;
    }

    #[inline]
    fn add_term_type_internal_refs(
        ty: &TermType,
        internal_refs: &mut GHashMap<*const TermInner, usize>,
    ) {
        if let TermType::Op(op) = ty {
            for term in &op.terms {
                Self::add_internal_ref(term, internal_refs);
            }
        }
    }

    fn garbage_collect(&mut self) {
        let before = self.map.len();
        let mut internal_refs = GHashMap::new();
        for (ty, term) in self.map.iter() {
            Self::add_internal_ref(term, &mut internal_refs);
            Self::add_term_type_internal_refs(ty, &mut internal_refs);
            Self::add_term_type_internal_refs(term.deref(), &mut internal_refs);
        }
        if let Some(id2term) = &self.id2term {
            for term in id2term.values() {
                Self::add_internal_ref(term, &mut internal_refs);
            }
        }

        let mut stack: Vec<Term> = self
            .map
            .values()
            .filter(|term| {
                let ptr = term.inner.as_ptr();
                let internal_refs = internal_refs.get(&ptr).copied().unwrap_or(0);
                term.inner.count() > internal_refs
            })
            .cloned()
            .collect();

        let mut live = GHashSet::new();
        while let Some(term) = stack.pop() {
            if !live.insert(term.inner.as_ptr()) {
                continue;
            }
            if let TermType::Op(op) = term.deref() {
                stack.extend(op.terms.iter().cloned());
            }
        }
        self.map
            .retain(|_, term| live.contains(&term.inner.as_ptr()));
        if let Some(id2term) = &mut self.id2term {
            id2term.retain(|_, term| live.contains(&term.inner.as_ptr()));
            id2term.shrink_to_fit();
        }
        let after = self.map.len();
        self.map.shrink_to_fit();
        debug!(
            "term GC cleared {} terms ({} -> {})",
            before - after,
            before,
            after
        );
    }
}

thread_local! {
    static TERM_MANAGER: UnsafeCell<TermManager> = UnsafeCell::new(TermManager::new());
}

#[inline]
pub fn term_mgr() -> &'static mut TermManager {
    TERM_MANAGER.with(|m| unsafe { &mut *m.get() })
}

/// Set global TermManager
pub fn set_term_mgr(manager: TermManager) {
    *term_mgr() = manager;
}

pub fn term_gc() {
    term_mgr().garbage_collect();
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct TermManagerSnapshot {
    avl_vid: usize,
    avl_tid: usize,
    terms: Vec<SerializedTerm>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct SerializedTerm {
    id: usize,
    sort: Sort,
    ty: SerializedTermType,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum SerializedTermType {
    Const(BitVec),
    Var(usize),
    Op(SerializedOpTerm),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct SerializedOpTerm {
    op: String,
    terms: Vec<usize>,
}

impl TermManager {
    fn to_snapshot(&self) -> TermManagerSnapshot {
        let mut terms: Vec<_> = self
            .map
            .values()
            .map(|term| SerializedTerm {
                id: term.id(),
                sort: term.sort(),
                ty: SerializedTermType::from(term.deref()),
            })
            .collect();
        terms.sort_by_key(|term| term.id);
        TermManagerSnapshot {
            avl_vid: self.avl_vid,
            avl_tid: self.avl_tid,
            terms,
        }
    }

    fn from_snapshot(snapshot: TermManagerSnapshot) -> Self {
        let mut manager = Self::new();
        let mut id2term = GHashMap::new();

        for term in snapshot.terms {
            let id = term.id;
            let ty = term.ty.into_term_type(&id2term);
            let new_term = Term {
                inner: Grc::new(TermInner {
                    id,
                    sort: term.sort,
                    ty: ty.clone(),
                }),
            };
            manager.map.insert(ty, new_term.clone());
            id2term.insert(id, new_term);
        }

        manager.avl_vid = snapshot.avl_vid;
        manager.avl_tid = snapshot.avl_tid;
        manager
    }
}

impl Serialize for TermManager {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.to_snapshot().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for TermManager {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let snapshot = TermManagerSnapshot::deserialize(deserializer)?;
        Ok(Self::from_snapshot(snapshot))
    }
}

impl From<&TermType> for SerializedTermType {
    fn from(value: &TermType) -> Self {
        match value {
            TermType::Const(c) => Self::Const(c.clone()),
            TermType::Var(v) => Self::Var(*v),
            TermType::Op(op) => Self::Op(SerializedOpTerm {
                op: op.op.to_string(),
                terms: op.terms.iter().map(|term| term.id()).collect(),
            }),
        }
    }
}

impl SerializedTermType {
    fn into_term_type(self, id2term: &GHashMap<usize, Term>) -> TermType {
        match self {
            Self::Const(c) => TermType::Const(c),
            Self::Var(v) => TermType::Var(v),
            Self::Op(op) => TermType::Op(OpTerm {
                op: FolOp::from(op.op.as_str()),
                terms: op
                    .terms
                    .into_iter()
                    .map(|id| id2term[&id].clone())
                    .collect(),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fol::Term;

    #[test]
    fn term_manager_round_trip() {
        let x = Term::new_var(Sort::Bv(4));
        let y = Term::new_var(Sort::Bv(4));
        let expr = &x + &y;
        let expr_id = expr.id();

        let snapshot = term_mgr().to_snapshot();
        let manager = TermManager::from_snapshot(snapshot);

        drop(expr);
        drop(y);
        drop(x);
        set_term_mgr(manager);

        term_mgr().enable_id_map();
        let expr = term_mgr().get_term_by_id(expr_id).unwrap();
        assert_eq!(expr.id(), expr_id);

        let z = Term::new_var(Sort::Bv(4));
        assert!(z.id() > expr_id);
    }

    #[test]
    fn optional_id_map_tracks_new_terms() {
        term_mgr().enable_id_map();
        let x = Term::new_var(Sort::bool());
        assert_eq!(term_mgr().get_term_by_id(x.id()).unwrap(), x);
        term_mgr().disable_id_map();
    }

    #[test]
    fn term_gc_collects_dead_dag() {
        let c = Term::bool_const(true);
        let c_id = c.id();
        let x = Term::new_var(Sort::bool());
        let expr = &c & &x;
        drop(c);
        drop(x);
        drop(expr);

        term_gc();

        assert_ne!(Term::bool_const(true).id(), c_id);
    }

    #[test]
    fn term_gc_collects_dead_dag_with_id_map_enabled() {
        set_term_mgr(TermManager::new());

        term_mgr().enable_id_map();
        let c = Term::bool_const(true);
        let x = Term::new_var(Sort::bool());
        let expr = &c & &x;
        let expr_id = expr.id();
        drop(c);
        drop(x);
        drop(expr);

        term_gc();

        assert!(term_mgr().is_empty());
        assert!(term_mgr().get_term_by_id(expr_id).is_none());
    }
}
