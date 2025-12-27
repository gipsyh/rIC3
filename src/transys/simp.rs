use super::{Transys, TransysIf};
use crate::{
    config::PreprocConfig,
    transys::{certify::Restore, frts::FrTs, scorr::Scorr},
};
use giputils::hash::GHashSet;
use log::{debug, info};
use logicrs::{Lit, Var};

impl Transys {
    pub fn coi_refine(&mut self, rst: &mut Restore) {
        let mut mark = GHashSet::new();
        let mut queue = Vec::new();
        for v in self
            .constraint
            .iter()
            .chain(self.bad.iter())
            .chain(self.justice.iter())
            .map(|l| l.var())
        {
            if !mark.contains(&v) {
                mark.insert(v);
                queue.push(v);
            }
        }
        if !self.justice.is_empty() {
            for v in self.latch.iter() {
                if !mark.contains(v) {
                    mark.insert(*v);
                    queue.push(*v);
                }
            }
        }
        while let Some(v) = queue.pop() {
            if let Some(n) = self.next.get(&v) {
                let nv = n.var();
                if !mark.contains(&nv) {
                    mark.insert(nv);
                    queue.push(nv);
                }
            }
            if let Some(i) = self.init.get(&v) {
                let iv = i.var();
                if !mark.contains(&iv) {
                    mark.insert(iv);
                    queue.push(iv);
                }
            }
            for &d in self.rel.dep(v).iter() {
                if !mark.contains(&d) {
                    mark.insert(d);
                    queue.push(d);
                }
            }
        }
        for v in self.input.iter().chain(self.latch.iter()) {
            if !mark.contains(v) {
                self.init.remove(v);
                self.next.remove(v);
            }
        }
        self.input.retain(|i| mark.contains(i));
        self.latch.retain(|i| mark.contains(i));
        let mut removed = 0;
        for v in Var::CONST + 1..=self.max_var() {
            if !mark.contains(&v) {
                removed += self.rel[v].len();
                self.rel.del_rel(v);
                rst.remove(v);
            }
        }
        debug!("ts coi simplify: removed {removed} clauses");
    }

    pub fn rearrange(&mut self, rst: &mut Restore) {
        let mut additional = vec![Var::CONST];
        additional.extend(
            self.constraint
                .iter()
                .chain(self.bad.iter())
                .chain(self.justice.iter())
                .map(|l| l.var())
                .chain(self.input.iter().copied())
                .chain(self.latch.iter().copied()),
        );
        for l in self.latch.iter() {
            if let Some(i) = self.init.get(l) {
                additional.push(i.var());
            }
            if let Some(n) = self.next.get(l) {
                additional.push(n.var());
            }
        }
        let domain_map = self.rel.rearrange(additional);
        let map_lit = |l: Lit| Lit::new(domain_map[l.var()], l.polarity());
        self.input = self.input.iter().map(|v| domain_map[*v]).collect();
        self.latch = self.latch.iter().map(|v| domain_map[*v]).collect();
        self.init = self
            .init
            .iter()
            .map(|(v, i)| (domain_map[*v], map_lit(*i)))
            .collect();
        self.next = self
            .next
            .iter()
            .map(|(v, &n)| (domain_map[*v], map_lit(n)))
            .collect();
        self.bad = self.bad.map(map_lit);
        self.constraint = self.constraint.map(map_lit);
        self.justice = self.justice.map(map_lit);
        rst.filter_map_var(&|v| domain_map.get(&v).copied());
    }

    pub fn simplify(&mut self, rst: &mut Restore) {
        self.coi_refine(rst);
        let frozens = self.frozens();
        self.rel = self.rel.simplify(frozens.iter().copied());
        self.coi_refine(rst);
        self.constraint.retain(|l| !l.is_constant(true));
        self.constraint.sort();
        self.constraint.dedup();
        self.rearrange(rst);
    }
}

impl Transys {
    pub fn preproc(&self, cfg: &PreprocConfig, mut rst: Restore) -> (Self, Restore) {
        let mut ts = self.clone();
        if cfg.preproc {
            ts.simplify(&mut rst);
            info!("trivial simplified ts: {}", ts.statistic());
            if cfg.scorr {
                let scorr = Scorr::new(ts, cfg, rst);
                (ts, rst) = scorr.scorr();
            }
            if cfg.frts {
                let frts = FrTs::new(ts, cfg, rst);
                (ts, rst) = frts.fr();
            }
        }
        info!("preprocessed ts has {}", ts.statistic());
        (ts, rst)
    }
}
