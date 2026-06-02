use super::WlTransys;
use giputils::hash::GHashMap;
use logicrs::fol::{Term, current_term_mgr};
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};

#[derive(Serialize, Deserialize)]
struct SerializedWlTransys {
    input: Vec<usize>,
    latch: Vec<usize>,
    init: Vec<(usize, usize)>,
    next: Vec<(usize, usize)>,
    bad: Vec<usize>,
    output: Vec<usize>,
    constraint: Vec<usize>,
    justice: Vec<usize>,
}

impl From<&WlTransys> for SerializedWlTransys {
    fn from(wts: &WlTransys) -> Self {
        let mut init: Vec<_> = wts.init.iter().map(|(l, i)| (l.id(), i.id())).collect();
        init.sort_unstable_by_key(|(l, _)| *l);

        let mut next: Vec<_> = wts.next.iter().map(|(l, n)| (l.id(), n.id())).collect();
        next.sort_unstable_by_key(|(l, _)| *l);

        Self {
            input: terms_to_ids(&wts.input),
            latch: terms_to_ids(&wts.latch),
            init,
            next,
            bad: terms_to_ids(&wts.bad),
            output: terms_to_ids(&wts.output),
            constraint: terms_to_ids(&wts.constraint),
            justice: terms_to_ids(&wts.justice),
        }
    }
}

impl Serialize for WlTransys {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        SerializedWlTransys::from(self).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for WlTransys {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wts = SerializedWlTransys::deserialize(deserializer)?;
        let id2term = current_term_mgr().get_id2term_map();
        Ok(Self {
            input: ids_to_terms(wts.input, &id2term)?,
            latch: ids_to_terms(wts.latch, &id2term)?,
            init: id_pairs_to_term_map(wts.init, &id2term)?,
            next: id_pairs_to_term_map(wts.next, &id2term)?,
            bad: ids_to_terms(wts.bad, &id2term)?,
            output: ids_to_terms(wts.output, &id2term)?,
            constraint: ids_to_terms(wts.constraint, &id2term)?,
            justice: ids_to_terms(wts.justice, &id2term)?,
        })
    }
}

fn terms_to_ids(terms: &[Term]) -> Vec<usize> {
    terms.iter().map(Term::id).collect()
}

fn term_from_serialized_id<E>(id: usize, id2term: &GHashMap<usize, Term>) -> Result<Term, E>
where
    E: de::Error,
{
    id2term
        .get(&id)
        .cloned()
        .ok_or_else(|| E::custom(format!("term id {id} is not in TermManager")))
}

fn ids_to_terms<E>(ids: Vec<usize>, id2term: &GHashMap<usize, Term>) -> Result<Vec<Term>, E>
where
    E: de::Error,
{
    ids.into_iter()
        .map(|id| term_from_serialized_id(id, id2term))
        .collect()
}

fn id_pairs_to_term_map<E>(
    pairs: Vec<(usize, usize)>,
    id2term: &GHashMap<usize, Term>,
) -> Result<GHashMap<Term, Term>, E>
where
    E: de::Error,
{
    pairs
        .into_iter()
        .map(|(k, v)| {
            Ok((
                term_from_serialized_id(k, id2term)?,
                term_from_serialized_id(v, id2term)?,
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use giputils::bitvec::BitVec;
    use logicrs::fol::Sort;

    #[test]
    fn wltransys_round_trip_by_term_id() {
        let input = Term::new_var(Sort::Bv(4));
        let latch = Term::new_var(Sort::Bv(4));
        let init = Term::bv_const(BitVec::zero(4));
        let next = &input + &latch;
        let bad = input.teq(&latch);

        let wts = WlTransys {
            input: vec![input.clone()],
            latch: vec![latch.clone()],
            init: GHashMap::from_iter([(latch.clone(), init.clone())]),
            next: GHashMap::from_iter([(latch.clone(), next.clone())]),
            bad: vec![bad.clone()],
            output: vec![next.clone()],
            constraint: vec![Term::bool_const(true)],
            justice: vec![bad.clone()],
        };

        let content = ron::to_string(&wts).unwrap();
        let restored: WlTransys = ron::from_str(&content).unwrap();

        assert_eq!(restored.input, vec![input]);
        assert_eq!(restored.latch, vec![latch.clone()]);
        assert_eq!(restored.init[&latch], init);
        assert_eq!(restored.next[&latch], next);
        assert_eq!(restored.bad, vec![bad.clone()]);
        assert_eq!(restored.output, vec![next]);
        assert_eq!(restored.constraint, vec![Term::bool_const(true)]);
        assert_eq!(restored.justice, vec![bad]);
    }
}
