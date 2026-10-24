use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};
use std::fmt::{self, Debug};

#[derive(Clone, Copy, PartialEq, Eq, Hash, EnumAsInner, Serialize, Deserialize)]
pub enum Sort {
    /// Bit-vector sort with the given bit width.
    Bv(usize),
    /// Array sort: first field is the index bit width, second field is the element bit width.
    Array(usize, usize),
}

impl Sort {
    #[inline]
    pub fn bool() -> Self {
        Sort::Bv(1)
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bv(1))
    }

    #[inline]
    pub fn size(&self) -> usize {
        match self {
            Sort::Bv(s) => *s,
            Sort::Array(i, e) => {
                let i = (*i).try_into().unwrap();
                let shifted = 1usize.checked_shl(i).unwrap();
                shifted.checked_mul(*e).unwrap()
            }
        }
    }

    #[inline]
    pub fn bv(&self) -> usize {
        if let Sort::Bv(w) = self { *w } else { panic!() }
    }

    #[inline]
    pub fn array(&self) -> (usize, usize) {
        if let Sort::Array(i, e) = self {
            (*i, *e)
        } else {
            panic!()
        }
    }

    #[inline]
    pub fn array_depth(&self) -> usize {
        if let Sort::Array(index, _) = self {
            1usize.checked_shl(*index as _).unwrap()
        } else {
            panic!()
        }
    }
}

impl Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Sort::Bv(w) => write!(f, "Bv{w}"),
            Sort::Array(w, d) => write!(f, "Array{w},{d}"),
        }
    }
}
