use std::ops::{Deref, DerefMut};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptionU8(u8);

impl OptionU8 {
    pub const NONE: Self = Self(u8::MAX);

    #[inline]
    pub fn some(v: u8) -> Self {
        Self(v)
    }

    #[inline]
    pub fn is_some(&self) -> bool {
        *self != Self::NONE
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        *self == Self::NONE
    }
}

impl Default for OptionU8 {
    #[inline]
    fn default() -> Self {
        Self::NONE
    }
}

impl Deref for OptionU8 {
    type Target = u8;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for OptionU8 {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OptionU32(u32);

impl OptionU32 {
    pub const NONE: Self = Self(u32::MAX);

    #[inline]
    pub fn some(v: u32) -> Self {
        Self(v)
    }

    #[inline]
    pub fn is_some(&self) -> bool {
        *self != Self::NONE
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        *self == Self::NONE
    }
}

impl Default for OptionU32 {
    #[inline]
    fn default() -> Self {
        Self::NONE
    }
}

impl Deref for OptionU32 {
    type Target = u32;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for OptionU32 {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub trait TerminateCtrl: Send + Sync {
    fn terminate(&self);

    fn is_terminated(&self) -> bool {
        panic!("unsupported is_terminated");
    }
}
