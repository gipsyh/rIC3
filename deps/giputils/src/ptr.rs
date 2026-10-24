use std::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::Arc,
};

macro_rules! define_rc_wrapper {
    ($wrapper:ident, $inner:ident) => {
        #[derive(Debug, Default)]
        pub struct $wrapper<T> {
            inner: $inner<T>,
        }

        impl<T> $wrapper<T> {
            #[inline]
            pub fn new(v: T) -> Self {
                Self {
                    inner: $inner::new(v),
                }
            }

            #[inline]
            pub fn as_ptr(&self) -> *const T {
                $inner::as_ptr(&self.inner)
            }

            /// # Safety
            #[inline]
            pub unsafe fn from_ptr(p: *const T) -> Self {
                Self {
                    inner: unsafe { $inner::from_raw(p) },
                }
            }

            #[inline]
            pub fn count(&self) -> usize {
                $inner::strong_count(&self.inner)
            }

            #[inline]
            pub fn increment_count(&self) {
                unsafe { $inner::increment_strong_count(self.as_ptr()) }
            }

            /// # Safety
            #[inline]
            #[allow(clippy::mut_from_ref)]
            pub unsafe fn get_mut_from_unmut(&self) -> &mut T {
                unsafe { &mut *(self.as_ptr() as *mut T) }
            }
        }

        impl<T> Deref for $wrapper<T> {
            type Target = T;

            #[inline]
            fn deref(&self) -> &Self::Target {
                self.inner.deref()
            }
        }

        impl<T> DerefMut for $wrapper<T> {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target {
                unsafe { &mut *($inner::as_ptr(&self.inner) as *mut T) }
            }
        }

        impl<T> PartialEq for $wrapper<T> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                $inner::as_ptr(&self.inner) == $inner::as_ptr(&other.inner)
            }
        }

        impl<T> Eq for $wrapper<T> {}

        unsafe impl<T> Sync for $wrapper<T> {}

        impl<T> Clone for $wrapper<T> {
            #[inline]
            fn clone(&self) -> Self {
                Self {
                    inner: self.inner.clone(),
                }
            }
        }
    };
}

define_rc_wrapper!(Grc, Arc);
define_rc_wrapper!(Garc, Arc);

/// A non-owning pointer: like [`NonNull`], it merely stores an address and does
/// not allocate or drop anything, but unlike [`NonNull`] the pointee can be
/// accessed without `unsafe`. There is no reference counting and no
/// [`Drop`] — the pointer borrows data owned elsewhere, and the caller is
/// responsible for keeping that data alive for as long as the `Gptr` is used.
///
/// `Gptr<T>` is always non-null. It is constructed from a reference, so the
/// borrow is established without `unsafe`; thereafter both shared and mutable
/// access go through [`Deref`] / [`DerefMut`].
#[derive(Clone, Copy, Debug)]
pub struct Gptr<T> {
    ptr: NonNull<T>,
}

impl<T> Gptr<T> {
    /// Creates a `Gptr` borrowing `r`. The caller must ensure `r` outlives
    /// every use of the returned `Gptr`; this is not enforced by the borrow
    /// checker because the pointer carries no lifetime.
    #[inline]
    pub fn new(r: &T) -> Self {
        Self {
            ptr: NonNull::from(r),
        }
    }

    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }
}

impl<T> Deref for Gptr<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> DerefMut for Gptr<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.ptr.as_mut() }
    }
}

unsafe impl<T> Sync for Gptr<T> {}

unsafe impl<T> Send for Gptr<T> {}
