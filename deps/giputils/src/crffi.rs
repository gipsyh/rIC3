use std::mem::{forget, size_of};

#[repr(C)]
#[derive(Debug)]
pub struct RustVec {
    cap: usize,
    ptr: usize,
    len: usize,
    sizet: usize,
}

impl RustVec {
    pub fn new<T>(v: Vec<T>) -> Self {
        let res = Self {
            cap: v.capacity(),
            ptr: v.as_ptr() as usize,
            len: v.len(),
            sizet: size_of::<T>(),
        };
        forget(v);
        res
    }
}

impl Drop for RustVec {
    fn drop(&mut self) {
        let vec: Vec<u8> = unsafe {
            Vec::from_raw_parts(
                self.ptr as *mut u8,
                self.len * self.sizet,
                self.cap * self.sizet,
            )
        };
        drop(vec);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_vec_drop(vec: RustVec) {
    drop(vec)
}
