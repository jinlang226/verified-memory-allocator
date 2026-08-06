#![feature(core_intrinsics)]
#![feature(allocator_api)]
#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(unused_assignments)]
#![allow(unused_macros)]
#![feature(thread_id_value)]
#![verifier::exec_allows_no_decreases_clause]

// bottom bread

mod os_mem;
mod thread;

// fundamentals and definitions

mod tokens;
mod types;
mod flags;
mod layout;
mod config;
mod bin_sizes;
mod dealloc_token;
mod page_organization;
mod os_mem_util;

// utilities

mod pigeonhole;

// implementation

mod linked_list;
mod bitmap;
mod commit_mask;

mod arena;
mod alloc_fast;
mod alloc_generic;
mod free;
mod realloc;
mod segment;
mod commit_segment;
mod os_commit;
mod os_alloc;
mod page;
mod queues;
mod init;

use vstd::prelude::*;

verus!{

use crate::types::print_hex;

#[verifier::external_body]
#[verus::line_count::ignore]
fn main()
{
    unimplemented!()
}

}

#[verifier::external_body]
fn big_test(heap: crate::types::HeapPtr)
{
    unimplemented!()
}

// Called from C overrides

// verus_mi_thread_init_default_heap should be called once-per-thread,
// and must be called before verus_mi_heap_malloc

use core::ffi::c_void;
use crate::types::todo;

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_thread_init_default_heap() -> *mut c_void
{
    unimplemented!()
}

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_heap_malloc(heap: *mut c_void, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn verus_mi_free(ptr: *mut c_void)
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn calloc(number: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

verus!{

#[inline(always)]
#[verifier::external_body]
#[verus::line_count::ignore]
pub fn count_size_overflow(count: usize, size: usize) -> (x: (usize, bool))
    ensures x.1 <==> (count * size >= usize::MAX),
          !x.1 ==> x.0 == count * size
{
    unimplemented!()
}

}


#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn free(ptr: *mut c_void)
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocf(ptr: *mut c_void, newsize: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_size(ptr: *mut c_void) -> usize
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_usable_size(ptr: *mut c_void) -> usize
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn valloc(size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn vfree(ptr: *mut c_void)
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn malloc_good_size(size: usize) -> usize
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn posix_memalign(p: *mut *mut c_void, alignment: usize, size: usize) -> i32
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn aligned_alloc(alignment: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn cfree(ptr: *mut c_void)
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn pvalloc(size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocarray(ptr: *mut c_void, count: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn reallocarr(ptr: *mut c_void, count: usize, size: usize) -> i32
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn memalign(alignment: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn _aligned_malloc(alignment: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_malloc(size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_calloc(number: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_realloc(ptr: *mut c_void, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_free(ptr: *mut c_void)
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_cfree(ptr: *mut c_void)
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_valloc(size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_pvalloc(size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __libc_memalign(alignment: usize, size: usize) -> *mut c_void
{
    unimplemented!()
}

#[cfg(feature = "override_system_allocator")]
#[verifier::external]
#[no_mangle]
pub unsafe extern "C" fn __posix_memalign(p: *mut *mut c_void, alignment: usize, size: usize) -> i32
{
    unimplemented!()
}


// TODO need to figure out how to override the C++ new / delete operators

#[cfg(feature = "override_system_allocator")]
extern "C" {
    #[verifier::external]
    #[no_mangle]
    pub fn get_default_heap() -> *mut c_void;

    #[verifier::external]
    #[no_mangle]
    pub fn thread_id_helper() -> u64;

/*
    #[verifier::external]
    #[no_mangle]
    pub fn malloc(size: usize) -> *mut c_void;

    #[no_mangle]
    fn calloc(number: usize, size: usize) -> *mut c_void;

    #[no_mangle]
    fn realloc(ptr: *mut c_void, size: usize) -> *mut c_void;

    #[verifier::external]
    #[no_mangle]
    pub fn free(ptr: *mut c_void);
    */
}
