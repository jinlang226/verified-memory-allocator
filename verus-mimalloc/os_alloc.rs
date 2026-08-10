use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;


verus!{

#[verifier::external_body]
pub fn os_alloc_aligned_offset(
    size: usize,
    alignment: usize,
    offset: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
{
    if offset > SEGMENT_SIZE as usize {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    if offset == 0 {
        return os_alloc_aligned(size, alignment, request_commit, allow_large);
    } else {
        todo(); loop{}
        /*
        let extra = align_up(offset, alignment) - offset;
        let oversize = size + extra;

        let (start, commited, is_large) = os_alloc_aligned(oversize, alignment, request_commit, allow_large);
        if start == 0 {
            return 0;
        }

        let p = start + extra;
        if commited && extra > get_page_size() {
            todo();
        }
        */
    }
}

#[verifier::external_body]
pub fn os_good_alloc_size(size: usize) -> (res: usize)
{
    let kib = 1024;
    let mib = 1024*1024;

    let align_size = if size < 512 * kib {
        get_page_size()
    } else if size < 2 * mib {
        64 * kib
    } else if size < 8 * mib {
        256 * kib
    } else if size < 32 * mib {
        mib
    } else {
        4 * mib
    };

    if unlikely(size >= usize::MAX - align_size) {
        size
    } else {
        let x = align_up(size, align_size);
        return x;
    }
}

#[verifier::external_body]
pub fn os_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
{
    if size == 0 {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }
    let size1 = os_good_alloc_size(size);
    let alignment1 = align_up(alignment, get_page_size());
    os_mem_alloc_aligned(size1, alignment1, request_commit, allow_large)
}

#[verifier::external_body]
pub fn os_mem_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
{
    let mut allow_large = allow_large;
    if !request_commit {
        allow_large = false;
    }

    if (!(alignment >= get_page_size() && ((alignment & (alignment - 1)) == 0))) {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    let (p, is_large, Tracked(mem)) = os_mem_alloc(size, alignment, request_commit, allow_large);
    if p.addr() == 0 {
        return (p, is_large, Tracked(mem));
    }

    if p.addr() % alignment != 0 {
        todo();
    }

    (p, is_large, Tracked(mem))
}

#[verifier::external_body]
fn os_mem_alloc(
    size: usize,
    try_alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
{
    if size == 0 {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    let mut allow_large = allow_large;
    if !request_commit {
        allow_large = false;
    }

    let mut try_alignment = try_alignment;
    if try_alignment == 0 { try_alignment = 1; }

    unix_mmap(core::ptr::null_mut(), size, try_alignment, request_commit, false, allow_large)
}

#[verifier::external_body]
fn use_large_os_page(size: usize, alignment: usize) -> bool {
    false
}

#[verifier::external_body]
fn unix_mmap(
    addr: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
    large_only: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
{
    let is_large = true;
    if (large_only || use_large_os_page(size, try_alignment)) && allow_large {
        todo();
    }

    let is_large = false;
    let (p, Tracked(mem)) = unix_mmapx(addr, size, try_alignment, prot_rw);
    if p.addr() != 0 {
        if allow_large && use_large_os_page(size, try_alignment) {
            todo();
        }
        return (p, is_large, Tracked(mem));
    } else {
        todo(); loop{}
    }
}

exec static ALIGNED_BASE: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

#[inline]
#[verifier::external_body]
fn aligned_base_add(s: usize) -> usize {
    ALIGNED_BASE.fetch_add(s, core::sync::atomic::Ordering::AcqRel)
}

#[inline]
#[verifier::external_body]
fn aligned_base_cas(s: usize, t: usize) {
    let _ = ALIGNED_BASE.compare_exchange(s, t, core::sync::atomic::Ordering::AcqRel, core::sync::atomic::Ordering::Acquire);
}

const HINT_BASE: usize = (2 as usize) << (40 as usize);
const HINT_AREA: usize = (4 as usize) << (40 as usize);
const HINT_MAX: usize = (30 as usize) << (40 as usize);

#[verifier::external_body]
fn os_get_aligned_hint(try_alignment: usize, size: usize) -> (hint: usize)
{

    if try_alignment <= 1 || try_alignment > SEGMENT_SIZE as usize {
        return 0;
    }

    let size = align_up(size, SEGMENT_SIZE as usize);
    if size > 1024*1024*1024 {
        return 0;
    }

    let mut hint = aligned_base_add(size);
    if hint == 0 || hint > HINT_MAX {
        let iinit = HINT_BASE;

        //let r = heap_random_next();
        //let iinit = iinit + ((MI_SEGMENT_SIZE * ((r>>17) & 0xFFFFF)) % MI_HINT_AREA);

        let expected = hint.wrapping_add(size);
        aligned_base_cas(expected, iinit);
        hint = aligned_base_add(size);
    }

    if hint % try_alignment != 0 {
        return 0;
    }
    return hint;
}

#[verifier::external_body]
fn unix_mmapx(
    hint: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
) -> (res: (*mut u8, Tracked<MemChunk>))
{
    if hint.addr()  == 0 && INTPTR_SIZE >= 8 {
        let hinti = os_get_aligned_hint(try_alignment, size);
        let hint = hint.with_addr(hinti);
        if hint.addr() != 0 {
            let (p, Tracked(mem)) = if prot_rw {
                mmap_prot_read_write(hint, size)
            } else {
                mmap_prot_none(hint, size)
            };
            if p.addr() != MAP_FAILED {
                return (p, Tracked(mem));
            }
        }
    }
    let (p, Tracked(mem)) = if prot_rw {
        mmap_prot_read_write(hint, size)
    } else {
        mmap_prot_none(hint, size)
    };
    if p.addr() != MAP_FAILED {
        return (p, Tracked(mem));
    }

    return (core::ptr::null_mut(), Tracked(mem));
}

}

