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
    requires alignment + page_size() <= usize::MAX,
        size as int % page_size() == 0,
        size == SEGMENT_SIZE,
        alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_has_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
            && (alignment != 0 ==> (addr as int + offset) % alignment as int == 0)
        )
    })
{
    unimplemented!()
}

#[verifier::external_body]
pub fn os_good_alloc_size(size: usize) -> (res: usize)
    requires size as int % page_size() == 0,
    ensures res as int % page_size() == 0,
      res >= size,
      size == SEGMENT_SIZE ==> res == SEGMENT_SIZE
{
    unimplemented!()
}

#[verifier::external_body]
pub fn os_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        alignment + page_size() <= usize::MAX,
        size == SEGMENT_SIZE,
        size as int % page_size() == 0,
        alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_has_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
            && (alignment != 0 ==> addr as int % alignment as int == 0)
        )
    })
{
    unimplemented!()
}

#[verifier::external_body]
pub fn os_mem_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_exact_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
            && (alignment != 0 ==> addr as int % alignment as int == 0)
        )
    })
{
    unimplemented!()
}

#[verifier::external_body]
fn os_mem_alloc(
    size: usize,
    try_alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        try_alignment == 1 || try_alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && mem@.os_exact_range(addr as int, size as int)
            && (request_commit ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (request_commit ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!request_commit ==> mem@.os_has_range_no_read_write(addr as int, size as int))
        )
    })
{
    unimplemented!()
}

#[verifier::external_body]
fn use_large_os_page(size: usize, alignment: usize) -> bool
{
    unimplemented!()
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
    requires
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        try_alignment == 1 || try_alignment as int % page_size() == 0,
    ensures ({ let (addr, is_large, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.points_to.provenance() == addr@.provenance
            && mem@.os_exact_range(addr as int, size as int)
            && addr as int + size <= usize::MAX
            && (prot_rw ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (prot_rw ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!prot_rw ==> mem@.os_has_range_no_read_write(addr as int, size as int))
        )
    })
{
    unimplemented!()
}

exec static ALIGNED_BASE: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

#[verifier::external_body]
#[inline]
fn aligned_base_add(s: usize) -> usize
{
    unimplemented!()
}

#[verifier::external_body]
#[inline]
fn aligned_base_cas(s: usize, t: usize)
{
    unimplemented!()
}

const HINT_BASE: usize = (2 as usize) << (40 as usize);
const HINT_AREA: usize = (4 as usize) << (40 as usize);
const HINT_MAX: usize = (30 as usize) << (40 as usize);

#[verifier::external_body]
fn os_get_aligned_hint(try_alignment: usize, size: usize) -> (hint: usize)
    requires size <= SEGMENT_SIZE,
    ensures try_alignment != 0 ==> hint % try_alignment == 0,
      try_alignment <= 1 ==> hint == 0
{
    unimplemented!()
}

#[verifier::external_body]
fn unix_mmapx(
    hint: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
) -> (res: (*mut u8, Tracked<MemChunk>))
    requires
        hint as int % page_size() == 0,
        size as int % page_size() == 0,
        size <= SEGMENT_SIZE,
        try_alignment > 1 ==> try_alignment as int % page_size() == 0,
    ensures ({ let (addr, mem) = res;
        addr as int != 0 ==> (
            mem@.wf()
            && mem@.os_exact_range(addr as int, size as int)
            && mem@.points_to.provenance() == addr@.provenance
            && addr as int + size <= usize::MAX
            && (prot_rw ==> mem@.os_has_range_read_write(addr as int, size as int))
            && (prot_rw ==> mem@.pointsto_has_range(addr as int, size as int))
            && (!prot_rw ==> mem@.os_has_range_no_read_write(addr as int, size as int))
        )
    })
{
    unimplemented!()
}

}

