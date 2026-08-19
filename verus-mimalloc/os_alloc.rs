use core::intrinsics::{unlikely, likely};
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_basic};
use vstd::prelude::*;
use crate::config::*;
use crate::os_mem::*;
use crate::os_mem_util::lemma_os_exact_range_contains_subrange;
use crate::layout::*;
use crate::types::todo;


verus!{

pub open spec fn os_mem_alloc_alignment_ok(alignment: usize) -> bool {
    &&& alignment as int >= page_size()
    &&& (alignment & sub(alignment, 1usize)) == 0usize
}

pub fn os_alloc_aligned_offset(
    size: usize,
    alignment: usize,
    offset: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        offset == 0 && size != 0 ==> size <= SEGMENT_SIZE as usize,
        offset == 0 && size != 0 ==> (alignment as int) + page_size() - 1 <= usize::MAX as int,
    ensures
        offset > SEGMENT_SIZE as usize ==> res.0.addr() == 0,
        offset > SEGMENT_SIZE as usize ==> res.1 == allow_large,
        offset == 0 && size == 0 ==> res.0.addr() == 0,
        offset == 0 && size == 0 ==> res.1 == allow_large,
        offset == 0 && size != 0 && res.0.addr() != 0 ==> res.0 as int % page_size() == 0,
        offset == 0 && size != 0 && res.0.addr() != 0 ==>
            res.0 as int + size as int + page_size() - 1 <= usize::MAX as int,
        offset == 0 && size != 0 && res.0.addr() != 0 ==> res.2@.wf(),
        offset == 0 && size != 0 && res.0.addr() != 0 ==> res.2@.os_has_range(res.0 as int, size as int),
        offset == 0 && size == SEGMENT_SIZE as usize && res.0.addr() != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.2@.os_exact_range(res.0 as int, size as int),
        offset == 0 && size != 0 && res.0.addr() != 0 && request_commit ==> res.2@.os_has_range_read_write(res.0 as int, size as int),
        offset == 0 && size != 0 && res.0.addr() != 0 && request_commit ==> res.2@.has_pointsto_for_all_read_write(),
        offset == 0 && size != 0 && res.0.addr() != 0 && !request_commit ==> res.2@.os_has_range_no_read_write(res.0 as int, size as int),
        offset == 0 && size != 0 && res.0.addr() != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() % alignment == 0,
        offset == 0 && size != 0 && res.0.addr() != 0 ==> res.0@.provenance == res.2@.points_to.provenance(),
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

#[verifier::rlimit(200)]
#[verus_verify]
pub fn os_good_alloc_size(size: usize) -> (res: usize)
    ensures
        res >= size,
        size <= SEGMENT_SIZE as usize ==> res <= SEGMENT_SIZE as usize,
        size <= SEGMENT_SIZE as usize ==> res as int % page_size() == 0,
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

    proof {
        assert(page_size() == 4096) by(compute_only);
        assert(kib == 1024);
        assert(mib == 1048576);
        assert(64 * kib == 65536);
        assert(256 * kib == 262144);
        assert(4 * mib == 4194304);
        assert(SEGMENT_SIZE as int == 33554432) by(compute_only);

        if size < 512 * kib {
            assert(align_size == page_size());
            assert(align_size == 4096);
            assert(align_size <= 4194304);
            assert((align_size as int) % page_size() == 0);
            assert((SEGMENT_SIZE as int) % 4096 == 0) by(compute_only);
            assert((SEGMENT_SIZE as int) % (align_size as int) == 0);
        } else if size < 2 * mib {
            assert(align_size == 64 * kib);
            assert(align_size == 65536);
            assert(align_size <= 4194304);
            assert((align_size as int) % page_size() == 0);
            assert((SEGMENT_SIZE as int) % 65536 == 0) by(compute_only);
            assert((SEGMENT_SIZE as int) % (align_size as int) == 0);
        } else if size < 8 * mib {
            assert(align_size == 256 * kib);
            assert(align_size == 262144);
            assert(align_size <= 4194304);
            assert((align_size as int) % page_size() == 0);
            assert((SEGMENT_SIZE as int) % 262144 == 0) by(compute_only);
            assert((SEGMENT_SIZE as int) % (align_size as int) == 0);
        } else if size < 32 * mib {
            assert(align_size == mib);
            assert(align_size == 1048576);
            assert(align_size <= 4194304);
            assert((align_size as int) % page_size() == 0);
            assert((SEGMENT_SIZE as int) % 1048576 == 0) by(compute_only);
            assert((SEGMENT_SIZE as int) % (align_size as int) == 0);
        } else {
            assert(align_size == 4 * mib);
            assert(align_size == 4194304);
            assert(align_size <= 4194304);
            assert((align_size as int) % page_size() == 0);
            assert((SEGMENT_SIZE as int) % 4194304 == 0) by(compute_only);
            assert((SEGMENT_SIZE as int) % (align_size as int) == 0);
        }

        assert(align_size > 0);
        assert(align_size <= 4194304);
        assert((align_size as int) % page_size() == 0);
        assert((SEGMENT_SIZE as int) % (align_size as int) == 0);
    }

    if unlikely(size >= usize::MAX - align_size) {
        proof {
            if size <= SEGMENT_SIZE as usize {
                const_facts();
                assert(align_size as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
                    requires
                        align_size <= 4194304,
                        SEGMENT_SIZE as int == 33554432;
                assert(size as int <= SEGMENT_SIZE as int);
                assert((SEGMENT_SIZE as int) + (SEGMENT_SIZE as int) < usize::MAX as int) by(compute_only);
                assert((size as int) + (align_size as int) < usize::MAX as int) by(nonlinear_arith)
                    requires
                        size as int <= SEGMENT_SIZE as int,
                        align_size as int <= SEGMENT_SIZE as int,
                        (SEGMENT_SIZE as int) + (SEGMENT_SIZE as int) < usize::MAX as int;
                assert((size as int) < (usize::MAX as int) - (align_size as int)) by(nonlinear_arith)
                    requires
                        (size as int) + (align_size as int) < usize::MAX as int;
                assert(((usize::MAX - align_size) as int) == (usize::MAX as int) - (align_size as int)) by(bit_vector);
                assert((usize::MAX - align_size) as int <= size as int);
                assert(false) by(nonlinear_arith)
                    requires
                        (size as int) < (usize::MAX as int) - (align_size as int),
                        ((usize::MAX - align_size) as int) == (usize::MAX as int) - (align_size as int),
                        (usize::MAX - align_size) as int <= size as int;
            }
        }
        size
    } else {
        proof {
            assert(size < usize::MAX - align_size);
            assert((size as int) < ((usize::MAX - align_size) as int));
            assert(((usize::MAX - align_size) as int) == ((usize::MAX as int) - (align_size as int))) by(bit_vector);
            assert((size as int) < ((usize::MAX as int) - (align_size as int))) by(nonlinear_arith)
                requires
                    (size as int) < ((usize::MAX - align_size) as int),
                    ((usize::MAX - align_size) as int) == ((usize::MAX as int) - (align_size as int));
            assert((size as int) + (align_size as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    (size as int) < ((usize::MAX as int) - (align_size as int));
            assert((size as int) + (align_size as int) - 1 <= usize::MAX as int) by(nonlinear_arith)
                requires
                    (size as int) + (align_size as int) <= usize::MAX as int;
        }
        let x = align_up(size, align_size);
        proof {
            assert(size <= x);
            if size <= SEGMENT_SIZE as usize {
                const_facts();
                assert(0 <= size as int);
                assert(size as int <= SEGMENT_SIZE as int);
                assert(size as int <= x as int);
                lemma_round_multiple_le_cap(x as int, size as int, align_size as int, SEGMENT_SIZE as int);
                assert(x as int <= SEGMENT_SIZE as int);
                assert((SEGMENT_SIZE as usize) as int == SEGMENT_SIZE as int);
                assert(x <= SEGMENT_SIZE as usize);
                assert(page_size() > 0);
                lemma_multiple_of_multiple(x as int, align_size as int, page_size());
            }
        }
        return x;
    }
}

pub fn os_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size != 0 ==> size <= SEGMENT_SIZE as usize,
        size != 0 ==> (alignment as int) + page_size() - 1 <= usize::MAX as int,
    ensures
        size == 0 ==> res.0.addr() == 0,
        size == 0 ==> res.1 == allow_large,
        size != 0 && res.0.addr() != 0 ==> res.0 as int % page_size() == 0,
        size != 0 && res.0.addr() != 0 ==>
            res.0 as int + size as int + page_size() - 1 <= usize::MAX as int,
        size != 0 && res.0.addr() != 0 ==> res.2@.wf(),
        size != 0 && res.0.addr() != 0 ==> res.2@.os_has_range(res.0 as int, size as int),
        size == SEGMENT_SIZE as usize && res.0.addr() != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.2@.os_exact_range(res.0 as int, size as int),
        size != 0 && res.0.addr() != 0 && request_commit ==> res.2@.os_has_range_read_write(res.0 as int, size as int),
        size != 0 && res.0.addr() != 0 && request_commit ==> res.2@.has_pointsto_for_all_read_write(),
        size != 0 && res.0.addr() != 0 && !request_commit ==> res.2@.os_has_range_no_read_write(res.0 as int, size as int),
        size != 0 && res.0.addr() != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() % alignment == 0,
        size != 0 && res.0.addr() != 0 ==> res.0@.provenance == res.2@.points_to.provenance(),
{
    if size == 0 {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }
    proof {
        assert(size != 0);
        assert(size <= SEGMENT_SIZE as usize);
        assert(page_size() == 4096) by(compute_only);
        assert(page_size() > 0);
        assert((alignment as int) + page_size() - 1 <= usize::MAX as int);
    }
    let size1 = os_good_alloc_size(size);
    let alignment1 = align_up(alignment, get_page_size());
    proof {
        assert(size1 <= SEGMENT_SIZE as usize);
        assert(size1 as int % page_size() == 0);
    }
    proof {
        assert(size1 >= size);
        assert(size1 != 0);
    }
    proof {
        if os_mem_alloc_alignment_ok(alignment) {
            assert(page_size() == 4096) by(compute_only);
            assert(alignment >= 4096usize);
            assert(alignment != 0);
            assert((alignment & sub(alignment, 1usize)) == 0usize);
            assert(alignment % 4096usize == 0usize) by(bit_vector)
                requires
                    alignment >= 4096usize,
                    (alignment & sub(alignment, 1usize)) == 0usize;
            assert((alignment as int) % page_size() == 0) by(nonlinear_arith)
                requires
                    alignment % 4096usize == 0usize,
                    page_size() == 4096;
            lemma_round_multiple_le_cap(alignment1 as int, alignment as int, page_size(), alignment as int);
            assert(alignment1 <= alignment);
            assert(alignment1 == alignment);
        }
    }
    os_mem_alloc_aligned(size1, alignment1, request_commit, allow_large)
}

pub fn os_mem_alloc_aligned(
    size: usize,
    alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size != 0 ==> size <= SEGMENT_SIZE as usize,
        size != 0 ==> size as int % page_size() == 0,
    ensures
        size == 0 ==> res.0.addr() == 0,
        !os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() == 0,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() != 0,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() != MAP_FAILED,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.1 == false,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.2@.wf(),
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.2@.os_exact_range(res.0 as int, size as int),
        size != 0 && os_mem_alloc_alignment_ok(alignment) && request_commit ==> res.2@.os_has_range_read_write(res.0 as int, size as int),
        size != 0 && os_mem_alloc_alignment_ok(alignment) && request_commit ==> res.2@.has_pointsto_for_all_read_write(),
        size != 0 && os_mem_alloc_alignment_ok(alignment) && !request_commit ==> res.2@.os_has_range_no_read_write(res.0 as int, size as int),
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() + size < usize::MAX,
        size != 0 && os_mem_alloc_alignment_ok(alignment) && request_commit ==> res.0 as int % page_size() == 0,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0@.provenance == res.2@.points_to.provenance(),
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0.addr() % alignment == 0,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==> res.0 as int % page_size() == 0,
        size != 0 && os_mem_alloc_alignment_ok(alignment) ==>
            res.0 as int + size as int + page_size() - 1 <= usize::MAX as int,
{
    let mut allow_large = allow_large;
    if !request_commit {
        allow_large = false;
    }

    if (!(alignment >= get_page_size() && ((alignment & (alignment - 1)) == 0))) {
        proof {
            assert(page_size() == 4096) by(compute_only);
            assert(!os_mem_alloc_alignment_ok(alignment));
        }
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    proof {
        assert(page_size() == 4096) by(compute_only);
        assert(alignment >= 4096usize);
        assert(alignment != 0);
        assert((alignment & sub(alignment, 1usize)) == 0usize);
        assert(alignment % 4096usize == 0usize) by(bit_vector)
            requires
                alignment >= 4096usize,
                (alignment & sub(alignment, 1usize)) == 0usize;
        assert(alignment as int % 4096 == 0) by(nonlinear_arith)
            requires alignment % 4096usize == 0usize;
        assert(alignment as int % page_size() == 0);
        assert(os_mem_alloc_alignment_ok(alignment));
    }

    let (p, is_large, Tracked(mem)) = os_mem_alloc(size, alignment, request_commit, allow_large);
    if p.addr() == 0 {
        return (p, is_large, Tracked(mem));
    }

    if p.addr() % alignment != 0 {
        todo();
    }

    proof {
        if size != 0 && os_mem_alloc_alignment_ok(alignment) {
            assert(p.addr() % alignment == 0);
            assert(p as int == p.addr() as int);
            assert((p.addr() as int) % (alignment as int) == 0) by(nonlinear_arith)
                requires
                    p.addr() % alignment == 0,
                    alignment != 0;
            assert(p as int % alignment as int == 0);
            assert(page_size() > 0);
            lemma_multiple_of_multiple(p as int, alignment as int, page_size());
            lemma_page_aligned_end_fits(p as int, size as int);
        }
    }

    (p, is_large, Tracked(mem))
}

fn os_mem_alloc(
    size: usize,
    try_alignment: usize,
    request_commit: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size != 0 ==> size <= SEGMENT_SIZE as usize,
        size != 0 ==> size as int % page_size() == 0,
        size != 0 ==> try_alignment != 0,
        size != 0 ==> try_alignment as int % page_size() == 0,
    ensures
        size == 0 ==> res.0.addr() == 0,
        size == 0 ==> res.1 == allow_large,
        size != 0 ==> res.0.addr() != 0,
        size != 0 ==> res.0.addr() != MAP_FAILED,
        size != 0 ==> res.1 == false,
        size != 0 ==> res.2@.wf(),
        size != 0 ==> res.2@.os_exact_range(res.0 as int, size as int),
        size != 0 && request_commit ==> res.2@.os_has_range_read_write(res.0 as int, size as int),
        size != 0 && request_commit ==> res.2@.has_pointsto_for_all_read_write(),
        size != 0 && !request_commit ==> res.2@.os_has_range_no_read_write(res.0 as int, size as int),
        size != 0 ==> res.0.addr() + size < usize::MAX,
        size != 0 && request_commit ==> res.0 as int % page_size() == 0,
        size != 0 ==> res.0@.provenance == res.2@.points_to.provenance(),
{
    if size == 0 {
        return (core::ptr::null_mut(), allow_large, Tracked(MemChunk::empty()));
    }

    let mut allow_large = allow_large;
    if !request_commit {
        allow_large = false;
    }

    let mut try_alignment = try_alignment;
    proof {
        assert(try_alignment != 0);
        assert(try_alignment as int % page_size() == 0);
    }
    if try_alignment == 0 { try_alignment = 1; }

    proof {
        assert(page_size() == 4096) by(compute_only);
        assert(core::ptr::null_mut::<u8>() as int == 0);
        assert(try_alignment as int % page_size() == 0);
    }

    unix_mmap(core::ptr::null_mut(), size, try_alignment, request_commit, false, allow_large)
}

#[verus_verify]
fn use_large_os_page(size: usize, alignment: usize) -> (b: bool)
    ensures b == false,
{
    false
}

fn unix_mmap(
    addr: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
    large_only: bool,
    allow_large: bool,
) -> (res: (*mut u8, bool, Tracked<MemChunk>))
    requires
        size <= SEGMENT_SIZE as usize,
        size as int % page_size() == 0,
        addr as int % page_size() == 0,
        try_alignment as int % page_size() == 0,
    ensures
        res.0.addr() != 0,
        res.0.addr() != MAP_FAILED,
        res.1 == false,
        res.2@.wf(),
        res.2@.os_exact_range(res.0 as int, size as int),
        prot_rw ==> res.2@.os_has_range_read_write(res.0 as int, size as int),
        prot_rw ==> res.2@.has_pointsto_for_all_read_write(),
        !prot_rw ==> res.2@.os_has_range_no_read_write(res.0 as int, size as int),
        res.0.addr() + size < usize::MAX,
        prot_rw ==> res.0 as int % page_size() == 0,
        res.0@.provenance == res.2@.points_to.provenance(),
{
    let is_large = true;
    if (large_only || use_large_os_page(size, try_alignment)) && allow_large {
        todo();
    }

    let is_large = false;
    proof {
        assert(size <= SEGMENT_SIZE as usize);
        assert(size as int % page_size() == 0);
        assert(addr as int % page_size() == 0);
        assert(try_alignment as int % page_size() == 0);
    }
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
#[verus_verify]
fn aligned_base_add(s: usize) -> usize
{
    ALIGNED_BASE.fetch_add(s, core::sync::atomic::Ordering::AcqRel)
}

#[inline]
#[verus_verify]
fn aligned_base_cas(s: usize, t: usize)
{
    let _ = ALIGNED_BASE.compare_exchange(s, t, core::sync::atomic::Ordering::AcqRel, core::sync::atomic::Ordering::Acquire);
}

const HINT_BASE: usize = (2 as usize) << (40 as usize);
const HINT_AREA: usize = (4 as usize) << (40 as usize);
const HINT_MAX: usize = (30 as usize) << (40 as usize);

#[verus_verify]
fn os_get_aligned_hint(try_alignment: usize, size: usize) -> (hint: usize)
    requires
        size <= SEGMENT_SIZE as usize,
    ensures
        hint != 0 ==> try_alignment > 0,
        hint != 0 ==> hint as int % try_alignment as int == 0,
        try_alignment > 0 && hint != 0 ==> hint as int % try_alignment as int == 0,
{

    if try_alignment <= 1 || try_alignment > SEGMENT_SIZE as usize {
        return 0;
    }

    proof {
        const_facts();
        assert(size as int <= SEGMENT_SIZE as int);
        assert((size as int) + ((SEGMENT_SIZE as usize) as int) - 1
            <= (SEGMENT_SIZE as int) + (SEGMENT_SIZE as int) - 1) by(nonlinear_arith)
            requires
                size as int <= SEGMENT_SIZE as int,
                (SEGMENT_SIZE as usize) as int == SEGMENT_SIZE as int;
        assert((size as int) + ((SEGMENT_SIZE as usize) as int) - 1 <= usize::MAX as int);
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

#[verifier::rlimit(200)]
proof fn lemma_multiple_of_multiple(x: int, y: int, z: int)
    requires
        z > 0,
        y > 0,
        x % y == 0,
        y % z == 0,
    ensures
        x % z == 0,
{
    lemma_fundamental_div_mod(x, y);
    lemma_fundamental_div_mod(y, z);
    let a = x / y;
    let b = y / z;
    assert(x == y * a);
    assert(y == z * b);
    assert(x == (z * b) * a);
    assert((z * b) * a == (b * a) * z) by(nonlinear_arith);
    assert(x == (b * a) * z);
    lemma_mod_multiples_basic(b * a, z);
}

#[verifier::rlimit(200)]
proof fn lemma_sum_page_aligned(a: int, b: int)
    requires
        a % page_size() == 0,
        b % page_size() == 0,
    ensures
        (a + b) % page_size() == 0,
{
    assert(page_size() == 4096) by(compute_only);
    assert(0 < page_size());
    lemma_fundamental_div_mod(a, page_size());
    lemma_fundamental_div_mod(b, page_size());
    let qa = a / page_size();
    let qb = b / page_size();
    assert(a == page_size() * qa);
    assert(b == page_size() * qb);
    assert(a + b == page_size() * qa + page_size() * qb) by(nonlinear_arith)
        requires
            a == page_size() * qa,
            b == page_size() * qb;
    assert(page_size() * qa + page_size() * qb == page_size() * (qa + qb)) by(nonlinear_arith);
    assert(a + b == page_size() * (qa + qb));
    lemma_mod_multiples_basic(qa + qb, page_size());
}

#[verifier::rlimit(200)]
proof fn lemma_page_aligned_end_fits(addr: int, len: int)
    requires
        0 <= addr,
        0 <= len,
        addr % page_size() == 0,
        len % page_size() == 0,
        addr + len < usize::MAX as int,
    ensures
        addr + len + page_size() - 1 <= usize::MAX as int,
{
    assert(page_size() == 4096) by(compute_only);
    assert(usize::MAX as int == 18446744073709551615) by(compute_only);
    let p = page_size();
    let cap = (usize::MAX as int) + 1;
    assert(cap == p * 4503599627370496) by(nonlinear_arith)
        requires
            p == 4096,
            usize::MAX as int == 18446744073709551615,
            cap == (usize::MAX as int) + 1;
    lemma_sum_page_aligned(addr, len);
    lemma_fundamental_div_mod(addr + len, p);
    lemma_fundamental_div_mod(cap, p);
    assert(0 < p);
    assert(cap == 4503599627370496 * p) by(nonlinear_arith)
        requires
            cap == p * 4503599627370496;
    lemma_mod_multiples_basic(4503599627370496, p);
    assert(cap % p == 0);
    let qe = (addr + len) / p;
    let qc = cap / p;
    assert(addr + len == p * qe);
    assert(cap == p * qc);
    assert(addr + len < cap) by(nonlinear_arith)
        requires
            addr + len < usize::MAX as int,
            cap == (usize::MAX as int) + 1;
    assert(qe < qc) by(nonlinear_arith)
        requires
            addr + len == p * qe,
            cap == p * qc,
            addr + len < cap,
            0 < p;
    assert(qe + 1 <= qc);
    assert(addr + len + p <= cap) by(nonlinear_arith)
        requires
            addr + len == p * qe,
            cap == p * qc,
            qe + 1 <= qc,
            0 < p;
    assert(addr + len + p - 1 <= usize::MAX as int) by(nonlinear_arith)
        requires
            addr + len + p <= cap,
            cap == (usize::MAX as int) + 1;
}

fn unix_mmapx(
    hint: *mut u8,
    size: usize,
    try_alignment: usize,
    prot_rw: bool,
) -> (res: (*mut u8, Tracked<MemChunk>))
    requires
        size <= SEGMENT_SIZE as usize,
        size as int % page_size() == 0,
        hint as int % page_size() == 0,
        try_alignment as int % page_size() == 0,
    ensures
        res.0.addr() != MAP_FAILED,
        res.0.addr() != 0 ==> res.1@.wf(),
        res.0.addr() != 0 ==> res.1@.os_exact_range(res.0 as int, size as int),
        res.0.addr() != 0 && prot_rw ==> res.1@.os_has_range_read_write(res.0 as int, size as int),
        res.0.addr() != 0 && prot_rw ==> res.1@.has_pointsto_for_all_read_write(),
        res.0.addr() != 0 && !prot_rw ==> res.1@.os_has_range_no_read_write(res.0 as int, size as int),
        res.0.addr() != 0 ==> res.0.addr() + size < usize::MAX,
        res.0.addr() != 0 && prot_rw ==> res.0 as int % page_size() == 0,
        res.0.addr() != 0 ==> res.0@.provenance == res.1@.points_to.provenance(),
{
    if hint.addr()  == 0 && INTPTR_SIZE >= 8 {
        let hinti = os_get_aligned_hint(try_alignment, size);
        let hint = hint.with_addr(hinti);
        if hint.addr() != 0 {
            proof {
                assert(page_size() == 4096) by(compute_only);
                assert(page_size() > 0);
                assert(hinti != 0);
                assert(try_alignment > 0);
                lemma_multiple_of_multiple(hinti as int, try_alignment as int, page_size());
                assert(hint as int == hinti as int);
                assert(hint as int % page_size() == 0);
            }
            let (p, Tracked(mem)) = if prot_rw {
                mmap_prot_read_write(hint, size)
            } else {
                mmap_prot_none(hint, size)
            };
            proof {
                if p.addr() != MAP_FAILED {
                    if prot_rw {
                        assert(mem.wf());
                        assert(mem.os_exact_range(p as int, size as int));
                        assert(mem.os_has_range_read_write(p as int, size as int));
                        assert(mem.has_pointsto_for_all_read_write());
                        assert(p.addr() + size < usize::MAX);
                        assert(p as int % page_size() == 0);
                        assert(p@.provenance == mem.points_to.provenance());
                    } else {
                        assert(mem.wf());
                        assert(mem.os_exact_range(p as int, size as int));
                        assert(mem.os_has_range_no_read_write(p as int, size as int));
                        assert(p.addr() + size < usize::MAX);
                        assert(p@.provenance == mem.points_to.provenance());
                    }
                }
            }
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
    proof {
        if p.addr() != MAP_FAILED {
            if prot_rw {
                assert(mem.wf());
                assert(mem.os_exact_range(p as int, size as int));
                assert(mem.os_has_range_read_write(p as int, size as int));
                assert(mem.has_pointsto_for_all_read_write());
                assert(p.addr() + size < usize::MAX);
                assert(p as int % page_size() == 0);
                assert(p@.provenance == mem.points_to.provenance());
            } else {
                assert(mem.wf());
                assert(mem.os_exact_range(p as int, size as int));
                assert(mem.os_has_range_no_read_write(p as int, size as int));
                assert(p.addr() + size < usize::MAX);
                assert(p@.provenance == mem.points_to.provenance());
            }
        }
    }
    if p.addr() != MAP_FAILED {
        return (p, Tracked(mem));
    }

    proof {
        assert(MAP_FAILED == usize::MAX);
        assert(0usize != MAP_FAILED);
        assert(core::ptr::null_mut::<u8>().addr() == 0);
    }
    return (core::ptr::null_mut(), Tracked(mem));
}

}

