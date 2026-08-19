#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::arithmetic::div_mod::{
    group_mod_properties, lemma_add_mod_noop, lemma_div_is_ordered, lemma_div_multiples_vanish,
    lemma_div_pos_is_pos, lemma_fundamental_div_mod, lemma_indistinguishable_quotients,
    lemma_div_multiples_vanish_fancy, lemma_mod_multiples_basic,
};

use crate::commit_mask::*;
use crate::types::*;
use crate::layout::*;
use crate::config::*;
use crate::segment::*;
use crate::os_mem_util::*;
use crate::tokens::*;
use crate::os_mem::*;

verus!{

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_constants()
    ensures
        COMMIT_SIZE as usize == SLICE_SIZE as usize,
        COMMIT_SIZE as usize == 65536,
        SEGMENT_SIZE as usize == 33554432,
        COMMIT_MASK_BITS as usize == 512,
        SEGMENT_SIZE as usize == COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize,
        SLICE_SIZE as usize <= SEGMENT_SIZE as usize,
        2 * SEGMENT_SIZE as usize + COMMIT_SIZE as usize <= usize::MAX,
{
    assert(COMMIT_SIZE == SLICE_SIZE) by(compute_only);
    assert(COMMIT_SIZE == 65536) by(compute_only);
    assert(SEGMENT_SIZE == 33554432) by(compute_only);
    assert(COMMIT_MASK_BITS == 512) by(compute_only);
    assert(SEGMENT_SIZE == COMMIT_MASK_BITS * COMMIT_SIZE) by(compute_only);
}


spec fn segment_commit_mask_bit_bytes(segment_id: SegmentId, i: int) -> Set<int> {
    let start = segment_start(segment_id);
    Set::range(start + i * COMMIT_SIZE, start + (i + 1) * COMMIT_SIZE)
}

spec fn segment_commit_mask_byte_bit(segment_id: SegmentId, addr: int) -> int {
    (addr - segment_start(segment_id)) / COMMIT_SIZE as int
}

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_bit_bytes_inverse(segment_id: SegmentId, i: int, addr: int)
    requires
        segment_commit_mask_bit_bytes(segment_id, i).contains(addr),
    ensures
        segment_commit_mask_byte_bit(segment_id, addr) == i,
{
    let start = segment_start(segment_id);
    let d = COMMIT_SIZE as int;
    assert(COMMIT_SIZE as int > 0) by(compute_only);
    assert(d > 0);
    assert(start + i * d <= addr < start + (i + 1) * d);
    let x = addr - start;
    assert(i * d <= x < (i + 1) * d) by(nonlinear_arith)
        requires
            start + i * d <= addr,
            addr < start + (i + 1) * d,
            x == addr - start,
    { }
    lemma_div_multiples_vanish(i, d);
    assert((i * d) / d == i) by {
        assert(i * d == d * i) by(nonlinear_arith);
    }
    lemma_div_is_ordered(i * d, x, d);
    assert(i <= x / d);
    assert(x <= i * d + d - 1) by(nonlinear_arith)
        requires
            x < (i + 1) * d;
    lemma_div_is_ordered(x, i * d + d - 1, d);
    lemma_div_multiples_vanish_fancy(i, d - 1, d);
    assert((i * d + d - 1) / d == i) by {
        assert(i * d + d - 1 == d * i + (d - 1)) by(nonlinear_arith);
    }
    assert(x / d <= i);
}

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_bytes_contains(mask: &CommitMask, segment_id: SegmentId, addr: int)
    ensures
        mask.bytes(segment_id).contains(addr) <==>
            mask@.contains(segment_commit_mask_byte_bit(segment_id, addr))
                && segment_commit_mask_bit_bytes(segment_id, segment_commit_mask_byte_bit(segment_id, addr)).contains(addr),
{
    reveal(CommitMask::bytes);
    let start = segment_start(segment_id);
    assert forall |i: int, addr: int| #[trigger] mask@.contains(i) &&
        Set::range(start + i * COMMIT_SIZE, start + (i + 1) * COMMIT_SIZE).contains(addr) implies
        #[trigger] ((addr - start) / COMMIT_SIZE as int) == i by {
        assert(segment_commit_mask_bit_bytes(segment_id, i).contains(addr));
        lemma_segment_commit_mask_bit_bytes_inverse(segment_id, i, addr);
    }
    mask@.lemma_map_flatten_by_contains(
        |i: int| Set::range(start + i * COMMIT_SIZE, start + (i + 1) * COMMIT_SIZE),
        |addr: int| (addr - start) / COMMIT_SIZE as int,
        addr,
    );
}

#[verifier::rlimit(200)]
pub proof fn lemma_segment_commit_mask_bytes_subset(mask: &CommitMask, other: &CommitMask, segment_id: SegmentId)
    requires
        mask@ <= other@,
    ensures
        mask.bytes(segment_id) <= other.bytes(segment_id),
{
    assert forall |addr: int| #[trigger] mask.bytes(segment_id).contains(addr) implies
        other.bytes(segment_id).contains(addr) by {
        lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
        let bit = segment_commit_mask_byte_bit(segment_id, addr);
        assert(mask@.contains(bit));
        assert(segment_commit_mask_bit_bytes(segment_id, bit).contains(addr));
        assert(other@.contains(bit));
        lemma_segment_commit_mask_bytes_contains(other, segment_id, addr);
    }
}





#[verifier::rlimit(200)]
pub proof fn lemma_commit_mask_bytes_same_segment_start(
    mask: &CommitMask,
    sid1: SegmentId,
    sid2: SegmentId,
)
    requires
        segment_start(sid1) == segment_start(sid2),
    ensures
        mask.bytes(sid1) =~= mask.bytes(sid2),
{
    reveal(CommitMask::bytes);
    assert(mask.bytes(sid1) =~= mask.bytes(sid2));
}

#[verifier::rlimit(200)]
pub proof fn lemma_empty_commit_mask_bytes(mask: &CommitMask, segment_id: SegmentId)
    requires
        mask@ =~= Set::empty(),
    ensures
        mask.bytes(segment_id) =~= Set::empty(),
{
    assert forall |addr: int| #[trigger] mask.bytes(segment_id).contains(addr) implies false by {
        lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
        let bit = segment_commit_mask_byte_bit(segment_id, addr);
        assert(mask@.contains(bit));
        assert(false);
    }
}

#[verifier::rlimit(200)]
pub proof fn lemma_segment_info_range_subset_commit_mask_bytes(
    mask: &CommitMask,
    segment_id: SegmentId,
)
    requires
        Set::range(0, 1) <= mask@,
    ensures
        segment_info_range(segment_id) <= mask.bytes(segment_id),
{
    assert forall |addr: int| #[trigger] segment_info_range(segment_id).contains(addr) implies
        mask.bytes(segment_id).contains(addr) by {
        assert(segment_start(segment_id) <= addr < segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + SIZEOF_PAGE_HEADER * (SLICES_PER_SEGMENT + 1));
        assert(SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1) <= COMMIT_SIZE as int) by(compute_only);
        assert(segment_start(segment_id) <= addr < segment_start(segment_id) + COMMIT_SIZE as int) by(nonlinear_arith)
            requires
                segment_start(segment_id) <= addr,
                addr < segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + SIZEOF_PAGE_HEADER * (SLICES_PER_SEGMENT + 1),
                SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1) <= COMMIT_SIZE as int;
        assert(segment_commit_mask_bit_bytes(segment_id, 0).contains(addr));
        assert(mask@.contains(0));
        lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
    }
}

#[verifier::rlimit(200)]
pub proof fn lemma_segment_commit_mask_bytes_subset_of_rw_range(
    mask: &CommitMask,
    segment_id: SegmentId,
    mem: MemChunk,
    lo: int,
    hi: int,
)
    requires
        mask@ <= Set::range(lo, hi),
        mem.os_has_range_read_write(
            segment_start(segment_id) + lo * COMMIT_SIZE as int,
            (hi - lo) * COMMIT_SIZE as int),
    ensures
        mask.bytes(segment_id) <= mem.os_rw_bytes(),
{
    assert forall |addr: int| #[trigger] mask.bytes(segment_id).contains(addr) implies
        mem.os_rw_bytes().contains(addr) by {
        lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
        let bit = segment_commit_mask_byte_bit(segment_id, addr);
        assert(mask@.contains(bit));
        assert(lo <= bit < hi);
        assert(segment_commit_mask_bit_bytes(segment_id, bit).contains(addr));
        let start = segment_start(segment_id);
        assert(start + bit * COMMIT_SIZE as int <= addr < start + (bit + 1) * COMMIT_SIZE as int);
        assert(start + lo * COMMIT_SIZE as int <= addr < start + hi * COMMIT_SIZE as int) by(nonlinear_arith)
            requires
                lo <= bit,
                bit < hi,
                start + bit * COMMIT_SIZE as int <= addr,
                addr < start + (bit + 1) * COMMIT_SIZE as int,
                0 <= COMMIT_SIZE as int;
        assert(start + lo * COMMIT_SIZE as int + (hi - lo) * COMMIT_SIZE as int == start + hi * COMMIT_SIZE as int) by(nonlinear_arith);
        assert(set_int_range(
            start + lo * COMMIT_SIZE as int,
            start + lo * COMMIT_SIZE as int + (hi - lo) * COMMIT_SIZE as int).contains(addr));
        assert(set_int_range(
            start + lo * COMMIT_SIZE as int,
            start + hi * COMMIT_SIZE as int).contains(addr));
    }
}

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_view_subset_from_bytes_subset(mask: &CommitMask, other: &CommitMask, segment_id: SegmentId)
    requires
        mask.bytes(segment_id) <= other.bytes(segment_id),
    ensures
        mask@ <= other@,
{
    assert forall |bit: int| #[trigger] mask@.contains(bit) implies other@.contains(bit) by {
        let start = segment_start(segment_id);
        let d = COMMIT_SIZE as int;
        let addr = start + bit * d;
        assert(COMMIT_SIZE as int > 0) by(compute_only);
        assert(d > 0);
        assert(segment_commit_mask_bit_bytes(segment_id, bit).contains(addr));
        lemma_segment_commit_mask_bit_bytes_inverse(segment_id, bit, addr);
        assert(segment_commit_mask_byte_bit(segment_id, addr) == bit);
        lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
        assert(mask.bytes(segment_id).contains(addr));
        assert(other.bytes(segment_id).contains(addr));
        lemma_segment_commit_mask_bytes_contains(other, segment_id, addr);
    }
}

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_bytes_disjoint(mask: &CommitMask, other: &CommitMask, segment_id: SegmentId)
    requires
        mask@.disjoint(other@),
    ensures
        mask.bytes(segment_id).disjoint(other.bytes(segment_id)),
{
    assert forall |addr: int| #[trigger] mask.bytes(segment_id).contains(addr) implies
        !other.bytes(segment_id).contains(addr) by {
        lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
        lemma_segment_commit_mask_bytes_contains(other, segment_id, addr);
        let bit = segment_commit_mask_byte_bit(segment_id, addr);
        assert(mask@.contains(bit));
        if other.bytes(segment_id).contains(addr) {
            assert(other@.contains(bit));
            assert(false);
        }
    }
}

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_bytes_range(mask: &CommitMask, segment_id: SegmentId, lo: int, hi: int)
    requires
        0 <= lo <= hi <= COMMIT_MASK_BITS as int,
        mask@ =~= Set::range(lo, hi),
    ensures
        mask.bytes(segment_id) =~= set_int_range(
            segment_start(segment_id) + lo * COMMIT_SIZE as int,
            segment_start(segment_id) + hi * COMMIT_SIZE as int,
        ),
{
    let start = segment_start(segment_id);
    let d = COMMIT_SIZE as int;
    assert(COMMIT_SIZE as int > 0) by(compute_only);
    assert(d > 0);
    assert forall |addr: int| #[trigger] mask.bytes(segment_id).contains(addr) ==
        set_int_range(start + lo * d, start + hi * d).contains(addr) by {
        if mask.bytes(segment_id).contains(addr) {
            lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
            let bit = segment_commit_mask_byte_bit(segment_id, addr);
            assert(lo <= bit < hi);
            assert(segment_commit_mask_bit_bytes(segment_id, bit).contains(addr));
            assert(start + bit * d <= addr < start + (bit + 1) * d);
            assert(start + lo * d <= addr) by(nonlinear_arith)
                requires
                    lo <= bit,
                    0 < d,
                    start + bit * d <= addr;
            assert(addr < start + hi * d) by(nonlinear_arith)
                requires
                    bit < hi,
                    0 < d,
                    addr < start + (bit + 1) * d;
        }
        if set_int_range(start + lo * d, start + hi * d).contains(addr) {
            let bit = segment_commit_mask_byte_bit(segment_id, addr);
            assert(start + lo * d <= addr < start + hi * d);
            assert(lo * d <= addr - start) by(nonlinear_arith)
                requires start + lo * d <= addr;
            lemma_div_is_ordered(lo * d, addr - start, d);
            lemma_div_multiples_vanish(lo, d);
            assert((d * lo) / d == lo);
            assert(d * lo == lo * d) by(nonlinear_arith);
            assert(lo <= bit);
            if hi == lo {
                assert(false) by(nonlinear_arith)
                    requires
                        start + lo * d <= addr,
                        addr < start + hi * d,
                        hi == lo;
            } else {
                assert(lo < hi);
                assert(0 < hi) by(nonlinear_arith) requires 0 <= lo, lo < hi;
                assert(addr - start <= hi * d - 1) by(nonlinear_arith)
                    requires addr < start + hi * d;
                lemma_div_is_ordered(addr - start, hi * d - 1, d);
                lemma_mod_multiples_basic(hi - 1, d);
                assert(((hi - 1) * d) % d == 0);
                lemma_indistinguishable_quotients((hi - 1) * d, hi * d - 1, d);
                lemma_div_multiples_vanish(hi - 1, d);
                assert((hi * d - 1) / d == hi - 1);
                assert(bit <= hi - 1);
                assert(bit < hi);
            }
            lemma_fundamental_div_mod(addr - start, d);
            broadcast use group_mod_properties;
            assert(addr - start == d * bit + ((addr - start) % d));
            assert(0 <= (addr - start) % d < d);
            assert(start + bit * d <= addr) by(nonlinear_arith)
                requires
                    addr - start == d * bit + ((addr - start) % d),
                    0 <= (addr - start) % d;
            assert(addr < start + (bit + 1) * d) by(nonlinear_arith)
                requires
                    addr - start == d * bit + ((addr - start) % d),
                    (addr - start) % d < d;
            assert(segment_commit_mask_bit_bytes(segment_id, bit).contains(addr));
            assert(mask@.contains(bit));
            lemma_segment_commit_mask_bytes_contains(mask, segment_id, addr);
        }
    }
}

#[verifier::rlimit(200)]
proof fn lemma_commit_multiple_is_page_multiple(x: int)
    requires
        x % COMMIT_SIZE as int == 0,
    ensures
        x % page_size() == 0,
{
    assert(COMMIT_SIZE as int == 65536) by(compute_only);
    assert(page_size() == 4096) by(compute_only);
    assert(0 < COMMIT_SIZE as int);
    lemma_fundamental_div_mod(x, COMMIT_SIZE as int);
    let q = x / COMMIT_SIZE as int;
    assert(x == COMMIT_SIZE as int * q);
    assert(COMMIT_SIZE as int == page_size() * 16) by(nonlinear_arith)
        requires
            COMMIT_SIZE as int == 65536,
            page_size() == 4096;
    assert(x == page_size() * (16 * q)) by(nonlinear_arith)
        requires
            x == COMMIT_SIZE as int * q,
            COMMIT_SIZE as int == page_size() * 16;
    lemma_mod_multiples_basic(16 * q, page_size());
}

#[verifier::rlimit(200)]
proof fn lemma_aligned_between_same(x: int, aligned: int, unit: int)
    requires
        0 < unit,
        x % unit == 0,
        aligned % unit == 0,
        x <= aligned,
        aligned <= x + unit - 1,
    ensures
        aligned == x,
{
    if x < aligned {
        lemma_fundamental_div_mod(x, unit);
        lemma_fundamental_div_mod(aligned, unit);
        assert(x == unit * (x / unit));
        assert(aligned == unit * (aligned / unit));
        assert(x / unit < aligned / unit) by(nonlinear_arith)
            requires
                x == unit * (x / unit),
                aligned == unit * (aligned / unit),
                x < aligned,
                0 < unit;
        assert(x / unit + 1 <= aligned / unit);
        assert(x + unit <= aligned) by(nonlinear_arith)
            requires
                x == unit * (x / unit),
                aligned == unit * (aligned / unit),
                x / unit + 1 <= aligned / unit,
                0 < unit;
        assert(false) by(nonlinear_arith)
            requires
                x + unit <= aligned,
                aligned <= x + unit - 1;
    }
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

#[verifier::rlimit(200)]
proof fn lemma_segment_start_page_aligned(segment_id: SegmentId)
    ensures
        segment_start(segment_id) % page_size() == 0,
{
    lemma_segment_start_basics(segment_id);
    assert(SEGMENT_SIZE as int == 33554432) by(compute_only);
    assert(page_size() == 4096) by(compute_only);
    assert(0 < SEGMENT_SIZE as int);
    lemma_fundamental_div_mod(segment_start(segment_id), SEGMENT_SIZE as int);
    let q = segment_start(segment_id) / SEGMENT_SIZE as int;
    assert(segment_start(segment_id) == SEGMENT_SIZE as int * q);
    assert(SEGMENT_SIZE as int == page_size() * 8192) by(nonlinear_arith)
        requires
            SEGMENT_SIZE as int == 33554432,
            page_size() == 4096;
    assert(segment_start(segment_id) == page_size() * (8192 * q)) by(nonlinear_arith)
        requires
            segment_start(segment_id) == SEGMENT_SIZE as int * q,
            SEGMENT_SIZE as int == page_size() * 8192;
    lemma_mod_multiples_basic(8192 * q, page_size());
}

#[verifier::rlimit(200)]
proof fn lemma_commit_mask_bit_range(start: usize, full_size: usize)
    requires
        start as int % COMMIT_SIZE as int == 0,
        full_size as int % COMMIT_SIZE as int == 0,
        start as int + full_size as int <= SEGMENT_SIZE as int,
    ensures
        full_size / COMMIT_SIZE as usize <= COMMIT_MASK_BITS as usize,
        (start / COMMIT_SIZE as usize) as int + (full_size / COMMIT_SIZE as usize) as int
            <= COMMIT_MASK_BITS as int,
{
    lemma_segment_commit_mask_constants();
    let d = COMMIT_SIZE as usize;
    let bits = COMMIT_MASK_BITS as usize;
    let segsize = SEGMENT_SIZE as usize;
    assert(d > 0);
    assert(segsize == bits * d);
    assert(start as int + full_size as int <= segsize as int);
    assert(full_size as int <= segsize as int) by(nonlinear_arith)
        requires
            start as int + full_size as int <= segsize as int;
    assert((full_size / d) as int <= bits as int) by(nonlinear_arith)
        requires
            d > 0,
            segsize == bits * d,
            full_size as int <= segsize as int;
    assert(start as int / d as int + full_size as int / d as int
        == (start as int + full_size as int) / d as int) by(nonlinear_arith)
        requires
            d > 0,
            start as int % d as int == 0,
            full_size as int % d as int == 0;
    assert((start / d) as int == start as int / d as int) by(nonlinear_arith)
        requires d > 0;
    assert((full_size / d) as int == full_size as int / d as int) by(nonlinear_arith)
        requires d > 0;
    assert((start as int + full_size as int) / d as int <= bits as int) by(nonlinear_arith)
        requires
            d > 0,
            segsize == bits * d,
            start as int + full_size as int <= segsize as int;
}

pub open spec fn clock_now_millis_from_timespec(tv_sec: i64, tv_nsec: i64, millis: i64) -> bool {
    millis == tv_sec.wrapping_mul(1000).wrapping_add((((tv_nsec as u64) / 1000000) as i64))
}

#[verus_verify]
fn clock_now() -> (now: i64)
    ensures
        exists |tv_sec: i64, tv_nsec: i64| #[trigger] clock_now_millis_from_timespec(tv_sec, tv_nsec, now),
{
    let t = clock_gettime_monotonic();
    proof {
        assert(clock_now_millis_from_timespec(
            t.tv_sec,
            t.tv_nsec,
            t.tv_sec.wrapping_mul(1000).wrapping_add((((t.tv_nsec as u64) / 1000000) as i64)),
        ));
        assert(exists |tv_sec: i64, tv_nsec: i64| #[trigger] clock_now_millis_from_timespec(
            tv_sec,
            tv_nsec,
            t.tv_sec.wrapping_mul(1000).wrapping_add((((t.tv_nsec as u64) / 1000000) as i64)),
        ));
    }
    t.tv_sec.wrapping_mul(1000).wrapping_add( (((t.tv_nsec as u64) / 1000000) as i64) )
}

// Should not be called for huge segments, I think? TODO can probably optimize out some checks
#[verus_verify]
fn segment_commit_mask(
    segment_ptr: *mut u8,
    conservative: bool,
    p: usize,
    size: usize,
    cm: &mut CommitMask)
 -> (res: (*mut u8, usize)) // start_p, full_size
    requires
        cm.concrete_empty(),
        segment_ptr.addr() as int + SEGMENT_SIZE as int <= usize::MAX as int,
        segment_ptr.addr() as int + SEGMENT_SIZE as int + page_size() - 1 <= usize::MAX as int,
        segment_ptr as int % page_size() == 0,
        size != 0 && size <= SEGMENT_SIZE as usize ==> segment_ptr.addr() <= p,
    ensures
        res.1 <= SEGMENT_SIZE as usize,
        res.1 as int % COMMIT_SIZE as int == 0,
        res.1 as int % page_size() == 0,
        res.1 != 0 ==> res.0 as int % page_size() == 0,
        res.1 != 0 ==> res.0 as int + res.1 as int + page_size() - 1 <= usize::MAX as int,
        res.1 != 0 ==> segment_ptr as int <= res.0 as int,
        res.1 != 0 ==> res.0 as int + res.1 as int <= segment_ptr as int + SEGMENT_SIZE as int,
        res.1 != 0 ==> (res.0 as int - segment_ptr as int) % COMMIT_SIZE as int == 0,
        res.1 != 0 ==> res.0@.provenance == segment_ptr@.provenance,
        res.1 != 0 ==> size != 0 && size <= SEGMENT_SIZE as usize,
        res.1 != 0 ==> final(cm)@ =~= Set::range(
            (res.0 as int - segment_ptr as int) / COMMIT_SIZE as int,
            (res.0 as int - segment_ptr as int + res.1 as int) / COMMIT_SIZE as int,
        ),
        size != 0 && size <= SEGMENT_SIZE as usize && segment_ptr.addr() <= p
            && segment_ptr as int % COMMIT_SIZE as int == 0
            && p as int % COMMIT_SIZE as int == 0
            && size as int % COMMIT_SIZE as int == 0
            && p as int + size as int <= segment_ptr as int + SEGMENT_SIZE as int ==>
                res.0.addr() == p && res.1 == size
                && final(cm)@ =~= Set::range(
                    (p as int - segment_ptr as int) / COMMIT_SIZE as int,
                    (p as int - segment_ptr as int + size as int) / COMMIT_SIZE as int,
                ),
{

    if size == 0 || size > SEGMENT_SIZE as usize {
        return (core::ptr::null_mut(), 0);
    }

    let segstart: usize = SLICE_SIZE as usize;
    let segsize: usize = SEGMENT_SIZE as usize;
    proof {
        lemma_segment_commit_mask_constants();
        assert(segment_ptr.addr() + segsize <= usize::MAX) by(nonlinear_arith)
            requires
                segment_ptr.addr() as int + SEGMENT_SIZE as int <= usize::MAX as int,
                segsize == SEGMENT_SIZE as usize;
    }

    if p >= segment_ptr.addr() + segsize {
        return (core::ptr::null_mut(), 0);
    }

    proof {
        assert(segment_ptr.addr() <= p);
    }
    let pstart: usize = p - segment_ptr.addr();
    proof {
        assert(pstart < segsize) by(nonlinear_arith)
            requires
                segment_ptr.addr() <= p,
                p < segment_ptr.addr() + segsize,
                pstart == p - segment_ptr.addr();
        assert(pstart + size <= usize::MAX) by(nonlinear_arith)
            requires
                pstart < segsize,
                size <= segsize,
                segsize == SEGMENT_SIZE as usize,
                2 * SEGMENT_SIZE as usize + COMMIT_SIZE as usize <= usize::MAX;
        assert(pstart + COMMIT_SIZE as usize - 1 <= usize::MAX) by(nonlinear_arith)
            requires
                pstart < segsize,
                segsize == SEGMENT_SIZE as usize,
                2 * SEGMENT_SIZE as usize + COMMIT_SIZE as usize <= usize::MAX;
        assert(pstart + size + COMMIT_SIZE as usize - 1 <= usize::MAX) by(nonlinear_arith)
            requires
                pstart < segsize,
                size <= segsize,
                segsize == SEGMENT_SIZE as usize,
                2 * SEGMENT_SIZE as usize + COMMIT_SIZE as usize <= usize::MAX;
    }

    let mut start: usize;
    let mut end: usize;
    if conservative {
        start = align_up(pstart, COMMIT_SIZE as usize);
        end = align_down(pstart + size, COMMIT_SIZE as usize);
        proof {
            assert(pstart as int <= segsize as int) by(nonlinear_arith)
                requires pstart < segsize;
            assert(segsize as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
                requires
                    segsize == SEGMENT_SIZE as usize,
                    SEGMENT_SIZE as usize == COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize,
                    COMMIT_SIZE as usize > 0;
            assert(start as int <= segsize as int);
            assert(start as int % COMMIT_SIZE as int == 0);
            assert(end as int % COMMIT_SIZE as int == 0);
        }
    } else {
        start = align_down(pstart, COMMIT_SIZE as usize);
        end = align_up(pstart + size, COMMIT_SIZE as usize);
        proof {
            assert(start as int <= pstart as int);
            assert(start as int <= segsize as int) by(nonlinear_arith)
                requires
                    start as int <= pstart as int,
                    pstart < segsize;
            assert(start as int % COMMIT_SIZE as int == 0);
            assert(end as int % COMMIT_SIZE as int == 0);
        }
    }
    proof {
        assert(start as int <= segsize as int);
        assert(start as int % COMMIT_SIZE as int == 0);
        assert(end as int % COMMIT_SIZE as int == 0);
    }

    if pstart >= segstart && start < segstart {
        start = segstart;
    }
    proof {
        assert(segstart as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
            requires
                segstart == SLICE_SIZE as usize,
                COMMIT_SIZE as usize == SLICE_SIZE as usize,
                COMMIT_SIZE as usize > 0;
        assert(start as int <= segsize as int) by(nonlinear_arith)
            requires
                start as int <= segsize as int,
                segstart <= segsize;
        assert(start as int % COMMIT_SIZE as int == 0);
    }

    if end > segsize {
        end = segsize;
    }
    proof {
        assert(segsize as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
            requires
                segsize == SEGMENT_SIZE as usize,
                SEGMENT_SIZE as usize == COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize,
                COMMIT_SIZE as usize > 0;
        assert(end as int <= segsize as int);
        assert(end as int % COMMIT_SIZE as int == 0);
        assert(start as int <= segsize as int);
    }

    proof {
        assert(segment_ptr.addr() + start <= usize::MAX) by(nonlinear_arith)
            requires
                segment_ptr.addr() + segsize <= usize::MAX,
                start <= segsize;
    }
    let start_p = segment_ptr.with_addr(segment_ptr.addr() + start);
    let full_size = if end > start { end - start } else { 0 };
    proof {
        if end > start {
            assert(start + full_size == end) by(nonlinear_arith)
                requires
                    full_size == end - start,
                    end > start;
            assert(full_size as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
                requires
                    end as int % COMMIT_SIZE as int == 0,
                    start as int % COMMIT_SIZE as int == 0,
                    full_size == end - start,
                    end > start,
                    COMMIT_SIZE as usize > 0;
            assert(start as int + full_size as int <= segsize as int) by(nonlinear_arith)
                requires
                    start + full_size == end,
                    end <= segsize;
            lemma_commit_multiple_is_page_multiple(full_size as int);
        } else {
            assert(full_size as int % COMMIT_SIZE as int == 0);
            lemma_commit_multiple_is_page_multiple(full_size as int);
            assert(start as int + full_size as int <= segsize as int) by(nonlinear_arith)
                requires
                    start <= segsize,
                    full_size == 0;
        }
    }
    if full_size == 0 {
        return (start_p, full_size);
    }

    proof {
        lemma_commit_multiple_is_page_multiple(start as int);
        lemma_sum_page_aligned(segment_ptr as int, start as int);
        assert(segment_ptr.addr() as int == segment_ptr as int);
        assert((segment_ptr.addr() + start) as int == segment_ptr as int + start as int) by(nonlinear_arith)
            requires
                segment_ptr.addr() + start <= usize::MAX,
                segment_ptr.addr() as int == segment_ptr as int;
        assert(start_p as int == (segment_ptr.addr() + start) as int);
        assert(start_p as int == segment_ptr as int + start as int);
        assert((start_p as int - segment_ptr as int) % COMMIT_SIZE as int == 0) by(nonlinear_arith)
            requires
                start_p as int == segment_ptr as int + start as int,
                start as int % COMMIT_SIZE as int == 0,
                COMMIT_SIZE as int > 0;
        assert(start_p as int % page_size() == 0);
        assert(segment_ptr as int <= start_p as int) by(nonlinear_arith)
            requires
                start_p as int == segment_ptr as int + start as int,
                0 <= start as int;
        assert(start_p@.provenance == segment_ptr@.provenance);
        assert(start_p as int + full_size as int <= segment_ptr.addr() as int + SEGMENT_SIZE as int) by(nonlinear_arith)
            requires
                start_p as int == segment_ptr as int + start as int,
                segment_ptr.addr() as int == segment_ptr as int,
                start as int + full_size as int <= segsize as int,
                segsize == SEGMENT_SIZE as usize;
        assert(start_p as int + full_size as int + page_size() - 1 <= usize::MAX as int) by(nonlinear_arith)
            requires
                start_p as int + full_size as int <= segment_ptr.addr() as int + SEGMENT_SIZE as int,
                segment_ptr.addr() as int + SEGMENT_SIZE as int + page_size() - 1 <= usize::MAX as int;
    }

    let bitidx = start / COMMIT_SIZE as usize;
    let bitcount = full_size / COMMIT_SIZE as usize;
    proof {
        lemma_commit_mask_bit_range(start, full_size);
        assert(bitcount <= COMMIT_MASK_BITS as usize);
        assert(bitidx as int + bitcount as int <= COMMIT_MASK_BITS as int);
        assert(COMMIT_MASK_BITS as int == 512) by(nonlinear_arith)
            requires
                COMMIT_MASK_BITS as usize == 512;
        assert(cm.concrete_empty());
    }
    cm.create(bitidx, bitcount);

    proof {
        let lo = (start_p as int - segment_ptr as int) / COMMIT_SIZE as int;
        let hi = (start_p as int - segment_ptr as int + full_size as int) / COMMIT_SIZE as int;
        assert(start_p as int - segment_ptr as int == start as int) by(nonlinear_arith)
            requires start_p as int == segment_ptr as int + start as int;
        assert(bitidx as int == lo) by(nonlinear_arith)
            requires
                bitidx == start / COMMIT_SIZE as usize,
                lo == (start_p as int - segment_ptr as int) / COMMIT_SIZE as int,
                start_p as int - segment_ptr as int == start as int,
                COMMIT_SIZE as usize > 0;
        assert(bitcount as int == full_size as int / COMMIT_SIZE as int) by(nonlinear_arith)
            requires
                bitcount == full_size / COMMIT_SIZE as usize,
                COMMIT_SIZE as usize > 0;
        assert(hi == lo + bitcount as int) by(nonlinear_arith)
            requires
                hi == (start_p as int - segment_ptr as int + full_size as int) / COMMIT_SIZE as int,
                lo == (start_p as int - segment_ptr as int) / COMMIT_SIZE as int,
                bitcount as int == full_size as int / COMMIT_SIZE as int,
                (start_p as int - segment_ptr as int) % COMMIT_SIZE as int == 0,
                full_size as int % COMMIT_SIZE as int == 0,
                COMMIT_SIZE as int > 0;
        if bitcount == COMMIT_MASK_BITS as usize {
            lemma_fundamental_div_mod(full_size as int, COMMIT_SIZE as int);
            assert(full_size as int / COMMIT_SIZE as int == COMMIT_MASK_BITS as int) by(nonlinear_arith)
                requires
                    bitcount as int == full_size as int / COMMIT_SIZE as int,
                    bitcount == COMMIT_MASK_BITS as usize;
            assert(full_size as int == COMMIT_SIZE as int * COMMIT_MASK_BITS as int) by(nonlinear_arith)
                requires
                    full_size as int == COMMIT_SIZE as int * (full_size as int / COMMIT_SIZE as int)
                        + full_size as int % COMMIT_SIZE as int,
                    full_size as int % COMMIT_SIZE as int == 0,
                    full_size as int / COMMIT_SIZE as int == COMMIT_MASK_BITS as int;
            assert(full_size as int == SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    full_size as int == COMMIT_SIZE as int * COMMIT_MASK_BITS as int,
                    SEGMENT_SIZE as usize == COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize;
            assert(start == 0) by(nonlinear_arith)
                requires
                    start as int + full_size as int <= SEGMENT_SIZE as int,
                    full_size as int == SEGMENT_SIZE as int;
            assert(bitidx == 0) by(nonlinear_arith)
                requires
                    bitidx == start / COMMIT_SIZE as usize,
                    start == 0;
            assert(lo == 0);
            assert(hi == COMMIT_MASK_BITS as int) by(nonlinear_arith)
                requires
                    hi == lo + bitcount as int,
                    lo == 0,
                    bitcount == COMMIT_MASK_BITS as usize;
            assert(cm@ =~= Set::range(lo, hi));
        } else {
            assert(cm@ =~= Set::range(bitidx as int, bitidx as int + bitcount as int));
            assert(cm@ =~= Set::range(lo, hi));
        }
        if size != 0 && size <= SEGMENT_SIZE as usize && segment_ptr.addr() <= p
            && segment_ptr as int % COMMIT_SIZE as int == 0
            && p as int % COMMIT_SIZE as int == 0
            && size as int % COMMIT_SIZE as int == 0
            && p as int + size as int <= segment_ptr as int + SEGMENT_SIZE as int
        {
            assert(segment_ptr.addr() as int == segment_ptr as int);
            assert(p < segment_ptr.addr() + segsize) by(nonlinear_arith)
                requires
                    p as int + size as int <= segment_ptr as int + SEGMENT_SIZE as int,
                    segment_ptr.addr() as int == segment_ptr as int,
                    segsize == SEGMENT_SIZE as usize,
                    size != 0;
            assert(pstart as int == p as int - segment_ptr as int) by(nonlinear_arith)
                requires
                    pstart == p - segment_ptr.addr(),
                    segment_ptr.addr() <= p,
                    segment_ptr.addr() as int == segment_ptr as int;
            assert(pstart as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
                requires
                    pstart as int == p as int - segment_ptr as int,
                    p as int % COMMIT_SIZE as int == 0,
                    segment_ptr as int % COMMIT_SIZE as int == 0,
                    COMMIT_SIZE as int > 0;
            assert((pstart + size) as int == pstart as int + size as int) by(nonlinear_arith)
                requires
                    pstart + size <= usize::MAX;
            assert((pstart + size) as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
                requires
                    (pstart + size) as int == pstart as int + size as int,
                    pstart as int % COMMIT_SIZE as int == 0,
                    size as int % COMMIT_SIZE as int == 0,
                    COMMIT_SIZE as int > 0;
            lemma_aligned_between_same(pstart as int, start as int, COMMIT_SIZE as int);
            assert(start == pstart);
            lemma_aligned_between_same(end as int, (pstart + size) as int, COMMIT_SIZE as int);
            assert(end == pstart + size);
            assert(full_size == size) by(nonlinear_arith)
                requires
                    full_size == end - start,
                    end > start,
                    start == pstart,
                    end == pstart + size,
                    size != 0;
            assert(start_p.addr() == p) by(nonlinear_arith)
                requires
                    start_p as int == segment_ptr as int + start as int,
                    start == pstart,
                    pstart as int == p as int - segment_ptr as int;
            assert(bitidx as int == (p as int - segment_ptr as int) / COMMIT_SIZE as int) by(nonlinear_arith)
                requires
                    bitidx == start / COMMIT_SIZE as usize,
                    start == pstart,
                    pstart as int == p as int - segment_ptr as int,
                    COMMIT_SIZE as usize > 0;
            assert(bitcount as int == size as int / COMMIT_SIZE as int) by(nonlinear_arith)
                requires
                    bitcount == full_size / COMMIT_SIZE as usize,
                    full_size == size,
                    COMMIT_SIZE as usize > 0;
            assert((p as int - segment_ptr as int + size as int) / COMMIT_SIZE as int
                == (p as int - segment_ptr as int) / COMMIT_SIZE as int + size as int / COMMIT_SIZE as int) by(nonlinear_arith)
                requires
                    (p as int - segment_ptr as int) % COMMIT_SIZE as int == 0,
                    size as int % COMMIT_SIZE as int == 0,
                    COMMIT_SIZE as int > 0;
            if bitcount == COMMIT_MASK_BITS as usize {
                assert(bitidx == 0) by(nonlinear_arith)
                    requires
                        bitidx as int + bitcount as int <= COMMIT_MASK_BITS as int,
                        bitcount == COMMIT_MASK_BITS as usize;
                assert(cm@ =~= Set::range(0, COMMIT_MASK_BITS as int));
            } else {
                assert(cm@ =~= Set::range(bitidx as int, bitidx as int + bitcount as int));
            }
            assert(cm@ =~= Set::range(
                (p as int - segment_ptr as int) / COMMIT_SIZE as int,
                (p as int - segment_ptr as int + size as int) / COMMIT_SIZE as int,
            ));
        }
    }

    return (start_p, full_size);
}

#[verifier::spinoff_prover]
#[verus_verify]
fn segment_commitx(
    segment: SegmentPtr,
    commit: bool,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires
        commit ==> local.wf_main() || (local.wf_main_for_page_access() && local.mem_chunk_good(segment.segment_id@)),
        commit ==> segment.segment_ptr.addr() != 0,
        !commit ==> local.wf_main(),
        !commit ==> local.wf_main_for_page_access(),
        !commit ==> size <= SEGMENT_SIZE as usize,
        !commit && size != 0 ==> p as int % COMMIT_SIZE as int == 0,
        !commit && size != 0 ==> size as int % COMMIT_SIZE as int == 0,
        !commit && size != 0 ==> p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int,
        !commit && size != 0 ==> forall |j: int|
            (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int <= j
                < (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int ==>
                    local.decommit_mask(segment.segment_id@)@.contains(j),
        segment.wf(),
        segment.is_in(*local),
        size != 0 && size <= SEGMENT_SIZE as usize ==> segment.segment_ptr.addr() <= p,
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
        final(local).unused_pages == old(local).unused_pages,
        final(local).thread_token == old(local).thread_token,
        final(local).thread_id == old(local).thread_id,
        final(local).heap == old(local).heap,
        final(local).tld == old(local).tld,
        final(local).segments.dom() == old(local).segments.dom(),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) && sid != segment.segment_id@ ==>
            final(local).segments[sid] == old(local).segments[sid],
        segment.is_in(*final(local)),
        final(local).segments[segment.segment_id@].wf(
            segment.segment_id@,
            final(local).thread_token.value().segments.index(segment.segment_id@),
            final(local).instance),
        final(local).segments[segment.segment_id@].main2 == old(local).segments[segment.segment_id@].main2,
        old(local).mem_chunk_good(segment.segment_id@) ==> final(local).mem_chunk_good(segment.segment_id@),
        commit && success ==> final(local).segments[segment.segment_id@].mem.has_new_pointsto(
            &old(local).segments[segment.segment_id@].mem),
        commit && success && size != 0 && size <= SEGMENT_SIZE as usize
            && segment.segment_ptr.addr() <= p
            && p as int % COMMIT_SIZE as int == 0
            && size as int % COMMIT_SIZE as int == 0
            && p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int ==>
                set_int_range(p as int, p as int + size as int)
                    <= final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
                        - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),
        final(local).wf_main_for_page_access(),
        !commit ==> final(local).wf_main(),
        !commit ==> final(local).wf_main_for_page_access(),
        !commit ==> segment.is_in(*final(local)),
        !commit ==> final(local).page_organization == old(local).page_organization,
        !commit ==> final(local).pages == old(local).pages,
        !commit ==> final(local).psa == old(local).psa,
        !commit ==> final(local).unused_pages == old(local).unused_pages,
        !commit ==> final(local).thread_token == old(local).thread_token,
        !commit ==> final(local).heap == old(local).heap,
        !commit ==> final(local).tld == old(local).tld,
        !commit ==> final(local).segments.dom() == old(local).segments.dom(),
{
    let ghost sid = segment.segment_id@;
    let ghost local_snap = *local;

    let mut mask: CommitMask = CommitMask::empty();
    proof {
        assert(mask.concrete_empty());
        assert((segment.segment_ptr as int) + (SEGMENT_SIZE as int) < (usize::MAX as int));
        assert((segment.segment_ptr.addr() as int) + (SEGMENT_SIZE as int) <= (usize::MAX as int));
            lemma_segment_start_page_aligned(segment.segment_id@);
            assert(segment.segment_ptr as int == segment_start(segment.segment_id@));
            assert(segment.segment_ptr as int % page_size() == 0);
            assert(SEGMENT_SIZE as int % page_size() == 0) by(compute_only);
            lemma_page_aligned_end_fits(segment.segment_ptr as int, SEGMENT_SIZE as int);
            assert(segment.segment_ptr.addr() as int + SEGMENT_SIZE as int + page_size() - 1 <= usize::MAX as int);
    }
    let (start, full_size) = segment_commit_mask(
        segment.segment_ptr as *mut u8, !commit, p, size, &mut mask);

    if mask.is_empty() || full_size == 0 {
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.segments[segment.segment_id@].wf(
                segment.segment_id@,
                local.thread_token.value().segments.index(segment.segment_id@),
                local.instance));
            assert(local.segments[segment.segment_id@].mem == local_snap.segments[segment.segment_id@].mem);
            if commit && size != 0 && size <= SEGMENT_SIZE as usize
                && segment.segment_ptr.addr() <= p
                && p as int % COMMIT_SIZE as int == 0
                && size as int % COMMIT_SIZE as int == 0
                && p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int
            {
                lemma_segment_ptr_commit_aligned(segment);
                assert(start.addr() == p);
                assert(full_size == size);
                assert(full_size != 0);
                assert(mask@ =~= Set::range(
                    (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int,
                    (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int,
                ));
                let lo = (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int;
                let hi = (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int;
                let rel = p as int - segment.segment_ptr as int;
                let d = COMMIT_SIZE as int;
                assert(mask@ =~= Set::empty());
                assert(COMMIT_SIZE as int > 0) by(compute_only);
                assert(d > 0);
                assert(rel >= 0) by(nonlinear_arith)
                    requires
                        segment.segment_ptr.addr() <= p,
                        segment.segment_ptr.addr() as int == segment.segment_ptr as int,
                        rel == p as int - segment.segment_ptr as int;
                lemma_fundamental_div_mod(rel, d);
                lemma_add_mod_noop(rel, size as int, d);
                lemma_fundamental_div_mod(rel + size as int, d);
                assert((rel + size as int) % d == 0);
                assert(rel == d * lo);
                assert(rel + size as int == d * hi);
                assert(hi > lo) by(nonlinear_arith)
                    requires
                        rel == d * lo,
                        rel + size as int == d * hi,
                        size != 0,
                        d > 0;
                assert(Set::<int>::range(lo, hi).contains(lo));
                assert(mask@.contains(lo));
                assert(false);
            }
        }
        return true;
    }

    proof {
        if !commit {
            lemma_segment_commit_mask_constants();
            lemma_segment_start_basics(sid);
            assert(segment.segment_ptr as int == segment_start(sid));
            assert(segment.segment_ptr as int % SEGMENT_SIZE as int == 0);
            lemma_fundamental_div_mod(segment.segment_ptr as int, SEGMENT_SIZE as int);
            assert(segment.segment_ptr as int == SEGMENT_SIZE as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int));
            assert(segment.segment_ptr as int == COMMIT_SIZE as int * (COMMIT_MASK_BITS as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int))) by(nonlinear_arith)
                requires
                    segment.segment_ptr as int == SEGMENT_SIZE as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int),
                    SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int;
            lemma_mod_multiples_basic(COMMIT_MASK_BITS as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int), COMMIT_SIZE as int);
            assert(segment.segment_ptr as int % COMMIT_SIZE as int == 0);
            assert(size != 0);
            assert(size <= SEGMENT_SIZE as usize);
            assert(segment.segment_ptr.addr() <= p);
            assert(segment.segment_ptr.addr() as int <= p as int);
            assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
            assert(p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int);
            assert(start.addr() == p);
            assert(full_size == size);
            assert(start as int == p as int);
            let lo = (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int;
            let hi = (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int;
            let rel = p as int - segment.segment_ptr as int;
            let d = COMMIT_SIZE as int;
            assert(mask@ =~= Set::range(lo, hi));
            assert(rel >= 0) by(nonlinear_arith)
                requires
                    segment.segment_ptr.addr() as int <= p as int,
                    segment.segment_ptr.addr() as int == segment.segment_ptr as int,
                    rel == p as int - segment.segment_ptr as int;
            lemma_fundamental_div_mod(p as int, d);
            lemma_fundamental_div_mod(segment.segment_ptr as int, d);
            assert(p as int == d * (p as int / d));
            assert(segment.segment_ptr as int == d * (segment.segment_ptr as int / d));
            assert(rel == d * ((p as int / d) - (segment.segment_ptr as int / d))) by(nonlinear_arith)
                requires
                    rel == p as int - segment.segment_ptr as int,
                    p as int == d * (p as int / d),
                    segment.segment_ptr as int == d * (segment.segment_ptr as int / d);
            lemma_mod_multiples_basic((p as int / d) - (segment.segment_ptr as int / d), d);
            assert(rel % d == 0);
            lemma_div_pos_is_pos(rel, d);
            assert(0 <= lo);
            assert(size as int % d == 0);
            assert(rel + size as int >= rel) by(nonlinear_arith);
            lemma_div_is_ordered(rel, rel + size as int, d);
            assert(lo <= hi);
            assert(rel + size as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int,
                    rel == p as int - segment.segment_ptr as int;
            lemma_div_is_ordered(rel + size as int, SEGMENT_SIZE as int, d);
            lemma_div_multiples_vanish(COMMIT_MASK_BITS as int, d);
            assert(SEGMENT_SIZE as int == d * COMMIT_MASK_BITS as int) by(nonlinear_arith)
                requires SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int,
                    d == COMMIT_SIZE as int;
            assert(SEGMENT_SIZE as int / d == COMMIT_MASK_BITS as int);
            assert(hi <= COMMIT_MASK_BITS as int);
            lemma_fundamental_div_mod(rel, d);
            assert(rel == d * lo);
            lemma_add_mod_noop(rel, size as int, d);
            assert((rel + size as int) % d == 0);
            lemma_fundamental_div_mod(rel + size as int, d);
            assert(rel + size as int == d * hi);
            lemma_segment_commit_mask_bytes_range(&mask, sid, lo, hi);
            assert(segment_start(sid) + lo * d == start as int) by(nonlinear_arith)
                requires
                    segment.segment_ptr as int == segment_start(sid),
                    rel == p as int - segment.segment_ptr as int,
                    rel == d * lo,
                    start as int == p as int;
            assert(segment_start(sid) + hi * d == start as int + full_size as int) by(nonlinear_arith)
                requires
                    segment.segment_ptr as int == segment_start(sid),
                    rel == p as int - segment.segment_ptr as int,
                    rel + size as int == d * hi,
                    start as int == p as int,
                    full_size == size;
            assert(mask.bytes(sid) =~= set_int_range(start as int, start as int + full_size as int));
            assert(mask@ <= local_snap.decommit_mask(sid)@) by {
                assert forall |j: int| #[trigger] mask@.contains(j) implies
                    local_snap.decommit_mask(sid)@.contains(j) by {
                    assert(lo <= j < hi);
                }
            }
        }
    }

    if commit && !segment.get_commit_mask(Tracked(&*local)).all_set(&mask) {

        let mut is_zero = false;
        let mut cmask = CommitMask::empty();
        segment.get_commit_mask(Tracked(&*local)).create_intersect(&mask, &mut cmask);

        proof {
            assert(local.mem_chunk_good(sid));
            assert(local.segments[sid].mem.wf());
            assert(local.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
            assert(local.segments[sid].mem.points_to.provenance() == sid.provenance);
            assert(start@.provenance == segment.segment_ptr@.provenance);
            assert(segment.segment_ptr@.provenance == sid.provenance);
            assert(start@.provenance == local.segments[sid].mem.points_to.provenance());
            assert(segment.segment_ptr as int == segment_start(sid));
            assert(start as int + full_size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int);
            lemma_os_exact_range_contains_subrange(
                local.segments[sid].mem,
                segment_start(sid),
                SEGMENT_SIZE as int,
                start as int,
                full_size as int,
            );
            assert(local.segments[sid].mem.os_has_range(start as int, full_size as int));
        }
        let success;
        segment_get_mut_local!(segment, local, l => {
            let (_success, _is_zero) =
                crate::os_commit::os_commit(start, full_size, Tracked(&mut l.mem));
            success = _success;
        });
        if (!success) {
            proof {
                assert(local.page_organization == local_snap.page_organization);
                assert(local.pages == local_snap.pages);
                assert(local.psa == local_snap.psa);
                assert(local.unused_pages == local_snap.unused_pages);
                assert(local.thread_token == local_snap.thread_token);
                assert(local.thread_id == local_snap.thread_id);
                assert(local.heap == local_snap.heap);
                assert(local.tld == local_snap.tld);
                assert(local.segments.dom() == local_snap.segments.dom());
                assert(segment.is_in(*local));
                if local_snap.wf_main() {
                    local_snap.wf_main_implies_page_access();
                }
                assert(local_snap.wf_main_for_page_access());
                assert(local.segments[sid].main.id() == local_snap.segments[sid].main.id());
                assert(local.segments[sid].main2 == local_snap.segments[sid].main2);
                assert(local.thread_token == local_snap.thread_token);
                assert(local.instance == local_snap.instance);
                assert(local.segments[sid].wf(
                    sid,
                    local.thread_token.value().segments.index(sid),
                    local.instance));
            }
            return false;
        }

        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.set(&mask);
        });
        proof {
            let old_commit = local_snap.commit_mask(sid);
            let final_commit = local.commit_mask(sid);
            assert(final_commit@ =~= old_commit@ + mask@);
            assert(old_commit@ <= final_commit@) by {
                assert forall |bit: int| #[trigger] old_commit@.contains(bit) implies final_commit@.contains(bit) by { }
            };
            lemma_segment_commit_mask_bytes_subset(&old_commit, &final_commit, sid);
            let lo = (start as int - segment.segment_ptr as int) / COMMIT_SIZE as int;
            let hi = (start as int - segment.segment_ptr as int + full_size as int) / COMMIT_SIZE as int;
            assert(mask@ =~= Set::range(lo, hi));
            assert(segment_start(sid) + lo * COMMIT_SIZE as int == start as int) by(nonlinear_arith)
                requires
                    segment.segment_ptr as int == segment_start(sid),
                    lo == (start as int - segment.segment_ptr as int) / COMMIT_SIZE as int,
                    (start as int - segment.segment_ptr as int) % COMMIT_SIZE as int == 0,
                    COMMIT_SIZE as int > 0;
            assert((hi - lo) * COMMIT_SIZE as int == full_size as int) by(nonlinear_arith)
                requires
                    hi == (start as int - segment.segment_ptr as int + full_size as int) / COMMIT_SIZE as int,
                    lo == (start as int - segment.segment_ptr as int) / COMMIT_SIZE as int,
                    (start as int - segment.segment_ptr as int) % COMMIT_SIZE as int == 0,
                    full_size as int % COMMIT_SIZE as int == 0,
                    COMMIT_SIZE as int > 0;
            assert(segment.segment_ptr.addr() != 0);
            assert(segment.segment_ptr as int <= start as int);
            assert(start.addr() != 0);
            assert(local.segments[sid].mem.os_has_range_read_write(start as int, full_size as int));
            assert(local.segments[sid].mem.os_has_range_read_write(
                segment_start(sid) + lo * COMMIT_SIZE as int,
                (hi - lo) * COMMIT_SIZE as int));
            lemma_segment_commit_mask_bytes_subset_of_rw_range(&mask, sid, local.segments[sid].mem, lo, hi);
            assert(local.segments[sid].mem.has_new_pointsto(&local_snap.segments[sid].mem));
            assert(final_commit.bytes(sid) <= local.segments[sid].mem.os_rw_bytes()) by {
                assert forall |addr: int| #[trigger] final_commit.bytes(sid).contains(addr) implies
                    local.segments[sid].mem.os_rw_bytes().contains(addr) by {
                    lemma_segment_commit_mask_bytes_contains(&final_commit, sid, addr);
                    let bit = segment_commit_mask_byte_bit(sid, addr);
                    assert(final_commit@.contains(bit));
                    assert((old_commit@ + mask@).contains(bit));
                    if old_commit@.contains(bit) {
                        lemma_segment_commit_mask_bytes_contains(&old_commit, sid, addr);
                        assert(old_commit.bytes(sid).contains(addr));
                        assert(local_snap.segments[sid].mem.os_rw_bytes().contains(addr));
                        assert(local.segments[sid].mem.os_rw_bytes().contains(addr));
                    } else {
                        assert(mask@.contains(bit));
                        lemma_segment_commit_mask_bytes_contains(&mask, sid, addr);
                        assert(mask.bytes(sid).contains(addr));
                    }
                }
            };
        }
    }
    else if !commit && segment.get_commit_mask(Tracked(&*local)).any_set(&mask) {
        let mut cmask = CommitMask::empty();
        segment.get_commit_mask(Tracked(&*local)).create_intersect(&mask, &mut cmask);
        let ghost local_before_os_decommit = *local;
        proof {
            assert(local.mem_chunk_good(sid));
            assert(mask.bytes(sid) =~= set_int_range(start as int, start as int + full_size as int));
            let old_commit = local.commit_mask(sid);
            let old_decommit = local.decommit_mask(sid);
            assert(old_decommit.bytes(sid) <= old_commit.bytes(sid));
            assert(mask@ <= old_decommit@);
            lemma_segment_commit_mask_bytes_subset(&mask, &old_decommit, sid);
            assert(mask.bytes(sid) <= old_decommit.bytes(sid));
            assert(mask.bytes(sid) <= old_commit.bytes(sid));
            assert(old_commit.bytes(sid).subset_of(local.segments[sid].mem.os_rw_bytes()));
            assert(set_int_range(start as int, start as int + full_size as int)
                <= local.segments[sid].mem.os_rw_bytes());
            assert(local.segments[sid].mem.os_has_range_read_write(start as int, full_size as int));
            local.wf_main_implies_page_access();
            local.segment_pages_range_total_subset_used_total(sid);
            assert forall |addr: int| #[trigger] set_int_range(start as int, start as int + full_size as int).contains(addr) implies
                local.segments[sid].mem.points_to.dom().contains(addr) by {
                assert(mask.bytes(sid).contains(addr));
                assert(old_decommit.bytes(sid).contains(addr));
                assert(old_commit.bytes(sid).contains(addr));
                assert(local.segments[sid].mem.os_rw_bytes().contains(addr));
                if !local.segments[sid].mem.points_to.dom().contains(addr) {
                    assert(local.segments[sid].mem.os_rw_bytes() <=
                        local.segments[sid].mem.points_to.dom()
                            + segment_info_range(sid)
                            + local.segment_pages_range_total(sid));
                    if segment_info_range(sid).contains(addr) {
                        assert((old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr));
                        assert(false);
                    }
                    if local.segment_pages_range_total(sid).contains(addr) {
                        assert(local.segment_pages_used_total(sid).contains(addr));
                        assert((old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr));
                        assert(false);
                    }
                    assert(false);
                }
            }
            assert(local.segments[sid].mem.committed_pointsto_has_range(start as int, full_size as int));
        }
        if segment.get_allow_decommit(Tracked(&*local)) {
            proof {
                assert(local.mem_chunk_good(sid));
                assert(local.segments[sid].mem.wf());
                assert(local.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
                assert(local.segments[sid].mem.points_to.provenance() == sid.provenance);
                assert(start@.provenance == segment.segment_ptr@.provenance);
                assert(segment.segment_ptr@.provenance == sid.provenance);
                assert(start@.provenance == local.segments[sid].mem.points_to.provenance());
                assert(segment.segment_ptr as int == segment_start(sid));
                assert(start as int + full_size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int);
                lemma_os_exact_range_contains_subrange(
                    local.segments[sid].mem,
                    segment_start(sid),
                    SEGMENT_SIZE as int,
                    start as int,
                    full_size as int,
                );
                assert(local.segments[sid].mem.os_has_range(start as int, full_size as int));
                let old_commit = local.commit_mask(sid);
                let old_decommit = local.decommit_mask(sid);
                assert(old_decommit.bytes(sid) <= old_commit.bytes(sid));
                assert(mask@ <= old_decommit@);
                lemma_segment_commit_mask_bytes_subset(&mask, &old_decommit, sid);
                assert(mask.bytes(sid) <= old_decommit.bytes(sid));
                assert(mask.bytes(sid) <= old_commit.bytes(sid));
                assert(old_commit.bytes(sid).subset_of(local.segments[sid].mem.os_rw_bytes()));
                assert(set_int_range(start as int, start as int + full_size as int)
                    <= local.segments[sid].mem.os_rw_bytes());
                assert(local.segments[sid].mem.os_has_range_read_write(start as int, full_size as int));
                local.wf_main_implies_page_access();
                local.segment_pages_range_total_subset_used_total(sid);
                assert forall |addr: int| #[trigger] set_int_range(start as int, start as int + full_size as int).contains(addr) implies
                    local.segments[sid].mem.points_to.dom().contains(addr) by {
                    assert(mask.bytes(sid).contains(addr));
                    assert(old_decommit.bytes(sid).contains(addr));
                    assert(old_commit.bytes(sid).contains(addr));
                    assert(local.segments[sid].mem.os_rw_bytes().contains(addr));
                    if !local.segments[sid].mem.points_to.dom().contains(addr) {
                        assert(local.segments[sid].mem.os_rw_bytes() <=
                            local.segments[sid].mem.points_to.dom()
                                + segment_info_range(sid)
                                + local.segment_pages_range_total(sid));
                        assert((local.segments[sid].mem.points_to.dom()
                                + segment_info_range(sid)
                                + local.segment_pages_range_total(sid)).contains(addr));
                        if segment_info_range(sid).contains(addr) {
                            assert((old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr));
                            assert(false);
                        }
                        if local.segment_pages_range_total(sid).contains(addr) {
                            assert(local.segment_pages_used_total(sid).contains(addr));
                            assert((old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr));
                            assert(false);
                        }
                        assert(false);
                    }
                }
                assert(local.segments[sid].mem.committed_pointsto_has_range(start as int, full_size as int));
            }
            segment_get_mut_local!(segment, local, l => {
                crate::os_commit::os_decommit(start, full_size, Tracked(&mut l.mem));
            });
            proof {
                assert(local.segments[sid].mem.wf());
                assert(local.segments[sid].mem.range_os() =~= local_before_os_decommit.segments[sid].mem.range_os());
                assert(local_before_os_decommit.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
                assert(local.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
                assert(local.segments[sid].mem.points_to.provenance() == sid.provenance);
                assert(mask.bytes(sid) =~= set_int_range(start as int, start as int + full_size as int));
                assert((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                    <= local.segments[sid].mem.os_rw_bytes());
                assert(local.segments[sid].mem.os_rw_bytes() <=
                    (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                        + local.segments[sid].mem.points_to.dom());
                assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid))
                    <= local.segments[sid].mem.points_to.dom());
            }
        }
        proof {
            assert(local.segments[sid].mem.os_rw_bytes() <=
                (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                    + local.segments[sid].mem.points_to.dom());
            assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid))
                <= local.segments[sid].mem.points_to.dom());
            assert((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                <= local.segments[sid].mem.os_rw_bytes());
        }
        let ghost local_before_commit_mask_clear = *local;
        proof {
            assert(local_before_commit_mask_clear.segments[sid].mem.wf());
            assert(local_before_commit_mask_clear.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
            assert(local_before_commit_mask_clear.segments[sid].mem.points_to.provenance() == sid.provenance);
        }
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.clear(&mask);
        });
        proof {
            assert(local.segments[sid].mem == local_before_commit_mask_clear.segments[sid].mem);
            assert(local.segments[sid].mem.os_rw_bytes() <=
                (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                    + local.segments[sid].mem.points_to.dom());
            assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid))
                <= local.segments[sid].mem.points_to.dom());
            assert(local.segments[sid].mem.wf());
            assert(local.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
            assert(local.segments[sid].mem.points_to.provenance() == sid.provenance);
            let old_commit = local_snap.commit_mask(sid);
            let final_commit = local.commit_mask(sid);
            assert(local_before_os_decommit.commit_mask(sid) == old_commit);
            assert(local_before_commit_mask_clear.commit_mask(sid) == old_commit);
            assert(final_commit@ =~= old_commit@ - mask@);
            assert(final_commit@ <= old_commit@);
            lemma_segment_commit_mask_bytes_subset(&final_commit, &old_commit, sid);
            assert(final_commit@.disjoint(mask@));
            lemma_segment_commit_mask_bytes_disjoint(&final_commit, &mask, sid);
            assert(local_snap.mem_chunk_good(sid));
            assert(old_commit.bytes(sid).subset_of(local_snap.segments[sid].mem.os_rw_bytes()));
            assert((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                <= local.segments[sid].mem.os_rw_bytes());
            assert forall |addr: int| #[trigger] final_commit.bytes(sid).contains(addr) implies
                local.segments[sid].mem.os_rw_bytes().contains(addr) by {
                assert(old_commit.bytes(sid).contains(addr));
                assert(local_snap.segments[sid].mem.os_rw_bytes().contains(addr));
                if mask.bytes(sid).contains(addr) {
                    assert(false);
                }
                assert((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid)).contains(addr));
            }
            assert(local.commit_mask(sid).bytes(sid).subset_of(local.segments[sid].mem.os_rw_bytes()));
        }
    }

    proof {
        if commit {
            assert(local.segments[sid].mem.has_new_pointsto(&local_snap.segments[sid].mem));
            assert(local_snap.commit_mask(sid).bytes(sid) <= local.commit_mask(sid).bytes(sid));
            assert(local.commit_mask(sid).bytes(sid) <= local.segments[sid].mem.os_rw_bytes());
        }
        if !commit {
            assert(local.commit_mask(sid).bytes(sid).subset_of(local.segments[sid].mem.os_rw_bytes()));
        }
    }

    proof {
        if !commit && local.segments[sid].mem == local_snap.segments[sid].mem {
            let old_commit = local_snap.commit_mask(sid);
            let old_decommit = local_snap.decommit_mask(sid);
            assert(mask@ <= old_decommit@);
            lemma_segment_commit_mask_bytes_subset(&mask, &old_decommit, sid);
            local_snap.wf_main_implies_page_access();
            local_snap.segment_pages_range_total_subset_used_total(sid);
            assert forall |addr: int| #[trigger] mask.bytes(sid).contains(addr) implies
                local_snap.segments[sid].mem.points_to.dom().contains(addr) by {
                assert(old_decommit.bytes(sid).contains(addr));
                assert(old_commit.bytes(sid).contains(addr));
                assert(local_snap.segments[sid].mem.os_rw_bytes().contains(addr));
                if !local_snap.segments[sid].mem.points_to.dom().contains(addr) {
                    assert(local_snap.segments[sid].mem.os_rw_bytes() <=
                        local_snap.segments[sid].mem.points_to.dom()
                            + segment_info_range(sid)
                            + local_snap.segment_pages_range_total(sid));
                    if segment_info_range(sid).contains(addr) {
                        assert((old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr));
                        assert(false);
                    }
                    if local_snap.segment_pages_range_total(sid).contains(addr) {
                        assert(local_snap.segment_pages_used_total(sid).contains(addr));
                        assert((old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr));
                        assert(false);
                    }
                    assert(false);
                }
            }
            assert(local.segments[sid].mem.os_rw_bytes() <=
                (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                    + local.segments[sid].mem.points_to.dom()) by {
                assert forall |addr: int| #[trigger] local.segments[sid].mem.os_rw_bytes().contains(addr) implies
                    ((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                        + local.segments[sid].mem.points_to.dom()).contains(addr) by {
                    if mask.bytes(sid).contains(addr) {
                        assert(local.segments[sid].mem.points_to.dom().contains(addr));
                    } else {
                        assert((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid)).contains(addr));
                    }
                }
            };
            assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid))
                <= local.segments[sid].mem.points_to.dom());
        }
    }

    let ghost local_before_decommit_expire_update = *local;
    proof {
        if !commit {
            assert(local.segments[sid].mem.os_rw_bytes() <=
                (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                    + local.segments[sid].mem.points_to.dom());
            assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid))
                <= local.segments[sid].mem.points_to.dom());
        }
    }

    if commit && segment.get_main_ref(Tracked(&*local)).decommit_mask.any_set(&mask) {
        segment_get_mut_main!(segment, local, main => {
            main.decommit_expire = clock_now().wrapping_add(option_decommit_delay());
        });
    }

    let ghost local_before_decommit_mask_clear = *local;
    proof {
        if !commit {
            assert(local_before_decommit_mask_clear == local_before_decommit_expire_update);
            assert(local_before_decommit_mask_clear.segments[sid].mem.os_rw_bytes() <=
                (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                    + local_before_decommit_mask_clear.segments[sid].mem.points_to.dom());
            assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid))
                <= local_before_decommit_mask_clear.segments[sid].mem.points_to.dom());
        }
    }
    segment_get_mut_main!(segment, local, main => {
        main.decommit_mask.clear(&mask);
    });

    proof {
        if !commit {
            assert(local_snap.wf_main_for_page_access());
            assert(local.segments.dom() == local_snap.segments.dom());
            assert(local.segments.dom().contains(sid));
            assert(segment.is_in(*local));
            assert(is_tld_ptr(local.tld.ptr(), local.tld_id));
            assert(local.thread_token.instance_id() == local.instance.id());
            assert(local.thread_token.key() == local.thread_id);
            assert(local.thread_id == local.is_thread@);
            assert(local.checked_token.instance_id() == local.instance.id());
            assert(local.checked_token.key() == local.thread_id);
            assert(local.my_inst.instance_id() == local.instance.id());
            assert(local.my_inst.value() == local.instance.id());
            assert(local.thread_token.value().segments.dom() == local.segments.dom());
            assert(local.thread_token.value().heap_id == local.heap_id);
            assert(local.heap.wf(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id(), local.page_empty_global@.s.points_to.ptr()));
            assert forall |page_id: PageId| #[trigger] local.pages.dom().contains(page_id) implies
                (local.unused_pages.dom().contains(page_id) <==> !local.thread_token.value().pages.dom().contains(page_id))
            by { }
            assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
            assert forall |page_id: PageId| #[trigger] local.pages.dom().contains(page_id) implies
                local.thread_token.value().pages.dom().contains(page_id) ==>
                    local.pages.index(page_id).wf(
                        page_id,
                        local.thread_token.value().pages.index(page_id),
                        local.instance,
                    )
            by { }
            assert forall |page_id: PageId| #[trigger] local.pages.dom().contains(page_id) implies
                local.unused_pages.dom().contains(page_id) ==>
                    local.pages.index(page_id).wf_unused(page_id, local.unused_pages[page_id], local.page_organization.popped, local.instance)
            by { }
            assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
                local.segments[segment_id].wf(
                    segment_id,
                    local.thread_token.value().segments.index(segment_id),
                    local.instance,
                )
            by {
                if segment_id != sid {
                    assert(local.segments[segment_id] == local_snap.segments[segment_id]);
                } else {
                    assert(local.segments[segment_id].main.id() == local_snap.segments[segment_id].main.id());
                    assert(local.segments[segment_id].main2.id() == local_snap.segments[segment_id].main2.id());
                    assert(local.thread_token.value().segments.index(segment_id).shared_access == local_snap.thread_token.value().segments.index(segment_id).shared_access);
                }
            }
            assert(local.tld.is_init());
            assert(local.page_organization.invariant());
            assert(page_organization_queues_match(local.page_organization.unused_dlist_headers,
                    local.tld.value().segments.span_queue_headers@));
            assert(page_organization_used_queues_match(local.page_organization.used_dlist_headers,
                    local.heap.pages.value()@));
            assert(page_organization_pages_match(local.page_organization.pages,
                    local.pages, local.psa, local.page_organization.popped));
            assert(page_organization_segments_match(local.page_organization.segments, local.segments));
            assert forall |page_id: PageId| #[trigger] local.page_organization.pages.dom().contains(page_id) implies
                (!local.page_organization.pages[page_id].is_used <==> local.unused_pages.dom().contains(page_id))
            by { }
            assert forall |page_id: PageId| #[trigger] local.page_organization.pages.dom().contains(page_id) implies
                local.page_organization.pages[page_id].is_used ==>
                    page_organization_matches_token_page(
                        local.page_organization.pages[page_id],
                        local.thread_token.value().pages[page_id])
            by { }
            assert forall |page_id: PageId| (#[trigger] local.unused_pages.dom().contains(page_id)) implies
                local.page_organization.pages.dom().contains(page_id)
            by { }
            assert forall |page_id: PageId| #[trigger] local.unused_pages.dom().contains(page_id) implies
                local.unused_pages[page_id] == local.psa[page_id]
            by { }
            assert forall |page_id: PageId| #[trigger] local.thread_token.value().pages.dom().contains(page_id) implies
                local.thread_token.value().pages[page_id].shared_access == local.psa[page_id]
            by { }
            assert(local.page_organization_valid());
            assert(local.page_empty_global@.wf_empty_page_global());
            assert(local.wf_main_for_page_access());
            assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
                local.mem_chunk_good(segment_id)
            by {
                if segment_id != sid {
                    assert(local.segments.dom() == local_snap.segments.dom());
                    assert(local.segments[segment_id] == local_snap.segments[segment_id]);
                    assert(local.segments[segment_id].mem == local_snap.segments[segment_id].mem);
                    assert(local.commit_mask(segment_id) == local_snap.commit_mask(segment_id));
                    assert(local.decommit_mask(segment_id) == local_snap.decommit_mask(segment_id));
                    assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.is_used_primary(pid) == local_snap.is_used_primary(pid) by {
                        assert(local.page_organization == local_snap.page_organization);
                    }
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.page_count(pid) == local_snap.page_count(pid) by {
                        assert(local.pages == local_snap.pages);
                    }
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.page_capacity(pid) == local_snap.page_capacity(pid) by {
                        assert(local.pages == local_snap.pages);
                    }
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.block_size(pid) == local_snap.block_size(pid) by {
                        assert(local.pages == local_snap.pages);
                    }
                    local.segment_metadata_update_preserves_mem_chunk_good(local_snap, segment_id);
                } else {
                    assert(segment_id == sid);
                    assert(local.segments.dom().contains(sid));
                    assert(local_snap.mem_chunk_good(sid));
                    assert(local.segments[sid].mem == local_before_decommit_mask_clear.segments[sid].mem);
                    assert(local_before_decommit_mask_clear.segments[sid].mem.wf());
                    assert(local_before_decommit_mask_clear.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
                    assert(local_before_decommit_mask_clear.segments[sid].mem.points_to.provenance() == sid.provenance);
                    assert(local.segments[sid].mem.wf());
                    assert(local.segments[sid].mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
                    assert(local.segments[sid].mem.points_to.provenance() == sid.provenance);
                    assert(local.commit_mask(sid).bytes(sid).subset_of(local.segments[sid].mem.os_rw_bytes()));
                    let old_commit = local_snap.commit_mask(sid);
                    let old_decommit = local_snap.decommit_mask(sid);
                    let final_commit = local.commit_mask(sid);
                    let final_decommit = local.decommit_mask(sid);
                    assert(old_decommit.bytes(sid) <= old_commit.bytes(sid));
                    lemma_segment_commit_mask_view_subset_from_bytes_subset(&old_decommit, &old_commit, sid);
                    assert(mask@ <= old_decommit@);
                    lemma_segment_commit_mask_bytes_subset(&mask, &old_decommit, sid);
                    assert(local_before_decommit_mask_clear.decommit_mask(sid) == old_decommit);
                    assert(final_decommit@ =~= old_decommit@ - mask@);
                    assert(final_decommit@ <= old_decommit@);
                    lemma_segment_commit_mask_bytes_subset(&final_decommit, &old_decommit, sid);
                    assert((old_commit@ - mask@) <= final_commit@);
                    assert(final_decommit@ <= final_commit@) by {
                        assert forall |bit: int| #[trigger] final_decommit@.contains(bit) implies
                            final_commit@.contains(bit) by {
                            assert(old_decommit@.contains(bit));
                            assert(!mask@.contains(bit));
                            assert(old_commit@.contains(bit));
                            assert((old_commit@ - mask@).contains(bit));
                        }
                    }
                    lemma_segment_commit_mask_bytes_subset(&final_decommit, &final_commit, sid);
                    assert((old_commit.bytes(sid) - old_decommit.bytes(sid))
                        <= (final_commit.bytes(sid) - final_decommit.bytes(sid))) by {
                        assert forall |addr: int| #[trigger] (old_commit.bytes(sid) - old_decommit.bytes(sid)).contains(addr) implies
                            (final_commit.bytes(sid) - final_decommit.bytes(sid)).contains(addr) by {
                            lemma_segment_commit_mask_bytes_contains(&old_commit, sid, addr);
                            lemma_segment_commit_mask_bytes_contains(&old_decommit, sid, addr);
                            lemma_segment_commit_mask_bytes_contains(&final_decommit, sid, addr);
                            let bit = segment_commit_mask_byte_bit(sid, addr);
                            assert(old_commit@.contains(bit));
                            assert(!old_decommit.bytes(sid).contains(addr));
                            if final_decommit.bytes(sid).contains(addr) {
                                assert(old_decommit.bytes(sid).contains(addr));
                                assert(false);
                            }
                            if mask@.contains(bit) {
                                lemma_segment_commit_mask_bytes_contains(&mask, sid, addr);
                                assert(mask.bytes(sid).contains(addr));
                                assert(old_decommit.bytes(sid).contains(addr));
                                assert(false);
                            }
                            assert((old_commit@ - mask@).contains(bit));
                            assert(final_commit@.contains(bit));
                            lemma_segment_commit_mask_bytes_contains(&final_commit, sid, addr);
                            assert(final_commit.bytes(sid).contains(addr));
                        }
                    }
                    assert(local.decommit_mask(sid).bytes(sid) <= local.commit_mask(sid).bytes(sid));
                    assert(segment_info_range(sid) <= local.commit_mask(sid).bytes(sid) - local.decommit_mask(sid).bytes(sid));
                    assert(local.page_organization == local_snap.page_organization);
                    assert(local.pages == local_snap.pages);
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.is_used_primary(pid) == local_snap.is_used_primary(pid) by { }
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.page_count(pid) == local_snap.page_count(pid) by { }
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.page_capacity(pid) == local_snap.page_capacity(pid) by { }
                    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                        local.block_size(pid) == local_snap.block_size(pid) by { }
                    local.segment_page_totals_preserved(local_snap, sid);
                    assert(local_snap.segment_pages_used_total(sid) <= old_commit.bytes(sid) - old_decommit.bytes(sid));
                    assert(local.segment_pages_used_total(sid) <= local.commit_mask(sid).bytes(sid) - local.decommit_mask(sid).bytes(sid));
                    assert(local.segments[sid].mem.os_rw_bytes() <=
                        local.segments[sid].mem.points_to.dom()
                            + segment_info_range(sid)
                            + local.segment_pages_range_total(sid)) by {
                        assert forall |addr: int| #[trigger] local.segments[sid].mem.os_rw_bytes().contains(addr) implies
                            (local.segments[sid].mem.points_to.dom()
                                + segment_info_range(sid)
                                + local.segment_pages_range_total(sid)).contains(addr) by {
                            if local.segments[sid].mem.points_to.dom().contains(addr) {
                            } else {
                                assert(local_before_decommit_mask_clear.segments[sid].mem.os_rw_bytes() <=
                                    (local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid))
                                        + local_before_decommit_mask_clear.segments[sid].mem.points_to.dom());
                                assert(local.segments[sid].mem == local_before_decommit_mask_clear.segments[sid].mem);
                                assert((local_snap.segments[sid].mem.os_rw_bytes() - mask.bytes(sid)).contains(addr));
                                assert(local_snap.segments[sid].mem.os_rw_bytes().contains(addr));
                                assert(!mask.bytes(sid).contains(addr));
                                assert(local_snap.segments[sid].mem.os_rw_bytes() <=
                                    local_snap.segments[sid].mem.points_to.dom()
                                        + segment_info_range(sid)
                                        + local_snap.segment_pages_range_total(sid));
                                if local_snap.segments[sid].mem.points_to.dom().contains(addr) {
                                    assert((local_snap.segments[sid].mem.points_to.dom() - mask.bytes(sid)).contains(addr));
                                    assert(local_before_decommit_mask_clear.segments[sid].mem.points_to.dom().contains(addr));
                                    assert(local.segments[sid].mem.points_to.dom().contains(addr));
                                    assert(false);
                                }
                                if segment_info_range(sid).contains(addr) {
                                } else {
                                    assert(local_snap.segment_pages_range_total(sid).contains(addr));
                                    assert(local.segment_pages_range_total(sid).contains(addr));
                                }
                            }
                        }
                    };
                    assert(local.mem_chunk_good(segment_id));
                }
            }
            assert(local.wf_main());
        }
    }

    proof {
        assert(local.page_organization == local_snap.page_organization);
        assert(local.pages == local_snap.pages);
        assert(local.psa == local_snap.psa);
        assert(local.unused_pages == local_snap.unused_pages);
        assert(local.thread_token == local_snap.thread_token);
        assert(local.thread_id == local_snap.thread_id);
        assert(local.heap == local_snap.heap);
        assert(local.tld == local_snap.tld);
        assert(local.segments.dom() == local_snap.segments.dom());
        assert(segment.is_in(*local));
        if local_snap.wf_main() {
            local_snap.wf_main_implies_page_access();
        }
        assert(local_snap.wf_main_for_page_access());
        assert(local.thread_token == local_snap.thread_token);
        assert(local.instance == local_snap.instance);
        assert(local.segments[sid].main.id() == local_snap.segments[sid].main.id());
        assert(local.segments[sid].main2 == local_snap.segments[sid].main2);
        assert(local.segments[sid].wf(
            sid,
            local.thread_token.value().segments.index(sid),
            local.instance));
        if local_snap.mem_chunk_good(sid) {
            if commit {
                let old_commit = local_snap.commit_mask(sid);
                let old_decommit = local_snap.decommit_mask(sid);
                let final_commit = local.commit_mask(sid);
                let final_decommit = local.decommit_mask(sid);
                assert(local_before_decommit_mask_clear.decommit_mask(sid) == old_decommit);
                assert(final_decommit@ =~= old_decommit@ - mask@);
                assert(final_decommit@ <= old_decommit@);
                lemma_segment_commit_mask_bytes_subset(&final_decommit, &old_decommit, sid);
                assert(old_commit@ <= final_commit@);
                lemma_segment_commit_mask_bytes_subset(&old_commit, &final_commit, sid);
                assert(local.commit_mask(sid).bytes(sid) <= local.segments[sid].mem.os_rw_bytes());
                assert(local.segments[sid].mem.has_new_pointsto(&local_snap.segments[sid].mem));
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                    local.is_used_primary(pid) == local_snap.is_used_primary(pid) by { }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                    local.page_count(pid) == local_snap.page_count(pid) by { }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                    local.page_capacity(pid) == local_snap.page_capacity(pid) by { }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) ==>
                    local.block_size(pid) == local_snap.block_size(pid) by { }
                local.mem_chunk_good_preserved_by_commit_update(local_snap, sid);
            }
            assert(local.mem_chunk_good(sid));
        }
        if commit {
            if local_snap.wf_main() {
                assert(local_snap.segments.dom().contains(sid));
                assert(local_snap.mem_chunk_good(sid));
            }
            assert(local.segments[sid].mem.has_new_pointsto(&local_snap.segments[sid].mem));
        }
        if commit && size != 0 && size <= SEGMENT_SIZE as usize
            && segment.segment_ptr.addr() <= p
            && p as int % COMMIT_SIZE as int == 0
            && size as int % COMMIT_SIZE as int == 0
            && p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int
        {
            lemma_segment_ptr_commit_aligned(segment);
            assert(start.addr() == p);
            assert(full_size == size);
            assert(mask@ =~= Set::range(
                (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int,
                (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int,
            ));
            lemma_segment_commit_mask_aligned_bytes(&mask, segment, p, size);
            let requested = set_int_range(p as int, p as int + size as int);
            let old_commit = local_snap.commit_mask(sid);
            let old_decommit = local_snap.decommit_mask(sid);
            let final_commit = local.commit_mask(sid);
            let final_decommit = local.decommit_mask(sid);
            assert(final_commit == local_before_decommit_mask_clear.commit_mask(sid));
            assert(local_before_decommit_mask_clear.decommit_mask(sid) == old_decommit);
            assert(final_decommit@ =~= old_decommit@ - mask@);
            if mask@ <= old_commit@ {
                assert(old_commit@ <= final_commit@);
                assert(mask@ <= final_commit@);
            } else {
                assert(local_before_decommit_expire_update.commit_mask(sid)@ =~= old_commit@ + mask@);
                assert(local_before_decommit_mask_clear.commit_mask(sid) ==
                    local_before_decommit_expire_update.commit_mask(sid));
                assert(mask@ <= final_commit@) by {
                    assert forall |bit: int| #[trigger] mask@.contains(bit) implies final_commit@.contains(bit) by {
                        assert((old_commit@ + mask@).contains(bit));
                    }
                };
            }
            lemma_segment_commit_mask_bytes_subset(&mask, &final_commit, sid);
            assert(mask.bytes(sid) <= final_commit.bytes(sid));
            assert(final_decommit@.disjoint(mask@));
            lemma_segment_commit_mask_bytes_disjoint(&final_decommit, &mask, sid);
            assert(mask.bytes(sid).disjoint(final_decommit.bytes(sid)));
            assert(requested <= final_commit.bytes(sid) - final_decommit.bytes(sid)) by {
                assert forall |addr: int| #[trigger] requested.contains(addr) implies
                    (final_commit.bytes(sid) - final_decommit.bytes(sid)).contains(addr) by {
                    assert(mask.bytes(sid).contains(addr));
                    assert(final_commit.bytes(sid).contains(addr));
                    assert(!final_decommit.bytes(sid).contains(addr));
                }
            };
        }
        assert(local.wf_main_for_page_access());
        if !commit {
            assert(local.page_organization == local_snap.page_organization);
            assert(local.pages == local_snap.pages);
            assert(local.psa == local_snap.psa);
            assert(local.unused_pages == local_snap.unused_pages);
            assert(local.thread_token == local_snap.thread_token);
            assert(local.heap == local_snap.heap);
            assert(local.tld == local_snap.tld);
            assert(local.segments.dom() == local_snap.segments.dom());
        }
    }
    return true;
}

#[verus_verify]
pub fn segment_ensure_committed(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>
) -> (success: bool)
    requires
        local.wf_main() || (local.wf_main_for_page_access() && local.mem_chunk_good(segment.segment_id@)),
        segment.segment_ptr.addr() != 0,
        segment.wf(),
        segment.is_in(*local),
        size != 0 && size <= SEGMENT_SIZE as usize ==> segment.segment_ptr.addr() <= p,
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
        final(local).unused_pages == old(local).unused_pages,
        final(local).thread_token == old(local).thread_token,
        final(local).thread_id == old(local).thread_id,
        final(local).heap == old(local).heap,
        final(local).tld == old(local).tld,
        final(local).segments.dom() == old(local).segments.dom(),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) && sid != segment.segment_id@ ==>
            final(local).segments[sid] == old(local).segments[sid],
        segment.is_in(*final(local)),
        final(local).segments[segment.segment_id@].wf(
            segment.segment_id@,
            final(local).thread_token.value().segments.index(segment.segment_id@),
            final(local).instance),
        final(local).segments[segment.segment_id@].main2 == old(local).segments[segment.segment_id@].main2,
        old(local).mem_chunk_good(segment.segment_id@) ==> final(local).mem_chunk_good(segment.segment_id@),
        success ==> final(local).segments[segment.segment_id@].mem.has_new_pointsto(
            &old(local).segments[segment.segment_id@].mem),
        success && size != 0 && size <= SEGMENT_SIZE as usize
            && segment.segment_ptr.addr() <= p
            && p as int % COMMIT_SIZE as int == 0
            && size as int % COMMIT_SIZE as int == 0
            && p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int ==>
                set_int_range(p as int, p as int + size as int)
                    <= final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
                        - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),
        final(local).wf_main_for_page_access(),
{
    if segment.get_commit_mask(Tracked(&*local)).is_full()
        && segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.segments[segment.segment_id@].wf(
                segment.segment_id@,
                local.thread_token.value().segments.index(segment.segment_id@),
                local.instance));
            assert(local.segments[segment.segment_id@].mem == old(local).segments[segment.segment_id@].mem);
            if size != 0 && size <= SEGMENT_SIZE as usize
                && segment.segment_ptr.addr() <= p
                && p as int % COMMIT_SIZE as int == 0
                && size as int % COMMIT_SIZE as int == 0
                && p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int
            {
                lemma_segment_ptr_commit_aligned(segment);
                let sid = segment.segment_id@;
                let commit_mask = local.commit_mask(sid);
                let decommit_mask = local.decommit_mask(sid);
                let requested = set_int_range(p as int, p as int + size as int);
                assert(commit_mask@ =~= Set::range(0, COMMIT_MASK_BITS as int));
                assert(decommit_mask@ =~= Set::empty());
                lemma_empty_commit_mask_bytes(&decommit_mask, sid);
                assert(decommit_mask.bytes(sid) =~= Set::empty());
                assert(requested <= commit_mask.bytes(sid)) by {
                    assert forall |addr: int| #[trigger] requested.contains(addr) implies
                        commit_mask.bytes(sid).contains(addr) by {
                        let bit = segment_commit_mask_byte_bit(sid, addr);
                        assert(segment.segment_ptr as int == segment_start(sid));
                        assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
                        assert(p as int <= addr < p as int + size as int);
                        assert(segment_start(sid) <= addr < segment_start(sid) + SEGMENT_SIZE as int) by(nonlinear_arith)
                            requires
                                segment.segment_ptr as int == segment_start(sid),
                                segment.segment_ptr.addr() as int == segment.segment_ptr as int,
                                segment.segment_ptr.addr() <= p,
                                p as int <= addr,
                                addr < p as int + size as int,
                                p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int;
                        let rel_addr = addr - segment_start(sid);
                        assert(0 <= rel_addr < SEGMENT_SIZE as int) by(nonlinear_arith)
                            requires
                                segment_start(sid) <= addr,
                                addr < segment_start(sid) + SEGMENT_SIZE as int,
                                rel_addr == addr - segment_start(sid);
                        assert(COMMIT_SIZE as int > 0) by(compute_only);
                        lemma_div_is_ordered(0, rel_addr, COMMIT_SIZE as int);
                        assert(0 <= bit);
                        assert(SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int) by(compute_only);
                        lemma_div_is_ordered(rel_addr, SEGMENT_SIZE as int, COMMIT_SIZE as int);
                        lemma_div_multiples_vanish(COMMIT_MASK_BITS as int, COMMIT_SIZE as int);
                        assert(SEGMENT_SIZE as int / COMMIT_SIZE as int == COMMIT_MASK_BITS as int);
                        assert(bit < COMMIT_MASK_BITS as int);
                        assert(commit_mask@.contains(bit));
                        assert(segment_commit_mask_bit_bytes(sid, bit).contains(addr)) by {
                            assert(bit == rel_addr / COMMIT_SIZE as int);
                            lemma_fundamental_div_mod(rel_addr, COMMIT_SIZE as int);
                            assert(rel_addr == COMMIT_SIZE as int * bit + rel_addr % COMMIT_SIZE as int);
                            assert(0 <= rel_addr % (COMMIT_SIZE as int));
                            assert(rel_addr % (COMMIT_SIZE as int) < COMMIT_SIZE as int);
                        }
                        lemma_segment_commit_mask_bytes_contains(&commit_mask, sid, addr);
                    }
                };
                assert(requested <= commit_mask.bytes(sid) - decommit_mask.bytes(sid)) by {
                    assert forall |addr: int| #[trigger] requested.contains(addr) implies
                        (commit_mask.bytes(sid) - decommit_mask.bytes(sid)).contains(addr) by {
                        assert(commit_mask.bytes(sid).contains(addr));
                        assert(!decommit_mask.bytes(sid).contains(addr));
                    }
                };
            }
        }

        return true;
    }

    segment_commitx(segment, true, p, size, Tracked(local))
}

#[verifier::rlimit(200)]
pub proof fn lemma_segment_ptr_commit_aligned(segment: SegmentPtr)
    requires
        segment.wf(),
    ensures
        segment.segment_ptr as int % COMMIT_SIZE as int == 0,
{
    lemma_segment_commit_mask_constants();
    lemma_segment_start_basics(segment.segment_id@);
    assert(segment.segment_ptr as int == segment_start(segment.segment_id@));
    assert(segment.segment_ptr as int % SEGMENT_SIZE as int == 0);
    lemma_fundamental_div_mod(segment.segment_ptr as int, SEGMENT_SIZE as int);
    assert(segment.segment_ptr as int == SEGMENT_SIZE as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int));
    assert(segment.segment_ptr as int == COMMIT_SIZE as int * (COMMIT_MASK_BITS as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int))) by(nonlinear_arith)
        requires
            segment.segment_ptr as int == SEGMENT_SIZE as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int),
            SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int;
    lemma_mod_multiples_basic(COMMIT_MASK_BITS as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int), COMMIT_SIZE as int);
}

#[verifier::rlimit(200)]
proof fn lemma_segment_commit_mask_aligned_bytes(mask: &CommitMask, segment: SegmentPtr, p: usize, size: usize)
    requires
        segment.wf(),
        size != 0,
        size <= SEGMENT_SIZE as usize,
        segment.segment_ptr.addr() <= p,
        p as int % COMMIT_SIZE as int == 0,
        size as int % COMMIT_SIZE as int == 0,
        p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int,
        mask@ =~= Set::range(
            (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int,
            (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int,
        ),
    ensures
        mask.bytes(segment.segment_id@) =~= set_int_range(p as int, p as int + size as int),
{
    lemma_segment_commit_mask_constants();
    lemma_segment_ptr_commit_aligned(segment);
    let sid = segment.segment_id@;
    let d = COMMIT_SIZE as int;
    let rel = p as int - segment.segment_ptr as int;
    let lo = rel / d;
    let hi = (rel + size as int) / d;
    assert(segment.segment_ptr as int == segment_start(sid));
    assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
    assert(rel >= 0) by(nonlinear_arith)
        requires
            segment.segment_ptr.addr() <= p,
            segment.segment_ptr.addr() as int == segment.segment_ptr as int,
            rel == p as int - segment.segment_ptr as int;
    lemma_fundamental_div_mod(p as int, d);
    lemma_fundamental_div_mod(segment.segment_ptr as int, d);
    assert(p as int == d * (p as int / d));
    assert(segment.segment_ptr as int == d * (segment.segment_ptr as int / d));
    assert(rel == d * ((p as int / d) - (segment.segment_ptr as int / d))) by(nonlinear_arith)
        requires
            rel == p as int - segment.segment_ptr as int,
            p as int == d * (p as int / d),
            segment.segment_ptr as int == d * (segment.segment_ptr as int / d);
    lemma_mod_multiples_basic((p as int / d) - (segment.segment_ptr as int / d), d);
    assert(rel % d == 0);
    lemma_div_pos_is_pos(rel, d);
    assert(0 <= lo);
    lemma_div_is_ordered(rel, rel + size as int, d);
    assert(lo <= hi);
    assert(rel + size as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
        requires
            p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int,
            rel == p as int - segment.segment_ptr as int;
    lemma_div_is_ordered(rel + size as int, SEGMENT_SIZE as int, d);
    assert(SEGMENT_SIZE as int == d * COMMIT_MASK_BITS as int) by(nonlinear_arith)
        requires
            SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int,
            d == COMMIT_SIZE as int;
    lemma_div_multiples_vanish(COMMIT_MASK_BITS as int, d);
    assert(SEGMENT_SIZE as int / d == COMMIT_MASK_BITS as int);
    assert(hi <= COMMIT_MASK_BITS as int);
    lemma_fundamental_div_mod(rel, d);
    assert(rel == d * lo);
    lemma_add_mod_noop(rel, size as int, d);
    assert((rel + size as int) % d == 0);
    lemma_fundamental_div_mod(rel + size as int, d);
    assert(rel + size as int == d * hi);
    lemma_segment_commit_mask_bytes_range(mask, sid, lo, hi);
    assert(segment_start(sid) + lo * d == p as int) by(nonlinear_arith)
        requires
            segment.segment_ptr as int == segment_start(sid),
            rel == p as int - segment.segment_ptr as int,
            rel == d * lo;
    assert(segment_start(sid) + hi * d == p as int + size as int) by(nonlinear_arith)
        requires
            segment.segment_ptr as int == segment_start(sid),
            rel == p as int - segment.segment_ptr as int,
            rel + size as int == d * hi;
}

#[verifier::rlimit(200)]
proof fn lemma_segment_main_metadata_update_preserves_wf_main(local: Local, old_local: Local, sid: SegmentId)
    requires
        old_local.wf_main(),
        local.thread_id == old_local.thread_id,
        local.my_inst == old_local.my_inst,
        local.instance == old_local.instance,
        local.thread_token == old_local.thread_token,
        local.checked_token == old_local.checked_token,
        local.is_thread == old_local.is_thread,
        local.heap_id == old_local.heap_id,
        local.heap == old_local.heap,
        local.tld_id == old_local.tld_id,
        local.tld == old_local.tld,
        local.pages == old_local.pages,
        local.psa == old_local.psa,
        local.unused_pages == old_local.unused_pages,
        local.page_organization == old_local.page_organization,
        local.page_empty_global == old_local.page_empty_global,
        local.segments.dom() == old_local.segments.dom(),
        local.segments.dom().contains(sid),
        local.segments[sid].mem == old_local.segments[sid].mem,
        local.segments[sid].main.id() == old_local.segments[sid].main.id(),
        local.segments[sid].main2 == old_local.segments[sid].main2,
        local.segments[sid].main2.id() == old_local.segments[sid].main2.id(),
        local.commit_mask(sid) == old_local.commit_mask(sid),
        local.decommit_mask(sid) == old_local.decommit_mask(sid),
        forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) && segment_id != sid ==>
            local.segments[segment_id] == old_local.segments[segment_id],
    ensures
        local.wf_main(),
{
    assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
        local.segments[segment_id].wf(
            segment_id,
            local.thread_token.value().segments.index(segment_id),
            local.instance,
        ) by {
        if segment_id != sid {
            assert(local.segments[segment_id] == old_local.segments[segment_id]);
        } else {
            assert(local.thread_token.value().segments.index(segment_id).shared_access == old_local.thread_token.value().segments.index(segment_id).shared_access);
        }
    }
    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
        local.is_used_primary(pid) == old_local.is_used_primary(pid) by { }
    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
        local.page_count(pid) == old_local.page_count(pid) by { }
    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
        local.page_capacity(pid) == old_local.page_capacity(pid) by { }
    assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
        local.block_size(pid) == old_local.block_size(pid) by { }
    assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
        local.mem_chunk_good(segment_id) by {
        if segment_id != sid {
            assert(local.segments[segment_id] == old_local.segments[segment_id]);
        }
        local.segment_metadata_update_preserves_mem_chunk_good(old_local, segment_id);
    }
    assert(page_organization_segments_match(local.page_organization.segments, local.segments)) by {
        assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
            local.page_organization.segments[segment_id].used == local.segments[segment_id].main2.value().used by {
            if segment_id != sid {
                assert(local.segments[segment_id] == old_local.segments[segment_id]);
            } else {
                assert(local.segments[segment_id].main2 == old_local.segments[segment_id].main2);
            }
        }
    }
    assert(local.page_organization_valid());
    assert(local.wf_main());
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn segment_perhaps_decommit(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        local.wf_main(),
        segment.wf(),
        segment.is_in(*local),
        size != 0 && size <= SEGMENT_SIZE as usize ==> segment.segment_ptr.addr() <= p,
        size != 0 && size <= SEGMENT_SIZE as usize ==> p as int % COMMIT_SIZE as int == 0,
        size != 0 && size <= SEGMENT_SIZE as usize ==> size as int % COMMIT_SIZE as int == 0,
        size != 0 && size <= SEGMENT_SIZE as usize ==> p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int,
        size != 0 && size <= SEGMENT_SIZE as usize ==>
            set_int_range(p as int, p as int + size as int).disjoint(segment_info_range(segment.segment_id@)),
        size != 0 && size <= SEGMENT_SIZE as usize ==>
            set_int_range(p as int, p as int + size as int).disjoint(local.segment_pages_used_total(segment.segment_id@)),
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).wf_main(),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
        final(local).unused_pages == old(local).unused_pages,
        final(local).segments.dom() == old(local).segments.dom(),
        segment.is_in(*final(local)),
{
    let ghost local_initial = *local;
    let ghost sid = segment.segment_id@;
    proof {
        lemma_segment_commit_mask_constants();
        lemma_segment_ptr_commit_aligned(segment);
    }

    if !segment.get_allow_decommit(Tracked(&*local)) {
        return;
    }

    if option_decommit_delay() == 0 {
        todo();
    } else {

        let mut mask: CommitMask = CommitMask::empty();
        proof {
            assert(mask.concrete_empty());
            lemma_segment_start_page_aligned(sid);
            assert(segment.segment_ptr as int == segment_start(sid));
            assert(segment.segment_ptr as int % page_size() == 0);
            assert(SEGMENT_SIZE as int % page_size() == 0) by(compute_only);
            lemma_page_aligned_end_fits(segment.segment_ptr as int, SEGMENT_SIZE as int);
            assert((segment.segment_ptr as int) + (SEGMENT_SIZE as int) < (usize::MAX as int));
            assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
            assert((segment.segment_ptr.addr() as int) + (SEGMENT_SIZE as int) <= (usize::MAX as int));
            assert((segment.segment_ptr.addr() as int) + (SEGMENT_SIZE as int) + page_size() - 1 <= (usize::MAX as int));
        }
        let (start, full_size) =
            segment_commit_mask(segment.segment_ptr as *mut u8, true, p, size, &mut mask);

        if mask.is_empty() || full_size == 0 {
            return;
        }

        proof {
            assert(full_size != 0);
            assert(size != 0 && size <= SEGMENT_SIZE as usize);
            assert(segment.segment_ptr.addr() <= p);
            assert(p as int % COMMIT_SIZE as int == 0);
            assert(size as int % COMMIT_SIZE as int == 0);
            assert(p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int);
            assert(segment.segment_ptr as int % COMMIT_SIZE as int == 0);
            assert(start.addr() == p);
            assert(full_size == size);
            assert(mask@ =~= Set::range(
                (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int,
                (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int,
            ));
            lemma_segment_commit_mask_aligned_bytes(&mask, segment, p, size);
        }

        let ghost local_before_decommit_mask_set = *local;
        let mut cmask = CommitMask::empty();
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.create_intersect(&mask, &mut cmask);
            main.decommit_mask.set(&cmask);
        });

        proof {
            let range = set_int_range(p as int, p as int + size as int);
            assert(local_before_decommit_mask_set == local_initial);
            assert(range.disjoint(segment_info_range(sid)));
            assert(range.disjoint(local_before_decommit_mask_set.segment_pages_used_total(sid)));
            assert(mask.bytes(sid) =~= range);
            let old_commit = local_before_decommit_mask_set.commit_mask(sid);
            let old_decommit = local_before_decommit_mask_set.decommit_mask(sid);
            let final_decommit = local.decommit_mask(sid);
            assert(local.segments.dom() == local_before_decommit_mask_set.segments.dom());
            assert(local.segments[sid].mem == local_before_decommit_mask_set.segments[sid].mem);
            assert(local.commit_mask(sid) == old_commit);
            assert(cmask@ =~= old_commit@.intersect(mask@));
            assert(final_decommit@ =~= old_decommit@ + cmask@);
            assert(cmask@ <= old_commit@) by {
                assert forall |bit: int| #[trigger] cmask@.contains(bit) implies old_commit@.contains(bit) by {
                    assert(old_commit@.intersect(mask@).contains(bit));
                }
            }
            assert(cmask@ <= mask@) by {
                assert forall |bit: int| #[trigger] cmask@.contains(bit) implies mask@.contains(bit) by {
                    assert(old_commit@.intersect(mask@).contains(bit));
                }
            }
            assert(old_decommit.bytes(sid) <= old_commit.bytes(sid));
            lemma_segment_commit_mask_view_subset_from_bytes_subset(&old_decommit, &old_commit, sid);
            assert(old_decommit@ <= old_commit@);
            assert(final_decommit@ <= old_commit@) by {
                assert forall |bit: int| #[trigger] final_decommit@.contains(bit) implies old_commit@.contains(bit) by {
                    assert((old_decommit@ + cmask@).contains(bit));
                }
            }
            lemma_segment_commit_mask_bytes_subset(&final_decommit, &old_commit, sid);
            lemma_segment_commit_mask_bytes_subset(&cmask, &mask, sid);
            assert(cmask.bytes(sid) <= range);

            assert(local.page_organization.pages.dom() == local_before_decommit_mask_set.page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_before_decommit_mask_set.is_used_primary(pid) by {
                assert(local.page_organization == local_before_decommit_mask_set.page_organization);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_count(pid) == local_before_decommit_mask_set.page_count(pid) by {
                assert(local.pages == local_before_decommit_mask_set.pages);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_capacity(pid) == local_before_decommit_mask_set.page_capacity(pid) by {
                assert(local.pages == local_before_decommit_mask_set.pages);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.block_size(pid) == local_before_decommit_mask_set.block_size(pid) by {
                assert(local.pages == local_before_decommit_mask_set.pages);
            }
            local.segment_page_totals_preserved(local_before_decommit_mask_set, sid);

            assert(segment_info_range(sid) <= old_commit.bytes(sid) - final_decommit.bytes(sid)) by {
                assert forall |addr: int| #[trigger] segment_info_range(sid).contains(addr) implies
                    (old_commit.bytes(sid) - final_decommit.bytes(sid)).contains(addr) by {
                    assert(local_before_decommit_mask_set.mem_chunk_good(sid));
                    assert(old_commit.bytes(sid).contains(addr));
                    assert(!old_decommit.bytes(sid).contains(addr));
                    if final_decommit.bytes(sid).contains(addr) {
                        lemma_segment_commit_mask_bytes_contains(&final_decommit, sid, addr);
                        let bit = segment_commit_mask_byte_bit(sid, addr);
                        assert(final_decommit@.contains(bit));
                        assert((old_decommit@ + cmask@).contains(bit));
                        if old_decommit@.contains(bit) {
                            lemma_segment_commit_mask_bytes_contains(&old_decommit, sid, addr);
                            assert(old_decommit.bytes(sid).contains(addr));
                            assert(false);
                        }
                        if cmask@.contains(bit) {
                            lemma_segment_commit_mask_bytes_contains(&cmask, sid, addr);
                            assert(cmask.bytes(sid).contains(addr));
                            assert(range.contains(addr));
                            assert(false);
                        }
                    }
                }
            }
            assert(local.segment_pages_used_total(sid) <= old_commit.bytes(sid) - final_decommit.bytes(sid)) by {
                assert forall |addr: int| #[trigger] local.segment_pages_used_total(sid).contains(addr) implies
                    (old_commit.bytes(sid) - final_decommit.bytes(sid)).contains(addr) by {
                    assert(local.segment_pages_used_total(sid) =~= local_before_decommit_mask_set.segment_pages_used_total(sid));
                    assert(local_before_decommit_mask_set.segment_pages_used_total(sid).contains(addr));
                    assert(local_before_decommit_mask_set.mem_chunk_good(sid));
                    assert(old_commit.bytes(sid).contains(addr));
                    assert(!old_decommit.bytes(sid).contains(addr));
                    if final_decommit.bytes(sid).contains(addr) {
                        lemma_segment_commit_mask_bytes_contains(&final_decommit, sid, addr);
                        let bit = segment_commit_mask_byte_bit(sid, addr);
                        assert(final_decommit@.contains(bit));
                        assert((old_decommit@ + cmask@).contains(bit));
                        if old_decommit@.contains(bit) {
                            lemma_segment_commit_mask_bytes_contains(&old_decommit, sid, addr);
                            assert(old_decommit.bytes(sid).contains(addr));
                            assert(false);
                        }
                        if cmask@.contains(bit) {
                            lemma_segment_commit_mask_bytes_contains(&cmask, sid, addr);
                            assert(cmask.bytes(sid).contains(addr));
                            assert(range.contains(addr));
                            assert(false);
                        }
                    }
                }
            }
            assert(local.mem_chunk_good(sid));
            assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
                local.mem_chunk_good(segment_id) by {
                if segment_id == sid {
                    assert(local.mem_chunk_good(sid));
                } else {
                    assert(local.segments[segment_id] == local_before_decommit_mask_set.segments[segment_id]);
                    assert(local.commit_mask(segment_id) == local_before_decommit_mask_set.commit_mask(segment_id));
                    assert(local.decommit_mask(segment_id) == local_before_decommit_mask_set.decommit_mask(segment_id));
                    local.segment_metadata_update_preserves_mem_chunk_good(local_before_decommit_mask_set, segment_id);
                }
            }
            assert forall |segment_id: SegmentId| #[trigger] local.segments.dom().contains(segment_id) implies
                local.segments[segment_id].wf(
                    segment_id,
                    local.thread_token.value().segments.index(segment_id),
                    local.instance,
                ) by {
                if segment_id != sid {
                    assert(local.segments[segment_id] == local_before_decommit_mask_set.segments[segment_id]);
                } else {
                    assert(local.segments[segment_id].main.id() == local_before_decommit_mask_set.segments[segment_id].main.id());
                    assert(local.segments[segment_id].main2.id() == local_before_decommit_mask_set.segments[segment_id].main2.id());
                    assert(local.thread_token.value().segments.index(segment_id).shared_access == local_before_decommit_mask_set.thread_token.value().segments.index(segment_id).shared_access);
                }
            }
            assert(local.wf_main());
            assert(segment.is_in(*local));
        }

        let ghost local_snap = *local;

        let now = clock_now();
        if segment.get_decommit_expire(Tracked(&*local)) == 0 {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire = now.wrapping_add(option_decommit_delay());
            });
            proof {
                lemma_segment_main_metadata_update_preserves_wf_main(*local, local_snap, sid);
                assert(segment.is_in(*local));
            }
        } else if segment.get_decommit_expire(Tracked(&*local)) <= now {
            let ded = option_decommit_extend_delay();
            if segment.get_decommit_expire(Tracked(&*local)).wrapping_add(option_decommit_extend_delay()) <= now {
                segment_delayed_decommit(segment, true, Tracked(&mut *local));
            } else {
                segment_get_mut_main!(segment, local, main => {
                    main.decommit_expire = now.wrapping_add(option_decommit_extend_delay());
                });
                proof {
                    lemma_segment_main_metadata_update_preserves_wf_main(*local, local_snap, sid);
                    assert(segment.is_in(*local));
                }
            }
        } else {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire =
                    main.decommit_expire.wrapping_add(option_decommit_extend_delay());
            });
            proof {
                lemma_segment_main_metadata_update_preserves_wf_main(*local, local_snap, sid);
                assert(segment.is_in(*local));
            }
        }
    }

    proof {
        assert(common_preserves(local_initial, *local));
        assert(local.page_organization == local_initial.page_organization);
        assert(local.pages == local_initial.pages);
        assert(local.psa == local_initial.psa);
        assert(local.unused_pages == local_initial.unused_pages);
        assert(local.segments.dom() == local_initial.segments.dom());
    }
}

pub fn segment_delayed_decommit(
    segment: SegmentPtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        local.wf_main(),
        segment.wf(),
        segment.is_in(*local),
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).wf_main(),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa,
        final(local).unused_pages == old(local).unused_pages,
        final(local).segments.dom() == old(local).segments.dom(),
        segment.is_in(*final(local)),
{
    if !segment.get_allow_decommit(Tracked(&*local))
        || segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        return;
    }

    let now = clock_now();
    if !force && now < segment.get_decommit_expire(Tracked(&*local)) {
        return;
    }


    let mut idx = 0;
    proof {
        lemma_segment_commit_mask_constants();
        assert(0 <= idx);
        assert(idx < COMMIT_MASK_BITS);
    }
    loop
        invariant_except_break
            local.wf_main(),
            segment.wf(),
            segment.is_in(*local),
            0 <= idx < COMMIT_MASK_BITS,
        invariant
            local.wf_main(),
            common_preserves(*old(local), *local),
            local.page_organization == old(local).page_organization,
            local.pages == old(local).pages,
            local.psa == old(local).psa,
    {

        let mask = segment.get_decommit_mask(Tracked(&*local));
        let (next_idx, count) = mask.next_run(idx);
        if count == 0 {
            break;
        }
        proof {
            lemma_segment_commit_mask_constants();
            assert(count > 0);
            assert(next_idx as int + count as int <= COMMIT_MASK_BITS as int);
            assert(next_idx < COMMIT_MASK_BITS as usize) by(nonlinear_arith)
                requires
                    count > 0,
                    next_idx as int + count as int <= COMMIT_MASK_BITS as int;
            assert(next_idx as int * COMMIT_SIZE as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    next_idx <= COMMIT_MASK_BITS as usize,
                    COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize == SEGMENT_SIZE as usize;
            assert((segment.segment_ptr.addr() as int) + next_idx as int * COMMIT_SIZE as int
                <= (usize::MAX as int)) by(nonlinear_arith)
                requires
                    segment.segment_ptr.addr() as int + SEGMENT_SIZE as int <= usize::MAX as int,
                    next_idx as int * COMMIT_SIZE as int <= SEGMENT_SIZE as int;
            assert(count as int * COMMIT_SIZE as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    count <= COMMIT_MASK_BITS as usize,
                    COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize == SEGMENT_SIZE as usize;
            assert(count as int * COMMIT_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
                requires
                    count as int * COMMIT_SIZE as int <= SEGMENT_SIZE as int,
                    SEGMENT_SIZE as usize <= usize::MAX;
        }
        idx = next_idx;

        let p = segment.segment_ptr.addr() + idx * COMMIT_SIZE as usize;
        let size = count * COMMIT_SIZE as usize;
        proof {
            lemma_segment_commit_mask_constants();
            lemma_segment_start_basics(segment.segment_id@);
            assert(segment.segment_ptr as int == segment_start(segment.segment_id@));
            assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
            assert(segment.segment_ptr as int % SEGMENT_SIZE as int == 0);
            lemma_fundamental_div_mod(segment.segment_ptr as int, SEGMENT_SIZE as int);
            assert(segment.segment_ptr as int == SEGMENT_SIZE as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int));
            assert(segment.segment_ptr as int == COMMIT_SIZE as int * (COMMIT_MASK_BITS as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int))) by(nonlinear_arith)
                requires
                    segment.segment_ptr as int == SEGMENT_SIZE as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int),
                    SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int;
            lemma_mod_multiples_basic(COMMIT_MASK_BITS as int * ((segment.segment_ptr as int) / SEGMENT_SIZE as int), COMMIT_SIZE as int);
            assert(segment.segment_ptr as int % COMMIT_SIZE as int == 0);
            assert(segment.segment_ptr.addr() <= p);
            assert(size <= SEGMENT_SIZE as usize);
            assert(p as int == segment.segment_ptr as int + idx as int * COMMIT_SIZE as int) by(nonlinear_arith)
                requires
                    p == segment.segment_ptr.addr() + idx * COMMIT_SIZE as usize,
                    segment.segment_ptr.addr() as int == segment.segment_ptr as int,
                    segment.segment_ptr.addr() as int + idx as int * COMMIT_SIZE as int <= usize::MAX as int;
            assert(p as int % COMMIT_SIZE as int == 0) by(nonlinear_arith)
                requires
                    p as int == segment.segment_ptr as int + idx as int * COMMIT_SIZE as int,
                    segment.segment_ptr as int % COMMIT_SIZE as int == 0,
                    COMMIT_SIZE as int > 0;
            assert(size as int == count as int * COMMIT_SIZE as int);
            lemma_mod_multiples_basic(count as int, COMMIT_SIZE as int);
            assert(size as int % COMMIT_SIZE as int == 0);
            assert(p as int + size as int <= segment.segment_ptr as int + SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    p as int == segment.segment_ptr as int + idx as int * COMMIT_SIZE as int,
                    size as int == count as int * COMMIT_SIZE as int,
                    idx as int + count as int <= COMMIT_MASK_BITS as int,
                    SEGMENT_SIZE as int == COMMIT_MASK_BITS as int * COMMIT_SIZE as int;
            assert(mask == local.decommit_mask(segment.segment_id@));
            assert((p as int - segment.segment_ptr as int) / COMMIT_SIZE as int == idx as int) by(nonlinear_arith)
                requires
                    p as int == segment.segment_ptr as int + idx as int * COMMIT_SIZE as int,
                    COMMIT_SIZE as int > 0;
            assert((p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int == idx as int + count as int) by(nonlinear_arith)
                requires
                    p as int == segment.segment_ptr as int + idx as int * COMMIT_SIZE as int,
                    size as int == count as int * COMMIT_SIZE as int,
                    COMMIT_SIZE as int > 0;
            assert forall |j: int|
                (p as int - segment.segment_ptr as int) / COMMIT_SIZE as int <= j
                    < (p as int - segment.segment_ptr as int + size as int) / COMMIT_SIZE as int implies
                        local.decommit_mask(segment.segment_id@)@.contains(j) by {
                assert(idx as int <= j < idx as int + count as int);
                assert(mask@.contains(j));
            }
        }
        segment_commitx(segment, false, p, size, Tracked(&mut *local));
    }
    proof {
        assert(local.page_organization == old(local).page_organization);
        assert(local.pages == old(local).pages);
        assert(local.psa == old(local).psa);
        assert(local.unused_pages == old(local).unused_pages);
        assert(local.segments.dom() == old(local).segments.dom());
    }
}

}
