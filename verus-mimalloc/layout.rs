#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::layout::*;

use crate::types::{SegmentHeader, Page, PagePtr, SegmentPtr, todo, Heap, Tld};
use crate::tokens::{PageId, SegmentId, BlockId, HeapId, TldId};
use crate::config::*;

// Relationship between pointers and IDs

verus!{

pub open spec fn is_page_ptr(ptr: *mut Page, page_id: PageId) -> bool {
    ptr as int == page_header_start(page_id)
        && 0 <= page_id.idx <= SLICES_PER_SEGMENT
        && segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX
        && ptr@.provenance == page_id.segment_id.provenance
}

pub open spec fn is_segment_ptr(ptr: *mut SegmentHeader, segment_id: SegmentId) -> bool {
    ptr as int == segment_start(segment_id)
      && ptr as int + SEGMENT_SIZE < usize::MAX
      && ptr@.provenance == segment_id.provenance
}

pub open spec fn is_heap_ptr(ptr: *mut Heap, heap_id: HeapId) -> bool {
    heap_id.id == ptr.addr() && ptr@.provenance == heap_id.provenance
}

pub open spec fn is_tld_ptr(ptr: *mut Tld, tld_id: TldId) -> bool {
    tld_id.id == ptr.addr() && ptr@.provenance == tld_id.provenance
}

pub closed spec fn segment_start(segment_id: SegmentId) -> int {
    segment_id.id * (SEGMENT_SIZE as int)
}

pub open spec fn page_header_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SIZEOF_SEGMENT_HEADER + page_id.idx * SIZEOF_PAGE_HEADER
}

pub open spec fn page_start(page_id: PageId) -> int {
    segment_start(page_id.segment_id) + SLICE_SIZE * page_id.idx
}

pub closed spec fn start_offset(block_size: int) -> int {
    // Based on _mi_segment_page_start_from_slice
    if block_size >= INTPTR_SIZE as int && block_size <= 1024 {
        3 * MAX_ALIGN_GUARANTEE
    } else {
        0
    }
}

pub open spec fn block_start_at(page_id: PageId, block_size: int, block_idx: int) -> int {
    page_start(page_id)
         + start_offset(block_size)
         + block_idx * block_size
}

pub closed spec fn block_start(block_id: BlockId) -> int {
    block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int)
}

pub open spec fn is_block_ptr(ptr: *mut u8, block_id: BlockId) -> bool {
    &&& ptr@.provenance == block_id.page_id.segment_id.provenance
    &&& is_block_ptr1(ptr as int, block_id)
}

#[verifier::opaque]
pub open spec fn is_block_ptr1(ptr: int, block_id: BlockId) -> bool {
    // ptr should be in the range (segment start, segment end]
    // Yes, that's open at the start and closed at the end
    //  - segment start is invalid since that's where the SegmentHeader is
    //  - segment end is valid because there might be a huge block there
    &&& segment_start(block_id.page_id.segment_id) < ptr
        <= segment_start(block_id.page_id.segment_id) + (SEGMENT_SIZE as int)
        < usize::MAX

    // Has valid slice_idx (again this is <= to account for the huge slice)
    &&& 0 <= block_id.slice_idx <= SLICES_PER_SEGMENT

    // It also has to be in the right slice
    &&& segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
        <= ptr
        < segment_start(block_id.page_id.segment_id) + (block_id.slice_idx * SLICE_SIZE)
              + SLICE_SIZE

    // the pptr should actually agree with the block_id
    &&& ptr == block_start(block_id)

    &&& 0 <= block_id.page_id.segment_id.id

    // The block size must be a multiple of the word size
    &&& block_id.block_size >= size_of::<crate::linked_list::Node>()
    &&& block_id.block_size % size_of::<crate::linked_list::Node>() == 0
}

pub open spec fn is_page_ptr_opt(pptr: *mut Page, opt_page_id: Option<PageId>) -> bool {
    match opt_page_id {
        Some(page_id) => is_page_ptr(pptr, page_id) && pptr.addr() != 0,
        None => pptr.addr() == 0,
    }
}

#[verifier::external_body]
pub proof fn block_size_ge_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        block_id.block_size >= size_of::<crate::linked_list::Node>()
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn block_ptr_aligned_to_word()
    ensures forall |p, block_id| is_block_ptr(p, block_id) ==>
        p as int % align_of::<crate::linked_list::Node>() as int == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn block_start_at_diff(page_id: PageId, block_size: nat,
  block_idx1: nat, block_idx2: nat)
    ensures block_start_at(page_id, block_size as int, block_idx2 as int) ==
        block_start_at(page_id, block_size as int, block_idx1 as int) + (block_idx2 - block_idx1) * block_size
{
    unimplemented!()
}

// Bit lemmas

/*proof fn bitmask_is_mod(t: usize)
    ensures (t & (((1usize << 26usize) - 1) as usize)) == (t % (1usize << 26usize)),
{
    //assert((t & (sub(1usize << 26usize, 1) as usize)) == (t % (1usize << 26usize)))
    //    by(bit_vector);
}*/

/*proof fn bitmask_is_rounded_down(t: usize)
    ensures (t & !(((1usize << 26usize) - 1) as usize)) == t - (t % (1usize << 26usize))
{
    assert((t & !(sub((1usize << 26usize), 1) as usize)) == sub(t, (t % (1usize << 26usize))))
        by(bit_vector);
    assert((1usize << 26usize) >= 1usize) by(bit_vector);
    assert(t >= (t % (1usize << 26usize))) by(bit_vector);
}*/

/*proof fn mod_removes_remainder(s: int, t: int, r: int)
    requires
        0 <= r < t,
        0 <= s,
    ensures (s*t + r) - ((s*t + r) % t) == s*t
{
    /*
    if s == 0 {
        assert(r % t == r) by(nonlinear_arith)
            requires 0 <= r < t;
    } else {
        let x = ((s-1)*t + r);
        assert((x % t) == (x + t) % t) by(nonlinear_arith);
    }
    */
    //assert(((s*t + r) % t) == r) by(nonlinear_arith)
    //  requires 0 <= r < t, 0 < t;

    //let x = s*t + r;
    //assert((x / t) * t + x % t == x) by(nonlinear_arith);
}*/

// Executable calculations

#[verifier::external_body]
pub fn calculate_segment_ptr_from_block(ptr: *mut u8, Ghost(block_id): Ghost<BlockId>) -> (res: *mut SegmentHeader)
    requires is_block_ptr(ptr, block_id),
    ensures is_segment_ptr(res, block_id.page_id.segment_id)
{
    unimplemented!()
}

/*
pub fn calculate_slice_idx_from_block(block_ptr: PPtr<u8>, segment_ptr: PPtr<SegmentHeader>, Ghost(block_id): Ghost<BlockId>) -> (slice_idx: usize)
    requires
        is_block_ptr(block_ptr.id(), block_id),
        is_segment_ptr(segment_ptr.id(), block_id.page_id.segment_id)
    ensures slice_idx as int == block_id.slice_idx,
{
    let block_p = block_ptr.addr();
    let segment_p = segment_ptr.addr();

    // Based on _mi_segment_page_of
    let diff = segment_p - block_p;
    diff >> (SLICE_SHIFT as usize)
}
*/

#[verifier::external_body]
pub fn calculate_slice_page_ptr_from_block(block_ptr: *mut u8, segment_ptr: *mut SegmentHeader, Ghost(block_id): Ghost<BlockId>) -> (page_ptr: *mut Page)
    requires
        is_block_ptr(block_ptr, block_id),
        is_segment_ptr(segment_ptr, block_id.page_id.segment_id),
    ensures is_page_ptr(page_ptr, block_id.page_id_for_slice())
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
pub fn calculate_page_ptr_subtract_offset(
    page_ptr: *mut Page, offset: u32, Ghost(page_id): Ghost<PageId>, Ghost(target_page_id): Ghost<PageId>) -> (result: *mut Page)
    requires
        is_page_ptr(page_ptr, page_id),
        page_id.segment_id == target_page_id.segment_id,
        offset == (page_id.idx - target_page_id.idx) * SIZEOF_PAGE_HEADER,
    ensures
        is_page_ptr(result, target_page_id)
{
    unimplemented!()
}

/*
pub fn calculate_page_ptr_add_offset(
    page_ptr: *mut Page, offset: u32, Ghost(page_id): Ghost<PageId>) -> (result: *mut Page)
    requires
        is_page_ptr(page_ptr as int, page_id),
        offset <= 0x1_0000,
    ensures
        is_page_ptr(result as int, PageId { idx: (page_id.idx + offset) as nat, ..page_id }),
{
    todo(); loop { }
}
*/

/*
pub fn calculate_segment_page_start(
    segment_ptr: SegmentPtr,
    page_ptr: PagePtr)
) -> (p: PPtr<u8>)
    ensures
        p as int == page_start(page_ptr.page_id)
{
}
*/

#[verifier::external_body]
pub fn calculate_page_start(page_ptr: PagePtr, block_size: usize) -> (addr: usize)
    requires block_size > 0, page_ptr.wf(),
    ensures addr == block_start_at(page_ptr.page_id@, block_size as int, 0)
{
    unimplemented!()
}

#[verifier::external_body]
pub fn calculate_page_block_at(
    page_start: usize,
    block_size: usize,
    idx: usize,
    Ghost(page_id): Ghost<PageId>
) -> (p: usize)
    requires page_start == block_start_at(page_id, block_size as int, 0),
        block_start_at(page_id, block_size as int, 0)
            + idx as int * block_size as int <= segment_start(page_id.segment_id) + SEGMENT_SIZE,
        segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX,
    ensures
        p == block_start_at(page_id, block_size as int, idx as int),
        p == page_start + idx as int * block_size as int
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn mk_segment_id(p: *mut SegmentHeader) -> (id: SegmentId)
    requires p as int >= 0,
        p as int % SEGMENT_SIZE as int == 0,
        ((p as int + SEGMENT_SIZE as int) < usize::MAX),
    ensures is_segment_ptr(p, id)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_id_divis(sp: SegmentPtr)
    requires sp.wf(),
    ensures sp.segment_ptr as int % SEGMENT_SIZE as int == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub fn segment_page_start_from_slice(
    segment_ptr: SegmentPtr,
    slice: PagePtr,
    xblock_size: usize)
  -> (res: usize) // start_offset
    requires
        segment_ptr.wf(), slice.wf(), slice.page_id@.segment_id == segment_ptr.segment_id@
    ensures ({ let start_offset = res; {
        &&& xblock_size == 0 ==>
            start_offset == segment_start(segment_ptr.segment_id@)
                + slice.page_id@.idx * SLICE_SIZE
        &&& xblock_size > 0 ==>
            start_offset == block_start_at(slice.page_id@, xblock_size as int, 0)
    }})
{
    unimplemented!()
}

#[verifier::external_body]
proof fn bitand_with_mask_gives_rounding(x: usize, y: usize)
    requires y != 0, y & sub(y, 1) == 0,
    ensures x & !sub(y, 1) == (x / y) * y
{
    unimplemented!()
}

#[verifier::external_body]
proof fn two_mul_with_bit0(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1) / (2 * y1) == x1 / y1
{
    unimplemented!()
}

#[verifier::external_body]
proof fn two_mul_with_bit1(x1: int, y1: int)
    requires y1 != 0,
    ensures (2 * x1 + 1) / (2 * y1) == x1 / y1
{
    unimplemented!()
}


#[verifier::external_body]
#[inline]
pub fn align_down(x: usize, y: usize) -> (res: usize)
    requires y != 0,
    ensures
        res == (x as int / y as int) * y,
        res <= x < res + y,
        res % y == 0,
        (res / y * y) == res
{
    unimplemented!()
}

#[verifier::external_body]
#[inline]
pub fn align_up(x: usize, y: usize) -> (res: usize)
    requires y != 0,
        x + y - 1 <= usize::MAX,
    ensures
        res == ((x + y - 1) / y as int) * y,
        x <= res <= x + y - 1,
        res % y == 0,
        (res / y * y) == res
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn mod_trans(a: int, b: int, c: int)
    requires b != 0, c != 0, a % b == 0, b % c == 0,
    ensures a % c == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn mod_mul(a: int, b: int, c: int)
    requires b % c == 0, c != 0
    ensures (a * b) % c == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn mul_mod_right(a: int, b: int)
    requires b != 0,
    ensures (a * b) % b == 0
{
    unimplemented!()
}


impl SegmentPtr {
    #[verifier::external_body]
    #[inline]
    pub fn ptr_segment(page_ptr: PagePtr) -> (segment_ptr: SegmentPtr)
        requires page_ptr.wf(),
        ensures segment_ptr.wf(),
            segment_ptr.segment_id == page_ptr.page_id@.segment_id
    {
        unimplemented!()
    }
}

#[verifier::external_body]
pub proof fn is_page_ptr_nonzero(ptr: *mut Page, page_id: PageId)
    requires is_page_ptr(ptr, page_id),
    ensures ptr as int != 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn is_block_ptr_mult4(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int % 4 == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_mult_commit_size(segment_id: SegmentId)
    ensures segment_start(segment_id) % COMMIT_SIZE as int == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_mult8(segment_id: SegmentId)
    ensures segment_start(segment_id) % 8 == 0
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_ge0(segment_id: SegmentId)
    ensures segment_start(segment_id) >= 0
{
    unimplemented!()
}

#[verifier::external_body]
pub fn calculate_start_offset(block_size: usize) -> (res: u32)
    ensures res == start_offset(block_size as int)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn start_offset_le_slice_size(block_size: int)
    ensures 0 <= start_offset(block_size) <= SLICE_SIZE,
        start_offset(block_size) == 0 || start_offset(block_size) == 3 * MAX_ALIGN_GUARANTEE
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn segment_start_eq(sid: SegmentId, sid2: SegmentId)
    requires sid.id == sid2.id,
    ensures segment_start(sid) == segment_start(sid2)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn get_block_start_from_is_block_ptr(ptr: *mut u8, block_id: BlockId)
    requires is_block_ptr(ptr, block_id),
    ensures ptr as int == block_start(block_id)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn get_block_start_defn(block_id: BlockId)
    ensures block_start(block_id)
      == block_start_at(block_id.page_id, block_id.block_size as int, block_id.idx as int)
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn sub_distribute(a: int, b: int, c: int)
    ensures a * c - b * c == (a - b) * c
{
    unimplemented!()
}

}
