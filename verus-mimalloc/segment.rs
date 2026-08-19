#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::set_lib::*;
use vstd::arithmetic::div_mod::lemma_mod_multiples_basic;
use vstd::cell::pcell::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, BlockState, DelayState, PageId, PageState, SegmentId, SegmentState, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::arena::*;
use crate::commit_mask::CommitMask;
use crate::os_mem::MemChunk;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::linked_list::ThreadLLWithDelayBits;
use crate::init::current_thread_count;

verus!{

pub open spec fn good_count_for_block_size(block_size: int, count: int) -> bool {
    count * SLICE_SIZE < block_size * 0x10000
}

pub open spec fn segment_calculate_slices_required_bound(required: int) -> bool {
    required + 2 * SLICE_SIZE as int - 1 <= usize::MAX as int
}

#[verifier::rlimit(200)]
proof fn lemma_segment_os_alloc_constants()
    ensures
        SLICE_SIZE as usize == 65536,
        COMMIT_SIZE as usize == SLICE_SIZE as usize,
        COMMIT_MASK_BITS as usize == SLICES_PER_SEGMENT as usize,
        COMMIT_MASK_BITS as usize == 512,
        SLICES_PER_SEGMENT as usize * SLICE_SIZE as usize == SEGMENT_SIZE as usize,
        COMMIT_MASK_BITS as usize * COMMIT_SIZE as usize == SEGMENT_SIZE as usize,
        SEGMENT_SIZE as usize <= usize::MAX,
{
    assert(SLICE_SIZE == 65536) by(compute_only);
    assert(COMMIT_SIZE == SLICE_SIZE) by(compute_only);
    assert(COMMIT_MASK_BITS == SLICES_PER_SEGMENT) by(compute_only);
    assert(COMMIT_MASK_BITS == 512) by(compute_only);
    assert(SLICES_PER_SEGMENT * SLICE_SIZE == SEGMENT_SIZE) by(compute_only);
    assert(COMMIT_MASK_BITS * COMMIT_SIZE == SEGMENT_SIZE) by(compute_only);
    assert(SEGMENT_SIZE == 33554432) by(compute_only);
}


#[verifier::rlimit(200)]
proof fn lemma_mem_chunk_good1_same_segment(
    mem: MemChunk,
    sid1: SegmentId,
    sid2: SegmentId,
    commit1: Set<int>,
    commit2: Set<int>,
    decommit1: Set<int>,
    decommit2: Set<int>,
)
    requires
        mem_chunk_good1(mem, sid1, commit1, decommit1, Set::empty(), Set::empty()),
        segment_start(sid1) == segment_start(sid2),
        sid1.provenance == sid2.provenance,
        commit1 =~= commit2,
        decommit1 =~= decommit2,
    ensures
        mem_chunk_good1(mem, sid2, commit2, decommit2, Set::empty(), Set::empty()),
{
    assert(mem.os_exact_range(segment_start(sid2), SEGMENT_SIZE as int));
    assert(mem.points_to.provenance() == sid2.provenance);
    assert(commit2.subset_of(mem.os_rw_bytes()));
    assert(decommit2 <= commit2);
    assert(segment_info_range(sid1) =~= segment_info_range(sid2));
    assert(segment_info_range(sid2) <= commit2 - decommit2);
    assert(Set::<int>::empty() <= commit2 - decommit2);
    assert(mem.os_rw_bytes() <= mem.points_to.dom() + segment_info_range(sid2) + Set::<int>::empty());
}

#[verifier::rlimit(200)]
proof fn lemma_mem_chunk_good1_after_metadata_taken(
    allocated_mem: MemChunk,
    metadata_removed_mem: MemChunk,
    sid: SegmentId,
    commit_bytes: Set<int>,
    decommit_bytes: Set<int>,
)
    requires
        mem_chunk_good1(allocated_mem, sid, commit_bytes, decommit_bytes, Set::empty(), Set::empty()),
        metadata_removed_mem.wf(),
        metadata_removed_mem.os == allocated_mem.os,
        metadata_removed_mem.points_to.provenance() == allocated_mem.points_to.provenance(),
        metadata_removed_mem.points_to.dom() =~= allocated_mem.points_to.dom() - segment_info_range(sid),
    ensures
        mem_chunk_good1(metadata_removed_mem, sid, commit_bytes, decommit_bytes, Set::empty(), Set::empty()),
{
    assert(metadata_removed_mem.os_exact_range(segment_start(sid), SEGMENT_SIZE as int));
    assert(metadata_removed_mem.points_to.provenance() == sid.provenance);
    assert(metadata_removed_mem.os_rw_bytes() =~= allocated_mem.os_rw_bytes());
    assert(commit_bytes.subset_of(metadata_removed_mem.os_rw_bytes()));
    assert(decommit_bytes <= commit_bytes);
    assert(segment_info_range(sid) <= commit_bytes - decommit_bytes);
    assert(Set::<int>::empty() <= commit_bytes - decommit_bytes);
    assert(metadata_removed_mem.os_rw_bytes() <= metadata_removed_mem.points_to.dom() + segment_info_range(sid)) by {
        assert forall |addr: int| #[trigger] metadata_removed_mem.os_rw_bytes().contains(addr) implies
            (metadata_removed_mem.points_to.dom() + segment_info_range(sid)).contains(addr) by {
            assert(allocated_mem.os_rw_bytes().contains(addr));
            assert((allocated_mem.points_to.dom() + segment_info_range(sid)).contains(addr));
            if allocated_mem.points_to.dom().contains(addr) {
                if metadata_removed_mem.points_to.dom().contains(addr) {
                } else {
                    assert(segment_info_range(sid).contains(addr));
                }
            } else {
                assert(segment_info_range(sid).contains(addr));
            }
        };
    }
    assert(metadata_removed_mem.os_rw_bytes() <= metadata_removed_mem.points_to.dom() + segment_info_range(sid) + Set::<int>::empty());
}

#[verifier::rlimit(200)]
proof fn lemma_segment_calculate_slices_required_zero_bound()
    ensures
        segment_calculate_slices_required_bound(0),
{
    const_facts();
    assert(SLICE_SIZE as int == 65536) by(compute_only);
    assert(2 * SLICE_SIZE as int - 1 <= SEGMENT_SIZE as int) by(nonlinear_arith)
        requires
            SLICE_SIZE as int == 65536,
            SEGMENT_SIZE as int == 33554432;
    assert(SEGMENT_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
        requires
            SEGMENT_SIZE as int == 33554432,
            SEGMENT_SIZE as int + SEGMENT_SIZE as int - 1 <= usize::MAX as int;
}

closed spec fn segment_span_allocate_page_org_pre(
    org: PageOrg::State,
    segment_id: SegmentId,
    page_id: PageId,
    slice_count: int,
) -> bool {
    &&& org.invariant()
    &&& page_id.segment_id == segment_id
    &&& 0 < slice_count
    &&& (
        org.popped == Popped::VeryUnready(segment_id, page_id.idx as int, slice_count, false)
        || (
            org.popped == Popped::SegmentCreating(segment_id)
            && page_id.idx == 0
            && slice_count < SLICES_PER_SEGMENT
        )
    )
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn segment_page_alloc(
    heap: HeapPtr,
    block_size: usize,
    page_alignment: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        tld.wf(),
        tld.is_in(*old(local)),
        page_alignment == 0,
        INTPTR_SIZE as usize <= block_size,
        block_size as int <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        tld.wf(),
        tld.is_in(*final(local)),
        page_ptr.page_ptr.addr() == 0 ==> final(local).wf(),
        page_ptr.page_ptr.addr() != 0 ==> final(local).wf_main_for_page_access(),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.wf(),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.is_in(*final(local)),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.is_in_unused(*final(local)),
        page_ptr.page_ptr.addr() != 0 ==> final(local).mem_chunk_good(page_ptr.page_id@.segment_id),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.pages[page_ptr.page_id@].count.is_some(),
        page_ptr.page_ptr.addr() != 0 ==> good_count_for_block_size(
            block_size as int,
            final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int),
        page_ptr.page_ptr.addr() != 0 ==> final(local).segments[page_ptr.page_id@.segment_id].mem.pointsto_has_range(
            page_start(page_ptr.page_id@),
            final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int),
        page_ptr.page_ptr.addr() != 0 ==> (forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid)),
        page_ptr.page_ptr.addr() != 0 ==> set_int_range(
            page_start(page_ptr.page_id@),
            page_start(page_ptr.page_id@) + final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int)
                <= final(local).commit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id)
                    - final(local).decommit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id),
{

    if unlikely(page_alignment > ALIGNMENT_MAX as usize) {
        proof {
            assert(false);
        }
        todo();
    }

    if block_size <= SMALL_OBJ_SIZE_MAX as usize {
        proof {
            assert(block_size <= MEDIUM_PAGE_SIZE as usize) by {
                assert(SMALL_OBJ_SIZE_MAX < MEDIUM_PAGE_SIZE) by(compute_only);
            }
        }
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else if block_size <= MEDIUM_OBJ_SIZE_MAX as usize {
        proof {
            assert(MEDIUM_PAGE_SIZE as int <= usize::MAX as int) by(compute_only);
        }
        segments_page_alloc(heap, MEDIUM_PAGE_SIZE as usize, block_size, tld, Tracked(&mut *local))
    } else if block_size <= LARGE_OBJ_SIZE_MAX as usize {
        proof {
            assert(false) by(nonlinear_arith)
                requires block_size as int <= MEDIUM_OBJ_SIZE_MAX,
                    !(block_size <= MEDIUM_OBJ_SIZE_MAX as usize);
        }
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else {
        proof {
            assert(false) by(nonlinear_arith)
                requires block_size as int <= MEDIUM_OBJ_SIZE_MAX,
                    !(block_size <= MEDIUM_OBJ_SIZE_MAX as usize);
        }
        todo(); loop{}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn segments_page_alloc(
    heap: HeapPtr,
    required: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        tld.wf(),
        tld.is_in(*old(local)),
        INTPTR_SIZE as usize <= block_size,
        block_size as int <= MEDIUM_OBJ_SIZE_MAX,
        0 < required,
        required <= MEDIUM_PAGE_SIZE as usize,
        required == block_size || required == MEDIUM_PAGE_SIZE as usize,
        required == MEDIUM_PAGE_SIZE as usize ==> block_size > SMALL_OBJ_SIZE_MAX as usize,
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        tld.wf(),
        tld.is_in(*final(local)),
        page_ptr.page_ptr.addr() == 0 ==> final(local).wf(),
        page_ptr.page_ptr.addr() != 0 ==> final(local).wf_main_for_page_access(),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.wf(),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.is_in(*final(local)),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.is_in_unused(*final(local)),
        page_ptr.page_ptr.addr() != 0 ==> final(local).mem_chunk_good(page_ptr.page_id@.segment_id),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.pages[page_ptr.page_id@].count.is_some(),
        page_ptr.page_ptr.addr() != 0 ==> good_count_for_block_size(
            block_size as int,
            final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int),
        page_ptr.page_ptr.addr() != 0 ==> final(local).segments[page_ptr.page_id@.segment_id].mem.pointsto_has_range(
            page_start(page_ptr.page_id@),
            final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int),
        page_ptr.page_ptr.addr() != 0 ==> (forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid)),
        page_ptr.page_ptr.addr() != 0 ==> set_int_range(
            page_start(page_ptr.page_id@),
            page_start(page_ptr.page_id@) + final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int)
                <= final(local).commit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id)
                    - final(local).decommit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id),
{

    let alignment: usize = if required > MEDIUM_PAGE_SIZE as usize
        { MEDIUM_PAGE_SIZE as usize } else { SLICE_SIZE as usize };
    proof {
        assert(alignment == SLICE_SIZE as usize);
        assert(SLICE_SIZE as usize > 0) by(compute_only);
        assert(required as int + alignment as int - 1 <= usize::MAX as int) by {
            assert(MEDIUM_PAGE_SIZE as int + SLICE_SIZE as int - 1 <= usize::MAX as int) by(compute_only);
        }
    }
    let page_size = align_up(required, alignment);
    let slices_needed = page_size / SLICE_SIZE as usize;

    proof {
        assert(page_size as int <= SEGMENT_SIZE as int) by {
            assert(SLICE_SIZE == COMMIT_SIZE) by(compute_only);
            assert(MEDIUM_PAGE_SIZE as int <= SEGMENT_SIZE as int) by(compute_only);
        }
        assert(SLICE_SIZE as usize > 0) by(compute_only);
        assert((SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int) by(compute_only);
        assert(SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int) by(compute_only);
        assert((slices_needed as int) * (SLICE_SIZE as int) <= page_size as int) by(nonlinear_arith)
            requires slices_needed == page_size / SLICE_SIZE as usize;
        assert(slices_needed <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
            requires
                (slices_needed as int) * (SLICE_SIZE as int) <= page_size as int,
                page_size as int <= SEGMENT_SIZE as int,
                SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int,
                (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int,
                0 < SLICE_SIZE as int;
        assert(good_count_for_block_size(block_size as int, slices_needed as int)) by {
            reveal(good_count_for_block_size);
            assert(SLICE_SIZE as int == 65536) by(compute_only);
            if required == MEDIUM_PAGE_SIZE as usize {
                assert(MEDIUM_PAGE_SIZE as int == 524288) by(compute_only);
                assert(page_size as int == MEDIUM_PAGE_SIZE as int) by(nonlinear_arith)
                    requires
                        required as int == MEDIUM_PAGE_SIZE as int,
                        required <= page_size,
                        page_size as int <= required as int + SLICE_SIZE as int - 1,
                        page_size as int % SLICE_SIZE as int == 0,
                        MEDIUM_PAGE_SIZE as int == 524288,
                        SLICE_SIZE as int == 65536;
                assert(slices_needed as int == 8) by(nonlinear_arith)
                    requires
                        slices_needed == page_size / SLICE_SIZE as usize,
                        page_size as int == MEDIUM_PAGE_SIZE as int,
                        MEDIUM_PAGE_SIZE as int == 524288,
                        SLICE_SIZE as int == 65536;
                assert(SMALL_OBJ_SIZE_MAX as int == 16384) by(compute_only);
                assert((block_size as int) > (SMALL_OBJ_SIZE_MAX as int)) by(nonlinear_arith)
                    requires block_size > SMALL_OBJ_SIZE_MAX as usize;
                assert((slices_needed as int) * (SLICE_SIZE as int) < (block_size as int) * 65536) by(nonlinear_arith)
                    requires
                        slices_needed as int == 8,
                        SLICE_SIZE as int == 65536,
                        (block_size as int) > 16384;
            } else {
                assert(required == block_size);
                assert(page_size as int <= required as int + SLICE_SIZE as int - 1);
                assert((slices_needed as int) * (SLICE_SIZE as int) <= page_size as int);
                assert(INTPTR_SIZE as int == 8) by(compute_only);
                assert((slices_needed as int) * (SLICE_SIZE as int) < (block_size as int) * 65536) by(nonlinear_arith)
                    requires
                        (slices_needed as int) * (SLICE_SIZE as int) <= page_size as int,
                        page_size as int <= required as int + SLICE_SIZE as int - 1,
                        required == block_size,
                        INTPTR_SIZE as usize <= block_size,
                        INTPTR_SIZE as int == 8,
                        SLICE_SIZE as int == 65536;
            }
        }
    }

    let page_ptr = segments_page_find_and_allocate(slices_needed, tld,
          Tracked(&mut *local), Ghost(block_size as nat));
    if page_ptr.page_ptr.addr() == 0 {
        let roa = segment_reclaim_or_alloc(heap, slices_needed, block_size, tld,
            Tracked(&mut *local));
        if roa.segment_ptr.addr() == 0 {
            return PagePtr::null();
        } else {
            return segments_page_alloc(heap, required, block_size, tld, Tracked(&mut *local));
        }
    } else {
        return page_ptr;
    }
}

#[verus_verify]
fn segment_reclaim_or_alloc(
    heap: HeapPtr,
    needed_slices: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (segment_ptr: SegmentPtr)
    requires
        heap.wf(),
        heap.is_in(*old(local)),
        old(local).wf_basic(),
        old(local).wf_main(),
        old(local).page_organization.popped == Popped::No,
        tld.wf(),
        tld.is_in(*old(local)),
    ensures
        segment_calculate_slices_required_bound(0),
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        tld.wf(),
        tld.is_in(*final(local)),
{
    // TODO reclaiming

    let arena_id = heap.get_arena_id(Tracked(&*local));
    proof {
        lemma_segment_calculate_slices_required_zero_bound();
    }
    segment_alloc(0, 0, arena_id, tld, Tracked(&mut *local))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn segments_page_find_and_allocate(
    slice_count0: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    Ghost(block_size): Ghost<nat>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice_count0 <= SLICES_PER_SEGMENT as usize,
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        tld_ptr.wf(),
        tld_ptr.is_in(*final(local)),
        page_ptr.page_ptr.addr() == 0 ==> final(local).wf(),
        page_ptr.page_ptr.addr() != 0 ==> final(local).wf_main_for_page_access(),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.wf(),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.is_in(*final(local)),
        page_ptr.page_ptr.addr() != 0 ==> page_ptr.is_in_unused(*final(local)),
        page_ptr.page_ptr.addr() != 0 ==> final(local).mem_chunk_good(page_ptr.page_id@.segment_id),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.pages[page_ptr.page_id@].count.is_some(),
        page_ptr.page_ptr.addr() != 0 ==> final(local).page_organization.pages[page_ptr.page_id@].count.unwrap()
            == (if slice_count0 == 0 { 1 } else { slice_count0 }) as nat,
        page_ptr.page_ptr.addr() != 0 ==> final(local).segments[page_ptr.page_id@.segment_id].mem.pointsto_has_range(
            page_start(page_ptr.page_id@),
            final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int),
        page_ptr.page_ptr.addr() != 0 ==> (forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid)),
        page_ptr.page_ptr.addr() != 0 ==> set_int_range(
            page_start(page_ptr.page_id@),
            page_start(page_ptr.page_id@) + final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int)
                <= final(local).commit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id)
                    - final(local).decommit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id),
{
    let mut sbin_idx = slice_bin(slice_count0);
    let slice_count = if slice_count0 == 0 { 1 } else { slice_count0 };
    proof {
        assert(SLICES_PER_SEGMENT as usize >= 1) by(compute_only);
        assert(slice_count <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
            requires
                slice_count0 <= SLICES_PER_SEGMENT as usize,
                slice_count == if slice_count0 == 0 { 1 } else { slice_count0 },
                SLICES_PER_SEGMENT as usize >= 1;
    }

    while sbin_idx <= SEGMENT_BIN_MAX
        invariant
            local.wf(),
            tld_ptr.wf(),
            tld_ptr.is_in(*local),
            slice_count > 0,
            local.heap_id == old(local).heap_id,
            slice_count == (if slice_count0 == 0 { 1 } else { slice_count0 }),
            common_preserves(*old(local), *local),
    {
        proof {
            assert(0 <= sbin_idx as int && sbin_idx as int <= SEGMENT_BIN_MAX);
            local.page_organization.first_is_in(sbin_idx as int);
        }
        let mut slice_ptr = ptr_ref(tld_ptr.tld_ptr, Tracked(&local.tld))
              .segments.span_queue_headers[sbin_idx].first;
        let ghost mut list_idx = 0int;
        let ghost mut slice_page_id: Option<PageId> =
            local.page_organization.unused_dlist_headers[sbin_idx as int].first;

        while slice_ptr.addr() != 0
            invariant
                local.wf(),
                tld_ptr.wf(),
                tld_ptr.is_in(*local),
                is_page_ptr_opt(slice_ptr, slice_page_id),
                slice_page_id.is_some() ==>
                    local.page_organization.valid_unused_page(
                        slice_page_id.unwrap(), sbin_idx as int, list_idx),
                slice_count > 0,
                local.heap_id == old(local).heap_id,
                slice_count == (if slice_count0 == 0 { 1 } else { slice_count0 }),
                common_preserves(*old(local), *local),
        {
            proof {
                assert(slice_page_id.is_some());
            }
            let slice = PagePtr {
                page_ptr: slice_ptr,
                page_id: Ghost(slice_page_id.unwrap())
            };

            proof {
                assert(slice.wf());
                assert(local.page_organization.valid_unused_page(
                    slice.page_id@, sbin_idx as int, list_idx));
                reveal(PageOrg::State::valid_unused_page);
                assert(local.page_organization.pages.dom().contains(slice.page_id@));
                assert(slice.is_in(*local));
            }

            let found_slice_count = slice.get_count(Tracked(&*local)) as usize;
            proof {
                assert(local.page_organization.valid_unused_page(
                    slice.page_id@, sbin_idx as int, list_idx));
                reveal(PageOrg::State::valid_unused_page);
                assert(local.page_organization.pages[slice.page_id@].count.is_some());
                assert(found_slice_count as int
                    == local.page_organization.pages[slice.page_id@].count.unwrap());
                assert((SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int) by(compute_only);
                assert(found_slice_count <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
                    requires
                        found_slice_count as int
                            == local.page_organization.pages[slice.page_id@].count.unwrap(),
                        local.page_organization.pages[slice.page_id@].count.unwrap()
                            <= SLICES_PER_SEGMENT,
                        (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int;
            }
            if found_slice_count >= slice_count {
                let segment = SegmentPtr::ptr_segment(slice);


                span_queue_delete(
                    tld_ptr,
                    sbin_idx,
                    slice,
                    Tracked(&mut *local),
                    Ghost(list_idx),
                    Ghost(found_slice_count as int));



                if found_slice_count > slice_count {
                    proof {
                        let current_slice_count = found_slice_count;
                        let target_slice_count = slice_count;
                        assert((local).wf_main_for_page_access());
                        assert(tld_ptr.wf());
                        assert(tld_ptr.is_in(*local));
                        assert(slice.wf());
                        assert(slice.is_in(*local));
                        assert((local).page_organization.popped == Popped::VeryUnready(
                            slice.page_id@.segment_id,
                            slice.page_id@.idx as int,
                            current_slice_count as int,
                            false));
                        local.page_organization.very_unready_popped_range_facts();
                        assert(current_slice_count <= SLICES_PER_SEGMENT as usize);
                        assert(current_slice_count > target_slice_count);
                        assert(target_slice_count > 0);
                        assert(slice.page_id@.idx + current_slice_count <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                            requires
                                local.page_organization.popped == Popped::VeryUnready(
                                    slice.page_id@.segment_id,
                                    slice.page_id@.idx as int,
                                    current_slice_count as int,
                                    false),
                                slice.page_id@.idx + current_slice_count as int <= SLICES_PER_SEGMENT;
                        assert(slice.page_id@.idx + target_slice_count <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                            requires
                                slice.page_id@.idx + current_slice_count <= SLICES_PER_SEGMENT,
                                target_slice_count < current_slice_count;
                    }

                    segment_slice_split(
                        slice,
                        found_slice_count,
                        slice_count,
                        tld_ptr,
                        Tracked(&mut *local));
                }



                proof {
                    let sid = segment.segment_id@;
                    if local.wf_main() {
                        local.wf_main_implies_page_access();
                    }
                    assert(local.wf_main_for_page_access());
                    assert(segment.wf());
                    assert(segment.is_in(*local));
                    assert(local.segments[sid].wf(
                        sid,
                        local.thread_token.value().segments.index(sid),
                        local.instance));
                    assert(page_organization_segments_match(local.page_organization.segments, local.segments));
                    assert(local.page_organization.segments.dom().contains(sid));
                    assert(segment_start(sid) != 0);
                    assert(segment.segment_ptr as int == segment_start(sid));
                    assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
                    assert(segment.segment_ptr.addr() != 0);
                }
                let suc = segment_span_allocate(
                    segment,
                    slice,
                    slice_count,
                    tld_ptr,
                    Tracked(&mut *local));
                if !suc {
                    todo();
                }
                return slice;
            }

            let ghost next_slice_page_id =
                local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().next;
            proof {
                local.page_organization.next_is_in(slice.page_id@, sbin_idx as int, list_idx);
            }
            slice_ptr = slice.get_next(Tracked(&*local));
            proof {
                assert(is_page_ptr_opt(slice_ptr, next_slice_page_id));
                slice_page_id = next_slice_page_id;
                list_idx = list_idx + 1;
            }
        }

        proof {
            assert(SEGMENT_BIN_MAX < usize::MAX) by(compute_only);
            assert(sbin_idx < usize::MAX) by(nonlinear_arith)
                requires
                    sbin_idx <= SEGMENT_BIN_MAX,
                    SEGMENT_BIN_MAX < usize::MAX;
        }
        sbin_idx = sbin_idx + 1;
    }

    PagePtr::null()
}
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn span_queue_delete(
    tld_ptr: TldPtr,
    sbin_idx: usize,

    slice: PagePtr,

    Tracked(local): Tracked<&mut Local>,
    Ghost(list_idx): Ghost<int>,
    Ghost(count): Ghost<int>,
)
    requires
        old(local).wf(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        slice.is_in(*old(local)),
        old(local).page_organization.valid_unused_page(slice.page_id@, sbin_idx as int, list_idx),
        old(local).page_organization.pages[slice.page_id@].count.is_some(),
        count == old(local).page_organization.pages[slice.page_id@].count.unwrap(),
    ensures
        final(local).wf_main_for_page_access(),
        tld_ptr.wf(),
        tld_ptr.is_in(*final(local)),
        slice.wf(),
        slice.is_in(*final(local)),
        common_preserves(*old(local), *final(local)),
        final(local).mem_chunk_good(slice.page_id@.segment_id),
        forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid),
        final(local).page_organization.popped == Popped::VeryUnready(
            slice.page_id@.segment_id,
            slice.page_id@.idx as int,
            count,
            false),
{
    let ghost local_start = *local;
    let ghost next_state = PageOrg::take_step::take_page_from_unused_queue(
        local.page_organization,
        slice.page_id@,
        sbin_idx as int,
        list_idx);
    proof {
        assert(local.page_organization.popped == Popped::No);
        local.page_organization.take_page_from_unused_queue_page_facts(
            slice.page_id@, sbin_idx as int, list_idx);
        local.page_organization.take_page_from_unused_queue_dlist_facts(
            slice.page_id@, sbin_idx as int, list_idx);
    }
    let prev = slice.get_prev(Tracked(&*local));
    let next = slice.get_next(Tracked(&*local));

    if prev.addr() == 0 {
        tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx].first = next;
    } else {
        //assert(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().prev.is_some());
        let prev_page_ptr = PagePtr { page_ptr: prev,
            page_id: Ghost(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().prev.unwrap()), };
        proof {
            let prev_page_id = prev_page_ptr.page_id@;
            assert(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().prev
                == Some(prev_page_id));
            assert(is_page_ptr_opt(prev, Some(prev_page_id)));
            assert(prev_page_ptr.wf());
            assert(local.page_organization.pages.dom().contains(prev_page_id));
            assert(local.page_organization.pages[prev_page_id].is_used == false);
            assert(local.unused_pages.dom().contains(prev_page_id));
        }

        /*assert(local.page_organization_valid());
        assert(local.page_organization.pages.dom().contains(prev_page_ptr.page_id@));
        assert(page_organization_pages_match_data(
            local.page_organization.pages[prev_page_ptr.page_id@],
            local.pages[prev_page_ptr.page_id@],
            local.psa[prev_page_ptr.page_id@],
            prev_page_ptr.page_id@,
            local.page_organization.popped,
            ));

        assert(!local.page_organization.pages[prev_page_ptr.page_id@].is_used);
        assert(local.psa.dom().contains(prev_page_ptr.page_id@));*/

        unused_page_get_mut_next!(prev_page_ptr, local, n => {
            n = next;
        });
    }

    if next.addr() == 0 {
        tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx].last = prev;
    } else {
        let next_page_ptr = PagePtr { page_ptr: next,
            page_id: Ghost(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().next.unwrap()), };
        proof {
            let next_page_id = next_page_ptr.page_id@;
            assert(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().next
                == Some(next_page_id));
            assert(is_page_ptr_opt(next, Some(next_page_id)));
            assert(next_page_ptr.wf());
            assert(local.page_organization.pages.dom().contains(next_page_id));
            assert(local.page_organization.pages[next_page_id].is_used == false);
            assert(local.unused_pages.dom().contains(next_page_id));
        }

        //assert(local.psa.dom().contains(next_page_ptr.page_id@));

        unused_page_get_mut_prev!(next_page_ptr, local, p => {
            p = prev;
        });
    }

    proof {
        local.page_organization = next_state;
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { }
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { }
        assert(local.page_organization_valid());
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
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { }
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { }
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { }
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(local.wf_main_for_page_access());
        assert(local.page_organization.popped == Popped::VeryUnready(
            slice.page_id@.segment_id,
            slice.page_id@.idx as int,
            count,
            false));
        assert(local.pages.dom().contains(slice.page_id@));
        assert(slice.is_in(*local));
        assert(local.segments == local_start.segments);
        assert(local.page_organization.pages.dom() == local_start.page_organization.pages.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) == local_start.is_used_primary(pid) by {
            reveal(Local::is_used_primary);
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_count(pid) == local_start.page_count(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_capacity(pid) == local_start.page_capacity(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.block_size(pid) == local_start.block_size(pid) by { }
        assert(local_start.mem_chunk_good(slice.page_id@.segment_id));
        local.used_page_fields_preserved_mem_chunk_good(local_start, slice.page_id@.segment_id);
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by {
            assert(local_start.segments.dom().contains(sid));
            assert(local_start.mem_chunk_good(sid));
            local.used_page_fields_preserved_mem_chunk_good(local_start, sid);
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn segment_slice_split(
    slice: PagePtr,
    current_slice_count: usize,
    target_slice_count: usize,
    tld_ptr: TldPtr,

    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main_for_page_access(),
        slice.wf(),
        slice.is_in(*old(local)),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        old(local).mem_chunk_good(slice.page_id@.segment_id),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        0 < target_slice_count < current_slice_count,
        current_slice_count <= SLICES_PER_SEGMENT as usize,
        old(local).page_organization.popped == Popped::VeryUnready(
            slice.page_id@.segment_id,
            slice.page_id@.idx as int,
            current_slice_count as int,
            false),
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).wf_main_for_page_access(),
        final(local).mem_chunk_good(slice.page_id@.segment_id),
        forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid),
        final(local).page_organization.popped == Popped::VeryUnready(
            slice.page_id@.segment_id,
            slice.page_id@.idx as int,
            target_slice_count as int,
            false),
        slice.wf(),
        slice.is_in(*final(local)),
        tld_ptr.wf(),
        tld_ptr.is_in(*final(local)),
{
    let ghost local_snap = *local;
    proof {
        local.page_organization.very_unready_popped_range_facts();
        assert(slice.page_id@.idx + current_slice_count <= SLICES_PER_SEGMENT) by(nonlinear_arith)
            requires
                local.page_organization.popped == Popped::VeryUnready(
                    slice.page_id@.segment_id,
                    slice.page_id@.idx as int,
                    current_slice_count as int,
                    false),
                slice.page_id@.idx + current_slice_count as int <= SLICES_PER_SEGMENT;
        assert(slice.page_id@.idx + target_slice_count <= SLICES_PER_SEGMENT) by(nonlinear_arith)
            requires
                slice.page_id@.idx + current_slice_count <= SLICES_PER_SEGMENT,
                target_slice_count < current_slice_count;
    }
    let next_slice = slice.add_offset(target_slice_count);

    //let count_being_returned = target_slice_count - current_slice_count;
    proof {
        assert(current_slice_count - target_slice_count <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
            requires
                target_slice_count < current_slice_count,
                current_slice_count <= SLICES_PER_SEGMENT as usize;
    }
    let bin_idx = slice_bin(current_slice_count - target_slice_count);
    let ghost next_page_id = next_slice.page_id@;
    let ghost last_page_id = PageId {
        idx: (slice.page_id@.idx + current_slice_count - 1) as nat,
        ..slice.page_id@
    };
    let ghost next_state = PageOrg::take_step::split_page(
        local.page_organization,
        slice.page_id@,
        current_slice_count as int,
        target_slice_count as int,
        bin_idx as int);

    let first_in_queue;

    let cq = &mut tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[bin_idx];
    first_in_queue = cq.first;
    cq.first = next_slice.page_ptr;
    if first_in_queue.addr() == 0 {
        cq.last = next_slice.page_ptr;
    }

    if first_in_queue.addr() != 0 {
        proof {
            assert(local.page_organization == local_snap.page_organization);
            assert(page_organization_queues_match(
                local_snap.page_organization.unused_dlist_headers,
                local_snap.tld.value().segments.span_queue_headers@));
            assert(is_page_ptr_opt(
                first_in_queue,
                local_snap.page_organization.unused_dlist_headers[bin_idx as int].first));
            assert(local_snap.page_organization.unused_dlist_headers[bin_idx as int].first.is_some());
        }
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.unused_dlist_headers[bin_idx as int].first.unwrap()) };
        proof {
            let first_id = first_in_queue_ptr.page_id@;
            assert(first_in_queue_ptr.wf());
            reveal(PageOrg::State::ll_basics);
            reveal(PageOrg::State::ll_inv_valid_unused);
            reveal(PageOrg::State::valid_unused_page);
            assert(0 <= (bin_idx as int) && (bin_idx as int) < local_snap.page_organization.unused_lists.len());
            assert(valid_ll(
                local_snap.page_organization.pages,
                local_snap.page_organization.unused_dlist_headers[bin_idx as int],
                local_snap.page_organization.unused_lists[bin_idx as int]));
            assert(local_snap.page_organization.unused_lists[bin_idx as int].len() != 0);
            assert(local_snap.page_organization.unused_lists[bin_idx as int][0] == first_id);
            assert(local_snap.page_organization.valid_unused_page(first_id, bin_idx as int, 0));
            assert(local_snap.page_organization.pages[first_id].is_used == false);
            assert(local_snap.unused_pages.dom().contains(first_id));
            assert(local.unused_pages.dom().contains(first_id));
            assert(local.pages.dom().contains(first_id));
        }
        unused_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = next_slice.page_ptr;
        });
    }

    proof {
        assert(local_snap.page_organization.pages.dom().contains(slice.page_id@));
        assert(local_snap.page_organization.pages[slice.page_id@].is_used == false);
        assert(local_snap.unused_pages.dom().contains(slice.page_id@));
        assert(local.unused_pages.dom().contains(slice.page_id@));
        assert(local.pages.dom().contains(slice.page_id@));
    }
    unused_page_get_mut_count!(slice, local, c => {
        c = target_slice_count as u32;
    });

    proof {
        assert(next_page_id == PageId {
            segment_id: slice.page_id@.segment_id,
            idx: (slice.page_id@.idx + target_slice_count) as nat,
        });
        assert(slice.page_id@.idx <= next_page_id.idx && next_page_id.idx < slice.page_id@.idx + current_slice_count);
        assert(local_snap.page_organization.pages.dom().contains(next_page_id));
        assert(local_snap.page_organization.pages[next_page_id].is_used == false);
        assert(local_snap.unused_pages.dom().contains(next_page_id));
        assert(local.unused_pages.dom().contains(next_page_id));
        assert(local.pages.dom().contains(next_page_id));
    }
    unused_page_get_mut_inner!(next_slice, local, inner => {
        inner.xblock_size = 0;
    });
    unused_page_get_mut_prev!(next_slice, local, p => {
        p = core::ptr::null_mut();
    });
    unused_page_get_mut_next!(next_slice, local, n => {
        n = first_in_queue;
    });
    unused_page_get_mut_count!(next_slice, local, c => {
        c = (current_slice_count - target_slice_count) as u32;
    });
    unused_page_get_mut!(next_slice, local, page => {
        page.offset = 0;
    });
    proof {
        local.psa = local.psa.insert(next_slice.page_id@, local.unused_pages[next_slice.page_id@]);
    }


    if current_slice_count > target_slice_count + 1 {
        proof {
            assert(slice.page_id@.idx + (current_slice_count - 1) <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    slice.page_id@.idx + current_slice_count <= SLICES_PER_SEGMENT,
                    current_slice_count > 0;
        }
        let last_slice = slice.add_offset(current_slice_count - 1);
        proof {
            assert(last_slice.page_id@ == last_page_id);
            assert(slice.page_id@.idx <= last_page_id.idx && last_page_id.idx < slice.page_id@.idx + current_slice_count);
            assert(local_snap.page_organization.pages.dom().contains(last_page_id));
            assert(local_snap.page_organization.pages[last_page_id].is_used == false);
            assert(local_snap.unused_pages.dom().contains(last_page_id));
            assert(local.unused_pages.dom().contains(last_page_id));
            assert(local.pages.dom().contains(last_page_id));
        }
        unused_page_get_mut_inner!(last_slice, local, inner => {
            inner.xblock_size = 0;
        });
        unused_page_get_mut_count!(last_slice, local, c => {
            c = (current_slice_count - target_slice_count) as u32;
        });
        proof {
            const_facts();
            assert(SLICES_PER_SEGMENT as usize == 512) by(compute_only);
            assert(SIZEOF_PAGE_HEADER as u32 == 80) by(compute_only);
            assert((SIZEOF_PAGE_HEADER as u32) as int == SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(current_slice_count - target_slice_count <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
                requires
                    target_slice_count < current_slice_count,
                    current_slice_count <= SLICES_PER_SEGMENT as usize;
            assert(current_slice_count - target_slice_count - 1 <= 511) by(nonlinear_arith)
                requires
                    current_slice_count - target_slice_count <= SLICES_PER_SEGMENT as usize,
                    SLICES_PER_SEGMENT as usize == 512;
            assert(current_slice_count - target_slice_count - 1 <= u32::MAX as usize) by(nonlinear_arith)
                requires
                    current_slice_count - target_slice_count - 1 <= 511;
            assert((current_slice_count - target_slice_count - 1) as int <= u32::MAX as int) by(nonlinear_arith)
                requires
                    current_slice_count - target_slice_count - 1 <= 511;
            assert((current_slice_count - target_slice_count - 1) as u32 <= 511) by(bit_vector)
                requires
                    current_slice_count <= 512,
                    target_slice_count < current_slice_count;
            assert((current_slice_count - target_slice_count - 1) as u32
                * (SIZEOF_PAGE_HEADER as u32) <= u32::MAX) by(bit_vector)
                requires
                    (current_slice_count - target_slice_count - 1) as u32 <= 511,
                    SIZEOF_PAGE_HEADER as u32 == 80;
        }
        unused_page_get_mut!(last_slice, local, page => {

            

            //assert((current_slice_count - target_slice_count) as u32 * (SIZEOF_PAGE_HEADER as u32)
            //    == (current_slice_count - target_slice_count) as u32 * 32);
            page.offset = (current_slice_count - target_slice_count - 1) as u32
                * (SIZEOF_PAGE_HEADER as u32);
        });
        proof {
            local.psa = local.psa.insert(last_slice.page_id@, local.unused_pages[last_slice.page_id@]);
        }
    }

    proof {
        local.page_organization = next_state;
        assert(common_preserves(local_snap, *local));
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { }
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { }
        assert(local.page_organization_valid());
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
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { }
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { }
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { }
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(local.wf_main_for_page_access());
        assert(local.page_organization.popped == Popped::VeryUnready(
            slice.page_id@.segment_id,
            slice.page_id@.idx as int,
            target_slice_count as int,
            false));
        assert(slice.is_in(*local));
        assert(tld_ptr.is_in(*local));
        assert(local.segments == local_snap.segments);
        assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) == local_snap.is_used_primary(pid) by {
            reveal(Local::is_used_primary);
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_count(pid) == local_snap.page_count(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_capacity(pid) == local_snap.page_capacity(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.block_size(pid) == local_snap.block_size(pid) by { }
        local.used_page_fields_preserved_mem_chunk_good(local_snap, slice.page_id@.segment_id);
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by {
            assert(local_snap.segments.dom().contains(sid));
            assert(local_snap.mem_chunk_good(sid));
            local.used_page_fields_preserved_mem_chunk_good(local_snap, sid);
        }
    }

}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn segment_span_allocate(
    segment: SegmentPtr,
    slice: PagePtr,
    slice_count: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires
        old(local).wf_main_for_page_access(),
        old(local).mem_chunk_good(segment.segment_id@),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        segment.wf(),
        segment.segment_ptr.addr() != 0,
        segment.is_in(*old(local)),
        slice.wf(),
        slice.is_in(*old(local)),
        slice.page_id@.segment_id == segment.segment_id@,
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        segment_span_allocate_page_org_pre(
            old(local).page_organization,
            segment.segment_id@,
            slice.page_id@,
            slice_count as int),
    ensures
        success ==> common_preserves(*old(local), *final(local)),
        success ==> final(local).wf_main_for_page_access(),
        success ==> final(local).mem_chunk_good(segment.segment_id@),
        success ==> (forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid)),
        success && !old(local).page_organization.popped.is_SegmentCreating() ==>
            final(local).segments[segment.segment_id@].mem.pointsto_has_range(
                page_start(slice.page_id@), slice_count as int * SLICE_SIZE as int),
        success && !old(local).page_organization.popped.is_SegmentCreating() ==> set_int_range(
            page_start(slice.page_id@), page_start(slice.page_id@) + slice_count as int * SLICE_SIZE as int)
                <= final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
                    - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),
        success ==> final(local).segments.dom() == old(local).segments.dom(),
        success ==> (forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) && sid != segment.segment_id@ && old(local).mem_chunk_good(sid) ==>
            final(local).mem_chunk_good(sid)),
        success ==> segment.wf(),
        success ==> segment.is_in(*final(local)),
        success ==> tld_ptr.wf(),
        success ==> tld_ptr.is_in(*final(local)),
        success ==> old(local).page_organization.popped.is_SegmentCreating() ==>
            PageOrg::State::forget_about_first_page_strong(
                old(local).page_organization, final(local).page_organization, slice_count as int),
        success ==> !old(local).page_organization.popped.is_SegmentCreating() ==>
            PageOrg::State::allocate_popped_strong(
                old(local).page_organization, final(local).page_organization),
        success ==> !old(local).page_organization.popped.is_SegmentCreating() ==>
            final(local).page_organization.popped == Popped::Ready(slice.page_id@, true),
        success ==> !old(local).page_organization.popped.is_SegmentCreating() ==>
            final(local).page_organization.pages[slice.page_id@].count == Some(slice_count as nat),
{
    let ghost local_start = *local;
    proof {
        reveal(segment_span_allocate_page_org_pre);
        if local.page_organization.popped.is_VeryUnready() {
            local.page_organization.very_unready_popped_range_facts();
            assert(slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT);
        } else {
            local.page_organization.segment_creating_facts(segment.segment_id@);
            assert(slice.page_id@.idx == 0);
            assert((slice_count as int) < SLICES_PER_SEGMENT);
            assert(slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    slice.page_id@.idx == 0,
                    0 <= slice_count as int,
                    (slice_count as int) < SLICES_PER_SEGMENT;
        }
        lemma_segment_os_alloc_constants();
        assert((SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int) by(compute_only);
        assert(slice_count as int <= SLICES_PER_SEGMENT as int) by(nonlinear_arith)
            requires
                slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT,
                0 <= slice.page_id@.idx;
        assert(slice_count <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
            requires
                slice_count as int <= SLICES_PER_SEGMENT as int,
                (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int;
    }
    let ghost next_state = if local.page_organization.popped.is_SegmentCreating() {
        PageOrg::take_step::forget_about_first_page(local.page_organization, slice_count as int)
    } else {
        PageOrg::take_step::allocate_popped(local.page_organization)
    };

    let p = segment_page_start_from_slice(segment, slice, 0);

    proof {
        assert(slice_count > 0);
        assert(SLICE_SIZE as usize == COMMIT_SIZE as usize) by(compute_only);
        assert(SLICE_SIZE as int == COMMIT_SIZE as int) by(compute_only);
        lemma_segment_ptr_commit_aligned(segment);
        assert(SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int) by(compute_only);
        assert(slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
            requires
                slice_count as int <= SLICES_PER_SEGMENT as int,
                SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int,
                0 <= SLICE_SIZE as int;
        assert(SEGMENT_SIZE as int <= usize::MAX as int) by(compute_only);
        assert(slice_count as int * SLICE_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
            requires
                slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int,
                SEGMENT_SIZE as int <= usize::MAX as int;
        assert(p as int == segment_start(segment.segment_id@) + slice.page_id@.idx * SLICE_SIZE);
        assert(segment.segment_ptr.addr() as int == segment_start(segment.segment_id@));
        assert(segment.segment_ptr.addr() <= p) by(nonlinear_arith)
            requires
                p as int == segment_start(segment.segment_id@) + slice.page_id@.idx * SLICE_SIZE,
                segment.segment_ptr.addr() as int == segment_start(segment.segment_id@),
                0 <= slice.page_id@.idx,
                0 <= SLICE_SIZE;
        assert(p as int % COMMIT_SIZE as int == 0) by {
            assert(p as int == segment.segment_ptr as int + slice.page_id@.idx * COMMIT_SIZE as int) by(nonlinear_arith)
                requires
                    p as int == segment_start(segment.segment_id@) + slice.page_id@.idx * SLICE_SIZE,
                    segment.segment_ptr as int == segment_start(segment.segment_id@),
                    SLICE_SIZE as int == COMMIT_SIZE as int;
            lemma_mod_multiples_basic(slice.page_id@.idx as int, COMMIT_SIZE as int);
        }
        assert((slice_count * SLICE_SIZE as usize) as int == slice_count as int * SLICE_SIZE as int) by(nonlinear_arith)
            requires
                slice_count as int * SLICE_SIZE as int <= usize::MAX as int;
        assert((slice_count * SLICE_SIZE as usize) as int % COMMIT_SIZE as int == 0) by {
            assert((slice_count * SLICE_SIZE as usize) as int == slice_count as int * COMMIT_SIZE as int) by(nonlinear_arith)
                requires
                    (slice_count * SLICE_SIZE as usize) as int == slice_count as int * SLICE_SIZE as int,
                    SLICE_SIZE as int == COMMIT_SIZE as int;
            lemma_mod_multiples_basic(slice_count as int, COMMIT_SIZE as int);
        }
        assert(slice_count * SLICE_SIZE as usize != 0) by(nonlinear_arith)
            requires
                slice_count > 0,
                SLICE_SIZE as usize > 0;
        assert(p as int + (slice_count * SLICE_SIZE as usize) as int
            <= segment.segment_ptr as int + SEGMENT_SIZE as int) by(nonlinear_arith)
            requires
                p as int == segment_start(segment.segment_id@) + slice.page_id@.idx * SLICE_SIZE,
                segment.segment_ptr as int == segment_start(segment.segment_id@),
                (slice_count * SLICE_SIZE as usize) as int == slice_count as int * SLICE_SIZE as int,
                slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT,
                SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int;
    }
    if !segment_ensure_committed(segment, p, slice_count * SLICE_SIZE as usize, Tracked(&mut *local)) {
        return false;
    }

    proof {
        assert(local.page_organization == local_start.page_organization);
        assert(p as int == page_start(slice.page_id@));
        assert((slice_count * SLICE_SIZE as usize) as int == slice_count as int * SLICE_SIZE as int);
        assert(set_int_range(
            page_start(slice.page_id@),
            page_start(slice.page_id@) + slice_count as int * SLICE_SIZE as int)
                <= local.commit_mask(segment.segment_id@).bytes(segment.segment_id@)
                    - local.decommit_mask(segment.segment_id@).bytes(segment.segment_id@));
        assert(local.pages == local_start.pages);
        assert(local.psa == local_start.psa);
        assert(local.unused_pages == local_start.unused_pages);
        assert(local.thread_token == local_start.thread_token);
        assert(local.heap == local_start.heap);
        assert(local.tld == local_start.tld);
        assert(local.segments.dom() == local_start.segments.dom());
        assert(local.mem_chunk_good(segment.segment_id@));
        assert(local.wf_main_for_page_access());
    }

    let ghost old_local = *local;
    let ghost first_page_id = slice.page_id@;
    proof {
        assert(old_local.wf_main_for_page_access());
        assert(old_local.page_organization_valid());
        let sid = segment.segment_id@;
        let alloc_start = page_start(first_page_id);
        let alloc_len = slice_count as int * SLICE_SIZE as int;
        let alloc_range = set_int_range(alloc_start, alloc_start + alloc_len);
        assert(old_local.mem_chunk_good(sid));
        assert(alloc_range <= old_local.commit_mask(sid).bytes(sid)
            - old_local.decommit_mask(sid).bytes(sid));
        if !local_start.page_organization.popped.is_SegmentCreating() {
            assert(old_local.page_organization.popped.is_VeryUnready());
            assert(old_local.page_organization.popped.get_VeryUnready_0() == first_page_id.segment_id);
            assert(old_local.page_organization.popped.get_VeryUnready_1() == first_page_id.idx);
            assert(old_local.page_organization.popped.get_VeryUnready_2() == slice_count as int);
            old_local.page_organization.very_unready_popped_range_facts();
            old_local.very_unready_range_disjoint_used_total(first_page_id, slice_count as int);
            old_local.segment_pages_range_total_subset_used_total(sid);
            assert(alloc_range.disjoint(old_local.segment_pages_range_total(sid))) by {
                assert forall |addr: int| #[trigger] alloc_range.contains(addr) implies
                    !old_local.segment_pages_range_total(sid).contains(addr) by {
                    if old_local.segment_pages_range_total(sid).contains(addr) {
                        assert(old_local.segment_pages_used_total(sid).contains(addr));
                        assert(false);
                    }
                }
            };
            assert(alloc_range.disjoint(segment_info_range(sid))) by {
                assert forall |addr: int| #[trigger] alloc_range.contains(addr) implies
                    !segment_info_range(sid).contains(addr) by {
                    assert(page_start(first_page_id) <= addr < page_start(first_page_id) + alloc_len);
                    assert(first_page_id.idx > 0);
                    assert(page_start(first_page_id) >= segment_start(sid) + SLICE_SIZE as int) by(nonlinear_arith)
                        requires
                            page_start(first_page_id) == segment_start(sid) + SLICE_SIZE as int * first_page_id.idx,
                            first_page_id.idx > 0,
                            0 <= SLICE_SIZE as int;
                    assert(SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1)
                        <= SLICE_SIZE as int) by(compute_only);
                    if segment_info_range(sid).contains(addr) {
                        assert(addr < segment_start(sid) + SLICE_SIZE as int) by(nonlinear_arith)
                            requires
                                addr < segment_start(sid) + SIZEOF_SEGMENT_HEADER as int
                                    + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1),
                                SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1)
                                    <= SLICE_SIZE as int;
                        assert(false);
                    }
                }
            };
            assert(old_local.segments[sid].mem.pointsto_has_range(alloc_start, alloc_len)) by {
                assert(mem_chunk_good1(
                    old_local.segments[sid].mem,
                    sid,
                    old_local.commit_mask(sid).bytes(sid),
                    old_local.decommit_mask(sid).bytes(sid),
                    old_local.segment_pages_range_total(sid),
                    old_local.segment_pages_used_total(sid)));
                assert(old_local.commit_mask(sid).bytes(sid)
                    <= old_local.segments[sid].mem.os_rw_bytes());
                assert(old_local.segments[sid].mem.os_rw_bytes()
                    <= old_local.segments[sid].mem.points_to.dom()
                        + segment_info_range(sid)
                        + old_local.segment_pages_range_total(sid));
                assert forall |addr: int| #[trigger] alloc_range.contains(addr) implies
                    old_local.segments[sid].mem.range_points_to().contains(addr) by {
                    assert(old_local.commit_mask(sid).bytes(sid).contains(addr));
                    assert(old_local.segments[sid].mem.os_rw_bytes().contains(addr));
                    if !old_local.segments[sid].mem.range_points_to().contains(addr) {
                        assert((old_local.segments[sid].mem.points_to.dom()
                            + segment_info_range(sid)
                            + old_local.segment_pages_range_total(sid)).contains(addr));
                        if segment_info_range(sid).contains(addr) {
                            assert(false);
                        }
                        if old_local.segment_pages_range_total(sid).contains(addr) {
                            assert(false);
                        }
                        assert(false);
                    }
                }
            };
        }
    }

    //assert(local.page_organization.pages.dom().contains(slice.page_id@));

    let ghost range = first_page_id.range_from(0, slice_count as int);



    let tracked mut first_psa = local.unused_pages.tracked_remove(first_page_id);
    let mut page = ptr_mut_read(slice.page_ptr, Tracked(&mut first_psa.points_to));
    page.offset = 0;
    ptr_mut_write(slice.page_ptr, Tracked(&mut first_psa.points_to), page);
    proof {
        local.unused_pages.tracked_insert(first_page_id, first_psa);
        local.psa = local.psa.insert(first_page_id, local.unused_pages[first_page_id]);
        assert(SLICES_PER_SEGMENT as usize == 512) by(compute_only);
        assert(512usize <= u32::MAX as usize) by(compute_only);
        assert(slice_count <= u32::MAX as usize) by(nonlinear_arith)
            requires
                slice_count <= SLICES_PER_SEGMENT as usize,
                SLICES_PER_SEGMENT as usize == 512,
                512usize <= u32::MAX as usize;
    }
    unused_page_get_mut_count!(slice, local, count => {
        // this is usually already set. I think the one case where it actually needs to
        // be set is when initializing the segment.
        count = slice_count as u32;
    });
    proof {
        assert(SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int) by(compute_only);
        assert(slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
            requires
                slice_count as int <= SLICES_PER_SEGMENT as int,
                SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int,
                0 <= SLICE_SIZE as int;
        assert(SEGMENT_SIZE as int <= usize::MAX as int) by(compute_only);
        assert(slice_count as int * SLICE_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
            requires
                slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int,
                SEGMENT_SIZE as int <= usize::MAX as int;
        assert((SEGMENT_SIZE as usize) as int == SEGMENT_SIZE as int) by(compute_only);
        assert(slice_count * SLICE_SIZE as usize <= SEGMENT_SIZE as usize) by(nonlinear_arith)
            requires
                slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int,
                (SEGMENT_SIZE as usize) as int == SEGMENT_SIZE as int;
        assert(SEGMENT_SIZE as usize <= u32::MAX as usize) by(compute_only);
        assert(slice_count * SLICE_SIZE as usize <= u32::MAX as usize) by(nonlinear_arith)
            requires
                slice_count * SLICE_SIZE as usize <= SEGMENT_SIZE as usize,
                SEGMENT_SIZE as usize <= u32::MAX as usize;
    }
    unused_page_get_mut_inner!(slice, local, inner => {
        // Not entirely sure what the rationale for setting to bsize to this value is.
        // In normal operation, we're going to set the block_size to something else soon.
        // If we are currently setting up page 0 as part of segment initialization,
        // we do need to set this to some nonzero value.
        let bsize = slice_count * SLICE_SIZE as usize;
        inner.xblock_size = if bsize >= HUGE_BLOCK_SIZE as usize { HUGE_BLOCK_SIZE } else { bsize as u32 };
        //assert(inner.xblock_size != 0);
    });
    proof {
        assert(local.pages[first_page_id].inner.value().xblock_size != 0);
        assert(local.pages[first_page_id].wf_unused(first_page_id, local.unused_pages[first_page_id], local.page_organization.popped, local.instance));
        assert(local.segments[segment.segment_id@].wf(
            segment.segment_id@,
            local.thread_token.value().segments.index(segment.segment_id@),
            local.instance));
    }

    // Set up the remaining pages
    let mut i: usize = 1;
    let ghost local_snapshot = *local;
    let extra = slice_count - 1;
    proof {
        assert(extra == slice_count - 1);
        assert(first_page_id.idx + extra < SLICES_PER_SEGMENT) by(nonlinear_arith)
            requires
                first_page_id.idx + slice_count as int <= SLICES_PER_SEGMENT,
                extra == slice_count - 1,
                slice_count > 0;
        assert(local.unused_pages.dom().contains(first_page_id));
        assert forall |page_id|
            #[trigger] first_page_id.range_from(1, extra + 1).contains(page_id) implies
                local.unused_pages.dom().contains(page_id)
                && local.psa.dom().contains(page_id)
                && (local.unused_pages.dom().contains(page_id) ==>
                    local.unused_pages[page_id].points_to.is_init()
                    && is_page_ptr(local.unused_pages[page_id].points_to.ptr(), page_id))
                && local.unused_pages[page_id].points_to.ptr()@.provenance == local.unused_pages[page_id].exposed.provenance()
        by {
            assert(page_id.segment_id == first_page_id.segment_id);
            assert(first_page_id.idx + 1 <= page_id.idx < first_page_id.idx + extra + 1);
            if local.page_organization.popped.is_VeryUnready() {
                local.page_organization.very_unready_popped_range_facts();
                assert(local.page_organization.pages.dom().contains(page_id));
                assert(!local.page_organization.pages[page_id].is_used);
            } else {
                local.page_organization.segment_creating_facts(segment.segment_id@);
                assert(local.page_organization.pages.dom().contains(page_id));
                assert(!local.page_organization.pages[page_id].is_used);
            }
            assert(local.unused_pages.dom().contains(page_id));
            assert(local.pages.dom().contains(page_id));
            assert(local.pages[page_id].wf_unused(page_id, local.unused_pages[page_id], local.page_organization.popped, local.instance));
            assert(local.unused_pages[page_id].wf_unused(page_id, local.instance));
        }
    }
    // Establish the page-range invariant at loop entry: range_from(1, extra+1) is a subrange
    // of range_from(0, slice_count), whose pages are all unused and well-formed.

    while i <= extra
        invariant 1 <= i <= extra + 1,
          first_page_id.idx + extra < SLICES_PER_SEGMENT,
          *local == (Local { unused_pages: local.unused_pages, .. local_snapshot }),
          local.unused_pages.dom() == local_snapshot.unused_pages.dom(),
          slice.wf(),
          slice.page_id == first_page_id,
          forall |page_id|
              #[trigger] first_page_id.range_from(1, extra + 1).contains(page_id) ==>
                  local.unused_pages.dom().contains(page_id)
                  && (local.unused_pages.dom().contains(page_id) ==>
                    local.unused_pages[page_id].points_to.is_init()
                    && is_page_ptr(local.unused_pages[page_id].points_to.ptr(), page_id))
                    && local.unused_pages[page_id].points_to.ptr()@.provenance == local.unused_pages[page_id].exposed.provenance(),
          forall |page_id|
              #[trigger] local.unused_pages.dom().contains(page_id) ==>
              (
                  if first_page_id.range_from(1, i as int).contains(page_id) {
                      psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id])
                      && local.unused_pages[page_id].points_to.value().offset ==
                          (page_id.idx - first_page_id.idx) * SIZEOF_PAGE_HEADER
                  } else {
                      local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]
                  }
              ),
    {
        let ghost prelocal = *local;
        let this_slice = slice.add_offset(i);
        let ghost this_page_id = PageId { idx: (first_page_id.idx + i) as nat, .. first_page_id };

        proof {
            assert(first_page_id.range_from(1, extra + 1).contains(this_page_id));
            assert(local.unused_pages.dom().contains(this_page_id));
            assert(local.unused_pages[this_page_id].points_to.is_init());
            assert(is_page_ptr(local.unused_pages[this_page_id].points_to.ptr(), this_page_id));
            assert(this_slice.wf());
        }

        let tracked mut this_psa = local.unused_pages.tracked_remove(this_page_id);
        proof {
            assert(this_psa.points_to.is_init());
            assert(is_page_ptr(this_psa.points_to.ptr(), this_page_id));
            assert(this_psa.points_to.ptr() == this_slice.page_ptr);
        }
        let mut page = ptr_mut_read(this_slice.page_ptr, Tracked(&mut this_psa.points_to));

        

        

        
        proof {
            assert(SLICES_PER_SEGMENT as usize == 512) by(compute_only);
            assert(SIZEOF_PAGE_HEADER as u32 == 80) by(compute_only);
            assert(extra < SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    first_page_id.idx + extra < SLICES_PER_SEGMENT,
                    0 <= first_page_id.idx;
            assert(i <= 511) by(nonlinear_arith)
                requires
                    i <= extra,
                    extra < SLICES_PER_SEGMENT,
                    SLICES_PER_SEGMENT as usize == 512;
            assert(i as int <= 511);
            assert((i as u32) as int == i as int) by(bit_vector)
                requires i as int <= 511;
            assert(i as u32 <= 511) by(bit_vector)
                requires i as int <= 511;
            assert(i as u32 * SIZEOF_PAGE_HEADER as u32 <= u32::MAX) by(bit_vector)
                requires
                    i as u32 <= 511,
                    SIZEOF_PAGE_HEADER as u32 == 80;
        }
        page.offset = i as u32 * SIZEOF_PAGE_HEADER as u32;
        ptr_mut_write(this_slice.page_ptr, Tracked(&mut this_psa.points_to), page);
        proof {
            local.unused_pages.tracked_insert(this_page_id, this_psa);
        }

        i = i + 1;

        proof {
            assert forall |page_id|
              #[trigger] local.unused_pages.dom().contains(page_id) implies
              (
                  if first_page_id.range_from(1, i as int).contains(page_id) {
                      psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id])
                      && local.unused_pages[page_id].points_to.value().offset ==
                          (page_id.idx - first_page_id.idx) * SIZEOF_PAGE_HEADER
                  } else {
                      local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]
                  }
              )
           by {
              if first_page_id.range_from(1, i as int).contains(page_id) {
                      if page_id == this_page_id {
                          assert(psa_differ_only_in_offset(
                              local.unused_pages[page_id],
                              local_snapshot.unused_pages[page_id]));
                          assert(page_id.idx - first_page_id.idx == i - 1);
                          assert(local.unused_pages[page_id].points_to.value().offset ==
                              (page_id.idx - first_page_id.idx) * SIZEOF_PAGE_HEADER);
                      } else {
                          assert(prelocal.unused_pages.dom().contains(page_id));
                          assert(local.unused_pages[page_id] == prelocal.unused_pages[page_id]);
                          assert(psa_differ_only_in_offset(
                              local.unused_pages[page_id],
                              local_snapshot.unused_pages[page_id]));
                          assert(local.unused_pages[page_id].points_to.value().offset ==
                              (page_id.idx - first_page_id.idx) * SIZEOF_PAGE_HEADER);
                      }
                  } else {
                      assert(prelocal.unused_pages.dom().contains(page_id));
                      assert(local.unused_pages[page_id] == prelocal.unused_pages[page_id]);
                      assert(local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]);
                  }
           }
        }
    }

    proof {
        let ghost updated_unused_psa = Map::new(
            local.unused_pages.dom(),
            |page_id: PageId| local.unused_pages[page_id],
        );
        assert(local.page_organization == local_snapshot.page_organization);
        assert(local.psa == local_snapshot.psa);
        assert(local_snapshot.page_organization_valid());
        assert(page_organization_pages_match(
            local_snapshot.page_organization.pages,
            local_snapshot.pages,
            local_snapshot.psa,
            local_snapshot.page_organization.popped));
        assert(local_snapshot.page_organization.pages.dom() == local_snapshot.psa.dom());
        assert forall |page_id: PageId| #[trigger] local.unused_pages.dom().contains(page_id) implies
            local_snapshot.psa.dom().contains(page_id) by {
            assert(local_snapshot.unused_pages.dom().contains(page_id));
            assert(local_snapshot.page_organization.pages.dom().contains(page_id));
        }
        assert(updated_unused_psa.dom() <= local_snapshot.psa.dom());
        local.psa = local.psa.union_prefer_right(updated_unused_psa);
        assert(local.psa.dom() == local_snapshot.psa.dom());
        assert(local.page_organization.pages.dom() == local.psa.dom());
    }

    proof {
        assert(local.unused_pages.dom().contains(first_page_id));
        assert(local.unused_pages[first_page_id].points_to.is_init());
        assert(is_page_ptr(local.unused_pages[first_page_id].points_to.ptr(), first_page_id));
        assert(local.unused_pages[first_page_id].points_to.ptr() == slice.page_ptr);
        assert(local.pages.dom().contains(first_page_id));
        assert(local.pages[first_page_id] == local_snapshot.pages[first_page_id]);
        assert(local.unused_pages[first_page_id] == local_snapshot.unused_pages[first_page_id]);
        assert(local.page_organization == local_snapshot.page_organization);
        assert(local.instance == local_snapshot.instance);
        assert(local_snapshot.pages[first_page_id].wf_unused(
            first_page_id,
            local_snapshot.unused_pages[first_page_id],
            local_snapshot.page_organization.popped,
            local_snapshot.instance));
        assert(local.pages[first_page_id].wf_unused(first_page_id, local.unused_pages[first_page_id], local.page_organization.popped, local.instance));
        assert(local_snapshot.pages[first_page_id].inner.value().xblock_size != 0);
        assert(local.pages[first_page_id].inner.value().xblock_size == local_snapshot.pages[first_page_id].inner.value().xblock_size);
        assert(local.pages[first_page_id].inner.value().xblock_size != 0);
    }
    unused_page_get_mut_inner!(slice, local, inner => {
        inner.set_is_reset(false);
        inner.set_is_committed(false);
    });
    proof {
        assert(local.page_organization == local_snapshot.page_organization);
        assert(local_snapshot.pages[first_page_id].inner.value().xblock_size != 0);
        assert(local.pages[first_page_id].inner.value().xblock_size == local_snapshot.pages[first_page_id].inner.value().xblock_size);
        assert(local.pages[first_page_id].inner.value().xblock_size != 0);
        assert(local.segments == local_snapshot.segments);
        assert(local.thread_token == local_snapshot.thread_token);
        assert(local.instance == local_snapshot.instance);
        local.page_organization.lemma_used_bound(segment.segment_id@);
        assert(local_start.page_organization_valid());
        assert(page_organization_segments_match(local_start.page_organization.segments, local_start.segments));
        assert(local_start.page_organization.segments[segment.segment_id@].used == local_start.segments[segment.segment_id@].main2.value().used);
        assert(local_snapshot.segments[segment.segment_id@].main2 == local_start.segments[segment.segment_id@].main2);
        assert(local.page_organization.segments[segment.segment_id@].used == local.segments[segment.segment_id@].main2.value().used);
        assert(local.segments[segment.segment_id@].main2.value().used <= SLICES_PER_SEGMENT + 1);
        assert(local.segments[segment.segment_id@].main2.value().used < usize::MAX) by(nonlinear_arith)
            requires
                local.segments[segment.segment_id@].main2.value().used <= SLICES_PER_SEGMENT + 1,
                SLICES_PER_SEGMENT as int + 1 < usize::MAX as int;
        assert(segment.is_in(*local));
        assert(local_snapshot.thread_token.value().segments.dom().contains(segment.segment_id@));
        assert(local_snapshot.segments[segment.segment_id@].wf(
            segment.segment_id@,
            local_snapshot.thread_token.value().segments.index(segment.segment_id@),
            local_snapshot.instance));
        assert(local_snapshot.thread_token.value().segments[segment.segment_id@].is_enabled);
        assert(local.thread_token == local_snapshot.thread_token);
        assert(local.thread_id == local_snapshot.thread_id);
        assert(local_snapshot.thread_token == local_start.thread_token);
        assert(local_snapshot.thread_id == local_start.thread_id);
        assert(local_start.thread_token.key() == local_start.thread_id);
        assert(local.thread_token.key() == local.thread_id);
        assert(local.thread_token.value().segments.dom().contains(segment.segment_id@));
        assert(local.thread_token.value().segments[segment.segment_id@].is_enabled);
    }
    proof {
        assert(old_local.mem_chunk_good(segment.segment_id@));
        assert(local.segments == old_local.segments);
        assert(local.page_organization == old_local.page_organization);
        assert(local.page_organization.pages.dom() == old_local.page_organization.pages.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) == old_local.is_used_primary(pid) by {
            assert(local.page_organization == old_local.page_organization);
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_count(pid) == old_local.page_count(pid) by {
            if local.is_used_primary(pid) {
                if pid == first_page_id {
                    assert(!old_local.is_used_primary(first_page_id));
                    assert(false);
                } else {
                    assert(local.pages[pid] == old_local.pages[pid]);
                }
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_capacity(pid) == old_local.page_capacity(pid) by {
            if local.is_used_primary(pid) {
                if pid == first_page_id {
                    assert(!old_local.is_used_primary(first_page_id));
                    assert(false);
                } else {
                    assert(local.pages[pid] == old_local.pages[pid]);
                }
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.block_size(pid) == old_local.block_size(pid) by {
            if local.is_used_primary(pid) {
                if pid == first_page_id {
                    assert(!old_local.is_used_primary(first_page_id));
                    assert(false);
                } else {
                    assert(local.pages[pid] == old_local.pages[pid]);
                }
            }
        }
        local.used_page_fields_preserved_mem_chunk_good(old_local, segment.segment_id@);
        assert(local.mem_chunk_good(segment.segment_id@));
        local.page_organization = next_state;
        assert(local.segments == old_local.segments);
        assert(local.page_organization.pages.dom() == old_local.page_organization.pages.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) == old_local.is_used_primary(pid) by {
            if pid.segment_id != segment.segment_id@ {
                assert(local.page_organization.pages[pid] == old_local.page_organization.pages[pid]);
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_count(pid) == old_local.page_count(pid) by {
            if pid.segment_id != segment.segment_id@ {
                assert(local.pages[pid] == old_local.pages[pid]);
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_capacity(pid) == old_local.page_capacity(pid) by {
            if pid.segment_id != segment.segment_id@ {
                assert(local.pages[pid] == old_local.pages[pid]);
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.block_size(pid) == old_local.block_size(pid) by {
            if pid.segment_id != segment.segment_id@ {
                assert(local.pages[pid] == old_local.pages[pid]);
            }
        }
        local.used_page_fields_preserved_mem_chunk_good(old_local, segment.segment_id@);
        assert(local.mem_chunk_good(segment.segment_id@));
    }
    let ghost local_before_main2 = *local;
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used + 1;
    });

    proof {
        assert(local.segments.dom() == local_start.segments.dom());
        assert(local.segments[segment.segment_id@].mem == local_before_main2.segments[segment.segment_id@].mem);
        assert(local.commit_mask(segment.segment_id@) == local_before_main2.commit_mask(segment.segment_id@));
        assert(local.decommit_mask(segment.segment_id@) == local_before_main2.decommit_mask(segment.segment_id@));
        assert(local.page_organization.pages.dom() == local_before_main2.page_organization.pages.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) == local_before_main2.is_used_primary(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_count(pid) == local_before_main2.page_count(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_capacity(pid) == local_before_main2.page_capacity(pid) by { }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.block_size(pid) == local_before_main2.block_size(pid) by { }
        local.segment_page_totals_preserved(local_before_main2, segment.segment_id@);
        local.mem_chunk_good_preserved_by_page_totals(local_before_main2, segment.segment_id@);
        assert(local.mem_chunk_good(segment.segment_id@));
        assert forall |sid: SegmentId| #[trigger] local_start.segments.dom().contains(sid) && sid != segment.segment_id@ && local_start.mem_chunk_good(sid) implies
            local.mem_chunk_good(sid) by {
            assert(local.segments.dom().contains(sid));
            assert(local.segments[sid] == local_start.segments[sid]);
            assert(local.commit_mask(sid) == local_start.commit_mask(sid));
            assert(local.decommit_mask(sid) == local_start.decommit_mask(sid));
            assert forall |pid: PageId| #[trigger] local_start.page_organization.pages.dom().contains(pid) implies
                local.page_organization.pages.dom().contains(pid) by { }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                pid.segment_id == segment.segment_id@ || local_start.page_organization.pages.dom().contains(pid) by { }
            assert forall |pid: PageId| #[trigger] local_start.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_start.is_used_primary(pid) by {
                if pid.segment_id != segment.segment_id@ {
                    assert(local.page_organization.pages[pid] == local_start.page_organization.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local_start.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_count(pid) == local_start.page_count(pid) by {
                if pid.segment_id != segment.segment_id@ {
                    assert(local.pages[pid] == local_start.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local_start.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_capacity(pid) == local_start.page_capacity(pid) by {
                if pid.segment_id != segment.segment_id@ {
                    assert(local.pages[pid] == local_start.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local_start.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.block_size(pid) == local_start.block_size(pid) by {
                if pid.segment_id != segment.segment_id@ {
                    assert(local.pages[pid] == local_start.pages[pid]);
                }
            }
            local.mem_chunk_good_preserved_when_only_other_segment_pages_change(local_start, sid, segment.segment_id@);
        }
        assert(local.segments[segment.segment_id@].wf(
            segment.segment_id@,
            local.thread_token.value().segments.index(segment.segment_id@),
            local.instance));
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance) by {
            if sid != segment.segment_id@ {
                assert(local.segments[sid] == local_start.segments[sid]);
            }
        }
        assert(local.page_organization.invariant());
        assert(local.tld.is_init());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(local.page_organization.pages.dom() =~= local.pages.dom());
        assert(local.page_organization.pages.dom() =~= local.psa.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            page_organization_pages_match_data(
                local.page_organization.pages[pid],
                local.pages[pid],
                local.psa[pid],
                pid,
                local.page_organization.popped) by {
            reveal(page_organization_pages_match_data);
            let page_data = local.page_organization.pages[pid];
            let pla = local.pages[pid];
            let psa = local.psa[pid];
            assert(psa.points_to.is_init());
            match (*pla.count.value(), *pla.inner.value(), *pla.prev.value(), *pla.next.value()) {
                (count, inner, prev, next) => {
                    assert(match page_data.count {
                        None => true,
                        Some(c) => count as int == c,
                    });
                    assert(match page_data.full {
                        None => true,
                        Some(b) => inner.in_full() == b,
                    });
                    assert(match page_data.offset {
                        None => true,
                        Some(o) => psa.points_to.value().offset as int == o * SIZEOF_PAGE_HEADER,
                    });
                    assert(match page_data.dlist_entry {
                        None => true,
                        Some(page_queue_data) => is_page_ptr_opt(prev, page_queue_data.prev) && is_page_ptr_opt(next, page_queue_data.next),
                    });
                    if page_data.page_header_kind.is_None() {
                        if pid.idx == 0 {
                            assert(!page_data.is_used);
                            if !local.page_organization.popped.is_SegmentCreating() {
                                if pid == first_page_id {
                                    assert(local.pages[pid].inner.value().xblock_size != 0);
                                    assert(inner.xblock_size != 0);
                                } else {
                                    assert(old_local.page_organization_valid());
                                    assert(page_organization_pages_match(
                                        old_local.page_organization.pages,
                                        old_local.pages,
                                        old_local.psa,
                                        old_local.page_organization.popped));
                                    assert(old_local.page_organization.pages.dom().contains(pid));
                                    assert(page_organization_pages_match_data(
                                        old_local.page_organization.pages[pid],
                                        old_local.pages[pid],
                                        old_local.psa[pid],
                                        pid,
                                        old_local.page_organization.popped));
                                    assert(local.pages[pid] == old_local.pages[pid]);
                                    match (*old_local.pages[pid].count.value(), *old_local.pages[pid].inner.value(), *old_local.pages[pid].prev.value(), *old_local.pages[pid].next.value()) {
                                        (_, old_inner, _, _) => {
                                            if old_local.page_organization.popped.is_SegmentCreating() {
                                                match old_local.page_organization.popped {
                                                    Popped::SegmentCreating(sid) => {
                                                        if sid == pid.segment_id {
                                                            assert(sid == segment.segment_id@);
                                                            assert(first_page_id.segment_id == segment.segment_id@);
                                                            assert(first_page_id.idx == 0);
                                                            assert(pid == first_page_id);
                                                            assert(false);
                                                        }
                                                    }
                                                    _ => { }
                                                }
                                            }
                                            assert(old_inner.xblock_size != 0);
                                            assert(inner.xblock_size == old_inner.xblock_size);
                                            assert(inner.xblock_size != 0);
                                        }
                                    }
                                }
                            }
                        }
                        if pid.idx != 0 && page_data.offset == Some(0nat) {
                            if !(local.page_organization.popped.is_Ready() && local.page_organization.popped.get_Ready_0() == pid)
                                && !(local.page_organization.popped.is_VeryUnready() && local.page_organization.popped.get_VeryUnready_0() == pid.segment_id && local.page_organization.popped.get_VeryUnready_1() == pid.idx) {
                                assert(page_data.is_used <==> inner.xblock_size != 0);
                            }
                        }
                    }
                    assert(match page_data.page_header_kind {
                        None => {
                            (pid.idx == 0 ==> {
                                &&& !page_data.is_used
                                &&& (match local.page_organization.popped {
                                    Popped::SegmentCreating(sid) if sid == pid.segment_id => true,
                                    _ => inner.xblock_size != 0,
                                })
                                &&& (!local.page_organization.popped.is_SegmentCreating() ==> inner.xblock_size != 0)
                            })
                            && (pid.idx != 0 ==> page_data.offset == Some(0nat) ==> (
                                (!(local.page_organization.popped.is_Ready() && local.page_organization.popped.get_Ready_0() == pid) &&
                                    !(local.page_organization.popped.is_VeryUnready() && local.page_organization.popped.get_VeryUnready_0() == pid.segment_id && local.page_organization.popped.get_VeryUnready_1() == pid.idx))
                                  ==>
                                (page_data.is_used <==> inner.xblock_size != 0)
                            ))
                        }
                        Some(PageHeaderKind::Normal(_, bsize)) => {
                            &&& pid.idx != 0
                            &&& page_data.is_used
                            &&& inner.xblock_size != 0
                            &&& inner.xblock_size == bsize
                            &&& page_data.is_used
                            &&& page_data.offset == Some(0nat)
                        }
                    });
                }
            }
        }
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert(local.page_organization_valid());
        assert(local.wf_main_for_page_access());
        assert(local.segments[segment.segment_id@].mem == old_local.segments[segment.segment_id@].mem);
        assert(local.commit_mask(segment.segment_id@) == old_local.commit_mask(segment.segment_id@));
        assert(local.decommit_mask(segment.segment_id@) == old_local.decommit_mask(segment.segment_id@));
        if !local_start.page_organization.popped.is_SegmentCreating() {
            assert(local.segments[segment.segment_id@].mem.pointsto_has_range(
                page_start(slice.page_id@), slice_count as int * SLICE_SIZE as int));
        }
    }

    return true;
}

// segment_reclaim_or_alloc
//  -> segment_alloc
//  -> segment_os_alloc
//  -> arena_alloc_aligned

// For normal pages, required == 0
// For huge pages, required == ?
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn segment_alloc(
    required: usize,
    page_alignment: usize,
    req_arena_id: ArenaId,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    // os_tld,
    // huge_page,
) -> (segment_ptr: SegmentPtr)
    requires
        required == 0,
        page_alignment == 0,
        tld.wf(),
        tld.is_in(*old(local)),
        old(local).wf(),
        segment_calculate_slices_required_bound(required as int),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        segment_ptr.segment_ptr.addr() != 0 ==> segment_ptr.wf(),
        segment_ptr.segment_ptr.addr() != 0 ==> segment_ptr.is_in(*final(local)),
        tld.wf(),
        tld.is_in(*final(local)),
{

    let (segment_slices, pre_size, info_slices) = segment_calculate_slices(required);
    let eager_delay = (current_thread_count() > 1 &&
          tld.get_segments_count(Tracked(&*local)) < option_eager_commit_delay() as usize);
    let eager = !eager_delay && option_eager_commit();
    let commit = eager || (required > 0);
    let is_zero = false;

    let mut commit_mask = CommitMask::empty();
    let mut decommit_mask = CommitMask::empty();

    let (pre_segment_ptr, new_psegment_slices, new_ppre_size, new_pinfo_slices, is_zero, pcommit, memid, mem_large, is_pinned, align_offset, Tracked(mem_chunk)) = segment_os_alloc(
        required,
        page_alignment,
        eager_delay,
        req_arena_id,
        segment_slices,
        pre_size,
        info_slices,
        &mut commit_mask,
        &mut decommit_mask,
        commit,
        tld,
        Tracked(&mut *local));

    let ghost local_snap1 = *local;

    if pre_segment_ptr.is_null() {
        proof {
            assert(*local == local_snap1);
            assert(*local == *old(local));
            assert(local.wf());
            assert(common_preserves(*old(local), *local));
            assert(local.inst() == old(local).inst());
            assert(tld.is_in(*local));
        }
        return pre_segment_ptr;
    }

    let tracked thread_state_tok = local.take_thread_token();
    let ghost pre_segment_id = pre_segment_ptr.segment_id@;
    let ghost segment_state = SegmentState {
        shared_access: arbitrary(),
        is_enabled: false,
    };
    let tracked (Tracked(thread_state_tok), Ghost(tos), Tracked(thread_of_segment_tok))
        = local.instance.create_segment_mk_tokens(
            local.thread_id,
            pre_segment_id,
            segment_state,
            thread_state_tok);
    let ghost segment_id = Mim::State::mk_fresh_segment_id(tos, pre_segment_id);
    let segment_ptr = SegmentPtr {
        segment_ptr: pre_segment_ptr.segment_ptr,
        segment_id: Ghost(segment_id),
    };
    proof {
        assert(pre_segment_id.id == segment_id.id);
        assert(pre_segment_id.provenance == segment_id.provenance);
        lemma_segment_start_eq_id(pre_segment_id, segment_id);
        assert(segment_start(pre_segment_id) == segment_start(segment_id));
        assert(segment_ptr.wf());
    }
    let ghost allocated_mem_chunk = mem_chunk;

    // the C version skips this step if the bytes are all zeroed by the OS
    // We would need a complex transmute operation to do the same thing

    let tracked seg_header_points_to_raw = mem_chunk.take_points_to_range(
        segment_start(segment_id), SIZEOF_SEGMENT_HEADER as int);

    //assert(SIZEOF_SEGMENT_HEADER == vstd::layout::size_of::<SegmentHeader>());
    //assert(segment_start(segment_id) % vstd::layout::align_of::<SegmentHeader>() as int == 0);
    vstd::layout::layout_for_type_is_valid::<SegmentHeader>(); // $line_count$Proof$
    proof {
        segment_layout_facts();
        lemma_segment_start_usize_align(segment_id);
        assert(size_of::<SegmentHeader>() == SIZEOF_SEGMENT_HEADER);
        assert(SIZEOF_SEGMENT_HEADER != 0) by(compute_only);
        assert(size_of::<SegmentHeader>() != 0);
        assert(align_of::<SegmentHeader>() == 8);
        assert((segment_start(segment_id) as usize) as int == segment_start(segment_id));
        assert((segment_start(segment_id) as usize) % align_of::<SegmentHeader>() == 0) by(nonlinear_arith)
            requires
                (segment_start(segment_id) as usize) as int == segment_start(segment_id),
                segment_start(segment_id) % 8 == 0,
                align_of::<SegmentHeader>() == 8;
        assert(seg_header_points_to_raw.is_range(segment_start(segment_id), SIZEOF_SEGMENT_HEADER as int));
        assert(seg_header_points_to_raw.is_range((segment_start(segment_id) as usize) as int, size_of::<SegmentHeader>() as int));
    }

    let tracked mut seg_header_points_to = seg_header_points_to_raw.into_typed::<SegmentHeader>(segment_start(segment_id) as usize);
    let allow_decommit = option_allow_decommit() && !is_pinned && !mem_large;
    let (pcell_main, Tracked(pointsto_main)) = PCell::new(SegmentHeaderMain {
        memid: memid,
        mem_is_pinned: is_pinned,
        mem_is_large: mem_large,
        mem_is_committed: commit_mask.is_full(),
        mem_alignment: page_alignment,
        mem_align_offset: align_offset,
        allow_decommit: allow_decommit,
        decommit_expire: 0,
        decommit_mask: if allow_decommit { decommit_mask } else { CommitMask::empty() },
        commit_mask: commit_mask,
    });
    let (pcell_main2, Tracked(pointsto_main2)) = PCell::new(SegmentHeaderMain2 {
        next: core::ptr::null_mut(),
        abandoned: 0,
        abandoned_visits: 0,
        used: 0,
        cookie: 0,
        segment_slices: 0,
        segment_info_slices: 0,
        kind: if required == 0 { SegmentKind::Normal } else { SegmentKind::Huge },
        slice_entries: 0,
    });
    let (cur_thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    proof {
        is_thread.agrees(local.is_thread);
        assert(cur_thread_id == is_thread@);
        assert(is_thread@ == local.is_thread@);
        assert(local.thread_id == local.is_thread@);
        assert(cur_thread_id == local.thread_id);
    }
    //assert(segment_ptr.segment_ptr@.provenance == seg_header_points_to.ptr()@.provenance);
    ptr_mut_write(segment_ptr.segment_ptr, Tracked(&mut seg_header_points_to), SegmentHeader {
        main: pcell_main,
        abandoned_next: 0,
        main2: pcell_main2,
        thread_id: AtomicU64::new(
            Ghost((Ghost(local.instance), Ghost(segment_id))),
            cur_thread_id.thread_id,
            Tracked(thread_of_segment_tok),
        ),
        instance: Ghost(local.instance),
        segment_id: Ghost(segment_id),
    });

    //assert(segment_ptr.segment_ptr.id() + SEGMENT_SIZE < usize::MAX);
    let mut i: usize = 0;
    let mut cur_page_ptr = segment_ptr.segment_ptr.with_addr(
        segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER
    ) as *mut Page;
    //assert(i * SIZEOF_PAGE_HEADER == 0);
    let ghost old_mem_chunk = mem_chunk;
    let tracked mut psa_map = Map::<PageId, PageSharedAccess>::tracked_empty();
    let tracked mut pla_map = Map::<PageId, PageLocalAccess>::tracked_empty();
    //assert(segment_ptr.segment_ptr@.provenance == segment_ptr.segment_id@.provenance);
    while i <= SLICES_PER_SEGMENT as usize
        invariant mem_chunk.os == old_mem_chunk.os,
            mem_chunk.wf(),
            //mem_chunk.pointsto_has_range(segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER,
            //  COMMIT_SIZE - (SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER)),
            set_int_range(
                    segment_start(segment_id) + SIZEOF_SEGMENT_HEADER,
                    segment_start(segment_id) + COMMIT_SIZE) <= old_mem_chunk.points_to.dom(),
            mem_chunk.points_to.dom() =~= old_mem_chunk.points_to.dom() -
                set_int_range(
                    segment_start(segment_id),
                    segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER
                ),

            cur_page_ptr as int == segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER,
            cur_page_ptr@.provenance == segment_ptr.segment_ptr@.provenance,
            mem_chunk.points_to.provenance() == segment_ptr.segment_ptr@.provenance,
            segment_ptr.segment_ptr as int + SEGMENT_SIZE < usize::MAX,
            segment_ptr.wf(),
            segment_ptr.segment_id@ == segment_id,
            i <= SLICES_PER_SEGMENT + 1,
            forall |page_id: PageId|
                #[trigger] psa_map.dom().contains(page_id) ==>
                    page_id.segment_id == segment_id && 0 <= page_id.idx < i,
            forall |page_id: PageId|
                #[trigger] pla_map.dom().contains(page_id) ==>
                    page_id.segment_id == segment_id && 0 <= page_id.idx < i,
            forall |page_id: PageId|
                #![trigger psa_map.dom().contains(page_id)]
                #![trigger psa_map.index(page_id)]
                #![trigger pla_map.dom().contains(page_id)]
                #![trigger pla_map.index(page_id)]
            {
                page_id.segment_id == segment_id && 0 <= page_id.idx < i ==> {
                    &&& psa_map.dom().contains(page_id)
                    &&& pla_map.dom().contains(page_id)
                    &&& pla_map[page_id].inner.value().zeroed()
                    &&& pla_map[page_id].count.value() == 0
                    &&& pla_map[page_id].prev.value().addr() == 0
                    &&& pla_map[page_id].next.value().addr() == 0

                    &&& is_page_ptr(psa_map[page_id].points_to.ptr(), page_id)
                    &&& psa_map[page_id].points_to.is_init()
                    &&& psa_map[page_id].points_to.value().count.id() == pla_map[page_id].count.id()
                    &&& psa_map[page_id].points_to.value().inner.id() == pla_map[page_id].inner.id()
                    &&& psa_map[page_id].points_to.value().prev.id() == pla_map[page_id].prev.id()
                    &&& psa_map[page_id].points_to.value().next.id() == pla_map[page_id].next.id()
                    &&& psa_map[page_id].points_to.ptr()@.provenance == psa_map[page_id].exposed.provenance()
                    &&& psa_map[page_id].points_to.value().offset == 0
                    &&& psa_map[page_id].points_to.value().xthread_free.is_empty()
                    &&& psa_map[page_id].points_to.value().xthread_free.wf()
                    &&& psa_map[page_id].points_to.value().xthread_free.instance == local.instance
                    &&& psa_map[page_id].points_to.value().xheap.is_empty()
                }
            }
    {
        let ghost page_id = PageId { segment_id, idx: i as nat };

        let ghost phstart = segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER;
        proof {
            lemma_page_header_first_commit_range(segment_id, i as int);
            assert(phstart == page_header_start(page_id));
            assert(phstart + SIZEOF_PAGE_HEADER as int <= segment_start(segment_id) + COMMIT_SIZE as int);
            assert(set_int_range(phstart, phstart + SIZEOF_PAGE_HEADER as int) <= old_mem_chunk.points_to.dom()) by {
                assert forall |addr: int| #[trigger] set_int_range(phstart, phstart + SIZEOF_PAGE_HEADER as int).contains(addr) implies
                    old_mem_chunk.points_to.dom().contains(addr) by {
                    assert(phstart <= addr < phstart + SIZEOF_PAGE_HEADER as int);
                    assert(segment_start(segment_id) + SIZEOF_SEGMENT_HEADER <= phstart) by(nonlinear_arith)
                        requires
                            phstart == segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER,
                            0 <= i as int,
                            0 <= SIZEOF_PAGE_HEADER as int;
                    assert(segment_start(segment_id) + SIZEOF_SEGMENT_HEADER <= addr < segment_start(segment_id) + COMMIT_SIZE as int) by(nonlinear_arith)
                        requires
                            segment_start(segment_id) + SIZEOF_SEGMENT_HEADER <= phstart,
                            phstart <= addr,
                            addr < phstart + SIZEOF_PAGE_HEADER as int,
                            phstart + SIZEOF_PAGE_HEADER as int <= segment_start(segment_id) + COMMIT_SIZE as int;
                };
            }
            assert(set_int_range(phstart, phstart + SIZEOF_PAGE_HEADER as int) <= mem_chunk.points_to.dom()) by {
                assert forall |addr: int| #[trigger] set_int_range(phstart, phstart + SIZEOF_PAGE_HEADER as int).contains(addr) implies
                    mem_chunk.points_to.dom().contains(addr) by {
                    assert(mem_chunk.points_to.dom() =~= old_mem_chunk.points_to.dom() - set_int_range(
                        segment_start(segment_id),
                        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER));
                    assert(old_mem_chunk.points_to.dom().contains(addr));
                    assert(phstart <= addr);
                    assert(segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER == phstart);
                    assert(!set_int_range(
                        segment_start(segment_id),
                        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + i * SIZEOF_PAGE_HEADER).contains(addr));
                };
            }
        }
        vstd::layout::layout_for_type_is_valid::<Page>(); // $line_count$Proof$
        let tracked page_header_points_to_raw = mem_chunk.take_points_to_range(
            phstart, SIZEOF_PAGE_HEADER as int);
        proof {
            page_layout_facts();
            assert(size_of::<Page>() == SIZEOF_PAGE_HEADER);
            assert(SIZEOF_PAGE_HEADER != 0) by(compute_only);
            assert(size_of::<Page>() != 0);
            assert(align_of::<Page>() == 8);
            assert((phstart as usize) as int == phstart);
            assert((phstart as usize) % align_of::<Page>() == 0) by(nonlinear_arith)
                requires
                    (phstart as usize) as int == phstart,
                    phstart % 8 == 0,
                    align_of::<Page>() == 8;
            assert(page_header_points_to_raw.is_range(phstart, SIZEOF_PAGE_HEADER as int));
            assert(page_header_points_to_raw.is_range((phstart as usize) as int, size_of::<Page>() as int));
        }
        let tracked mut page_header_points_to = page_header_points_to_raw.into_typed::<Page>(phstart as usize);
        let (pcell_count, Tracked(pointsto_count)) = PCell::new(0);
        let (pcell_inner, Tracked(pointsto_inner)) = PCell::new(PageInner {
            flags0: 0,
            capacity: 0,
            reserved: 0,
            flags1: 0,
            flags2: 0,
            free: LL::empty(),
            used: 0,
            xblock_size: 0,
            local_free: LL::empty(),
        });
        let (pcell_prev, Tracked(pointsto_prev)) = PCell::new(core::ptr::null_mut());
        let (pcell_next, Tracked(pointsto_next)) = PCell::new(core::ptr::null_mut());
        let page = Page {
            count: pcell_count,
            offset: 0,
            inner: pcell_inner,
            xthread_free: ThreadLLWithDelayBits::empty(Tracked(local.instance.clone())),
            xheap: AtomicHeapPtr::empty(),
            prev: pcell_prev,
            next: pcell_next,
            padding: 0,
        };
        let tracked pla = PageLocalAccess {
            count: pointsto_count,
            inner: pointsto_inner,
            prev: pointsto_prev,
            next: pointsto_next,
        };
        ptr_mut_write(cur_page_ptr, Tracked(&mut page_header_points_to), page);
        let Tracked(exposed) = expose_provenance(cur_page_ptr);
        let tracked psa = PageSharedAccess { points_to: page_header_points_to, exposed };
        proof {
            psa_map.tracked_insert(page_id, psa);
            pla_map.tracked_insert(page_id, pla);
        }

        //assert(cur_page_ptr.id() + SIZEOF_PAGE_HEADER <= usize::MAX);

        i = i + 1;
        proof {
            assert(SIZEOF_SEGMENT_HEADER as int + SLICES_PER_SEGMENT as int * SIZEOF_PAGE_HEADER as int + SIZEOF_PAGE_HEADER as int <= SEGMENT_SIZE as int) by(compute_only);
            assert(cur_page_ptr.addr() + SIZEOF_PAGE_HEADER <= usize::MAX) by(nonlinear_arith)
                requires
                    cur_page_ptr as int == segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + (i - 1) * SIZEOF_PAGE_HEADER,
                    segment_start(segment_id) + SEGMENT_SIZE < usize::MAX,
                    i <= SLICES_PER_SEGMENT + 1,
                    SIZEOF_SEGMENT_HEADER as int + SLICES_PER_SEGMENT as int * SIZEOF_PAGE_HEADER as int + SIZEOF_PAGE_HEADER as int <= SEGMENT_SIZE as int;
        }
        cur_page_ptr = cur_page_ptr.with_addr(cur_page_ptr.addr() + SIZEOF_PAGE_HEADER);

        /*assert(psa_map.dom().contains(page_id));
        assert( pla_map.dom().contains(page_id));
        assert( pla_map[page_id].inner@.value.is_some());
        assert( pla_map[page_id].count@.value.is_some());
        assert( pla_map[page_id].prev@.value.is_some());
        assert( pla_map[page_id].prev@.value.is_some());
        assert( pla_map[page_id].inner@.value.unwrap().zeroed());
        assert( pla_map[page_id].count@.value.unwrap() == 0);
        assert( pla_map[page_id].prev@.value.unwrap().id() == 0);
        assert( pla_map[page_id].next@.value.unwrap().id() == 0);

        assert( is_page_ptr(psa_map[page_id].points_to@.pptr, page_id));
        assert( psa_map[page_id].points_to.is_init());
        assert( psa_map[page_id].points_to.value().count.id() == pla_map[page_id].count.id());
        assert( psa_map[page_id].points_to.value().inner.id() == pla_map[page_id].inner.id());
        assert( psa_map[page_id].points_to.value().prev.id() == pla_map[page_id].prev.id());
        assert( psa_map[page_id].points_to.value().next.id() == pla_map[page_id].next.id());
        assert( psa_map[page_id].points_to.value().offset == 0);
        assert( psa_map[page_id].points_to.value().xthread_free.is_empty());
        assert( psa_map[page_id].points_to.value().xheap.is_empty());*/

    }


    proof {
        assert(segment_ptr.segment_ptr.addr() != 0);
        assert(segment_ptr.wf());
        assert(segment_ptr.segment_ptr as int == segment_start(segment_id));
        assert(segment_ptr.segment_ptr.addr() as int == segment_ptr.segment_ptr as int);
        assert(segment_start(segment_id) != 0);
        let ghost creating_org = PageOrg::take_step::create_segment(local.page_organization, segment_id);
        let tracked segment_shared_access = SegmentSharedAccess { points_to: seg_header_points_to };
        let tracked thread_state_tok = local.instance.segment_enable(
            local.thread_id,
            segment_id,
            segment_shared_access,
            thread_state_tok,
            segment_shared_access);
        local.thread_token = thread_state_tok;
        local.page_organization = creating_org;
        let tracked segment_access = SegmentLocalAccess {
            mem: mem_chunk,
            main: pointsto_main,
            main2: pointsto_main2,
        };
        local.segments.tracked_insert(segment_id, segment_access);
        local.pages.tracked_union_prefer_right(pla_map);
        local.unused_pages.tracked_union_prefer_right(psa_map);
        local.psa = local.psa.union_prefer_right(psa_map);

        assert(local.page_organization == creating_org);
        assert(local.page_organization.invariant());
        assert(segment_ptr.is_in(*local));
        assert(tld.is_in(*local));
        assert(segment_ptr.wf());

        let ghost new_page_dom = page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1);
        assert(psa_map.dom() =~= new_page_dom) by {
            assert forall |pid: PageId| #[trigger] psa_map.dom().contains(pid) implies new_page_dom.contains(pid) by {
                assert(pid.segment_id == segment_id && 0 <= pid.idx < SLICES_PER_SEGMENT + 1);
            };
            assert forall |pid: PageId| #[trigger] new_page_dom.contains(pid) implies psa_map.dom().contains(pid) by {
                assert(pid.segment_id == segment_id);
                assert(0 <= pid.idx < SLICES_PER_SEGMENT as nat + 1);
                assert(pid.idx < SLICES_PER_SEGMENT + 1);
            };
        }
        assert(pla_map.dom() =~= new_page_dom) by {
            assert forall |pid: PageId| #[trigger] pla_map.dom().contains(pid) implies new_page_dom.contains(pid) by {
                assert(pid.segment_id == segment_id && 0 <= pid.idx < SLICES_PER_SEGMENT + 1);
            };
            assert forall |pid: PageId| #[trigger] new_page_dom.contains(pid) implies pla_map.dom().contains(pid) by {
                assert(pid.segment_id == segment_id);
                assert(0 <= pid.idx < SLICES_PER_SEGMENT as nat + 1);
                assert(pid.idx < SLICES_PER_SEGMENT + 1);
            };
        }
        assert(local_snap1.page_organization_valid());
        assert forall |pid: PageId| #[trigger] local_snap1.pages.dom().contains(pid) implies pid.segment_id != segment_id by {
            assert(local_snap1.page_organization.pages.dom().contains(pid));
            assert(local_snap1.page_organization.segments.dom().contains(pid.segment_id));
            assert(!local_snap1.page_organization.segments.dom().contains(segment_id));
        }
        assert forall |pid: PageId| #[trigger] local_snap1.thread_token.value().pages.dom().contains(pid) implies pid.segment_id != segment_id by {
            assert(local_snap1.thread_token.value().pages.dom().subset_of(local_snap1.pages.dom()));
            assert(local_snap1.pages.dom().contains(pid));
        }
        assert forall |pid: PageId| #[trigger] local_snap1.unused_pages.dom().contains(pid) implies pid.segment_id != segment_id by {
            assert(local_snap1.unused_pages.dom().contains(pid) ==> local_snap1.page_organization.pages.dom().contains(pid));
            assert(local_snap1.page_organization.segments.dom().contains(pid.segment_id));
            assert(!local_snap1.page_organization.segments.dom().contains(segment_id));
        }
        assert(local.thread_token.value().pages == local_snap1.thread_token.value().pages);
        assert(local.pages.dom() =~= local_snap1.pages.dom().union(new_page_dom));
        assert(local.unused_pages.dom() =~= local_snap1.unused_pages.dom().union(new_page_dom));
        assert(local.psa.dom() =~= local_snap1.psa.dom().union(new_page_dom));
        assert(local.thread_token.value().segments.dom() == local.segments.dom());
        assert(local.thread_token.value().heap_id == local.heap_id);
        assert(local.heap.wf(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id(), local.page_empty_global@.s.points_to.ptr()));
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid)) by {
            if pid.segment_id == segment_id {
                assert(new_page_dom.contains(pid));
                assert(local.unused_pages.dom().contains(pid));
                assert(!local.page_organization.pages[pid].is_used);
            } else {
                assert(local_snap1.page_organization.pages.dom().contains(pid));
            }
        }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.page_organization.pages.dom().contains(pid) by {
            if new_page_dom.contains(pid) {
            } else {
                assert(local_snap1.unused_pages.dom().contains(pid));
            }
        }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid] by {
            if new_page_dom.contains(pid) {
                assert(local.unused_pages[pid] == psa_map[pid]);
                assert(local.psa[pid] == psa_map[pid]);
            } else {
                assert(local_snap1.unused_pages.dom().contains(pid));
                assert(local_snap1.unused_pages[pid] == local_snap1.psa[pid]);
            }
        }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid] by {
            assert(local_snap1.thread_token.value().pages.dom().contains(pid));
            assert(!new_page_dom.contains(pid));
        }
        assert(local.page_organization_valid());
        local.segment_creating_pages_totals_empty(segment_id);
        assert(local.segment_pages_used_total(segment_id) =~= Set::empty());
        assert(local.segment_pages_range_total(segment_id) =~= Set::empty());
        lemma_commit_mask_bytes_same_segment_start(&commit_mask, pre_segment_id, segment_id);
        lemma_commit_mask_bytes_same_segment_start(&decommit_mask, pre_segment_id, segment_id);
        assert(local.commit_mask(segment_id) == commit_mask);
        assert(local.commit_mask(segment_id).bytes(segment_id) =~= commit_mask.bytes(segment_id));
        assert(local.decommit_mask(segment_id).bytes(segment_id) =~= decommit_mask.bytes(segment_id)) by {
            if allow_decommit {
                assert(local.decommit_mask(segment_id) == decommit_mask);
            } else {
                lemma_empty_commit_mask_bytes(&decommit_mask, segment_id);
                assert(local.decommit_mask(segment_id)@ =~= Set::empty());
                reveal(CommitMask::bytes);
                assert(local.decommit_mask(segment_id).bytes(segment_id) =~= Set::<int>::empty());
            }
        }
        assert(mem_chunk_good1(
            allocated_mem_chunk,
            segment_id,
            commit_mask.bytes(segment_id),
            decommit_mask.bytes(segment_id),
            Set::empty(),
            Set::empty())) by {
            lemma_mem_chunk_good1_same_segment(
                allocated_mem_chunk,
                pre_segment_id,
                segment_id,
                commit_mask.bytes(pre_segment_id),
                commit_mask.bytes(segment_id),
                decommit_mask.bytes(pre_segment_id),
                decommit_mask.bytes(segment_id));
        }
        assert(mem_chunk.os == allocated_mem_chunk.os);
        assert(mem_chunk.points_to.provenance() == allocated_mem_chunk.points_to.provenance());
        assert(segment_info_range(segment_id) =~= set_int_range(
            segment_start(segment_id),
            segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + (SLICES_PER_SEGMENT + 1) * SIZEOF_PAGE_HEADER)) by {
            reveal(segment_info_range);
        }
        assert(mem_chunk.points_to.dom() =~= allocated_mem_chunk.points_to.dom() - segment_info_range(segment_id)) by {
            assert(old_mem_chunk.points_to.dom() =~= allocated_mem_chunk.points_to.dom() - set_int_range(
                segment_start(segment_id), segment_start(segment_id) + SIZEOF_SEGMENT_HEADER));
            assert(mem_chunk.points_to.dom() =~= old_mem_chunk.points_to.dom() - set_int_range(
                segment_start(segment_id),
                segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + (SLICES_PER_SEGMENT + 1) * SIZEOF_PAGE_HEADER));
        }
        lemma_mem_chunk_good1_after_metadata_taken(
            allocated_mem_chunk,
            mem_chunk,
            segment_id,
            local.commit_mask(segment_id).bytes(segment_id),
            local.decommit_mask(segment_id).bytes(segment_id));
        assert(local.mem_chunk_good(segment_id));
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by {
            if sid == segment_id {
            } else {
                assert(local_snap1.segments.dom().contains(sid));
                assert(local_snap1.mem_chunk_good(sid));
                assert(local.segments[sid] == local_snap1.segments[sid]);
                assert(local.commit_mask(sid) == local_snap1.commit_mask(sid));
                assert(local.decommit_mask(sid) == local_snap1.decommit_mask(sid));
                assert forall |pid: PageId| #[trigger] local_snap1.page_organization.pages.dom().contains(pid) implies
                    local.page_organization.pages.dom().contains(pid) by { }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    pid.segment_id == segment_id || local_snap1.page_organization.pages.dom().contains(pid) by {
                    if pid.segment_id != segment_id {
                        assert(local_snap1.page_organization.segments.dom().contains(pid.segment_id));
                        assert(local_snap1.page_organization.pages.dom().contains(pid));
                    }
                }
                assert forall |pid: PageId| #[trigger] local_snap1.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) == local_snap1.is_used_primary(pid) by {
                    assert(pid.segment_id != segment_id);
                    assert(local.page_organization.pages[pid] == local_snap1.page_organization.pages[pid]);
                }
                assert forall |pid: PageId| #[trigger] local_snap1.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) ==> local.page_count(pid) == local_snap1.page_count(pid) by {
                    assert(pid.segment_id != segment_id);
                    assert(local.pages[pid] == local_snap1.pages[pid]);
                }
                assert forall |pid: PageId| #[trigger] local_snap1.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) ==> local.page_capacity(pid) == local_snap1.page_capacity(pid) by {
                    assert(pid.segment_id != segment_id);
                    assert(local.pages[pid] == local_snap1.pages[pid]);
                }
                assert forall |pid: PageId| #[trigger] local_snap1.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) ==> local.block_size(pid) == local_snap1.block_size(pid) by {
                    assert(pid.segment_id != segment_id);
                    assert(local.pages[pid] == local_snap1.pages[pid]);
                }
                local.mem_chunk_good_preserved_when_only_other_segment_pages_change(local_snap1, sid, segment_id);
            }
        }

        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid)) by {
            if new_page_dom.contains(pid) {
                assert(local.unused_pages.dom().contains(pid));
                assert(!local.thread_token.value().pages.dom().contains(pid));
            } else {
                assert(local_snap1.pages.dom().contains(pid));
            }
        }
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance) by {
            assert(!new_page_dom.contains(pid));
            assert(local_snap1.thread_token.value().pages.dom().contains(pid));
            assert(local_snap1.pages.dom().contains(pid));
            assert(local.pages.dom().contains(pid));
        }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance) by {
            assert(local.pages.dom().contains(pid));
            if new_page_dom.contains(pid) {
                assert(pid.segment_id == segment_id && 0 <= pid.idx < SLICES_PER_SEGMENT + 1);
                assert(pla_map.dom().contains(pid));
                assert(psa_map.dom().contains(pid));
                assert(local.pages[pid] == pla_map[pid]);
                assert(local.unused_pages[pid] == psa_map[pid]);
                assert(psa_map[pid].points_to.is_init());
                assert(is_page_ptr(psa_map[pid].points_to.ptr(), pid));
                assert(psa_map[pid].points_to.value().xthread_free.is_empty());
                assert(psa_map[pid].points_to.value().xthread_free.wf());
                assert(psa_map[pid].points_to.value().xthread_free.instance == local.instance);
                assert(pla_map[pid].inner.value().zeroed());
            } else {
                assert(local_snap1.unused_pages.dom().contains(pid));
                assert(local_snap1.pages.dom().contains(pid));
            }
        }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance) by {
            if sid == segment_id {
                assert(local.segments[sid].main2.value().used == 0);
                assert(local.thread_token.value().segments[sid].is_enabled);
            } else {
                assert(local_snap1.segments.dom().contains(sid));
            }
        }
        assert(local.wf_main_for_page_access());
        assert(local.wf_main());
    }


    let first_slice = PagePtr {
        page_ptr: segment_ptr.segment_ptr.with_addr(
            segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER) as *mut Page,
        page_id: Ghost(PageId { segment_id, idx: 0 }),
    };
    proof {
        assert(first_slice.wf());
        assert(first_slice.is_in(*local));
        assert(first_slice.page_id@.segment_id == segment_id);
        assert(first_slice.page_id@.idx == 0);
        assert(local.page_organization.popped == Popped::SegmentCreating(segment_id));
        assert(1 < SLICES_PER_SEGMENT) by(compute_only);
        reveal(segment_span_allocate_page_org_pre);
        assert(segment_span_allocate_page_org_pre(local.page_organization, segment_id, first_slice.page_id@, 1));
    }
    let ghost local_before_first_alloc = *local;
    let success = segment_span_allocate(segment_ptr, first_slice, 1, tld, Tracked(&mut *local));
    if !success {
        todo(); // TODO actually we don't need this check cause we can't fail
    }
    proof {
        assert(local.segments.dom() == local_before_first_alloc.segments.dom());
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by {
            if sid == segment_id {
                assert(local.mem_chunk_good(segment_id));
            } else {
                assert(local_before_first_alloc.segments.dom().contains(sid));
                assert(local_before_first_alloc.mem_chunk_good(sid));
            }
        }
    }
    //assert(local.wf_main());

    /*let all_page_headers_points_to_raw = mem_chunk.take_points_to_range(
        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER,
        (NUM_SLICES + 1) * SIZEOF_PAGE_HEADER,
    );*/

    let ghost local_snap = *local;
    let ghost next_state = PageOrg::take_step::forget_about_first_page2(local.page_organization);
    segment_get_mut_main2!(segment_ptr, local, main2 => {
        main2.used = main2.used - 1;
    });

    proof {
        local.page_organization = next_state;
        assert(PageOrg::State::forget_about_first_page2_strong(local_snap.page_organization, local.page_organization));
        assert(local.page_organization.pages == local_snap.page_organization.pages);
        assert(local.page_organization.unused_dlist_headers == local_snap.page_organization.unused_dlist_headers);
        assert(local.page_organization.used_dlist_headers == local_snap.page_organization.used_dlist_headers);
        assert(local.page_organization.unused_lists == local_snap.page_organization.unused_lists);
        assert(local.page_organization.used_lists == local_snap.page_organization.used_lists);
        assert(local.pages == local_snap.pages);
        assert(local.psa == local_snap.psa);
        assert(local.unused_pages == local_snap.unused_pages);
        assert(local.thread_token == local_snap.thread_token);
        assert(local.heap == local_snap.heap);
        assert(local.tld == local_snap.tld);
        assert(local.segments.dom() == local_snap.segments.dom());
        assert(page_organization_segments_match(local.page_organization.segments, local.segments)) by {
            assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                local.page_organization.segments[sid].used == local.segments[sid].main2.value().used by {
                if sid == segment_id {
                    assert(local_snap.page_organization.segments[sid].used == local_snap.segments[sid].main2.value().used);
                    assert(local.page_organization.segments[sid].used == local_snap.page_organization.segments[sid].used - 1);
                    assert(local.segments[sid].main2.value().used == local_snap.segments[sid].main2.value().used - 1);
                } else {
                    assert(local.page_organization.segments[sid] == local_snap.page_organization.segments[sid]);
                    assert(local.segments[sid].main2 == local_snap.segments[sid].main2);
                }
            };
        }
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid)) by {
            assert(local_snap.page_organization.pages.dom().contains(pid));
        }
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid) by {
            assert(local_snap.page_organization.pages.dom().contains(pid));
        }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid] by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid] by { }
        assert(local.page_organization_valid());
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid)) by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance) by { }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance) by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance) by {
            if sid == segment_id {
                assert(local.thread_token.value().segments[sid].is_enabled);
            } else {
                assert(local.segments[sid] == local_snap.segments[sid]);
            }
        }
        assert(local.wf_main_for_page_access());
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by {
            assert(local_snap.segments.dom().contains(sid));
            assert(local_snap.mem_chunk_good(sid));
            assert(local.segments[sid].mem == local_snap.segments[sid].mem);
            assert(local.commit_mask(sid) == local_snap.commit_mask(sid));
            assert(local.decommit_mask(sid) == local_snap.decommit_mask(sid));
            assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_snap.is_used_primary(pid) by {
                assert(local.page_organization.pages[pid] == local_snap.page_organization.pages[pid]);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_count(pid) == local_snap.page_count(pid) by {
                assert(local.pages[pid] == local_snap.pages[pid]);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_capacity(pid) == local_snap.page_capacity(pid) by {
                assert(local.pages[pid] == local_snap.pages[pid]);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.block_size(pid) == local_snap.block_size(pid) by {
                assert(local.pages[pid] == local_snap.pages[pid]);
            }
            local.segment_page_totals_preserved(local_snap, sid);
            local.mem_chunk_good_preserved_by_page_totals(local_snap, sid);
        }
    }

    if required == 0 {
        segment_span_free(segment_ptr, 1, SLICES_PER_SEGMENT as usize - 1, false, tld, Tracked(&mut *local));
    } else {
        todo();
    }

    return segment_ptr;
}

#[verifier::spinoff_prover]
fn segment_os_alloc(
    required: usize,
    page_alignment: usize,
    eager_delay: bool,
    req_arena_id: ArenaId,
    psegment_slices: usize,
    pre_size: usize,
    pinfo_slices: usize,
    pcommit_mask: &mut CommitMask,
    pdecommit_mask: &mut CommitMask,
    request_commit: bool,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
// outparams
// segment_ptr: SegmentPtr,
// new_psegment_slices: usize
// new_ppre_size: usize
// new_pinfo_slices: usize,
// is_zero: bool,
// pcommit: bool,
// memid: MemId,
// mem_large: bool,
// is_pinned: bool,
// align_offset: usize,
) -> (res: (SegmentPtr, usize, usize, usize, bool, bool, MemId, bool, bool, usize, Tracked<MemChunk>))
    requires
        page_alignment == 0,
        psegment_slices == SLICES_PER_SEGMENT as usize,
        pinfo_slices == 1,
        old(pdecommit_mask)@ =~= Set::empty(),
        psegment_slices <= SLICES_PER_SEGMENT as usize,
        pinfo_slices <= psegment_slices,
        pinfo_slices <= COMMIT_MASK_BITS as usize,
    ensures
        *final(local) == *old(local),
        res.1 <= SLICES_PER_SEGMENT as usize,
        res.3 <= res.1,
        res.3 <= COMMIT_MASK_BITS as usize,
        res.0.segment_ptr.addr() != 0 ==> res.0.wf(),
        res.0.segment_ptr.addr() != 0 ==> res.10@.wf(),
        res.0.segment_ptr.addr() != 0 ==> res.10@.os_exact_range(segment_start(res.0.segment_id@), SEGMENT_SIZE as int),
        res.0.segment_ptr.addr() != 0 ==> res.10@.points_to.provenance() == res.0.segment_id@.provenance,
        res.0.segment_ptr.addr() != 0 ==> res.10@.pointsto_has_range(segment_start(res.0.segment_id@), COMMIT_SIZE as int),
        res.0.segment_ptr.addr() != 0 ==> Set::range(0, 1) <= final(pcommit_mask)@,
        res.0.segment_ptr.addr() != 0 ==> final(pdecommit_mask)@ =~= Set::empty(),
        res.0.segment_ptr.addr() != 0 ==> mem_chunk_good1(
            res.10@,
            res.0.segment_id@,
            final(pcommit_mask).bytes(res.0.segment_id@),
            final(pdecommit_mask).bytes(res.0.segment_id@),
            Set::empty(),
            Set::empty()),
{


    let mut mem_large = !eager_delay;
    let mut is_pinned = false;
    let mut mem_id: usize = 0;
    let mut align_offset: usize = 0;
    let mut alignment: usize = SEGMENT_ALIGN as usize;
    let mut is_zero = false;
    let mut pcommit = request_commit;
    let mut psegment_slices = psegment_slices;
    let mut pinfo_slices = pinfo_slices;
    let mut pre_size = pre_size;
    let tracked mut mem = MemChunk::empty();

    if page_alignment > 0 {
        /*
        assert(page_alignment >= SEGMENT_ALIGN);
        alignment = page_alignment;
        let info_size = pinfo_sizes * SLICE_SIZE;
        align_offset = align_up(info_size, SEGMENT_ALIGN);
        */
        todo();
    }
    proof {
        lemma_segment_os_alloc_constants();
        assert(psegment_slices as int <= SLICES_PER_SEGMENT as int);
        assert(psegment_slices as int * SLICE_SIZE as int <= SLICES_PER_SEGMENT as int * SLICE_SIZE as int) by(nonlinear_arith)
            requires
                psegment_slices as int <= SLICES_PER_SEGMENT as int,
                0 <= SLICE_SIZE as int;
        assert(psegment_slices as int * SLICE_SIZE as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
            requires
                psegment_slices as int * SLICE_SIZE as int <= SLICES_PER_SEGMENT as int * SLICE_SIZE as int,
                SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int;
        assert(SEGMENT_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
            requires
                SEGMENT_SIZE as usize <= usize::MAX;
        assert(psegment_slices as int * SLICE_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
            requires
                psegment_slices as int * SLICE_SIZE as int <= SEGMENT_SIZE as int,
                SEGMENT_SIZE as int <= usize::MAX as int;
    }

    let segment_size = psegment_slices * SLICE_SIZE as usize;

    let mut segment = SegmentPtr::null();

    if page_alignment == 0 {
        // TODO get from cache if possible
    }

    if segment.is_null() {
        let (_segment, Tracked(_mem), commit, _large, _is_pinned, _is_zero, _mem_id) =
          arena_alloc_aligned(
            segment_size, alignment, align_offset, request_commit, mem_large, req_arena_id);
        segment = SegmentPtr {
            segment_ptr: _segment as *mut SegmentHeader,
            segment_id: Ghost(mk_segment_id(_segment as *mut SegmentHeader)),
        };
        mem_id = _mem_id;
        mem_large = _large;
        is_zero = _is_zero;
        is_pinned = _is_pinned;
        pcommit = commit;

        if segment.is_null() {
            return (segment,
                psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(MemChunk::empty()))
        }
        proof {
            mem = _mem;
        }
        if pcommit {
            pcommit_mask.create_full();
        } else {
            pcommit_mask.create_empty();
        }
    }

    let commit_needed = pinfo_slices;
    let mut commit_needed_mask = CommitMask::empty();
    commit_needed_mask.create(0, commit_needed);
    if !pcommit_mask.all_set(&commit_needed_mask) {
        //assert(commit_needed as int * COMMIT_SIZE as int <= segment_size);

        let (success, is_zero) = crate::os_commit::os_commit(
            segment.segment_ptr as *mut u8,
            commit_needed * COMMIT_SIZE as usize,
            Tracked(&mut mem));
        if !success {
            return (SegmentPtr::null(), 0, 0, 0, false, false, 0, false, false, 0, Tracked(MemChunk::empty()));
        }
        pcommit_mask.set(&commit_needed_mask);
    }

    // note: segment metadata is set by the caller

    // TODO what does _mi_segment_map_allocated_at do?


    proof {
        if segment.segment_ptr.addr() != 0 {
            assert(psegment_slices == SLICES_PER_SEGMENT as usize);
            assert(pinfo_slices == 1);
            assert(segment_size == SEGMENT_SIZE as usize) by(nonlinear_arith)
                requires
                    segment_size == psegment_slices * SLICE_SIZE as usize,
                    psegment_slices == SLICES_PER_SEGMENT as usize,
                    SLICES_PER_SEGMENT as usize * SLICE_SIZE as usize == SEGMENT_SIZE as usize;
            assert(alignment == SEGMENT_ALIGN as usize);
            assert(SEGMENT_ALIGN as usize == SEGMENT_SIZE as usize) by(compute_only);
            assert(crate::os_mem::page_size() == 4096) by(compute_only);
            assert(crate::os_alloc::os_mem_alloc_alignment_ok(alignment)) by {
                reveal(crate::os_alloc::os_mem_alloc_alignment_ok);
                assert(alignment as int >= crate::os_mem::page_size()) by(nonlinear_arith)
                    requires
                        alignment == SEGMENT_SIZE as usize,
                        SEGMENT_SIZE as int == 33554432,
                        crate::os_mem::page_size() == 4096;
                assert((alignment & sub(alignment, 1usize)) == 0usize) by(bit_vector)
                    requires alignment == SEGMENT_SIZE as usize;
            }
            assert(segment.segment_ptr.addr() % alignment == 0);
            assert((segment.segment_ptr.addr() as int) % (SEGMENT_SIZE as int) == 0) by(nonlinear_arith)
                requires
                    segment.segment_ptr.addr() % alignment == 0,
                    alignment == SEGMENT_SIZE as usize,
                    (SEGMENT_SIZE as usize) as int == SEGMENT_SIZE as int;
            assert(segment.segment_ptr.addr() + segment_size < usize::MAX);
            assert((segment.segment_ptr.addr() as int) + (SEGMENT_SIZE as int) < (usize::MAX as int)) by(nonlinear_arith)
                requires
                    segment.segment_ptr.addr() + segment_size < usize::MAX,
                    segment_size == SEGMENT_SIZE as usize,
                    (SEGMENT_SIZE as usize) as int == SEGMENT_SIZE as int;
            assert(segment.wf());
            assert(mem.os_exact_range(segment.segment_ptr as int, SEGMENT_SIZE as int));
            assert(segment.segment_ptr as int == segment_start(segment.segment_id@));
            assert(mem.os_exact_range(segment_start(segment.segment_id@), SEGMENT_SIZE as int));
            assert(mem.points_to.provenance() == segment.segment_id@.provenance);
            if pcommit {
                assert(mem.has_pointsto_for_all_read_write());
                assert(mem.pointsto_has_range(segment_start(segment.segment_id@), COMMIT_SIZE as int));
                assert(pcommit_mask@ =~= Set::range(0, COMMIT_MASK_BITS as int));
            } else {
                assert(commit_needed == 1);
                assert(commit_needed_mask@ =~= Set::range(0, 1));
                assert(pcommit_mask@.contains(0));
                assert(mem.pointsto_has_range(segment.segment_ptr as int, commit_needed * COMMIT_SIZE as usize));
                assert((commit_needed * COMMIT_SIZE as usize) as int == COMMIT_SIZE as int);
                assert(segment.segment_ptr as int == segment_start(segment.segment_id@));
                assert(mem.pointsto_has_range(segment_start(segment.segment_id@), COMMIT_SIZE as int));
                assert(pcommit_mask@ =~= Set::range(0, 1));
            }
            assert(Set::range(0, 1) <= pcommit_mask@);
            assert(pdecommit_mask@ =~= Set::empty());
            lemma_segment_info_range_subset_commit_mask_bytes(pcommit_mask, segment.segment_id@);
            lemma_empty_commit_mask_bytes(pdecommit_mask, segment.segment_id@);
            if pcommit {
                lemma_segment_commit_mask_bytes_subset_of_rw_range(
                    pcommit_mask, segment.segment_id@, mem, 0, COMMIT_MASK_BITS as int);
            } else {
                lemma_segment_commit_mask_bytes_subset_of_rw_range(
                    pcommit_mask, segment.segment_id@, mem, 0, 1);
            }
            assert(pcommit_mask.bytes(segment.segment_id@).subset_of(mem.os_rw_bytes()));
            assert(pdecommit_mask.bytes(segment.segment_id@) =~= Set::empty());
            assert(pdecommit_mask.bytes(segment.segment_id@) <= pcommit_mask.bytes(segment.segment_id@));
            assert(segment_info_range(segment.segment_id@) <=
                pcommit_mask.bytes(segment.segment_id@) - pdecommit_mask.bytes(segment.segment_id@));
            assert(Set::<int>::empty() <= pcommit_mask.bytes(segment.segment_id@) - pdecommit_mask.bytes(segment.segment_id@));
            assert(mem.os_rw_bytes() <= mem.points_to.dom() + segment_info_range(segment.segment_id@) + Set::<int>::empty()) by {
                assert forall |addr: int| #[trigger] mem.os_rw_bytes().contains(addr) implies
                    (mem.points_to.dom() + segment_info_range(segment.segment_id@) + Set::<int>::empty()).contains(addr) by {
                    if mem.points_to.dom().contains(addr) {
                    } else {
                        if pcommit {
                            assert(mem.has_pointsto_for_all_read_write());
                            assert(false);
                        } else {
                            assert(mem.pointsto_has_range(segment_start(segment.segment_id@), COMMIT_SIZE as int));
                            assert(mem.os_rw_bytes() <= set_int_range(segment_start(segment.segment_id@), segment_start(segment.segment_id@) + COMMIT_SIZE as int));
                            assert(set_int_range(segment_start(segment.segment_id@), segment_start(segment.segment_id@) + COMMIT_SIZE as int).contains(addr));
                            if segment_info_range(segment.segment_id@).contains(addr) {
                            } else {
                                assert(mem.points_to.dom().contains(addr));
                            }
                        }
                    }
                };
            }
            assert(mem_chunk_good1(
                mem,
                segment.segment_id@,
                pcommit_mask.bytes(segment.segment_id@),
                pdecommit_mask.bytes(segment.segment_id@),
                Set::empty(),
                Set::empty()));
        }
    }
    return (segment, psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(mem));
}

#[verus_verify]
fn segment_free(segment: SegmentPtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    ensures
        *final(local) == *old(local),
{
    todo();
    /*
    proof {
        let next_state = PageOrg::take_step::segment_freeing_start(local.page_organization, segment.segment_id@);
        local.page_organization = next_state;
        preserves_mem_chunk_good(*old(local), *local);
        assert(local.wf_main_for_page_access());
    }

    let mut slice = segment.get_page_header_ptr(0);
    let end = segment.get_page_after_end();
    let page_count = 0;
    while slice.page_ptr.to_usize() < end.to_usize()
        invariant local.wf_main(),
            segment.wf(),
            segment.is_in(*local),
            tld.is_in(*local),
            tld.wf(),
            slice.page_ptr.id() < end.id() ==> slice.wf(),
            slice.page_ptr.id() >= end.id() ==> slice.page_id@.idx == SLICES_PER_SEGMENT,
            slice.page_id@.segment_id == segment.segment_id@,
            local.page_organization.popped == Popped::SegmentFreeing(slice.page_id@.segment_id, slice.page_id@.idx as int),
            end.id() == page_header_start(
                PageId { segment_id: segment.segment_id@, idx: SLICES_PER_SEGMENT as nat }),
    {
        let ghost list_idx = local.page_organization.segment_freeing_is_in();

        if slice.get_inner_ref(Tracked(&*local)).xblock_size == 0 && !segment.is_kind_huge(Tracked(&*local)) {
            let count = slice.get_count(Tracked(&*local));
            let sbin_idx = slice_bin(count as usize);
            span_queue_delete(tld, sbin_idx, slice, Tracked(&mut *local), Ghost(list_idx), Ghost(count as int));
        } else {
            todo();
        }

        let count = slice.get_count(Tracked(&*local));
        proof { local.page_organization.get_count_bound(slice.page_id@); }
        slice = slice.add_offset(count as usize);
    }

    todo();

    // mi_segment_os_free(segment, tld);
    */
}

#[verifier::external_body]
fn segment_os_free(segment: SegmentPtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
{
    // TODO segment_map_freed_at(segment);

    //let size = segment_size(segment, Tracked(&*local)) as isize;
    //segments_track_size(-size, tld, Tracked(&mut *local));
    todo();

    /*
    let skip_cache_push = size != SEGMENT_SIZE
        || segment.get_mem_align_offset(Tracked(&*local)) != 0
        || segment.is_kind_huge(Tracked(&*local));

    let mut try_arena_free = skip_cache_push;
    if !skip_cache_push {
        // TODO implement segment cache
        // !_mi_segment_cache_push(segment, size, segment->memid, &segment->commit_mask, &segment->decommit_mask, segment->mem_is_large, segment->mem_is_pinned, tld->os))
    }
    */


}

// segment_slices = # of slices in the segment
// pre_size = size of the pages that contain the segment metadata
// info_slices = # of slices needed to contain the pages of the segment metadata
#[verus_verify]
fn segment_calculate_slices(required: usize)
  -> (res: (usize, usize, usize))
    requires
        segment_calculate_slices_required_bound(required as int),
    ensures
        required == 0 ==> res.0 == SLICES_PER_SEGMENT as usize,
        required == 0 ==> res.0 <= COMMIT_MASK_BITS as usize,
        required == 0 ==> res.2 == 1,
        required == 0 ==> res.2 <= COMMIT_MASK_BITS as usize,
        required == 0 ==> res.2 <= res.0,
{

    let page_size = crate::os_mem::get_page_size();
    proof {
        assert(crate::os_mem::page_size() == 4096) by(compute_only);
        assert(page_size as int == crate::os_mem::page_size());
        assert(page_size > 0);
        assert(SIZEOF_SEGMENT_HEADER as int + page_size as int - 1 <= usize::MAX as int) by(nonlinear_arith)
            requires
                page_size as int == 4096;
    }
    let i_size = align_up(SIZEOF_SEGMENT_HEADER, page_size);
    let guardsize = 0;

    let pre_size = i_size;
    proof {
        assert(SLICE_SIZE as int > 0) by(compute_only);
        assert(i_size as int <= SIZEOF_SEGMENT_HEADER as int + page_size as int - 1);
        assert(i_size as int <= SLICE_SIZE as int) by(nonlinear_arith)
            requires
                i_size as int <= SIZEOF_SEGMENT_HEADER as int + page_size as int - 1,
                page_size as int == 4096;
        assert(i_size as int + SLICE_SIZE as int - 1 <= usize::MAX as int) by(nonlinear_arith)
            requires
                i_size as int <= SLICE_SIZE as int,
                segment_calculate_slices_required_bound(required as int);
    }
    let j_size = align_up(i_size + guardsize, SLICE_SIZE as usize);
    proof {
        assert(SLICE_SIZE as int > 0) by(compute_only);
        assert((SLICE_SIZE as int) % (SLICE_SIZE as int) == 0) by(nonlinear_arith);
        lemma_round_multiple_le_cap(j_size as int, i_size as int, SLICE_SIZE as int, SLICE_SIZE as int);
        assert(j_size as int <= SLICE_SIZE as int);
        assert(j_size as int > 0) by(nonlinear_arith)
            requires
                SIZEOF_SEGMENT_HEADER as int > 0,
                SIZEOF_SEGMENT_HEADER as int <= i_size as int,
                i_size <= j_size;
        assert(j_size as int == SLICE_SIZE as int) by(nonlinear_arith)
            requires
                j_size as int > 0,
                j_size as int <= SLICE_SIZE as int,
                j_size as int % SLICE_SIZE as int == 0,
                SLICE_SIZE as int > 0;
        assert(required as int + j_size as int + SLICE_SIZE as int - 1 <= usize::MAX as int) by(nonlinear_arith)
            requires
                j_size as int <= SLICE_SIZE as int,
                segment_calculate_slices_required_bound(required as int);
    }
    let info_slices = j_size / SLICE_SIZE as usize;
    let segment_size = if required == 0 {
        SEGMENT_SIZE as usize
    } else {
        align_up(required + j_size + guardsize, SLICE_SIZE as usize)
    };
    let num_slices = segment_size / SLICE_SIZE as usize;

    proof {
        if required == 0 {
            lemma_segment_os_alloc_constants();
            assert(info_slices == 1);
            assert(num_slices == SLICES_PER_SEGMENT as usize);
            assert(COMMIT_MASK_BITS as usize == 512);
            assert(info_slices <= COMMIT_MASK_BITS as usize);
            assert(info_slices <= num_slices);
        }
    }

    (num_slices, pre_size, info_slices)
}

#[verifier::spinoff_prover]
fn segment_span_free(
    segment_ptr: SegmentPtr,
    slice_index: usize,
    slice_count: usize,
    allow_decommit: bool,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main_for_page_access(),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        segment_ptr.wf(),
        segment_ptr.is_in(*old(local)),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        old(local).page_organization.popped.is_VeryUnready(),
        old(local).page_organization.popped.get_VeryUnready_0() == segment_ptr.segment_id@,
        old(local).page_organization.popped.get_VeryUnready_1() == slice_index,
        old(local).page_organization.popped.get_VeryUnready_2() == slice_count,
    ensures
        final(local).wf_main(),
        final(local).wf_main_for_page_access(),
        common_preserves(*old(local), *final(local)),
        final(local).pages.dom() == old(local).pages.dom(),
        segment_ptr.is_in(*final(local)),
        tld_ptr.is_in(*final(local)),
        old(local).page_organization.popped.is_VeryUnready()
        && old(local).page_organization.popped.get_VeryUnready_0() == segment_ptr.segment_id@
        ==> final(local).page_organization.popped == if old(local).page_organization.popped.get_VeryUnready_3() {
            Popped::ExtraCount(segment_ptr.segment_id@)
        } else {
            Popped::No
        },
{
    proof {
        local.page_organization.get_count_bound_very_unready();
        assert((SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int) by(compute_only);
        assert(slice_count as int <= SLICES_PER_SEGMENT as int);
        assert(slice_count <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
            requires
                slice_count as int <= SLICES_PER_SEGMENT as int,
                (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int;
        assert(slice_index as int + slice_count as int <= SLICES_PER_SEGMENT as int);
        assert(slice_index as int <= SLICES_PER_SEGMENT as int) by(nonlinear_arith)
            requires
                slice_index as int + slice_count as int <= SLICES_PER_SEGMENT as int;
        assert(slice_index <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
            requires
                slice_index as int <= SLICES_PER_SEGMENT as int,
                (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int;
    }
    let bin_idx = slice_bin(slice_count);
    let ghost local_start = *local;
    let ghost next_state = PageOrg::take_step::free_to_unused_queue(local.page_organization, bin_idx as int);

    let slice = segment_ptr.get_page_header_ptr(slice_index);

    unused_page_get_mut_count!(slice, local, c => {
        c = slice_count as u32;
    });
    unused_page_get_mut!(slice, local, page => {
        page.offset = 0;
    });
    proof {
        local.psa = local.psa.insert(slice.page_id@, local.unused_pages[slice.page_id@]);
    }

    if slice_count > 1 {
        proof {
            assert((slice_index + slice_count - 1) as int == slice_index as int + slice_count as int - 1) by(nonlinear_arith)
                requires
                    slice_count > 1,
                    slice_index as int + slice_count as int <= SLICES_PER_SEGMENT as int,
                    SLICES_PER_SEGMENT as int <= usize::MAX as int;
            assert(slice_index + slice_count - 1 <= SLICES_PER_SEGMENT as usize) by(nonlinear_arith)
                requires
                    (slice_index + slice_count - 1) as int == slice_index as int + slice_count as int - 1,
                    slice_index as int + slice_count as int <= SLICES_PER_SEGMENT as int,
                    (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int;
            assert(slice_count as int <= SLICES_PER_SEGMENT as int);
            assert(SLICES_PER_SEGMENT as int <= u32::MAX as int) by(compute_only);
            assert((slice_count as u32) as int == slice_count as int) by(bit_vector)
                requires slice_count as int <= SLICES_PER_SEGMENT as int;
            assert((slice_count as u32 - 1) as int == slice_count as int - 1) by(bit_vector)
                requires
                    slice_count > 1,
                    (slice_count as u32) as int == slice_count as int;
            assert(SLICES_PER_SEGMENT as int == 512) by(compute_only);
            assert((slice_count as u32 - 1) as int <= 511) by(nonlinear_arith)
                requires
                    (slice_count as u32 - 1) as int == slice_count as int - 1,
                    slice_count as int <= SLICES_PER_SEGMENT as int,
                    SLICES_PER_SEGMENT as int == 512;
            assert(SIZEOF_PAGE_HEADER as u32 == 80) by(compute_only);
            assert((slice_count as u32 - 1) * (SIZEOF_PAGE_HEADER as u32) <= u32::MAX) by(bit_vector)
                requires
                    (slice_count as u32 - 1) as int <= 511,
                    SIZEOF_PAGE_HEADER as u32 == 80;
        }
        let last = segment_ptr.get_page_header_ptr(slice_index + slice_count - 1);

        unused_page_get_mut!(last, local, page => {

            

            

            
            page.offset = (slice_count as u32 - 1) * SIZEOF_PAGE_HEADER as u32;
        });
        proof {
            local.psa = local.psa.insert(last.page_id@, local.unused_pages[last.page_id@]);
        }
    }

    if allow_decommit {
        proof {
            assert(SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int) by(compute_only);
            assert(slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    slice_count as int <= SLICES_PER_SEGMENT as int,
                    SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int,
                    0 <= SLICE_SIZE as int;
            assert(SEGMENT_SIZE as int <= usize::MAX as int) by(compute_only);
            assert(slice_count as int * SLICE_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
                requires
                    slice_count as int * SLICE_SIZE as int <= SEGMENT_SIZE as int,
                    SEGMENT_SIZE as int <= usize::MAX as int;
            lemma_segment_ptr_commit_aligned(segment_ptr);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
                segment_ptr.segment_ptr as int, COMMIT_SIZE as int);
            assert(segment_ptr.segment_ptr as int == COMMIT_SIZE as int * ((segment_ptr.segment_ptr as int) / COMMIT_SIZE as int));
            assert(slice.page_id@.idx == slice_index as int);
            assert(slice.page_id@.segment_id == segment_ptr.segment_id@);
            assert(page_start(slice.page_id@) == segment_ptr.segment_ptr as int + slice_index as int * SLICE_SIZE as int);
            assert(COMMIT_SIZE as int == SLICE_SIZE as int) by(compute_only);
            assert(page_start(slice.page_id@) == COMMIT_SIZE as int * (((segment_ptr.segment_ptr as int) / COMMIT_SIZE as int) + slice_index as int)) by(nonlinear_arith)
                requires
                    page_start(slice.page_id@) == segment_ptr.segment_ptr as int + slice_index as int * SLICE_SIZE as int,
                    segment_ptr.segment_ptr as int == COMMIT_SIZE as int * ((segment_ptr.segment_ptr as int) / COMMIT_SIZE as int),
                    COMMIT_SIZE as int == SLICE_SIZE as int;
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
                ((segment_ptr.segment_ptr as int) / COMMIT_SIZE as int) + slice_index as int,
                COMMIT_SIZE as int);
            assert(page_start(slice.page_id@) % COMMIT_SIZE as int == 0);
            assert((slice_count * SLICE_SIZE as usize) as int == slice_count as int * SLICE_SIZE as int) by(nonlinear_arith)
                requires
                    slice_count as int * SLICE_SIZE as int <= usize::MAX as int;
            assert((slice_count * SLICE_SIZE as usize) as int == COMMIT_SIZE as int * slice_count as int) by(nonlinear_arith)
                requires
                    (slice_count * SLICE_SIZE as usize) as int == slice_count as int * SLICE_SIZE as int,
                    COMMIT_SIZE as int == SLICE_SIZE as int;
            vstd::arithmetic::div_mod::lemma_mod_multiples_basic(slice_count as int, COMMIT_SIZE as int);
            assert((slice_count * SLICE_SIZE as usize) as int % COMMIT_SIZE as int == 0);
            assert(slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT as int);
            assert(page_start(slice.page_id@) + slice_count as int * SLICE_SIZE as int <= segment_ptr.segment_ptr as int + SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    page_start(slice.page_id@) == segment_ptr.segment_ptr as int + slice_index as int * SLICE_SIZE as int,
                    slice.page_id@.idx == slice_index as int,
                    slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT as int,
                    SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int;
            assert(set_int_range(page_start(slice.page_id@), page_start(slice.page_id@) + slice_count as int * SLICE_SIZE as int)
                .disjoint(segment_info_range(segment_ptr.segment_id@))) by {
                assert forall |addr: int|
                    #[trigger] set_int_range(page_start(slice.page_id@), page_start(slice.page_id@) + slice_count as int * SLICE_SIZE as int).contains(addr)
                implies !segment_info_range(segment_ptr.segment_id@).contains(addr) by {
                    assert(page_start(slice.page_id@) <= addr);
                    assert(slice_index as int > 0);
                    assert(SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1) <= SLICE_SIZE as int) by(compute_only);
                    assert(segment_start(segment_ptr.segment_id@) + SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1) <= page_start(slice.page_id@)) by(nonlinear_arith)
                        requires
                            page_start(slice.page_id@) == segment_start(segment_ptr.segment_id@) + SLICE_SIZE as int * slice_index as int,
                            slice_index as int > 0,
                            SIZEOF_SEGMENT_HEADER as int + SIZEOF_PAGE_HEADER as int * (SLICES_PER_SEGMENT as int + 1) <= SLICE_SIZE as int;
                }
            }
            local.very_unready_range_disjoint_used_total(slice.page_id@, slice_count as int);
            assert(local.wf_basic());
            assert(local.page_organization_valid());
            assert(local.wf_main_for_page_access());
            assert(local.segments == local_start.segments);
            assert(local.page_organization == local_start.page_organization);
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_start.is_used_primary(pid) by {
                assert(local.page_organization == local_start.page_organization);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_count(pid) == local_start.page_count(pid) by {
                if pid == slice.page_id@ {
                    local.page_organization.very_unready_popped_range_facts();
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(!local.is_used_primary(pid));
                } else {
                    assert(local.pages[pid] == local_start.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_capacity(pid) == local_start.page_capacity(pid) by {
                assert(local.pages[pid].inner == local_start.pages[pid].inner);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.block_size(pid) == local_start.block_size(pid) by {
                assert(local.pages[pid].inner == local_start.pages[pid].inner);
            }
            assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                local.mem_chunk_good(sid) by {
                local.used_page_fields_preserved_mem_chunk_good(local_start, sid);
            }
            assert(local.wf_main());
        }
        segment_perhaps_decommit(segment_ptr,
            slice.slice_start(),
            slice_count * SLICE_SIZE as usize,
            Tracked(&mut *local));
    }
    proof {
        if !allow_decommit {
            assert(local.wf_basic());
            assert(local.page_organization_valid());
            assert(local.wf_main_for_page_access());
            assert(local.segments == local_start.segments);
            assert(local.page_organization == local_start.page_organization);
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_start.is_used_primary(pid) by {
                assert(local.page_organization == local_start.page_organization);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_count(pid) == local_start.page_count(pid) by {
                if pid == slice.page_id@ {
                    local.page_organization.very_unready_popped_range_facts();
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(!local.is_used_primary(pid));
                } else {
                    assert(local.pages[pid] == local_start.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_capacity(pid) == local_start.page_capacity(pid) by {
                assert(local.pages[pid].inner == local_start.pages[pid].inner);
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.block_size(pid) == local_start.block_size(pid) by {
                assert(local.pages[pid].inner == local_start.pages[pid].inner);
            }
            assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                local.mem_chunk_good(sid) by {
                local.used_page_fields_preserved_mem_chunk_good(local_start, sid);
            }
            assert(local.wf_main());
        }
        assert(local.wf_main());
    }
    let ghost local_snap = *local;

    let ghost first_in_queue_id = local.page_organization.unused_dlist_headers[bin_idx as int].first;
    let cq = &mut tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[bin_idx];
    let first_in_queue = cq.first;
    cq.first = slice.page_ptr;
    if first_in_queue.addr() == 0 {
        cq.last = slice.page_ptr;
    }

    if first_in_queue.addr() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.unused_dlist_headers[bin_idx as int].first.unwrap()) };
        unused_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = slice.page_ptr;
        });
    }
    unused_page_get_mut_prev!(slice, local, p => {
        p = core::ptr::null_mut();
    });
    unused_page_get_mut_next!(slice, local, n => {
        n = first_in_queue;
    });
    unused_page_get_mut_inner!(slice, local, inner => {
        inner.xblock_size = 0;
    });

    proof {
        local.page_organization = next_state;
        assert(common_preserves(local_start, *local));
        assert(local.pages.dom() == local_start.pages.dom());
        assert(local_snap.page_organization == local_start.page_organization);
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { }
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { }
        assert(local.page_organization_valid());
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
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { }
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { }
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { }
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(local.wf_main_for_page_access());
        assert(local.segments == local_snap.segments);
        assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) == local_snap.is_used_primary(pid) by {
            if pid == slice.page_id@ {
                assert(!local.page_organization.pages[pid].is_used);
                assert(!local_snap.page_organization.pages[pid].is_used);
                assert(!local.is_used_primary(pid));
                assert(!local_snap.is_used_primary(pid));
            } else if first_in_queue_id.is_some() && pid == first_in_queue_id.unwrap() {
                assert(!local.page_organization.pages[pid].is_used);
                assert(!local_snap.page_organization.pages[pid].is_used);
                assert(!local.is_used_primary(pid));
                assert(!local_snap.is_used_primary(pid));
            } else if slice_count > 1 && pid.segment_id == slice.page_id@.segment_id
                && pid.idx == slice.page_id@.idx + slice_count as int - 1 {
                local_snap.page_organization.very_unready_popped_range_facts();
                assert(!local.page_organization.pages[pid].is_used);
                assert(!local_snap.page_organization.pages[pid].is_used);
                assert(!local.is_used_primary(pid));
                assert(!local_snap.is_used_primary(pid));
            } else {
                assert(local.page_organization.pages[pid] == local_snap.page_organization.pages[pid]);
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_count(pid) == local_snap.page_count(pid) by {
            if pid == slice.page_id@ {
                assert(!local.is_used_primary(pid));
            } else if first_in_queue_id.is_some() && pid == first_in_queue_id.unwrap() {
                assert(!local.page_organization.pages[pid].is_used);
                assert(!local.is_used_primary(pid));
            } else {
                assert(local.pages[pid] == local_snap.pages[pid]);
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.page_capacity(pid) == local_snap.page_capacity(pid) by {
            if pid == slice.page_id@ {
                assert(!local.is_used_primary(pid));
            } else {
                assert(local.pages[pid].inner == local_snap.pages[pid].inner);
            }
        }
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            local.is_used_primary(pid) ==> local.block_size(pid) == local_snap.block_size(pid) by {
            if pid == slice.page_id@ {
                assert(!local.is_used_primary(pid));
            } else {
                assert(local.pages[pid].inner == local_snap.pages[pid].inner);
            }
        }
        assert(local_snap.wf_main());
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by {
            assert(local_snap.mem_chunk_good(sid));
            local.used_page_fields_preserved_mem_chunk_good(local_snap, sid);
        }
        assert(local.wf_main());
        assert(segment_ptr.is_in(*local));
        assert(tld_ptr.is_in(*local));
    }

}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
pub fn segment_page_free(page: PagePtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main_for_page_access(),
        page.wf(),
        page.is_in(*old(local)),
        tld.wf(),
        tld.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        page.wf(),
{
    let ghost local_before_clear = *local;
    let segment = SegmentPtr::ptr_segment(page);
    proof {
        assert(segment.wf());
    }
    segment_page_clear(page, tld, Tracked(&mut *local));
    let ghost local_after_clear = *local;
    proof {
        assert(local.wf());
        assert(common_preserves(local_before_clear, *local));
        assert(local.inst() == local_before_clear.inst());
        assert(segment.segment_id@ == page.page_id@.segment_id);
        assert(local.segments.dom().contains(segment.segment_id@));
        assert(segment.is_in(*local));
    }

    let used = segment.get_used(Tracked(&*local));
    if used == 0 {
        segment_free(segment, force, tld, Tracked(&mut *local));
        proof {
            assert(*local == local_after_clear);
        }
    } else if used == segment.get_abandoned(Tracked(&*local)) {
        todo();
    }
    proof {
        assert(local.wf());
        assert(common_preserves(local_before_clear, *local));
        assert(local.inst() == local_before_clear.inst());
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn segment_page_clear(page: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main_for_page_access(),
        page.wf(),
        page.is_in(*old(local)),
        tld.wf(),
        tld.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        page.wf(),
        page.is_in(*final(local)),
        tld.wf(),
        tld.is_in(*final(local)),
        final(local).segments.dom().contains(page.page_id@.segment_id),
{
    let ghost page_id = page.page_id@;
    let ghost next_state = PageOrg::take_step::set_range_to_not_used(local.page_organization);
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    //assert(page.is_used_and_primary(*local));
    //assert(local.thread_token.value().pages.dom().contains(page_id));
    let ghost page_state = local.thread_token.value().pages[page_id];

    let segment = SegmentPtr::ptr_segment(page);
    proof {
        assert(local.page_organization.invariant());
        assert(local.page_organization.popped.is_Used());
        local.page_organization.used_popped_range_facts();
        assert(local.page_organization.pages.dom().contains(page_id));
        assert(local.page_organization.pages[page_id].is_used);
        assert(!local.unused_pages.dom().contains(page_id));
        assert(local.thread_token.value().pages.dom().contains(page_id));
        assert(local.pages[page_id].wf(
            page_id,
            local.thread_token.value().pages[page_id],
            local.instance));
        assert(local.thread_token.value().pages[page_id].is_enabled);
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(local.page_organization.pages.dom() =~= local.pages.dom());
        reveal(PageOrg::State::page_id_domain);
        assert(local.page_organization.segments.dom().contains(page_id.segment_id));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert(local.segments.dom().contains(segment.segment_id@));
        assert(segment.wf());
        assert(segment.is_in(*local));
    }

    let mem_is_pinned = segment.get_mem_is_pinned(Tracked(&*local));
    let is_reset = page.get_inner_ref(Tracked(&*local)).get_is_reset();
    let option_page_reset = option_page_reset();
    if !mem_is_pinned && !is_reset && option_page_reset {
        todo();
    }

    let ghost local_before_token_updates = *local;
    page_get_mut_inner!(page, local, inner => {
        inner.set_is_zero_init(false);
        inner.capacity = 0;
        inner.reserved = 0;
        let (Tracked(ll_state1)) = inner.free.make_empty();
        inner.flags1 = 0;
        inner.flags2 = 0;
        inner.used = 0;
        inner.xblock_size = 0;
        let (Tracked(ll_state2)) = inner.local_free.make_empty();

        let tracked (_block_pt, _block_tokens) = LL::reconvene_state(
            local.instance.clone(), &local.thread_token, ll_state1, ll_state2,
            page_state.num_blocks as int);
    });

    proof {
        assert(local.thread_token.instance_id() == local.instance.id());
        assert(local.thread_token.key() == local.thread_id);
        assert(local.thread_token.value().pages.dom().contains(page_id));
        assert(local.thread_token.value().pages[page_id].is_enabled);
        assert(local.thread_token.value().pages[page_id].num_blocks == 0);
    }
    let tracked checked_tok = local.take_checked_token();
    let tracked perm = &local.instance.thread_local_state_guards_page(
                local.thread_id, page.page_id@, &local.thread_token).points_to;
    let Tracked(checked_tok) = ptr_ref(page.page_ptr, Tracked(perm)).xthread_free.check_is_good(
        Tracked(&local.thread_token),
        Tracked(checked_tok));
    proof {
        assert(checked_tok.instance_id() == local.instance.id());
        assert(checked_tok.key() == local.thread_id);
        assert(checked_tok.value().pages.contains(page_id));
        local.page_organization.used_popped_range_facts();
        assert(local.page_organization == local_before_token_updates.page_organization);
        assert(n_slices == local_before_token_updates.page_organization.pages[page_id].count.unwrap());
        assert forall |pid: PageId|
            #[trigger] page_id.range_from(0, n_slices as int).contains(pid)
        implies
            local.thread_token.value().pages.dom().contains(pid)
            && local.thread_token.value().pages[pid].is_enabled
            && local.thread_token.value().pages[pid].offset == pid.idx - page_id.idx
        by {
            assert(pid.segment_id == page_id.segment_id);
            assert(page_id.idx <= pid.idx < page_id.idx + n_slices);
            assert(local_before_token_updates.page_organization.pages.dom().contains(pid));
            assert(local_before_token_updates.page_organization.pages[pid].is_used);
            assert(local_before_token_updates.page_organization.pages[pid].offset.is_some());
            assert(local_before_token_updates.page_organization.pages[pid].offset.unwrap() == pid.idx - page_id.idx);
            assert(page_organization_pages_match(
                local_before_token_updates.page_organization.pages,
                local_before_token_updates.pages,
                local_before_token_updates.psa,
                local_before_token_updates.page_organization.popped));
            assert(page_organization_matches_token_page(
                local_before_token_updates.page_organization.pages[pid],
                local_before_token_updates.thread_token.value().pages[pid]));
            if pid == page_id {
                assert(local.thread_token.value().pages[pid].offset == local_before_token_updates.thread_token.value().pages[pid].offset);
                assert(local.thread_token.value().pages[pid].is_enabled == local_before_token_updates.thread_token.value().pages[pid].is_enabled);
            } else {
                assert(local.thread_token.value().pages[pid] == local_before_token_updates.thread_token.value().pages[pid]);
            }
        };
        assert(page_id.range_from(0, n_slices as int).subset_of(local.thread_token.value().pages.dom()));
        local.checked_token = checked_tok;
        assert(local.checked_token.value().pages.contains(page_id));
    }

    unused_page_get_mut!(page, local, page => {
        let Tracked(_delay_token) = page.xthread_free.disable();
        let Tracked(_heap_of_page_token) = page.xheap.disable();

    });
    proof {
        local.psa = local.psa.insert(page_id, local.unused_pages[page_id]);
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { }
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { }
        assert(local.page_organization_valid());
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
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { }
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { }
        assert(local.pages[page_id].wf_unused(
            page_id,
            local.unused_pages[page_id],
            local.page_organization.popped,
            local.instance));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { }
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(local.wf_main_for_page_access());
    }
    /*
    used_page_get_mut_prev!(page, local, p => {
        p = PPtr::from_usize(0);
    });
    used_page_get_mut_next!(page, local, n => {
        n = PPtr::from_usize(0);
    });
    */


    proof {
        assert(local.page_organization == next_state);
        assert(PageOrg::State::set_range_to_not_used_strong(
            local_before_token_updates.page_organization,
            local.page_organization,
        ));
        assert(local.segments.dom() == local_before_token_updates.segments.dom());
        assert(local.pages.dom() == local_before_token_updates.pages.dom());
        assert(local_before_token_updates.pages[page_id].wf(
            page_id,
            local_before_token_updates.thread_token.value().pages[page_id],
            local_before_token_updates.instance));
        assert(local_before_token_updates.page_capacity(page_id)
            == local_before_token_updates.thread_token.value().pages[page_id].num_blocks);
        assert(local_before_token_updates.block_size(page_id)
            == local_before_token_updates.thread_token.value().pages[page_id].block_size as int);
        assert(page_state == local_before_token_updates.thread_token.value().pages[page_id]);
        assert(set_int_range(
            page_start(page_id) + start_offset(local_before_token_updates.block_size(page_id)),
            page_start(page_id) + start_offset(local_before_token_updates.block_size(page_id))
                + page_state.num_blocks * local_before_token_updates.block_size(page_id),
        ) <= local.segments[page_id.segment_id].mem.points_to.dom());
        assert(set_int_range(
            page_start(page_id) + start_offset(local_before_token_updates.block_size(page_id)),
            page_start(page_id) + start_offset(local_before_token_updates.block_size(page_id))
                + local_before_token_updates.page_capacity(page_id) * local_before_token_updates.block_size(page_id),
        ) <= local.segments[page_id.segment_id].mem.points_to.dom());
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid)
        by {
            assert(local_before_token_updates.segments.dom().contains(sid));
            if sid == page_id.segment_id {
                assert(local.segments[sid].mem.os == local_before_token_updates.segments[sid].mem.os);
                assert(local_before_token_updates.segments[sid].mem.points_to.dom()
                    <= local.segments[sid].mem.points_to.dom());
                assert(local.segments[sid].mem.points_to.provenance()
                    == local_before_token_updates.segments[sid].mem.points_to.provenance());
            } else {
                assert(local.segments[sid] == local_before_token_updates.segments[sid]);
            }
            assert(local.segments[sid].mem.wf());
            assert(local.segments[sid].mem.os == local_before_token_updates.segments[sid].mem.os);
            assert(local_before_token_updates.segments[sid].mem.points_to.dom()
                <= local.segments[sid].mem.points_to.dom());
            assert(local.segments[sid].mem.points_to.provenance()
                == local_before_token_updates.segments[sid].mem.points_to.provenance());
            assert(local.commit_mask(sid) == local_before_token_updates.commit_mask(sid));
            assert(local.decommit_mask(sid) == local_before_token_updates.decommit_mask(sid));
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid)
                && local.is_used_primary(pid) implies
                    local_before_token_updates.is_used_primary(pid)
                    && local.page_count(pid) == local_before_token_updates.page_count(pid)
                    && local.page_capacity(pid) == local_before_token_updates.page_capacity(pid)
                    && local.block_size(pid) == local_before_token_updates.block_size(pid)
            by {
                PageOrg::State::set_range_to_not_used_page_facts(
                    local_before_token_updates.page_organization,
                    local.page_organization);
                let changed_range = page_id_range(page_id.segment_id, page_id.idx, page_id.idx + n_slices);
                if changed_range.contains(pid) {
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(false);
                } else {
                    assert(local.page_organization.pages[pid]
                        == local_before_token_updates.page_organization.pages[pid]);
                    assert(local.is_used_primary(pid));
                    assert(local_before_token_updates.is_used_primary(pid));
                    assert(pid != page_id);
                    assert(local.pages[pid] == local_before_token_updates.pages[pid]);
                }
            };
            if sid == page_id.segment_id {
                assert(set_int_range(
                    page_start(page_id) + start_offset(local_before_token_updates.block_size(page_id)),
                    page_start(page_id) + start_offset(local_before_token_updates.block_size(page_id))
                        + local_before_token_updates.page_capacity(page_id) * local_before_token_updates.block_size(page_id),
                ) <= local.segments[sid].mem.points_to.dom());
            }
            local.set_range_to_not_used_preserves_mem_chunk_good(
                local_before_token_updates,
                sid,
                page_id,
            );
        };
        assert(local.wf_main());
    }

    segment_span_free_coalesce(page, tld, Tracked(&mut *local));

    let ghost local_snap = *local;
    proof {
        assert(local.wf_main());
    }

    let ghost next_state = PageOrg::take_step::clear_ec(local.page_organization);
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used - 1;
    });
    proof {
        local.page_organization = next_state;
        assert(local.page_organization.popped == Popped::No);
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { }
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { }
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { }
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { }
        assert(local.page_organization_valid());
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
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { }
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { }
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { }
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid)
        by {
            assert(local_snap.wf_main());
            assert(local.segments.dom() == local_snap.segments.dom());
            assert(local_snap.segments.dom().contains(sid));
            assert(local_snap.mem_chunk_good(sid));
            assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_snap.is_used_primary(pid)
            by { }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_count(pid) == local_snap.page_count(pid)
            by { }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_capacity(pid) == local_snap.page_capacity(pid)
            by { }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.block_size(pid) == local_snap.block_size(pid)
            by { }
            if sid == segment.segment_id@ {
                assert(local.segments[sid].mem == local_snap.segments[sid].mem);
                assert(local.commit_mask(sid) == local_snap.commit_mask(sid));
                assert(local.decommit_mask(sid) == local_snap.decommit_mask(sid));
            } else {
                assert(local.segments[sid] == local_snap.segments[sid]);
                assert(local.segments[sid].mem == local_snap.segments[sid].mem);
                assert(local.commit_mask(sid) == local_snap.commit_mask(sid));
                assert(local.decommit_mask(sid) == local_snap.decommit_mask(sid));
            }
            local.segment_metadata_update_preserves_mem_chunk_good(local_snap, sid);
        }
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(local.wf_main());
        assert(local.wf());
    }

}

#[verifier::rlimit(200)]
#[verus_verify]
fn segment_span_free_coalesce(slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main_for_page_access(),
        slice.wf(),
        slice.is_in(*old(local)),
        tld.wf(),
        tld.is_in(*old(local)),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).page_organization.popped.is_VeryUnready(),
        old(local).page_organization.popped.get_VeryUnready_0() == slice.page_id@.segment_id,
        old(local).page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx,
        old(local).page_organization.popped.get_VeryUnready_3() == true,
        old(local).page_count(slice.page_id@)
            == old(local).page_organization.popped.get_VeryUnready_2(),
    ensures
        slice.wf(),
        slice.is_in(*final(local)),
        tld.wf(),
        tld.is_in(*final(local)),
        final(local).wf_main(),
        final(local).wf_main_for_page_access(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization.popped == Popped::ExtraCount(slice.page_id@.segment_id),
{
    let segment = SegmentPtr::ptr_segment(slice);
    let is_abandoned = segment.is_abandoned(Tracked(&*local));
    if is_abandoned { todo(); }

    let kind = segment.get_segment_kind(Tracked(&*local));
    if matches!(kind, SegmentKind::Huge) {
        todo();
    }

    let mut slice_count = slice.get_count(Tracked(&*local));


    //// Merge with the 'after' page

    proof {
        assert(local.page_organization.invariant());
        assert(local.page_organization.pages.dom().contains(slice.page_id@));
        assert(slice_count as int == local.page_count(slice.page_id@));
        assert(slice_count as int == local.page_organization.popped.get_VeryUnready_2());
        local.page_organization.get_count_bound_very_unready();
        assert(slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT);
        assert((slice_count as usize) as int == slice_count as int) by(bit_vector);
        assert(slice.page_id@.idx + slice_count as usize <= SLICES_PER_SEGMENT) by(nonlinear_arith)
            requires
                slice.page_id@.idx + slice_count as int <= SLICES_PER_SEGMENT,
                (slice_count as usize) as int == slice_count as int;
        assert(segment.wf());
        assert(segment.segment_id@ == slice.page_id@.segment_id);
    }
    let (page, less_than_end) = slice.add_offset_and_check(slice_count as usize, segment);
    proof {
        if less_than_end {
            assert(page.page_id@.idx < SLICES_PER_SEGMENT);
            assert(local.page_organization.popped.is_VeryUnready());
            assert(local.page_organization.popped.get_VeryUnready_0() == slice.page_id@.segment_id);
            assert(local.page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx);
            assert(local.page_organization.popped.get_VeryUnready_1()
                + local.page_organization.popped.get_VeryUnready_2() < SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    page.page_id@.idx == slice.page_id@.idx + slice_count as usize,
                    page.page_id@.idx < SLICES_PER_SEGMENT,
                    local.page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx,
                    local.page_organization.popped.get_VeryUnready_2()
                        == slice_count as int,
                    (slice_count as usize) as int == slice_count as int;
            local.page_organization.valid_page_after();
            assert(local.page_organization.pages.dom().contains(page.page_id@));
            assert(page.is_in(*local));
        }
    }
    if less_than_end && page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
        let ghost page_id = page.page_id@;
        let ghost local_snap = *local;
        let ghost next_state = PageOrg::take_step::merge_with_after(local.page_organization);

        let prev_ptr = page.get_prev(Tracked(&*local));
        let next_ptr = page.get_next(Tracked(&*local));

        let ghost prev_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev.unwrap();
        let prev = PagePtr {
            page_ptr: prev_ptr, page_id: Ghost(prev_page_id),
        };
        let ghost next_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
        let next = PagePtr {
            page_ptr: next_ptr, page_id: Ghost(next_page_id),
        };

        let n_count = page.get_count(Tracked(&*local));
        let sbin_idx = slice_bin(n_count as usize);

        if prev_ptr.addr() != 0 {
            unused_page_get_mut_next!(prev, local, n => {
                n = next_ptr;
            });
        }
        if next_ptr.addr() != 0 {
            unused_page_get_mut_prev!(next, local, p => {
                p = prev_ptr;
            });
        }

        let cq = &mut tld.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx];
        if prev_ptr.addr() == 0 {
            cq.first = next_ptr;
        }
        if next_ptr.addr() == 0 {
            cq.last = prev_ptr;
        }

        proof {
            local.page_organization.merge_with_after_page_facts();
            assert(page.page_id@ == page_id);
            assert(local.page_organization.pages[page_id].count.is_some());
            assert(n_count as int == local.page_organization.pages[page_id].count.unwrap());
            assert(slice_count as int + n_count as int <= SLICES_PER_SEGMENT);
            assert(SLICES_PER_SEGMENT as int <= u32::MAX as int) by(compute_only);
            assert(slice_count as int + n_count as int <= u32::MAX as int) by(nonlinear_arith)
                requires
                    slice_count as int + n_count as int <= SLICES_PER_SEGMENT,
                    SLICES_PER_SEGMENT as int <= u32::MAX as int;
        }
        slice_count += n_count;
        proof {
            local.page_organization = next_state;
            assert(local.page_organization.invariant());
            assert(page_organization_queues_match(
                local.page_organization.unused_dlist_headers,
                local.tld.value().segments.span_queue_headers@));
            assert(page_organization_pages_match(
                local.page_organization.pages,
                local.pages,
                local.psa,
                local.page_organization.popped));
            assert(page_organization_segments_match(local.page_organization.segments, local.segments));
            assert(page_organization_used_queues_match(
                local.page_organization.used_dlist_headers,
                local.heap.pages.value()@));
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
            by { }
            assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
                local.page_organization.pages.dom().contains(pid)
            by { }
            assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
                local.unused_pages[pid] == local.psa[pid]
            by { }
            assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
                local.thread_token.value().pages[pid].shared_access == local.psa[pid]
            by { }
            assert(local.page_organization_valid());
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
            assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
                (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
            by { }
            assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
            assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
                local.thread_token.value().pages.dom().contains(pid) ==>
                    local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
            by { }
            assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
                local.unused_pages.dom().contains(pid) ==>
                    local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
            by { }
            assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
            by { }
            let ghost final_id = PageId { segment_id: page_id.segment_id,
                idx: (page_id.idx + n_count as int - 1) as nat };
            assert(local.segments == local_snap.segments);
            assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == local_snap.is_used_primary(pid) by {
                if pid == page_id {
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(!local_snap.page_organization.pages[pid].is_used);
                    assert(!local.is_used_primary(pid));
                    assert(!local_snap.is_used_primary(pid));
                } else if pid == final_id {
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(!local_snap.page_organization.pages[pid].is_used);
                    assert(!local.is_used_primary(pid));
                    assert(!local_snap.is_used_primary(pid));
                } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(!local_snap.page_organization.pages[pid].is_used);
                    assert(!local.is_used_primary(pid));
                    assert(!local_snap.is_used_primary(pid));
                } else if next_ptr.addr() != 0 && pid == next_page_id {
                    assert(!local.page_organization.pages[pid].is_used);
                    assert(!local_snap.page_organization.pages[pid].is_used);
                    assert(!local.is_used_primary(pid));
                    assert(!local_snap.is_used_primary(pid));
                } else {
                    assert(local.page_organization.pages[pid] == local_snap.page_organization.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_count(pid) == local_snap.page_count(pid) by {
                if pid == page_id {
                    assert(!local.is_used_primary(pid));
                } else if pid == final_id {
                    assert(!local.is_used_primary(pid));
                } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                    assert(!local.is_used_primary(pid));
                } else if next_ptr.addr() != 0 && pid == next_page_id {
                    assert(!local.is_used_primary(pid));
                } else {
                    assert(local.pages[pid] == local_snap.pages[pid]);
                }
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.page_capacity(pid) == local_snap.page_capacity(pid) by {
                if pid == page_id {
                    assert(!local.is_used_primary(pid));
                } else if pid == final_id {
                    assert(!local.is_used_primary(pid));
                } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                    assert(!local.is_used_primary(pid));
                } else if next_ptr.addr() != 0 && pid == next_page_id {
                    assert(!local.is_used_primary(pid));
                } else {
                    assert(local.pages[pid].inner == local_snap.pages[pid].inner);
                }
            }
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) ==> local.block_size(pid) == local_snap.block_size(pid) by {
                if pid == page_id {
                    assert(!local.is_used_primary(pid));
                } else if pid == final_id {
                    assert(!local.is_used_primary(pid));
                } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                    assert(!local.is_used_primary(pid));
                } else if next_ptr.addr() != 0 && pid == next_page_id {
                    assert(!local.is_used_primary(pid));
                } else {
                    assert(local.pages[pid].inner == local_snap.pages[pid].inner);
                }
            }
            assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                local.mem_chunk_good(sid) by {
                assert(local_snap.mem_chunk_good(sid));
                local.used_page_fields_preserved_mem_chunk_good(local_snap, sid);
            }
            assert(local.tld.is_init());
            assert(local.page_empty_global@.wf_empty_page_global());
            assert(local.wf_main());
            assert(local.wf_main_for_page_access());
        }

    }



    //// Merge with the 'before' page

    // Had to factor this out for timeout-related reasons :\
    proof {
        assert(local.wf_main_for_page_access());
        assert(segment.is_in(*local));
        assert(local.page_organization.popped.get_VeryUnready_2() == slice_count);
        assert(slice_count as int <= SLICES_PER_SEGMENT);
    }
    let (slice, slice_count) = segment_span_free_coalesce_before(segment, slice, tld, Tracked(&mut *local), slice_count);
    proof {
        assert(local.page_organization.popped.get_VeryUnready_3() == true);
    }

    segment_span_free(segment, slice.get_index(), slice_count as usize, true, tld,
        Tracked(&mut *local));
    proof {
        assert(local.wf_main());
        assert(local.wf_main_for_page_access());
        assert(local.pages.dom() == old(local).pages.dom());
        assert(common_preserves(*old(local), *local));
        assert(slice.is_in(*local));
        assert(tld.is_in(*local));
        assert(local.page_organization.popped == Popped::ExtraCount(slice.page_id@.segment_id));
    }
}

#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn segment_span_free_coalesce_before(segment: SegmentPtr, slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>, slice_count: u32)
    -> (res: (PagePtr, u32))
    requires
        old(local).wf_main_for_page_access(),
        segment.wf(),
        segment.is_in(*old(local)),
        slice.wf(),
        slice.is_in(*old(local)),
        slice.page_id@.segment_id == segment.segment_id@,
        tld.wf(),
        tld.is_in(*old(local)),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        old(local).page_organization.popped.is_VeryUnready(),
        old(local).page_organization.popped.get_VeryUnready_0() == slice.page_id@.segment_id,
        old(local).page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx,
        old(local).page_organization.popped.get_VeryUnready_2() == slice_count,
        slice_count as int <= SLICES_PER_SEGMENT,
    ensures
        res.0.wf(),
        res.0.page_id@.segment_id == segment.segment_id@,
        common_preserves(*old(local), *final(local)),
        final(local).wf_main(),
        final(local).wf_main_for_page_access(),
        final(local).pages.dom() == old(local).pages.dom(),
        segment.is_in(*final(local)),
        res.0.is_in(*final(local)),
        tld.is_in(*final(local)),
        forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid),
        final(local).page_organization.popped.is_VeryUnready(),
        final(local).page_organization.popped.get_VeryUnready_0() == segment.segment_id@,
        final(local).page_organization.popped.get_VeryUnready_1() == res.0.page_id@.idx,
        final(local).page_organization.popped.get_VeryUnready_2() == res.1,
        final(local).page_organization.popped.get_VeryUnready_3()
            == old(local).page_organization.popped.get_VeryUnready_3(),
{

    let ghost orig_id = slice.page_id@;

    let mut slice = slice;
    let mut slice_count = slice_count;

    if slice.is_gt_0th_slice(segment) {
        let last = slice.sub_offset(1);
        proof {
            assert(slice.page_id@.idx > 0);
            assert(last.wf());
            assert(last.page_id@.segment_id == slice.page_id@.segment_id);
            assert(last.page_id@.idx == slice.page_id@.idx - 1);
            assert(local.page_organization.invariant());
            assert(local.page_organization.popped.is_VeryUnready());
            assert(local.page_organization.popped.get_VeryUnready_0() == slice.page_id@.segment_id);
            assert(local.page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx);
            local.page_organization.valid_page_before();
            assert(local.page_organization.pages.dom().contains(last.page_id@));
            assert(last.is_in(*local));
            assert(local.page_organization.pages[last.page_id@].offset.is_some());
        }
        let offset = last.get_ref(Tracked(&*local)).offset; // multiplied by SIZEOF_PAGE_HEADER
        let ghost o = local.page_organization.pages[last.page_id@].offset.unwrap();
        let ghost page_id = PageId { segment_id: last.page_id@.segment_id,
                idx: (last.page_id@.idx - o) as nat };
        proof {
            assert(local.page_organization.pages.dom().contains(page_id));
            assert(local.page_organization.pages[page_id].offset == Some(0nat));
            assert(last.page_id@.idx - o >= 0);
            assert(page_id.idx == last.page_id@.idx - o);
            assert(page_id.segment_id == last.page_id@.segment_id);
            assert(local.page_organization_valid());
            assert(page_organization_pages_match_data(
                local.page_organization.pages[last.page_id@],
                local.pages[last.page_id@],
                local.psa[last.page_id@],
                last.page_id@,
                local.page_organization.popped));
            assert(offset as int == o * SIZEOF_PAGE_HEADER);
            assert(offset as int == (last.page_id@.idx as int - page_id.idx as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    offset as int == o * SIZEOF_PAGE_HEADER,
                    page_id.idx == last.page_id@.idx - o;
        }
        let page_ptr = calculate_page_ptr_subtract_offset(last.page_ptr, offset,
            Ghost(last.page_id@),
            Ghost(page_id));
        let page = PagePtr { page_ptr, page_id: Ghost(page_id) };
        proof {
            assert(page.wf());
            assert(local.page_organization.pages.dom().contains(page.page_id@));
            assert(page.is_in(*local));
        }
        if page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
            let ghost local_snap = *local;
            let ghost old_slice_count = slice_count;
            let ghost next_state = PageOrg::take_step::merge_with_before(local.page_organization);
            proof {
                local.page_organization.merge_with_before_page_facts();
                local.page_organization.merge_with_before_dlist_facts();
            }

            let prev_ptr = page.get_prev(Tracked(&*local));
            let next_ptr = page.get_next(Tracked(&*local));

            let ghost prev_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev.unwrap();
            let prev = PagePtr {
                page_ptr: prev_ptr, page_id: Ghost(prev_page_id),
            };
            let ghost next_page_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();
            let next = PagePtr {
                page_ptr: next_ptr, page_id: Ghost(next_page_id),
            };

            let n_count = page.get_count(Tracked(&*local));
            let sbin_idx = slice_bin(n_count as usize);

            if prev_ptr.addr() != 0 {
                unused_page_get_mut_next!(prev, local, n => {
                    n = next_ptr;
                });
            }
            if next_ptr.addr() != 0 {
                unused_page_get_mut_prev!(next, local, p => {
                    p = prev_ptr;
                });
            }

            let cq = &mut tld.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx];
            if prev_ptr.addr() == 0 {
                cq.first = next_ptr;
            }
            if next_ptr.addr() == 0 {
                cq.last = prev_ptr;
            }

            proof {
                assert(local.page_organization == local_snap.page_organization);
                assert(local_snap.page_organization.popped.get_VeryUnready_2() == old_slice_count);
                assert(page.page_id@ == page_id);
                assert(local.page_organization.pages[page.page_id@].count.is_some());
                assert(n_count as int == local.page_organization.pages[page.page_id@].count.unwrap());
                assert(n_count as int == local.page_organization.pages[page_id].count.unwrap());
                assert(local.page_organization.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT);
                assert(page_organization_pages_match_data(
                    local_snap.page_organization.pages[page_id],
                    local_snap.pages[page_id],
                    local_snap.psa[page_id],
                    page_id,
                    local_snap.page_organization.popped));
                assert(is_page_ptr_opt(prev_ptr, local_snap.page_organization.pages[page_id].dlist_entry.unwrap().prev));
                assert(is_page_ptr_opt(next_ptr, local_snap.page_organization.pages[page_id].dlist_entry.unwrap().next));
                if prev_ptr.addr() != 0 {
                    assert(local_snap.page_organization.pages[page_id].dlist_entry.unwrap().prev == Some(prev_page_id));
                    assert(is_page_ptr_opt(prev_ptr, Some(prev_page_id)));
                }
                if next_ptr.addr() != 0 {
                    assert(local_snap.page_organization.pages[page_id].dlist_entry.unwrap().next == Some(next_page_id));
                    assert(is_page_ptr_opt(next_ptr, Some(next_page_id)));
                }
                assert(SLICES_PER_SEGMENT as int + SLICES_PER_SEGMENT as int <= u32::MAX as int) by(compute_only);
                assert(slice_count as int + n_count as int <= u32::MAX as int) by(nonlinear_arith)
                    requires
                        slice_count as int <= SLICES_PER_SEGMENT,
                        n_count as int <= SLICES_PER_SEGMENT,
                        SLICES_PER_SEGMENT as int + SLICES_PER_SEGMENT as int <= u32::MAX as int;
            }
            slice_count += n_count;
            slice = page;
            proof {
                assert(slice_count == old_slice_count + n_count);
                assert((old_slice_count + n_count) as int == old_slice_count as int + n_count as int) by(bit_vector)
                    requires
                        old_slice_count as int + n_count as int <= u32::MAX as int;
                assert(slice_count as int == old_slice_count as int + n_count as int);
                local.page_organization = next_state;
                assert(local.page_organization.popped.get_VeryUnready_0() == slice.page_id@.segment_id);
                assert(local.page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx);
                assert(local.page_organization.popped.get_VeryUnready_2() == slice_count as int);
                assert(local.page_organization.invariant());
                assert(page_organization_queues_match(
                    local.page_organization.unused_dlist_headers,
                    local.tld.value().segments.span_queue_headers@));
                assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
                assert(local.pages.dom() == local_snap.pages.dom());
                assert(local.psa == local_snap.psa);
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    page_organization_pages_match_data(
                        local.page_organization.pages[pid],
                        local.pages[pid],
                        local.psa[pid],
                        pid,
                        local.page_organization.popped) by {
                    assert(local_snap.page_organization.pages.dom().contains(pid));
                    if pid == page.page_id@ {
                        assert(pid.idx != 0);
                        assert(local.page_organization.pages[pid].offset.is_none());
                        assert(local.page_organization.pages[pid].count.is_none());
                        assert(local.page_organization.pages[pid].dlist_entry.is_none());
                        assert(local.page_organization.pages[pid].page_header_kind ==
                            local_snap.page_organization.pages[pid].page_header_kind);
                        assert(local.page_organization.pages[pid].page_header_kind.is_none());
                        assert(page_organization_pages_match_data(
                            local.page_organization.pages[pid],
                            local.pages[pid],
                            local.psa[pid],
                            pid,
                            local.page_organization.popped));
                    } else if pid == last.page_id@ {
                        assert(local.page_organization.pages[pid].offset.is_none());
                        assert(local.page_organization.pages[pid].count.is_none());
                        assert(local.page_organization.pages[pid].dlist_entry.is_none());
                        assert(local.page_organization.pages[pid].page_header_kind ==
                            local_snap.page_organization.pages[pid].page_header_kind);
                        assert(local.page_organization.pages[pid].page_header_kind.is_none());
                        assert(page_organization_pages_match_data(
                            local.page_organization.pages[pid],
                            local.pages[pid],
                            local.psa[pid],
                            pid,
                            local.page_organization.popped));
                    } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                        assert(page_organization_pages_match_data(
                            local_snap.page_organization.pages[pid],
                            local_snap.pages[pid],
                            local_snap.psa[pid],
                            pid,
                            local_snap.page_organization.popped));
                        assert(local.page_organization.pages[pid].is_used == local_snap.page_organization.pages[pid].is_used);
                        assert(local.page_organization.pages[pid].offset == local_snap.page_organization.pages[pid].offset);
                        assert(local.page_organization.pages[pid].count == local_snap.page_organization.pages[pid].count);
                        assert(local.page_organization.pages[pid].full == local_snap.page_organization.pages[pid].full);
                        assert(local.page_organization.pages[pid].page_header_kind == local_snap.page_organization.pages[pid].page_header_kind);
                        assert(local_snap.page_organization.pages[pid].dlist_entry.is_some());
                        local_snap.page_organization.very_unready_popped_range_facts();
                        if pid.segment_id == local_snap.page_organization.popped.get_VeryUnready_0()
                            && pid.idx == local_snap.page_organization.popped.get_VeryUnready_1() {
                            assert(local_snap.page_organization.pages[pid].dlist_entry.is_none());
                            assert(false);
                        }
                        assert(pid != page.page_id@);
                        assert(local.page_organization.pages[pid].dlist_entry.is_some());
                        assert(local.page_organization.pages[pid].dlist_entry.unwrap().prev ==
                            local_snap.page_organization.pages[pid].dlist_entry.unwrap().prev);
                        assert(local.page_organization.pages[pid].dlist_entry.unwrap().next ==
                            local_snap.page_organization.pages[page_id].dlist_entry.unwrap().next);
                        assert(local.pages[pid].count == local_snap.pages[pid].count);
                        assert(local.pages[pid].inner == local_snap.pages[pid].inner);
                        assert(local.pages[pid].prev == local_snap.pages[pid].prev);
                        assert(is_page_ptr_opt(
                            *local.pages[pid].prev.value(),
                            local.page_organization.pages[pid].dlist_entry.unwrap().prev));
                        assert(*local.pages[pid].next.value() == next_ptr);
                        assert(is_page_ptr_opt(
                            *local.pages[pid].next.value(),
                            local.page_organization.pages[pid].dlist_entry.unwrap().next));
                        assert(page_organization_pages_match_data(
                            local.page_organization.pages[pid],
                            local.pages[pid],
                            local.psa[pid],
                            pid,
                            local.page_organization.popped));
                    } else if next_ptr.addr() != 0 && pid == next_page_id {
                        assert(page_organization_pages_match_data(
                            local_snap.page_organization.pages[pid],
                            local_snap.pages[pid],
                            local_snap.psa[pid],
                            pid,
                            local_snap.page_organization.popped));
                        assert(local.page_organization.pages[pid].is_used == local_snap.page_organization.pages[pid].is_used);
                        assert(local.page_organization.pages[pid].offset == local_snap.page_organization.pages[pid].offset);
                        assert(local.page_organization.pages[pid].count == local_snap.page_organization.pages[pid].count);
                        assert(local.page_organization.pages[pid].full == local_snap.page_organization.pages[pid].full);
                        assert(local.page_organization.pages[pid].page_header_kind == local_snap.page_organization.pages[pid].page_header_kind);
                        assert(local_snap.page_organization.pages[pid].dlist_entry.is_some());
                        local_snap.page_organization.very_unready_popped_range_facts();
                        if pid.segment_id == local_snap.page_organization.popped.get_VeryUnready_0()
                            && pid.idx == local_snap.page_organization.popped.get_VeryUnready_1() {
                            assert(local_snap.page_organization.pages[pid].dlist_entry.is_none());
                            assert(false);
                        }
                        assert(pid != page.page_id@);
                        assert(local.page_organization.pages[pid].dlist_entry.is_some());
                        assert(local.page_organization.pages[pid].dlist_entry.unwrap().next ==
                            local_snap.page_organization.pages[pid].dlist_entry.unwrap().next);
                        assert(local.page_organization.pages[pid].dlist_entry.unwrap().prev ==
                            local_snap.page_organization.pages[page_id].dlist_entry.unwrap().prev);
                        assert(local.pages[pid].count == local_snap.pages[pid].count);
                        assert(local.pages[pid].inner == local_snap.pages[pid].inner);
                        assert(local.pages[pid].next == local_snap.pages[pid].next);
                        assert(is_page_ptr_opt(
                            *local.pages[pid].next.value(),
                            local.page_organization.pages[pid].dlist_entry.unwrap().next));
                        assert(*local.pages[pid].prev.value() == prev_ptr);
                        assert(is_page_ptr_opt(
                            *local.pages[pid].prev.value(),
                            local.page_organization.pages[pid].dlist_entry.unwrap().prev));
                        assert(page_organization_pages_match_data(
                            local.page_organization.pages[pid],
                            local.pages[pid],
                            local.psa[pid],
                            pid,
                            local.page_organization.popped));
                    } else {
                        assert(local.page_organization.pages[pid] == local_snap.page_organization.pages[pid]);
                        assert(local.pages[pid] == local_snap.pages[pid]);
                        assert(page_organization_pages_match_data(
                            local_snap.page_organization.pages[pid],
                            local_snap.pages[pid],
                            local_snap.psa[pid],
                            pid,
                            local_snap.page_organization.popped));
                        if local.page_organization.pages[pid].page_header_kind.is_none() {
                            if pid.idx == 0 {
                                assert(!local.page_organization.popped.is_SegmentCreating());
                                assert(!local_snap.page_organization.popped.is_SegmentCreating());
                            } else if local.page_organization.pages[pid].offset == Some(0nat) {
                                if local.page_organization.popped.get_VeryUnready_0() == pid.segment_id
                                    && local.page_organization.popped.get_VeryUnready_1() == pid.idx {
                                    assert(pid == page.page_id@);
                                    assert(false);
                                }
                                if local_snap.page_organization.popped.get_VeryUnready_0() == pid.segment_id
                                    && local_snap.page_organization.popped.get_VeryUnready_1() == pid.idx {
                                    local_snap.page_organization.very_unready_popped_range_facts();
                                    assert(local_snap.page_organization.pages[pid].offset.is_none());
                                    assert(false);
                                }
                            }
                        }
                        assert(page_organization_pages_match_data(
                            local.page_organization.pages[pid],
                            local.pages[pid],
                            local.psa[pid],
                            pid,
                            local.page_organization.popped));
                    }
                }
                assert(page_organization_pages_match(
                    local.page_organization.pages,
                    local.pages,
                    local.psa,
                    local.page_organization.popped));
                assert(page_organization_segments_match(local.page_organization.segments, local.segments));
                assert(page_organization_used_queues_match(
                    local.page_organization.used_dlist_headers,
                    local.heap.pages.value()@));
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
                by { }
                assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
                    local.page_organization.pages.dom().contains(pid)
                by { }
                assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
                    local.unused_pages[pid] == local.psa[pid]
                by { }
                assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
                    local.thread_token.value().pages[pid].shared_access == local.psa[pid]
                by { }
                assert(local.page_organization_valid());
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
                assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
                    (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
                by { }
                assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
                assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
                    local.thread_token.value().pages.dom().contains(pid) ==>
                        local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
                by { }
                assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
                    local.unused_pages.dom().contains(pid) ==>
                        local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
                by { }
                assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                    local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
                by { }
                assert(local.tld.is_init());
                assert(local.page_empty_global@.wf_empty_page_global());
                assert(local.wf_main_for_page_access());
                assert(local.segments == local_snap.segments);
                assert(local.page_organization.pages.dom() == local_snap.page_organization.pages.dom());
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) == local_snap.is_used_primary(pid) by {
                    if pid == page.page_id@ {
                        assert(!local.page_organization.pages[pid].is_used);
                        assert(!local_snap.page_organization.pages[pid].is_used);
                        assert(!local.is_used_primary(pid));
                        assert(!local_snap.is_used_primary(pid));
                    } else if pid == last.page_id@ {
                        assert(!local.page_organization.pages[pid].is_used);
                        assert(!local_snap.page_organization.pages[pid].is_used);
                        assert(!local.is_used_primary(pid));
                        assert(!local_snap.is_used_primary(pid));
                    } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                        assert(!local.page_organization.pages[pid].is_used);
                        assert(!local_snap.page_organization.pages[pid].is_used);
                        assert(!local.is_used_primary(pid));
                        assert(!local_snap.is_used_primary(pid));
                    } else if next_ptr.addr() != 0 && pid == next_page_id {
                        assert(!local.page_organization.pages[pid].is_used);
                        assert(!local_snap.page_organization.pages[pid].is_used);
                        assert(!local.is_used_primary(pid));
                        assert(!local_snap.is_used_primary(pid));
                    } else {
                        assert(local.page_organization.pages[pid] == local_snap.page_organization.pages[pid]);
                    }
                }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) ==> local.page_count(pid) == local_snap.page_count(pid) by {
                    if pid == page.page_id@ {
                        assert(!local.is_used_primary(pid));
                    } else if pid == last.page_id@ {
                        assert(!local.is_used_primary(pid));
                    } else if prev_ptr.addr() != 0 && pid == prev_page_id {
                        assert(!local.page_organization.pages[pid].is_used);
                        assert(!local.is_used_primary(pid));
                    } else if next_ptr.addr() != 0 && pid == next_page_id {
                        assert(!local.page_organization.pages[pid].is_used);
                        assert(!local.is_used_primary(pid));
                    } else {
                        assert(local.pages[pid] == local_snap.pages[pid]);
                    }
                }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) ==> local.page_capacity(pid) == local_snap.page_capacity(pid) by {
                    if pid == page.page_id@ {
                        assert(!local.is_used_primary(pid));
                    } else {
                        assert(local.pages[pid].inner == local_snap.pages[pid].inner);
                    }
                }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    local.is_used_primary(pid) ==> local.block_size(pid) == local_snap.block_size(pid) by {
                    if pid == page.page_id@ {
                        assert(!local.is_used_primary(pid));
                    } else {
                        assert(local.pages[pid].inner == local_snap.pages[pid].inner);
                    }
                }
                assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                    local.mem_chunk_good(sid) by {
                    assert(local_snap.mem_chunk_good(sid));
                    local.used_page_fields_preserved_mem_chunk_good(local_snap, sid);
                }
                assert(local.wf_main());
            }

        }
    }


    proof {
        assert(common_preserves(*old(local), *local));
        assert(local.pages.dom() == old(local).pages.dom());
        assert(local.page_organization.popped.is_VeryUnready());
        assert(local.page_organization.popped.get_VeryUnready_0() == segment.segment_id@);
        assert(local.page_organization.popped.get_VeryUnready_1() == slice.page_id@.idx);
        assert(local.page_organization.popped.get_VeryUnready_2() == slice_count);
        assert(local.page_organization.popped.get_VeryUnready_3()
            == old(local).page_organization.popped.get_VeryUnready_3());
        assert(segment.is_in(*local));
        assert(slice.is_in(*local));
        assert(tld.is_in(*local));
        if !local.wf_main() {
            assert(local.wf_main_for_page_access());
            assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
                local.mem_chunk_good(sid) by {
                assert(old(local).mem_chunk_good(sid));
            }
            assert(local.wf_main());
        }
    }
    (slice, slice_count)
}

}
