#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::set_lib::*;
use vstd::cell::pcell::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState, SegmentState, ThreadId};
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

#[verifier::external_body]
pub fn segment_page_alloc(
    heap: HeapPtr,
    block_size: usize,
    page_alignment: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
        2 <= block_size,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*final(local))
            && final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *final(local))
            && good_count_for_block_size(block_size as int,
                    final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int)
        ),
        page_ptr.page_ptr.addr() == 0 ==> final(local).wf()
{
    unimplemented!()
}

#[verifier::external_body]
fn segments_page_alloc(
    heap: HeapPtr,
    required: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
        2 <= block_size <= LARGE_OBJ_SIZE_MAX,
        1 <= required <= LARGE_OBJ_SIZE_MAX,
        (if block_size <= SMALL_OBJ_SIZE_MAX {
            required == block_size
        } else if block_size <= MEDIUM_OBJ_SIZE_MAX {
            required == MEDIUM_PAGE_SIZE
        } else {
            required == block_size
        }),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*final(local))
            && final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *final(local))
            && good_count_for_block_size(block_size as int,
                    final(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int)
        ),
        page_ptr.page_ptr.addr() == 0 ==>
            final(local).wf()
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_reclaim_or_alloc(
    heap: HeapPtr,
    needed_slices: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (segment_ptr: SegmentPtr)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
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
        1 <= slice_count0 <= SLICES_PER_SEGMENT,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        (page_ptr.page_ptr.addr() != 0 ==>
            page_ptr.wf()
            && page_ptr.is_in(*final(local))
            //&& allocated_block_tokens(blocks@, page_ptr.page_id@, block_size, n_blocks, local.instance)
            && final(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true)
            && page_init_is_committed(page_ptr.page_id@, *final(local))
            && (slice_count0 > 0 ==> final(local).page_organization.pages[page_ptr.page_id@].count == Some(slice_count0 as nat))
        ),
        (page_ptr.page_ptr.addr() == 0 ==> final(local).wf())
{
    unimplemented!()
}

#[verifier::external_body]
fn span_queue_delete(
    tld_ptr: TldPtr,
    sbin_idx: usize,

    slice: PagePtr,

    Tracked(local): Tracked<&mut Local>,
    Ghost(list_idx): Ghost<int>,
    Ghost(count): Ghost<int>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        old(local).page_organization.valid_unused_page(slice.page_id@, sbin_idx as int, list_idx),
        count == old(local).page_organization.pages[slice.page_id@].count.unwrap(),
        (match old(local).page_organization.popped {
            Popped::No => true,
            Popped::SegmentFreeing(sid, idx) =>
                slice.page_id@.segment_id == sid && slice.page_id@.idx == idx,
            _ => false,
        })
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization.popped == (match old(local).page_organization.popped {
            Popped::No => Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, count, false),
            Popped::SegmentFreeing(sid, idx) => Popped::SegmentFreeing(sid, idx + count),
            _ => arbitrary(),
        }),

        final(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).pages[slice.page_id@]
          == final(local).pages[slice.page_id@],
        final(local).page_organization.pages[slice.page_id@].is_used == false,
        //old(local).page_organization.pages[slice.page_id@]
        //    == final(local).page_organization.pages[slice.page_id@]
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_slice_split(
    slice: PagePtr,
    current_slice_count: usize,
    target_slice_count: usize,
    tld_ptr: TldPtr,

    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        slice.wf(),
        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, current_slice_count as int, false),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        //old(local).page_organization.pages[slice.page_id@].count.is_some(),
        old(local).page_organization.pages[slice.page_id@].is_used == false,
        SLICES_PER_SEGMENT >= current_slice_count > target_slice_count,
        target_slice_count > 0,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        slice.wf(),
        final(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, target_slice_count as int, false),
        final(local).page_organization.pages.dom().contains(slice.page_id@),
        final(local).page_organization.pages[slice.page_id@].is_used == false
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_span_allocate(
    segment: SegmentPtr,
    slice: PagePtr,
    slice_count: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires
        old(local).wf_main(),
        slice.wf(),
        segment.wf(),
        segment.segment_id == slice.page_id@.segment_id,
        segment.is_in(*old(local)),

        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, false)
          || (old(local).page_organization.popped == Popped::SegmentCreating(slice.page_id@.segment_id) && slice.page_id@.idx == 0 && slice_count < SLICES_PER_SEGMENT),
        old(local).page_organization.pages.dom().contains(slice.page_id@),
        old(local).page_organization.pages[slice.page_id@].is_used == false,

        SLICES_PER_SEGMENT >= slice_count > 0,
    ensures
        final(local).wf_main(),
        success ==> old(local).page_organization.popped.is_VeryUnready() ==> final(local).page_organization.popped == Popped::Ready(slice.page_id@, true),
        success ==> old(local).page_organization.popped.is_SegmentCreating() ==> final(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice_count as int, SLICES_PER_SEGMENT - slice_count as int, true),
        success ==> final(local).page_organization.pages.dom().contains(slice.page_id@),
        success ==> final(local).page_organization.pages[slice.page_id@].count
            == Some(slice_count as nat),
        success ==> page_init_is_committed(slice.page_id@, *final(local)),
        common_preserves(*old(local), *final(local)),
        segment.is_in(*final(local))
{
    unimplemented!()
}

// segment_reclaim_or_alloc
//  -> segment_alloc
//  -> segment_os_alloc
//  -> arena_alloc_aligned

#[verifier::external_body]
// For normal pages, required == 0
// For huge pages, required == ?
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
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        required == 0, // only handling non-huge-pages for now
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
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
    requires psegment_slices as int * SLICE_SIZE as int <= usize::MAX,
        pinfo_slices == 1,
        psegment_slices >= 1,
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        psegment_slices == SLICES_PER_SEGMENT,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        *final(pdecommit_mask) == *old(pdecommit_mask), // this is only modified if segment cache is used
    ({
        let (segment_ptr, new_psegment_slices, new_ppre_size, new_pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, mem_chunk) = res; {
        &&& (segment_ptr.segment_ptr.addr() != 0 ==> {
            &&& segment_ptr.wf()
            &&& mem_chunk@.wf()
            &&& mem_chunk@.os_exact_range(segment_ptr.segment_ptr as int, SEGMENT_SIZE as int)
            &&& mem_chunk@.points_to.provenance() == segment_ptr.segment_ptr@.provenance
            &&& segment_ptr.segment_ptr@.provenance == segment_ptr.segment_id@.provenance
            &&& set_int_range(segment_start(segment_ptr.segment_id@),
                    segment_start(segment_ptr.segment_id@) + COMMIT_SIZE).subset_of( final(pcommit_mask).bytes(segment_ptr.segment_id@) )
            &&& final(pcommit_mask).bytes(segment_ptr.segment_id@).subset_of(mem_chunk@.os_rw_bytes())
            &&& mem_chunk@.os_rw_bytes().subset_of(mem_chunk@.points_to.dom())
        })
        }
    })
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_free(segment: SegmentPtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        tld.wf(),
        tld.is_in(*old(local)),
        segment.wf(),
        segment.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_os_free(segment: SegmentPtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires 
        old(local).wf_main(),
        segment.wf(), segment.is_in(*old(local)),
        tld.wf(), tld.is_in(*old(local))
{
    unimplemented!()
}

#[verifier::external_body]
// segment_slices = # of slices in the segment
// pre_size = size of the pages that contain the segment metadata
// info_slices = # of slices needed to contain the pages of the segment metadata
fn segment_calculate_slices(required: usize)
  -> (res: (usize, usize, usize))
  requires required == 0,
  ensures ({ let (num_slices, pre_size, info_slices) = res;
      required == 0 ==> num_slices == SLICES_PER_SEGMENT
          && pre_size == crate::os_mem::page_size()
          && info_slices == 1
  })
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_span_free(
    segment_ptr: SegmentPtr,
    slice_index: usize,
    slice_count: usize,
    allow_decommit: bool,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        tld_ptr.wf(),
        tld_ptr.is_in(*old(local)),
        segment_ptr.wf(),
        segment_ptr.is_in(*old(local)),
        0 <= slice_index,
        slice_index + slice_count <= SLICES_PER_SEGMENT,

        old(local).page_organization.popped == Popped::VeryUnready(segment_ptr.segment_id@, slice_index as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3()),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        segment_ptr.is_in(*final(local)),
        final(local).page_organization.popped == if old(local).page_organization.popped.get_VeryUnready_3() {
            Popped::ExtraCount(segment_ptr.segment_id@)
        } else {
            Popped::No
        },
        final(local).pages.dom() =~= old(local).pages.dom()
{
    unimplemented!()
}

#[verifier::external_body]
pub fn segment_page_free(page: PagePtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_page_clear(page: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        page.is_in(*final(local)),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_span_free_coalesce(slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        slice.wf(),
        slice.is_in(*old(local)),
        match old(local).page_organization.popped {
            Popped::VeryUnready(sid, idx, c, _) => slice.page_id@.segment_id == sid
                && slice.page_id@.idx == idx
                && c == old(local).pages[slice.page_id@].count.value(),
            _ => false,
        },
    ensures
        final(local).wf_main(),
        slice.is_in(*final(local)),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization.popped == (match old(local).page_organization.popped {
            Popped::VeryUnready(_, _, _, b) => {
                if b {
                    Popped::ExtraCount(slice.page_id@.segment_id)
                } else {
                    Popped::No
                }
            }
            _ => arbitrary(),
        })
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
fn segment_span_free_coalesce_before(segment: SegmentPtr, slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>, slice_count: u32)
    -> (res: (PagePtr, u32))
    requires
        old(local).wf_main(),
        tld.wf(),
        tld.is_in(*old(local)),
        segment.wf(),
        segment.segment_id@ == slice.page_id@.segment_id,
        slice.wf(),
        slice.is_in(*old(local)),
        old(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3())
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        slice.is_in(*final(local)),
        slice.page_id@.segment_id == res.0.page_id@.segment_id,
        ({ let (slice, slice_count) = res;
          slice.wf()
          && final(local).page_organization.popped == Popped::VeryUnready(slice.page_id@.segment_id, slice.page_id@.idx as int, slice_count as int, old(local).page_organization.popped.get_VeryUnready_3())
          && slice.page_id@.idx + slice_count <= SLICES_PER_SEGMENT
        })
{
    unimplemented!()
}

}
