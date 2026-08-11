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
{

    if unlikely(page_alignment > ALIGNMENT_MAX as usize) {
        todo();
    }

    if block_size <= SMALL_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else if block_size <= MEDIUM_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, MEDIUM_PAGE_SIZE as usize, block_size, tld, Tracked(&mut *local))
    } else if block_size <= LARGE_OBJ_SIZE_MAX as usize {
        segments_page_alloc(heap, block_size, block_size, tld, Tracked(&mut *local))
    } else {
        todo(); loop{}
    }
}

#[verifier::external_body]
fn segments_page_alloc(
    heap: HeapPtr,
    required: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (page_ptr: PagePtr)
{

    let alignment: usize = if required > MEDIUM_PAGE_SIZE as usize
        { MEDIUM_PAGE_SIZE as usize } else { SLICE_SIZE as usize };
    let page_size = align_up(required, alignment);
    let slices_needed = page_size / SLICE_SIZE as usize;



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

#[verifier::external_body]
fn segment_reclaim_or_alloc(
    heap: HeapPtr,
    needed_slices: usize,
    block_size: usize,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (segment_ptr: SegmentPtr)
{
    // TODO reclaiming

    let arena_id = heap.get_arena_id(Tracked(&*local));
    segment_alloc(0, 0, arena_id, tld, Tracked(&mut *local))
}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn segments_page_find_and_allocate(
    slice_count0: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    Ghost(block_size): Ghost<nat>,
) -> (page_ptr: PagePtr)
{
    let mut sbin_idx = slice_bin(slice_count0);
    let slice_count = if slice_count0 == 0 { 1 } else { slice_count0 };

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
            let slice = PagePtr {
                page_ptr: slice_ptr,
                page_id: Ghost(slice_page_id.unwrap())
            };


            let found_slice_count = slice.get_count(Tracked(&*local)) as usize;
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
                    /*proof {
                        let current_slice_count = found_slice_count;
                        let target_slice_count = slice_count;
                        assert((local).wf_main());
                        assert(tld_ptr.wf());
                        assert(tld_ptr.is_in(*local));
                        assert(slice.wf());
                        assert((local).page_organization.popped == Some(Popped { page_id: slice.page_id@ }));
                        assert((local).page_organization.pages[slice.page_id@].countunwrap()
                            == current_slice_count);
                        assert(SLICES_PER_SEGMENT >= current_slice_count);
                        assert(current_slice_count > target_slice_count);
                        assert(target_slice_count > 0);
                    }*/

                    segment_slice_split(
                        slice,
                        found_slice_count,
                        slice_count,
                        tld_ptr,
                        Tracked(&mut *local));
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

                //assert(local.wf_main());
                //assert(slice.is_in(*local));
                //assert(allocated_block_tokens(block_tokens, slice.page_id@, block_size, n_blocks, local.instance));
                //assert(tld_ptr.is_in(*local));
                return slice;
            }

            slice_ptr = slice.get_next(Tracked(&*local));
        }

        sbin_idx = sbin_idx + 1;
    }

    PagePtr::null()
}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn span_queue_delete(
    tld_ptr: TldPtr,
    sbin_idx: usize,

    slice: PagePtr,

    Tracked(local): Tracked<&mut Local>,
    Ghost(list_idx): Ghost<int>,
    Ghost(count): Ghost<int>,
)
{
    let prev = slice.get_prev(Tracked(&*local));
    let next = slice.get_next(Tracked(&*local));

    if prev.addr() == 0 {
        tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[sbin_idx].first = next;
    } else {
        //assert(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().prev.is_some());
        let prev_page_ptr = PagePtr { page_ptr: prev,
            page_id: Ghost(local.page_organization.pages[slice.page_id@].dlist_entry.unwrap().prev.unwrap()), };
        //assert(prev_page_ptr.wf());

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
        //assert(next_page_ptr.wf());

        //assert(local.psa.dom().contains(next_page_ptr.page_id@));

        unused_page_get_mut_prev!(next_page_ptr, local, p => {
            p = prev;
        });
    }

}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_slice_split(
    slice: PagePtr,
    current_slice_count: usize,
    target_slice_count: usize,
    tld_ptr: TldPtr,

    Tracked(local): Tracked<&mut Local>,
)
{
    let next_slice = slice.add_offset(target_slice_count);

    //let count_being_returned = target_slice_count - current_slice_count;
    let bin_idx = slice_bin(current_slice_count - target_slice_count);

    let first_in_queue;

    let cq = &mut tld_ptr.get_mut(Tracked(local)).segments.span_queue_headers[bin_idx];
    first_in_queue = cq.first;
    cq.first = next_slice.page_ptr;
    if first_in_queue.addr() == 0 {
        cq.last = next_slice.page_ptr;
    }

    if first_in_queue.addr() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.unused_dlist_headers[bin_idx as int].first.unwrap()) };
        unused_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = next_slice.page_ptr;
        });
    }

    unused_page_get_mut_count!(slice, local, c => {
        c = target_slice_count as u32;
    });

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


    if current_slice_count > target_slice_count + 1 {
        let last_slice = slice.add_offset(current_slice_count - 1);
        unused_page_get_mut_inner!(last_slice, local, inner => {
            inner.xblock_size = 0;
        });
        unused_page_get_mut_count!(last_slice, local, c => {
            c = (current_slice_count - target_slice_count) as u32;
        });
        unused_page_get_mut!(last_slice, local, page => {

            

            //assert((current_slice_count - target_slice_count) as u32 * (SIZEOF_PAGE_HEADER as u32)
            //    == (current_slice_count - target_slice_count) as u32 * 32);
            page.offset = (current_slice_count - target_slice_count - 1) as u32
                * (SIZEOF_PAGE_HEADER as u32);
        });
    }

}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_span_allocate(
    segment: SegmentPtr,
    slice: PagePtr,
    slice_count: usize,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
{
    let p = segment_page_start_from_slice(segment, slice, 0);

    //assert(slice_count * SLICE_SIZE <= SLICES_PER_SEGMENT * SLICE_SIZE);
    if !segment_ensure_committed(segment, p, slice_count * SLICE_SIZE as usize, Tracked(&mut *local)) {
        return false;
    }

    let ghost old_local = *local;
    let ghost first_page_id = slice.page_id@;

    //assert(local.page_organization.pages.dom().contains(slice.page_id@));

    let ghost range = first_page_id.range_from(0, slice_count as int);



    let tracked mut first_psa = local.unused_pages.tracked_remove(first_page_id);
    let mut page = ptr_mut_read(slice.page_ptr, Tracked(&mut first_psa.points_to));
    page.offset = 0;
    ptr_mut_write(slice.page_ptr, Tracked(&mut first_psa.points_to), page);
    unused_page_get_mut_count!(slice, local, count => {
        // this is usually already set. I think the one case where it actually needs to
        // be set is when initializing the segment.
        count = slice_count as u32;
    });
    unused_page_get_mut_inner!(slice, local, inner => {
        // Not entirely sure what the rationale for setting to bsize to this value is.
        // In normal operation, we're going to set the block_size to something else soon.
        // If we are currently setting up page 0 as part of segment initialization,
        // we do need to set this to some nonzero value.
        let bsize = slice_count * SLICE_SIZE as usize;
        inner.xblock_size = if bsize >= HUGE_BLOCK_SIZE as usize { HUGE_BLOCK_SIZE } else { bsize as u32 };
        //assert(inner.xblock_size != 0);
    });

    // Set up the remaining pages
    let mut i: usize = 1;
    let ghost local_snapshot = *local;
    let extra = slice_count - 1;
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

        //assert(is_page_ptr(local.unused_pages[this_page_id].points_to@.pptr, this_page_id));
        //assert(i * SIZEOF_PAGE_HEADER <= SLICES_PER_SEGMENT * SIZEOF_PAGE_HEADER);

        let tracked mut this_psa = local.unused_pages.tracked_remove(this_page_id);
        let mut page = ptr_mut_read(this_slice.page_ptr, Tracked(&mut this_psa.points_to));

        

        

        
        page.offset = i as u32 * SIZEOF_PAGE_HEADER as u32;
        ptr_mut_write(this_slice.page_ptr, Tracked(&mut this_psa.points_to), page);

        i = i + 1;

        /*proof {
            assert forall |page_id|
              #[trigger] local.unused_pages.dom().contains(page_id) implies
              (
                  if first_page_id.range_from(1, i as int).contains(page_id) {
                      psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id])
                      && local.unused_pages[page_id].points_to.value().offset ==
                          page_id.idx - first_page_id.idx
                  } else {
                      local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]
                  }
              )
           by {
              if first_page_id.range_from(1, i as int).contains(page_id) {
                      assert(psa_differ_only_in_offset(
                          local.unused_pages[page_id],
                          local_snapshot.unused_pages[page_id]));
                      if page_id.idx - first_page_id.idx == i - 1 {
                          assert(page_id == this_page_id);
                          assert(local.unused_pages[this_page_id].points_to.value().offset == i - 1);
                          assert(local.unused_pages[page_id].points_to.value().offset ==
                              page_id.idx - first_page_id.idx);
                      } else {
                          assert(local.unused_pages[page_id].points_to.value().offset ==
                              page_id.idx - first_page_id.idx);
                      }
                  } else {
                      assert(local.unused_pages[page_id] == local_snapshot.unused_pages[page_id]);
                  }
           }
        }*/
    }

    unused_page_get_mut_inner!(slice, local, inner => {
        inner.set_is_reset(false);
        inner.set_is_committed(false);
    });
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used + 1;
    });


    return true;
}

// segment_reclaim_or_alloc
//  -> segment_alloc
//  -> segment_os_alloc
//  -> arena_alloc_aligned

// For normal pages, required == 0
// For huge pages, required == ?
#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_alloc(
    required: usize,
    page_alignment: usize,
    req_arena_id: ArenaId,
    tld: TldPtr,
    Tracked(local): Tracked<&mut Local>,
    // os_tld,
    // huge_page,
) -> (segment_ptr: SegmentPtr)
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

    // the C version skips this step if the bytes are all zeroed by the OS
    // We would need a complex transmute operation to do the same thing

    let tracked seg_header_points_to_raw = mem_chunk.take_points_to_range(
        segment_start(segment_id), SIZEOF_SEGMENT_HEADER as int);

    //assert(SIZEOF_SEGMENT_HEADER == vstd::layout::size_of::<SegmentHeader>());
    //assert(segment_start(segment_id) % vstd::layout::align_of::<SegmentHeader>() as int == 0);
    vstd::layout::layout_for_type_is_valid::<SegmentHeader>(); // $line_count$Proof$

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
        vstd::layout::layout_for_type_is_valid::<Page>(); // $line_count$Proof$
        let tracked page_header_points_to_raw = mem_chunk.take_points_to_range(
            phstart, SIZEOF_PAGE_HEADER as int);
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

        //assert(cur_page_ptr.id() + SIZEOF_PAGE_HEADER <= usize::MAX);

        i = i + 1;
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


    let first_slice = PagePtr {
        page_ptr: segment_ptr.segment_ptr.with_addr(
            segment_ptr.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER) as *mut Page,
        page_id: Ghost(PageId { segment_id, idx: 0 }),
    };
    //assert(first_slice.wf());
    let success = segment_span_allocate(segment_ptr, first_slice, 1, tld, Tracked(&mut *local));
    if !success {
        todo(); // TODO actually we don't need this check cause we can't fail
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

    if required == 0 {
        segment_span_free(segment_ptr, 1, SLICES_PER_SEGMENT as usize - 1, false, tld, Tracked(&mut *local));
    } else {
        todo();
    }

    return segment_ptr;
}

#[verifier::spinoff_prover]
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


    return (segment, psegment_slices, pre_size, pinfo_slices, is_zero, pcommit, mem_id, mem_large, is_pinned, align_offset, Tracked(mem));
}

#[verifier::external_body]
fn segment_free(segment: SegmentPtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
{
    todo();
    /*
    proof {
        let next_state = PageOrg::take_step::segment_freeing_start(local.page_organization, segment.segment_id@);
        local.page_organization = next_state;
        preserves_mem_chunk_good(*old(local), *local);
        assert(local.wf_main());
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
#[verifier::external_body]
fn segment_calculate_slices(required: usize)
  -> (res: (usize, usize, usize))
{

    let page_size = crate::os_mem::get_page_size();
    let i_size = align_up(SIZEOF_SEGMENT_HEADER, page_size);
    let guardsize = 0;

    let pre_size = i_size;
    let j_size = align_up(i_size + guardsize, SLICE_SIZE as usize);
    let info_slices = j_size / SLICE_SIZE as usize;
    let segment_size = if required == 0 {
        SEGMENT_SIZE as usize
    } else {
        align_up(required + j_size + guardsize, SLICE_SIZE as usize)
    };
    let num_slices = segment_size / SLICE_SIZE as usize;

    (num_slices, pre_size, info_slices)
}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_span_free(
    segment_ptr: SegmentPtr,
    slice_index: usize,
    slice_count: usize,
    allow_decommit: bool,
    tld_ptr: TldPtr,
    Tracked(local): Tracked<&mut Local>,
)
{
    let bin_idx = slice_bin(slice_count);

    let slice = segment_ptr.get_page_header_ptr(slice_index);

    unused_page_get_mut_count!(slice, local, c => {
        c = slice_count as u32;
    });
    unused_page_get_mut!(slice, local, page => {
        page.offset = 0;
    });

    if slice_count > 1 {
        let last = segment_ptr.get_page_header_ptr(slice_index + slice_count - 1);

        unused_page_get_mut!(last, local, page => {

            

            

            
            page.offset = (slice_count as u32 - 1) * SIZEOF_PAGE_HEADER as u32;
        });
    }

    if allow_decommit {
        segment_perhaps_decommit(segment_ptr,
            slice.slice_start(),
            slice_count * SLICE_SIZE as usize,
            Tracked(&mut *local));
    }
    //assert(local.wf_main());
    let ghost local_snap = *local;

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

}

#[verifier::external_body]
pub fn segment_page_free(page: PagePtr, force: bool, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
{
    let segment = SegmentPtr::ptr_segment(page);
    segment_page_clear(page, tld, Tracked(&mut *local));

    let used = segment.get_used(Tracked(&*local));
    if used == 0 {
        segment_free(segment, force, tld, Tracked(&mut *local));
    } else if used == segment.get_abandoned(Tracked(&*local)) {
        todo();
    }
}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_page_clear(page: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
{
    let ghost page_id = page.page_id@;
    let ghost next_state = PageOrg::take_step::set_range_to_not_used(local.page_organization);
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    //assert(page.is_used_and_primary(*local));
    //assert(local.thread_token.value().pages.dom().contains(page_id));
    let ghost page_state = local.thread_token.value().pages[page_id];

    let segment = SegmentPtr::ptr_segment(page);

    let mem_is_pinned = segment.get_mem_is_pinned(Tracked(&*local));
    let is_reset = page.get_inner_ref(Tracked(&*local)).get_is_reset();
    let option_page_reset = option_page_reset();
    if !mem_is_pinned && !is_reset && option_page_reset {
        todo();
    }

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

    let tracked checked_tok = local.take_checked_token();
    let tracked perm = &local.instance.thread_local_state_guards_page(
                local.thread_id, page.page_id@, &local.thread_token).points_to;
    let Tracked(checked_tok) = ptr_ref(page.page_ptr, Tracked(perm)).xthread_free.check_is_good(
        Tracked(&local.thread_token),
        Tracked(checked_tok));

    unused_page_get_mut!(page, local, page => {
        let Tracked(_delay_token) = page.xthread_free.disable();
        let Tracked(_heap_of_page_token) = page.xheap.disable();

    });
    /*
    used_page_get_mut_prev!(page, local, p => {
        p = PPtr::from_usize(0);
    });
    used_page_get_mut_next!(page, local, n => {
        n = PPtr::from_usize(0);
    });
    */


    segment_span_free_coalesce(page, tld, Tracked(&mut *local));

    let ghost local_snap = *local;

    let ghost next_state = PageOrg::take_step::clear_ec(local.page_organization);
    segment_get_mut_main2!(segment, local, main2 => {
        main2.used = main2.used - 1;
    });

}

#[verifier::external_body]
fn segment_span_free_coalesce(slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>)
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

    let (page, less_than_end) = slice.add_offset_and_check(slice_count as usize, segment);
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

        slice_count += n_count;

    }



    //// Merge with the 'before' page

    // Had to factor this out for timeout-related reasons :\
    let (slice, slice_count) = segment_span_free_coalesce_before(segment, slice, tld, Tracked(&mut *local), slice_count);

    segment_span_free(segment, slice.get_index(), slice_count as usize, true, tld,
        Tracked(&mut *local));
}

#[inline(always)]
#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_span_free_coalesce_before(segment: SegmentPtr, slice: PagePtr, tld: TldPtr, Tracked(local): Tracked<&mut Local>, slice_count: u32)
    -> (res: (PagePtr, u32))
{

    let ghost orig_id = slice.page_id@;

    let mut slice = slice;
    let mut slice_count = slice_count;

    if slice.is_gt_0th_slice(segment) {
        let last = slice.sub_offset(1);
        //assert(local.page_organization.pages.dom().contains(last.page_id@));
        let offset = last.get_ref(Tracked(&*local)).offset; // multiplied by SIZEOF_PAGE_HEADER
        //assert(local.page_organization.pages[last.page_id@].offset.is_some());
        let ghost o = local.page_organization.pages[last.page_id@].offset.unwrap();
        //assert(last.page_id@.idx - o >= 0);
        let ghost page_id = PageId { segment_id: last.page_id@.segment_id,
                idx: (last.page_id@.idx - o) as nat };
        let page_ptr = calculate_page_ptr_subtract_offset(last.page_ptr, offset,
            Ghost(last.page_id@),
            Ghost(page_id));
        let page = PagePtr { page_ptr, page_id: Ghost(page_id) };
        if page.get_inner_ref(Tracked(&*local)).xblock_size == 0 {
            let ghost local_snap = *local;
            let ghost next_state = PageOrg::take_step::merge_with_before(local.page_organization);

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

            slice_count += n_count;
            slice = page;

        }
    }


    (slice, slice_count)
}

}
