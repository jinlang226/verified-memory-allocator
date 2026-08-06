#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState};
use crate::types::*;
use crate::layout::*;
use crate::bin_sizes::*;
use crate::config::*;
use crate::page_organization::*;
use crate::linked_list::LL;
use crate::os_mem_util::*;
use crate::commit_segment::*;
use crate::segment::good_count_for_block_size;
use crate::queues::*;

verus!{

#[verifier::external_body]
pub fn find_page(heap_ptr: HeapPtr, size: usize, huge_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> 
            final(local).pages.index(page.page_id@).inner.value().xblock_size >= size
{
    unimplemented!()
}

#[verifier::external_body]
fn find_free_page(heap_ptr: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        size <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> 
            final(local).pages.index(page.page_id@).inner.value().xblock_size >= size
{
    unimplemented!()
}

#[verifier::external_body]
fn page_queue_find_free_ex(heap_ptr: HeapPtr, pq: usize, first_try: bool, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> 
            final(local).pages.index(page.page_id@).inner.value().xblock_size == size_of_bin(pq as int)
{
    unimplemented!()
}

#[verifier::external_body]
fn page_fresh(heap_ptr: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> 
            final(local).pages.index(page.page_id@).inner.value().xblock_size == size_of_bin(pq as int)
{
    unimplemented!()
}

#[verifier::external_body]
fn page_fresh_alloc(heap_ptr: HeapPtr, pq: usize, block_size: usize, page_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        2 <= block_size,
        valid_bin_idx(pq as int),
        block_size == size_of_bin(pq as int),
        block_size <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local))
            && page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> 
            final(local).pages.index(page.page_id@).inner.value().xblock_size == block_size
{
    unimplemented!()
}

#[verifier::external_body]
// READY --> USED
fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
    requires
        old(local).wf_main(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        page_ptr.wf(),
        page_ptr.is_in(*old(local)),
        old(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        block_size != 0,
        block_size % 8 == 0,
        block_size <= u32::MAX,
        valid_bin_idx(pq),
        size_of_bin(pq) == block_size,
        //old(local).page_organization[page_ptr.page_id@].block_size == Some(block_
        //old(local).page_inner(page_ptr.page_id@).xblock_size == block_size
        //old(local).segments[page_ptr.page_id@.segment_id]
        //  .mem.committed_pointsto_has_range(
        //    segment_start(page_ptr.page_id@.segment_id) + page_ptr.page_id@.idx * SLICE_SIZE,
        //    local.page_organization.pages[page_ptr.page_id@].count.unwrap() * SLIZE_SIZE),
        page_init_is_committed(page_ptr.page_id@, *old(local)),
        good_count_for_block_size(block_size as int,
              old(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        page_ptr.is_used(*final(local)),
        final(local).page_organization.popped == Popped::Used(page_ptr.page_id@, true),
        final(local).page_organization.pages[page_ptr.page_id@].page_header_kind == Some(PageHeaderKind::Normal(pq as int, block_size as int))
{
    unimplemented!()
}

#[verifier::external_body]
fn page_queue_of(page: PagePtr, Tracked(local): Tracked<&Local>) -> (res: (HeapPtr, usize, Ghost<int>))
    requires local.wf(),
        page.wf(), page.is_in(*local),
        page.is_used_and_primary(*local),
    ensures ({ let (heap, pq, list_idx) = res; {
        &&& heap.wf()
        &&& heap.is_in(*local)
        &&& (valid_bin_idx(pq as int) || pq == BIN_FULL)
        &&& local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx@)
    }})
{
    unimplemented!()
}

const MAX_RETIRE_SIZE: u32 = MEDIUM_OBJ_SIZE_MAX as u32;

#[verifier::external_body]
pub fn page_retire(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn page_free(page: PagePtr, pq: usize, force: bool, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
        old(local).pages[page.page_id@].inner.value().used == 0,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}
   
#[verifier::external_body]
fn page_to_full(page: PagePtr, heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>,
      Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        valid_bin_idx(pq as int),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) ==>
            final(local).page_organization.valid_used_page(next_id, pq as int, list_idx)
{
    unimplemented!()
}

#[verifier::external_body]
pub fn page_unfull(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).pages[page.page_id@].inner.value().in_full(),
    ensures final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn page_queue_enqueue_from(heap: HeapPtr, to: usize, from: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, from as int, list_idx),
        (valid_bin_idx(from as int) && to == BIN_FULL)
          || (match old(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(b, bsize)) =>
              from == BIN_FULL
                && to == b,
                //&& valid_bin_idx(to as int)
                //&& bsize == size_of_bin(to as int),
            None => false,
          })
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        old(local).page_organization.valid_used_page(next_id, from as int, list_idx + 1) ==>
            final(local).page_organization.valid_used_page(next_id, from as int, list_idx),
        page.is_used_and_primary(*final(local))
{
    unimplemented!()
}

#[verifier::external_body]
pub fn page_try_use_delayed_free(page: PagePtr, delay: usize, override_never: bool, Tracked(local): Tracked<&Local>) -> bool
    requires local.wf(), page.wf(), page.is_in(*local),
        page.is_used_and_primary(*local),
        delay == 0, !override_never
{
    unimplemented!()
}

}
