#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;

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

verus!{

   
#[verifier::external_body]
pub fn page_queue_remove(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires old(local).wf(), page.wf(), page.is_in(*old(local)),
        heap.wf(), heap.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        //valid_bin_idx(pq as int) || pq == BIN_FULL,
        //old(local).page_organization.pages[page.page_id@].page_header_kind ==
        //    Some(PageHeaderKind::Normal(crate::bin_sizes::size_of_bin(pq as int) as int)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        page.is_in(*final(local)),
        final(local).page_organization.popped == Popped::Used(page.page_id@, true),
        final(local).page_organization.pages[page.page_id@].page_header_kind
            == old(local).page_organization.pages[page.page_id@].page_header_kind,
        final(local).tld_id == old(local).tld_id,
        old(local).page_organization.valid_used_page(next_id, pq as int, list_idx + 1) ==>
            final(local).page_organization.valid_used_page(next_id, pq as int, list_idx),
        old(local).pages[page.page_id@].inner.value().used
            == final(local).pages[page.page_id@].inner.value().used
{
    unimplemented!()
}

#[verifier::external_body]
pub fn page_queue_push(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        (match old(local).page_organization.pages[page.page_id@].page_header_kind.unwrap() {
              PageHeaderKind::Normal(b, bsize) => {
                  (pq == BIN_FULL || pq as int == b)
                  && valid_bin_idx(b as int)
                  && bsize == crate::bin_sizes::size_of_bin(b)
                  && bsize <= MEDIUM_OBJ_SIZE_MAX
              }
          }),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        final(local).pages.index(page.page_id@).inner.value().xblock_size ==
            old(local).pages.index(page.page_id@).inner.value().xblock_size,
        final(local).tld_id == old(local).tld_id
{
    unimplemented!()
}

#[verifier::external_body]
pub fn page_queue_push_back(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(other_id): Ghost<PageId>, Ghost(other_pq): Ghost<int>, Ghost(other_list_idx): Ghost<int>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        (match old(local).page_organization.pages[page.page_id@].page_header_kind.unwrap() {
              PageHeaderKind::Normal(b, bsize) => {
                  (pq == BIN_FULL || b == pq as int)
                  && valid_bin_idx(b as int)
                  && bsize == crate::bin_sizes::size_of_bin(b)
                  && bsize <= MEDIUM_OBJ_SIZE_MAX
              }
          }),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        final(local).pages.index(page.page_id@).inner.value().xblock_size ==
            old(local).pages.index(page.page_id@).inner.value().xblock_size,
        final(local).tld_id == old(local).tld_id,

        old(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx) ==>
            final(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx)
{
    unimplemented!()
}


//spec fn local_direct_no_change_needed(loc1: Local, loc2: Local, pq: int) -> bool {
//}

spec fn local_direct_update(loc1: Local, loc2: Local, i: int, j: int, pq: int) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { pages_free_direct: loc2.heap.pages_free_direct, .. loc1.heap }
    &&& loc1.heap.pages_free_direct.id() == loc2.heap.pages_free_direct.id()
    &&& pfd_direct_update(
          loc1.heap.pages_free_direct.value()@,
          loc2.heap.pages_free_direct.value()@, i, j,
            loc1.page_empty_global@.s.points_to.ptr(),
            loc1.heap.pages.value()@[pq].first)
}

spec fn pfd_direct_update(pfd1: Seq<*mut Page>, pfd2: Seq<*mut Page>, i: int, j: int, emp: *mut Page, p: *mut Page) -> bool {
    &&& pfd1.len() == pfd2.len() == PAGES_DIRECT
    &&& (forall |k|
        #![trigger(pfd1.index(k))]
        #![trigger(pfd2.index(k))]
      0 <= k < pfd1.len() && !(i <= k < j) ==> pfd1[k] == pfd2[k])
    &&& (forall |k| #![trigger pfd2.index(k)]
        0 <= k < pfd2.len() && i <= k < j ==>
            pages_free_direct_match(pfd2[k], p, emp))
}

#[verifier::external_body]
proof fn holds_on_present_value(local: Local, pq: int)
    requires local.wf_main(),
        valid_bin_idx(pq as int) || pq == BIN_FULL,
    ensures
        pq != BIN_FULL ==> (forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) ==>
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct.value()@[k],
                    local.heap.pages.value()@[pq].first,
                    local.page_empty_global@.s.points_to.ptr())
        )
{
    unimplemented!()
}

#[verifier::external_body]
fn heap_queue_first_update(heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>, Ghost(old_p): Ghost<*mut Page>)
    requires
        old(local).wf_basic(),
        heap.wf(),
        heap.is_in(*old(local)),
        valid_bin_idx(pq as int) || pq == BIN_FULL,
        pq != BIN_FULL ==> (forall |k: int| k < PAGES_DIRECT &&
            pfd_lower(pq as int) <= k <= pfd_upper(pq as int) ==>
                pages_free_direct_match(
                    #[trigger] old(local).heap.pages_free_direct.value()@[k],
                    old_p, old(local).page_empty_global@.s.points_to.ptr())
        ),
        //old_p.addr() != 0 &&
        //  old_p.addr() == old(local).heap.pages.value()@[pq as int].first.addr()
        //  ==> old_p == old(local).heap.pages.value()@[pq as int].first,
        //old_p.addr() == old(local).page_empty_global@.s.points_to.ptr().addr()
        //  ==> old_p == old(local).page_empty_global@.s.points_to.ptr(),
        //old(local).heap.pages.value()@[pq as int].first.addr()
        //      == old(local).page_empty_global@.s.points_to.ptr().addr()
        //  ==> old(local).heap.pages.value()@[pq as int].first
        //      == old(local).page_empty_global@.s.points_to.ptr()
    ensures
        pq == BIN_FULL ==> *final(local) == *old(local),
        pq != BIN_FULL ==> local_direct_update(*old(local), *final(local),
            pfd_lower(pq as int) as int,
            pfd_upper(pq as int) as int + 1,
            pq as int)
{
    unimplemented!()
}

/*
proof fn ptr_ineqs(old_p: *mut Page, pq: usize, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main(),
        pq == BIN_FULL || valid_bin_idx(pq as int),
    ensures
        *local == *old(local),
        old_p.addr() != 0 &&
          old_p.addr() == local.heap.pages.value()@[pq as int].first.addr()
          ==> old_p == local.heap.pages.value()@[pq as int].first,
        old_p.addr() == local.page_empty_global@.s.points_to.ptr().addr()
          ==> old_p == local.page_empty_global@.s.points_to.ptr(),
        local.heap.pages.value()@[pq as int].first.addr()
              == local.page_empty_global@.s.points_to.ptr().addr()
          ==> local.heap.pages.value()@[pq as int].first
              == local.page_empty_global@.s.points_to.ptr()
{
    if local.heap.pages.value()@[pq as int].first
        != local.page_empty_global@.s.points_to.ptr()
    {
        let page_id = local.page_organization.used_dlist_headers[pq as int].first.unwrap();
        let tracked pt = local.pages.tracked_remove(page_id);
        pt.points_to.is_disjoint(&local.page_empty_global.borrow().s.points_to);
        local.pages.tracked_insert(page_id, pt);
    }

    assert(local.pages =~= old(local).pages);
}
*/

}
