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


#[verifier::spinoff_prover]
#[verifier::external_body]
pub fn page_queue_remove(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
{
    let ghost page_id = page.page_id@;

    let prev = page.get_prev(Tracked(&*local));
    let next = page.get_next(Tracked(&*local));
    let ghost prev_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev;
    let ghost next_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next;

    if prev.addr() != 0 {
        let prev = PagePtr { page_ptr: prev, page_id: Ghost(prev_id.unwrap()) };
        //assert(prev.wf());
        //assert(prev.is_in(*local));
        used_page_get_mut_next!(prev, local, n => {
            n = next;
        });
    }

    if next.addr() != 0 {
        let next = PagePtr { page_ptr: next, page_id: Ghost(next_id.unwrap()) };
        //assert(next.wf());
        //assert(next.is_in(*local));
        used_page_get_mut_prev!(next, local, p => {
            p = prev;
        });
    }

    let ghost mut old_val;
    heap_get_pages!(heap, local, pages => {
        let mut cq = &mut pages[pq];


        if next.addr() == 0 {
            cq.last = prev;
        }
        if prev.addr() == 0 {
            cq.first = next;
        }
    });

    let ghost local_snap = *local;

    if prev.addr() == 0 {
        heap_queue_first_update(heap, pq, Tracked(&mut *local), Ghost(old_val));
    }

    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_sub(1));

    // These shouldn't be necessary:
    // page->next = NULL;
    // page->prev = NULL;
    // mi_page_set_in_full(page, false)

}

#[verifier::spinoff_prover]
#[verifier::external_body]
pub fn page_queue_push(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>)
{
    page_get_mut_inner!(page, local, inner => {
        inner.set_in_full(pq == BIN_FULL as usize);
    });

    let first_in_queue;

    heap_get_pages!(heap, local, pages => {
        let mut cq = &mut pages[pq];
        first_in_queue = cq.first;

        cq.first = page.page_ptr;
        if first_in_queue.addr() == 0 {
            cq.last = page.page_ptr;
        }
    });

    if first_in_queue.addr() != 0 {
        let first_in_queue_ptr = PagePtr { page_ptr: first_in_queue,
            page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };
        //assert(first_in_queue_ptr.wf());
        //assert(first_in_queue_ptr.is_in(*old(local)));
        used_page_get_mut_prev!(first_in_queue_ptr, local, p => {
            p = page.page_ptr;
        });
    }

    used_page_get_mut_prev!(page, local, p => {
        p = core::ptr::null_mut();
    });
    used_page_get_mut_next!(page, local, n => {
        n = first_in_queue;
    });

    let ghost local_snap = *local;

    heap_queue_first_update(heap, pq, Tracked(&mut *local), Ghost(first_in_queue));

    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_add(1));

}

#[verifier::spinoff_prover]
#[verifier::external_body]
pub fn page_queue_push_back(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(other_id): Ghost<PageId>, Ghost(other_pq): Ghost<int>, Ghost(other_list_idx): Ghost<int>)
{
    page_get_mut_inner!(page, local, inner => {
        inner.set_in_full(pq == BIN_FULL as usize);
    });

    let last_in_queue;

    heap_get_pages!(heap, local, pages => {
        let mut cq = &mut pages[pq];
        last_in_queue = cq.last;

        cq.last = page.page_ptr;
        if last_in_queue.addr() == 0 {
            cq.first = page.page_ptr;
        }
    });

    used_page_get_mut_next!(page, local, n => {
        n = core::ptr::null_mut();
    });
    used_page_get_mut_prev!(page, local, p => {
        p = last_in_queue;
    });

    if last_in_queue.addr() != 0 {
        let last_in_queue_ptr = PagePtr { page_ptr: last_in_queue,
            page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].last.unwrap()) };
        //assert(last_in_queue_ptr.wf());
        //assert(last_in_queue_ptr.is_in(*old(local)));
        used_page_get_mut_next!(last_in_queue_ptr, local, n => {
            n = page.page_ptr;
        });
    }

    let ghost local_snap = *local;

    if last_in_queue.addr() == 0 {
        heap_queue_first_update(heap, pq, Tracked(&mut *local), Ghost(core::ptr::null_mut()));
    }

    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_add(1));

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
    unimplemented!();
}

#[verifier::external_body]
fn heap_queue_first_update(heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>, Ghost(old_p): Ghost<*mut Page>)
{

    let size = heap.get_pages(Tracked(&*local))[pq].block_size;
    if size > SMALL_SIZE_MAX {
        return;
    }
    //assert(pq != BIN_FULL);

    let mut page_ptr = heap.get_pages(Tracked(&*local))[pq].first;
    //assert(page_ptr == old(local).heap.pages.value()@[pq as int].first);
    if page_ptr.addr() == 0 {
        let (_page, Tracked(emp)) = heap.get_page_empty(Tracked(&*local));
        page_ptr = _page;
    }

    let idx = size / 8;

    if heap.get_pages_free_direct(Tracked(&*local))[idx].addr() == page_ptr.addr() {
        /*proof {
            let i = pfd_lower(pq as int) as int;
            let j = pfd_upper(pq as int) as int + 1;
            assert(idx == j - 1);

            let loc1 = *old(local);
            let loc2 = *local;
            let pq = pq as int;
            let pfd1 = loc1.heap.pages_free_direct.value()@;
            let pfd2 = loc2.heap.pages_free_direct.value()@;
            let emp = loc1.page_empty_global@.s.points_to@.pptr;
            let p = loc1.heap.pages.value()@[pq].first.id();
            assert forall |k| #![trigger pfd2.index(k)]
                0 <= k < pfd2.len() && i <= k < j implies
                    pages_free_direct_match(pfd2[k].id(), p, emp)
            by {
                let z = idx as int;
                assert(pages_free_direct_match(pfd2[z].id(), p, emp));
                if p == 0 {
                    assert(pfd2[k].id() == emp);
                } else {
                    assert(pfd2[k].id() == p);
                }
            }
            assert(local_direct_update(loc1, loc2, i, j, pq));
        }*/
        //assert(page_ptr == old(local).heap.pages.value()@[pq as int].first);
        //assert(old_p.addr() == page_ptr.addr());
        //assert(old_p.addr() != 0);
        //assert(old_p == page_ptr);
        //assert(local.heap.pages_free_direct.value()@[idx as int] == page_ptr);
        return;
    }

    let start = if idx <= 1 {
        0
    } else {
        let b = bin(size);
        let prev = pq - 1;

        /*
        // for large minimal alignment, need to do something here
        loop
            invariant
                old(local).wf_basic(),
                heap.wf(),
                heap.is_in(*old(local)),
                0 <= prev <=
        {
            let prev_block_size = heap.get_pages(Tracked(&*local))[prev].block_size;
            if !(b == bin(prev_block_size) && prev > 0) {
                break;
            }
            prev = prev - 1;
        }*/

        let prev_block_size = heap.get_pages(Tracked(&*local))[prev].block_size;
        let s = 1 + prev_block_size / 8;
        s
        //let t = if s > idx { idx } else { s };
        //t
    };


    let mut sz = start;
    while sz <= idx
        invariant
            local.wf_basic(),
            heap.wf(),
            heap.is_in(*local),
            start <= sz <= idx + 1,
            idx < PAGES_DIRECT,
            local_direct_update(*old(local), *local, start as int, sz as int, pq as int),
            page_ptr as int != 0,
            pages_free_direct_match(page_ptr,
                old(local).heap.pages.value()@[pq as int].first,
                local.page_empty_global@.s.points_to.ptr()),
    {
        let ghost prev_local = *local;
        heap_get_pages_free_direct!(heap, local, pages_free_direct => {
            pages_free_direct[sz] = page_ptr;
        });

        sz += 1;
    }
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
