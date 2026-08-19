#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId, PageState, SegmentId};
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
#[verifier::rlimit(200)]
#[verus_verify]
pub fn page_queue_remove(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        valid_bin_idx(pq as int) || pq == BIN_FULL as usize,
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        final(local).wf_main_for_page_access(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        final(local).block_size(page.page_id@) == old(local).block_size(page.page_id@),
        old(local).page_organization.pages[page.page_id@].dlist_entry.unwrap().next.is_some() ==>
            final(local).page_organization.valid_used_page(
                old(local).page_organization.pages[page.page_id@].dlist_entry.unwrap().next.unwrap(),
                pq as int,
                list_idx),
        final(local).page_organization.popped == Popped::Used(page.page_id@, true),
        final(local).page_organization.pages[page.page_id@].page_header_kind
            == old(local).page_organization.pages[page.page_id@].page_header_kind,
        forall |sid: SegmentId| #[trigger] final(local).segments.dom().contains(sid) ==>
            final(local).mem_chunk_good(sid),
        match final(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) =>
                valid_bin_idx(bin)
                && size == size_of_bin(bin)
                && bin == smallest_bin_fitting_size(size)
                && size <= MEDIUM_OBJ_SIZE_MAX,
            None => false,
        },
{
    let ghost page_id = page.page_id@;
    let ghost pre_org = local.page_organization;
    let ghost next_state = PageOrg::take_step::out_of_used_list(
        pre_org, page_id, pq as int, list_idx);

    proof {
        reveal(PageOrg::State::valid_used_page);
        reveal(PageOrg::State::ll_basics);
        pre_org.used_ll_stuff(pq as int, list_idx);
        pre_org.used_page_dlist_facts(page_id, pq as int, list_idx);
        pre_org.first_last_ll_stuff_used(pq as int);
    }

    let prev = page.get_prev(Tracked(&*local));
    let next = page.get_next(Tracked(&*local));
    let ghost prev_id = local.page_organization.pages[page_id].dlist_entry.unwrap().prev;
    let ghost next_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next;

    if prev.addr() != 0 {
        let prev = PagePtr { page_ptr: prev, page_id: Ghost(prev_id.unwrap()) };
        proof {
            assert(is_page_ptr_opt(prev.page_ptr, Some(prev.page_id@)));
            assert(prev.wf());
            assert(pre_org.pages.dom().contains(prev.page_id@));
            assert(local.pages.dom().contains(prev.page_id@));
            assert(prev.is_in(*local));
        }
        used_page_get_mut_next!(prev, local, n => {
            n = next;
        });
    }

    if next.addr() != 0 {
        let next = PagePtr { page_ptr: next, page_id: Ghost(next_id.unwrap()) };
        proof {
            assert(is_page_ptr_opt(next.page_ptr, Some(next.page_id@)));
            assert(next.wf());
            assert(pre_org.pages.dom().contains(next.page_id@));
            assert(local.pages.dom().contains(next.page_id@));
            assert(next.is_in(*local));
        }
        used_page_get_mut_prev!(next, local, p => {
            p = prev;
        });
    }

    let ghost old_val = local.heap.pages.value()@[pq as int].first;
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

    let ghost local_before_count = *local;
    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_sub(1));

    // These shouldn't be necessary:
    // page->next = NULL;
    // page->prev = NULL;
    // mi_page_set_in_full(page, false)

    proof {
        local.page_organization = next_state;
        assert(local.page_organization.invariant());
        assert(PageOrg::State::out_of_used_list_strong(
            pre_org, local.page_organization, page_id, pq as int, list_idx));
        if pre_org.pages[page_id].dlist_entry.unwrap().next.is_some() {
            let ghost next_page_id = pre_org.pages[page_id].dlist_entry.unwrap().next.unwrap();
            pre_org.used_next_is_in(page_id, pq as int, list_idx);
            assert(pre_org.valid_used_page(next_page_id, pq as int, list_idx + 1));
            PageOrg::State::preserved_by_out_of_used_list(
                pre_org, local.page_organization, page_id, pq as int, list_idx, next_page_id);
        }
        assert(local.page_organization.popped == Popped::Used(page_id, true));
        assert(local.page_organization.pages[page_id].page_header_kind
            == pre_org.pages[page_id].page_header_kind);
        match pre_org.pages[page_id].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) => {
                reveal(PageOrg::State::valid_used_page);
                assert(valid_bin_idx(bin));
                assert(size == size_of_bin(bin));
                assert(bin == smallest_bin_fitting_size(size));
                assert(size <= MEDIUM_OBJ_SIZE_MAX);
            }
            None => { assert(false); }
        }
        assert(common_preserves(*old(local), *local));
        assert(local.inst() == old(local).inst());
        assert(heap.is_in(*local));
        assert(page.is_in(*local));

        reveal(Local::page_organization_valid);
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by {
            if pid == page_id {
                assert(local.page_organization.pages[pid].is_used);
                assert(!local.unused_pages.dom().contains(pid));
            }
        };
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { };
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { };
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { };
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(local.page_organization_valid());

        reveal(Local::wf_main_for_page_access);
        assert(local.wf_basic());
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(HeapLocalAccess::wf);
        reveal(pages_free_direct_is_correct);
        reveal(pages_free_direct_match);
        assert((*old(local)).heap.wf(
            (*old(local)).heap_id,
            (*old(local)).thread_token.value().heap,
            (*old(local)).tld_id,
            (*old(local)).instance.id(),
            (*old(local)).page_empty_global@.s.points_to.ptr()));
        assert(local.heap.pages.value()@ == local_before_count.heap.pages.value()@);
        assert(local.heap.pages_free_direct.value()@ == local_before_count.heap.pages_free_direct.value()@);
        assert(local.page_empty_global@.s.points_to.ptr() == local_before_count.page_empty_global@.s.points_to.ptr());
        assert(pages_free_direct_is_correct(
            local.heap.pages_free_direct.value()@,
            local.heap.pages.value()@,
            local.page_empty_global@.s.points_to.ptr())) by {
            assert(local.heap.pages_free_direct.value()@.len() == PAGES_DIRECT);
            assert(local.heap.pages.value()@.len() == BIN_FULL + 1);
            assert forall |wsize: int|
                0 <= wsize < local.heap.pages_free_direct.value()@.len()
            implies
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct.value()@[wsize],
                    local.heap.pages.value()@[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
                    local.page_empty_global@.s.points_to.ptr())
            by {
                direct_wsize_bin_bounds(wsize);
                let bin_idx = smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                assert(bin_idx < BIN_FULL);
                assert(local.page_empty_global@.s.points_to.ptr() == (*old(local)).page_empty_global@.s.points_to.ptr());
                if bin_idx == pq as int {
                    assert(valid_bin_idx(pq as int));
                    if !(pfd_lower(pq as int) <= wsize <= pfd_upper(pq as int)) {
                        pfd_out_of_range_has_different_bin_size(pq as int, wsize);
                        assert(false);
                    }
                    if prev.addr() == 0 {
                        assert(local.heap.pages.value()@[pq as int].first == local_before_count.heap.pages.value()@[pq as int].first);
                        assert(local_before_count.heap.pages.value()@[pq as int].first == local_snap.heap.pages.value()@[pq as int].first);
                        if local_snap.heap.pages.value()@[pq as int].block_size > SMALL_SIZE_MAX {
                            assert(local_snap.heap.pages.value()@[pq as int].block_size == size_of_bin(pq as int));
                            pfd_lower_above_direct_for_large_bin(pq as int);
                            assert(false);
                        }
                        if valid_bin_idx(pq as int) && local_direct_update(
                            local_snap,
                            local_before_count,
                            pfd_lower(pq as int) as int,
                            pfd_upper(pq as int) as int + 1,
                            pq as int) {
                            assert(pages_free_direct_match(
                                local_before_count.heap.pages_free_direct.value()@[wsize],
                                local_snap.heap.pages.value()@[pq as int].first,
                                local_snap.page_empty_global@.s.points_to.ptr()));
                        } else {
                            assert(local_before_count == local_snap);
                            assert(is_page_ptr_opt(prev, prev_id));
                            assert(prev_id.is_none());
                            pre_org.used_page_dlist_facts(page_id, pq as int, list_idx);
                            assert(list_idx == 0);
                            assert(pre_org.used_dlist_headers[pq as int].first == Some(page_id));
                            assert(is_page_ptr_opt(
                                (*old(local)).heap.pages.value()@[pq as int].first,
                                pre_org.used_dlist_headers[pq as int].first));
                            assert(is_page_ptr((*old(local)).heap.pages.value()@[pq as int].first, page_id));
                            assert((*old(local)).heap.pages.value()@[pq as int].first.addr() != 0);
                            assert(local_snap.heap.pages.value()@[pq as int].first == next);
                            assert(pages_free_direct_match(
                                local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                                local_before_count.heap.pages.value()@[pq as int].first,
                                local_before_count.page_empty_global@.s.points_to.ptr()));
                            assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int]
                                == (*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int]);
                            small_bin_pfd_range_nonempty(pq as int);
                            pfd_range_has_bin_size(pq as int, pfd_upper(pq as int) as int);
                            assert(0 <= pfd_upper(pq as int) < (*old(local)).heap.pages_free_direct.value()@.len());
                            assert(smallest_bin_fitting_size((pfd_upper(pq as int) as int) * INTPTR_SIZE) == pq as int);
                            assert(pages_free_direct_match(
                                (*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                                (*old(local)).heap.pages.value()@[pq as int].first,
                                (*old(local)).page_empty_global@.s.points_to.ptr()));
                            assert(pages_free_direct_match(
                                (*old(local)).heap.pages_free_direct.value()@[wsize],
                                (*old(local)).heap.pages.value()@[pq as int].first,
                                (*old(local)).page_empty_global@.s.points_to.ptr()));
                            reveal(pages_free_direct_match);
                            if local_before_count.heap.pages.value()@[pq as int].first.addr() == 0 {
                                assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                                    == local_before_count.page_empty_global@.s.points_to.ptr() as int);
                                assert((*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                                    == (*old(local)).heap.pages.value()@[pq as int].first as int);
                                assert((*old(local)).heap.pages_free_direct.value()@[wsize] as int
                                    == (*old(local)).heap.pages.value()@[pq as int].first as int);
                                assert((*old(local)).heap.pages.value()@[pq as int].first as int
                                    == local_before_count.page_empty_global@.s.points_to.ptr() as int);
                            } else {
                                assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                                    == local_before_count.heap.pages.value()@[pq as int].first as int);
                                assert((*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                                    == (*old(local)).heap.pages.value()@[pq as int].first as int);
                                assert((*old(local)).heap.pages_free_direct.value()@[wsize] as int
                                    == (*old(local)).heap.pages.value()@[pq as int].first as int);
                                assert((*old(local)).heap.pages.value()@[pq as int].first as int
                                    == local_before_count.heap.pages.value()@[pq as int].first as int);
                            }
                            assert(local.heap.pages_free_direct.value()@[wsize]
                                == local_before_count.heap.pages_free_direct.value()@[wsize]);
                            assert(local.heap.pages.value()@[pq as int].first
                                == local_before_count.heap.pages.value()@[pq as int].first);
                            assert(local.page_empty_global@.s.points_to.ptr()
                                == local_before_count.page_empty_global@.s.points_to.ptr());
                            assert(pages_free_direct_match(
                                local.heap.pages_free_direct.value()@[wsize],
                                local.heap.pages.value()@[pq as int].first,
                                local.page_empty_global@.s.points_to.ptr()));
                        }
                    } else {
                        assert(local.heap.pages.value()@[pq as int].first == (*old(local)).heap.pages.value()@[pq as int].first);
                        assert(local.heap.pages_free_direct.value()@[wsize] == (*old(local)).heap.pages_free_direct.value()@[wsize]);
                        assert(pages_free_direct_match(
                            (*old(local)).heap.pages_free_direct.value()@[wsize],
                            (*old(local)).heap.pages.value()@[pq as int].first,
                            (*old(local)).page_empty_global@.s.points_to.ptr()));
                    }
                } else {
                    if prev.addr() == 0 {
                        if valid_bin_idx(pq as int) && local_direct_update(
                            local_snap,
                            local_before_count,
                            pfd_lower(pq as int) as int,
                            pfd_upper(pq as int) as int + 1,
                            pq as int) {
                            if pfd_lower(pq as int) <= wsize <= pfd_upper(pq as int) {
                                assert(valid_bin_idx(pq as int));
                                pfd_range_has_bin_size(pq as int, wsize);
                                assert(false);
                            }
                            assert(local_before_count.heap.pages_free_direct.value()@[wsize]
                                == local_snap.heap.pages_free_direct.value()@[wsize]);
                        } else {
                            assert(local_before_count == local_snap);
                        }
                    }
                    assert(local.heap.pages.value()@[bin_idx].first == (*old(local)).heap.pages.value()@[bin_idx].first);
                    assert(local.heap.pages_free_direct.value()@[wsize] == (*old(local)).heap.pages_free_direct.value()@[wsize]);
                    assert(pages_free_direct_match(
                        (*old(local)).heap.pages_free_direct.value()@[wsize],
                        (*old(local)).heap.pages.value()@[bin_idx].first,
                        (*old(local)).page_empty_global@.s.points_to.ptr()));
                }
            };
        };
        assert(local.heap.wf(
            local.heap_id,
            local.thread_token.value().heap,
            local.tld_id,
            local.instance.id(),
            local.page_empty_global@.s.points_to.ptr()));
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid)
        by {
            assert((*old(local)).segments.dom().contains(sid));
            assert((*old(local)).mem_chunk_good(sid));
            assert(local.segments == (*old(local)).segments);
            assert(local.page_organization.pages.dom() == (*old(local)).page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == (*old(local)).is_used_primary(pid)
            by {
                reveal(Local::is_used_primary);
                assert(local.page_organization.pages[pid].is_used == (*old(local)).page_organization.pages[pid].is_used);
                assert(local.page_organization.pages[pid].offset == (*old(local)).page_organization.pages[pid].offset);
            };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_count(pid) == (*old(local)).page_count(pid)
            by { };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_capacity(pid) == (*old(local)).page_capacity(pid)
            by { };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.block_size(pid) == (*old(local)).block_size(pid)
            by { };
            local.used_queue_update_preserves_mem_chunk_good(*old(local), sid);
        };
        assert(local.thread_id == local.is_thread@);
        assert(local.checked_token.instance_id() == local.instance.id());
        assert(local.checked_token.key() == local.thread_id);
        assert(local.my_inst.instance_id() == local.instance.id());
        assert(local.my_inst.value() == local.instance.id());
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { };
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { };
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { };
        assert(local.tld.is_init());
        assert(local.page_empty_global@.wf_empty_page_global());
        assert(local.wf_main_for_page_access());
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
pub fn page_queue_push(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf_main_for_page_access(),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        valid_bin_idx(pq as int),
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        match old(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) =>
                pq as int == bin
                && valid_bin_idx(bin)
                && size == size_of_bin(bin)
                && bin == smallest_bin_fitting_size(size)
                && size <= MEDIUM_OBJ_SIZE_MAX,
            None => false,
        },
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        final(local).block_size(page.page_id@) == old(local).block_size(page.page_id@),
{
    let ghost page_id = page.page_id@;
    let ghost pre_org = local.page_organization;
    let ghost next_state = PageOrg::take_step::into_used_list(pre_org, pq as int);
    proof {
        reveal(PageOrg::State::ll_basics);
        reveal(PageOrg::State::inv_used);
        pre_org.first_last_ll_stuff_used(pq as int);
    }

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

    let ghost local_before_count = *local;
    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_add(1));

    proof {
        local.page_organization = next_state;
        assert(local.page_organization.invariant());
        assert(local.page_organization.popped == Popped::No);
        assert(common_preserves(*old(local), *local));
        assert(local.inst() == old(local).inst());
        assert(heap.is_in(*local));
        assert(page.is_in(*local));

        reveal(Local::page_organization_valid);
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { };
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { };
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { };
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { };
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(local.page_organization_valid());

        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(HeapLocalAccess::wf);
        reveal(pages_free_direct_is_correct);
        reveal(pages_free_direct_match);
        assert(local.heap.pages.value()@ == local_before_count.heap.pages.value()@);
        assert(local.heap.pages_free_direct.value()@ == local_before_count.heap.pages_free_direct.value()@);
        assert(pages_free_direct_is_correct(
            local.heap.pages_free_direct.value()@,
            local.heap.pages.value()@,
            local.page_empty_global@.s.points_to.ptr())) by {
            assert(local.heap.pages_free_direct.value()@.len() == PAGES_DIRECT);
            assert(local.heap.pages.value()@.len() == BIN_FULL + 1);
            assert forall |wsize: int|
                0 <= wsize < local.heap.pages_free_direct.value()@.len()
            implies
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct.value()@[wsize],
                    local.heap.pages.value()@[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
                    local.page_empty_global@.s.points_to.ptr())
            by {
                direct_wsize_bin_bounds(wsize);
                let bin_idx = smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                let emp = local.page_empty_global@.s.points_to.ptr();
                assert(0 <= bin_idx < BIN_FULL);
                assert(emp == (*old(local)).page_empty_global@.s.points_to.ptr());
                if bin_idx == pq as int {
                    assert(valid_bin_idx(pq as int));
                    if (*old(local)).heap.pages.value()@[pq as int].block_size > SMALL_SIZE_MAX {
                        assert((*old(local)).heap.pages.value()@[pq as int].block_size == size_of_bin(pq as int));
                        pfd_lower_above_direct_for_large_bin(pq as int);
                        assert(wsize < pfd_lower(pq as int));
                        pfd_out_of_range_has_different_bin_size(pq as int, wsize);
                        assert(false);
                    }
                    small_bin_pfd_range_nonempty(pq as int);
                    if !(pfd_lower(pq as int) <= wsize <= pfd_upper(pq as int)) {
                        pfd_out_of_range_has_different_bin_size(pq as int, wsize);
                        assert(false);
                    }
                    assert(local.heap.pages.value()@[pq as int].first == local_snap.heap.pages.value()@[pq as int].first);
                    assert(local_direct_update(
                        local_snap,
                        local_before_count,
                        pfd_lower(pq as int) as int,
                        pfd_upper(pq as int) as int + 1,
                        pq as int) || local_before_count == local_snap);
                    if local_direct_update(
                        local_snap,
                        local_before_count,
                        pfd_lower(pq as int) as int,
                        pfd_upper(pq as int) as int + 1,
                        pq as int) {
                        assert(pages_free_direct_match(
                            local_before_count.heap.pages_free_direct.value()@[wsize],
                            local_snap.heap.pages.value()@[pq as int].first,
                            emp));
                    } else {
                        assert(local_before_count == local_snap);
                        assert(local_before_count.heap.pages.value()@[pq as int].first == page.page_ptr);
                        assert(page.page_ptr.addr() != 0);
                        assert(pages_free_direct_match(
                            local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                            local_before_count.heap.pages.value()@[pq as int].first,
                            emp));
                        assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                            == page.page_ptr as int);
                        assert(0 <= pfd_upper(pq as int) < (*old(local)).heap.pages_free_direct.value()@.len());
                        pfd_range_has_bin_size(pq as int, pfd_upper(pq as int) as int);
                        assert(smallest_bin_fitting_size((pfd_upper(pq as int) as int) * INTPTR_SIZE) == pq as int);
                        assert(pages_free_direct_is_correct(
                            (*old(local)).heap.pages_free_direct.value()@,
                            (*old(local)).heap.pages.value()@,
                            emp));
                        assert(pages_free_direct_match(
                            (*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                            (*old(local)).heap.pages.value()@[pq as int].first,
                            emp));
                        assert(pages_free_direct_match(
                            (*old(local)).heap.pages_free_direct.value()@[wsize],
                            (*old(local)).heap.pages.value()@[pq as int].first,
                            emp));
                        assert(local_before_count.heap.pages_free_direct.value()@[wsize]
                            == (*old(local)).heap.pages_free_direct.value()@[wsize]);
                        assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int]
                            == (*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int]);
                        if (*old(local)).heap.pages.value()@[pq as int].first.addr() == 0 {
                            assert((*old(local)).heap.pages_free_direct.value()@[wsize] as int == emp as int);
                            assert((*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int == emp as int);
                        } else {
                            assert((*old(local)).heap.pages_free_direct.value()@[wsize] as int
                                == (*old(local)).heap.pages.value()@[pq as int].first as int);
                            assert((*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                                == (*old(local)).heap.pages.value()@[pq as int].first as int);
                        }
                        assert(local_before_count.heap.pages_free_direct.value()@[wsize] as int == page.page_ptr as int);
                        assert(pages_free_direct_match(
                            local.heap.pages_free_direct.value()@[wsize],
                            local.heap.pages.value()@[pq as int].first,
                            emp));
                    }
                } else {
                    if local_direct_update(
                        local_snap,
                        local_before_count,
                        pfd_lower(pq as int) as int,
                        pfd_upper(pq as int) as int + 1,
                        pq as int) {
                        if pfd_lower(pq as int) <= wsize <= pfd_upper(pq as int) {
                            pfd_range_has_bin_size(pq as int, wsize);
                            assert(false);
                        }
                        assert(local_before_count.heap.pages_free_direct.value()@[wsize]
                            == local_snap.heap.pages_free_direct.value()@[wsize]);
                    } else {
                        assert(local_before_count == local_snap);
                    }
                    assert(local.heap.pages.value()@[bin_idx].first == (*old(local)).heap.pages.value()@[bin_idx].first);
                    assert(local.heap.pages_free_direct.value()@[wsize] == (*old(local)).heap.pages_free_direct.value()@[wsize]);
                    assert(pages_free_direct_match(
                        (*old(local)).heap.pages_free_direct.value()@[wsize],
                        (*old(local)).heap.pages.value()@[bin_idx].first,
                        emp));
                }
            };
        };
        assert(local.heap.wf(
            local.heap_id,
            local.thread_token.value().heap,
            local.tld_id,
            local.instance.id(),
            local.page_empty_global@.s.points_to.ptr()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { };
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { };
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid)
        by {
            assert((*old(local)).segments.dom().contains(sid));
            assert((*old(local)).mem_chunk_good(sid));
            assert(local.segments == (*old(local)).segments);
            assert(local.page_organization.pages.dom() == (*old(local)).page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == (*old(local)).is_used_primary(pid)
            by {
                reveal(Local::is_used_primary);
                assert(local.page_organization.pages[pid].is_used == (*old(local)).page_organization.pages[pid].is_used);
                assert(local.page_organization.pages[pid].offset == (*old(local)).page_organization.pages[pid].offset);
            };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_count(pid) == (*old(local)).page_count(pid)
            by { };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_capacity(pid) == (*old(local)).page_capacity(pid)
            by { };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.block_size(pid) == (*old(local)).block_size(pid)
            by { };
            local.used_queue_update_preserves_mem_chunk_good(*old(local), sid);
        };
        assert(local.wf_main());
        assert(local.wf());
        assert(page.is_used_and_primary(*local));
        assert(local.block_size(page_id) == (*old(local)).block_size(page_id));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn page_queue_push_back(heap: HeapPtr, pq: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(other_id): Ghost<PageId>, Ghost(other_pq): Ghost<int>, Ghost(other_list_idx): Ghost<int>)
    requires
        old(local).wf_main_for_page_access(),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
        page.is_in(*old(local)),
        valid_bin_idx(pq as int) || pq == BIN_FULL as usize,
        old(local).page_organization.popped == Popped::Used(page.page_id@, true),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) ==>
            old(local).mem_chunk_good(sid),
        match old(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) =>
                (pq as int != BIN_FULL ==> pq as int == bin)
                && valid_bin_idx(bin)
                && size == size_of_bin(bin)
                && bin == smallest_bin_fitting_size(size)
                && size <= MEDIUM_OBJ_SIZE_MAX,
            None => false,
        },
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        page.wf(),
        page.is_in(*final(local)),
        page.is_used_and_primary(*final(local)),
        other_id != page.page_id@ && old(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx) ==>
            final(local).page_organization.valid_used_page(other_id, other_pq, other_list_idx),
{
    let ghost page_id = page.page_id@;
    let ghost pre_org = local.page_organization;
    let ghost next_state = PageOrg::take_step::into_used_list_back(pre_org, pq as int);
    proof {
        reveal(PageOrg::State::ll_basics);
        pre_org.first_last_ll_stuff_used(pq as int);
    }

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

    let ghost local_before_count = *local;
    let c = heap.get_page_count(Tracked(&*local));
    heap.set_page_count(Tracked(&mut *local), c.wrapping_add(1));

    proof {
        local.page_organization = next_state;
        assert(local.page_organization.invariant());
        assert(PageOrg::State::into_used_list_back_strong(pre_org, local.page_organization, pq as int));
        if other_id != page_id && pre_org.valid_used_page(other_id, other_pq, other_list_idx) {
            PageOrg::State::preserved_by_into_used_list_back(
                pre_org, local.page_organization, pq as int, other_id, other_pq, other_list_idx);
        }
        assert(local.page_organization.popped == Popped::No);
        assert(common_preserves(*old(local), *local));
        assert(local.inst() == old(local).inst());
        assert(heap.is_in(*local));
        assert(page.is_in(*local));

        reveal(Local::page_organization_valid);
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by { };
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { };
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { };
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by { };
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(local.page_organization_valid());

        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(HeapLocalAccess::wf);
        reveal(pages_free_direct_is_correct);
        reveal(pages_free_direct_match);
        assert(local.heap.pages.value()@ == local_before_count.heap.pages.value()@);
        assert(local.heap.pages_free_direct.value()@ == local_before_count.heap.pages_free_direct.value()@);
        assert(pages_free_direct_is_correct(
            local.heap.pages_free_direct.value()@,
            local.heap.pages.value()@,
            local.page_empty_global@.s.points_to.ptr())) by {
            assert(local.heap.pages_free_direct.value()@.len() == PAGES_DIRECT);
            assert(local.heap.pages.value()@.len() == BIN_FULL + 1);
            assert forall |wsize: int|
                0 <= wsize < local.heap.pages_free_direct.value()@.len()
            implies
                pages_free_direct_match(
                    #[trigger] local.heap.pages_free_direct.value()@[wsize],
                    local.heap.pages.value()@[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
                    local.page_empty_global@.s.points_to.ptr())
            by {
                direct_wsize_bin_bounds(wsize);
                let bin_idx = smallest_bin_fitting_size(wsize * INTPTR_SIZE);
                let emp = local.page_empty_global@.s.points_to.ptr();
                assert(0 <= bin_idx < BIN_FULL);
                assert(emp == (*old(local)).page_empty_global@.s.points_to.ptr());
                if bin_idx == pq as int {
                    if pq == BIN_FULL as usize {
                        assert(BIN_FULL as int == pq as int);
                        assert(false);
                    }
                    assert(valid_bin_idx(pq as int));
                    if (*old(local)).heap.pages.value()@[pq as int].block_size > SMALL_SIZE_MAX {
                        assert((*old(local)).heap.pages.value()@[pq as int].block_size == size_of_bin(pq as int));
                        pfd_lower_above_direct_for_large_bin(pq as int);
                        assert(wsize < pfd_lower(pq as int));
                        pfd_out_of_range_has_different_bin_size(pq as int, wsize);
                        assert(false);
                    }
                    small_bin_pfd_range_nonempty(pq as int);
                    if !(pfd_lower(pq as int) <= wsize <= pfd_upper(pq as int)) {
                        pfd_out_of_range_has_different_bin_size(pq as int, wsize);
                        assert(false);
                    }
                    if last_in_queue.addr() == 0 {
                        assert(local.heap.pages.value()@[pq as int].first == local_snap.heap.pages.value()@[pq as int].first);
                        assert(local_direct_update(
                            local_snap,
                            local_before_count,
                            pfd_lower(pq as int) as int,
                            pfd_upper(pq as int) as int + 1,
                            pq as int) || local_before_count == local_snap);
                        if local_direct_update(
                            local_snap,
                            local_before_count,
                            pfd_lower(pq as int) as int,
                            pfd_upper(pq as int) as int + 1,
                            pq as int) {
                            assert(pages_free_direct_match(
                                local_before_count.heap.pages_free_direct.value()@[wsize],
                                local_snap.heap.pages.value()@[pq as int].first,
                                emp));
                        } else {
                            assert(local_before_count == local_snap);
                            assert(pages_free_direct_match(
                                local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                                local_before_count.heap.pages.value()@[pq as int].first,
                                emp));
                            assert(pages_free_direct_match(
                                (*old(local)).heap.pages_free_direct.value()@[wsize],
                                (*old(local)).heap.pages.value()@[pq as int].first,
                                emp));
                            assert((*old(local)).heap.pages_free_direct.value()@[wsize]
                                == local_before_count.heap.pages_free_direct.value()@[wsize]);
                            assert((*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int]
                                == local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int]);
                            assert(last_in_queue == (*old(local)).heap.pages.value()@[pq as int].last);
                            assert(is_page_ptr_opt(
                                (*old(local)).heap.pages.value()@[pq as int].last,
                                pre_org.used_dlist_headers[pq as int].last));
                            assert(pre_org.used_dlist_headers[pq as int].last.is_none());
                            assert(pre_org.used_dlist_headers[pq as int].first.is_none());
                            assert(is_page_ptr_opt(
                                (*old(local)).heap.pages.value()@[pq as int].first,
                                pre_org.used_dlist_headers[pq as int].first));
                            assert((*old(local)).heap.pages.value()@[pq as int].first.addr() == 0);
                            assert(0 <= pfd_upper(pq as int) < (*old(local)).heap.pages_free_direct.value()@.len());
                            pfd_range_has_bin_size(pq as int, pfd_upper(pq as int) as int);
                            assert(smallest_bin_fitting_size((pfd_upper(pq as int) as int) * INTPTR_SIZE) == pq as int);
                            assert(pages_free_direct_is_correct(
                                (*old(local)).heap.pages_free_direct.value()@,
                                (*old(local)).heap.pages.value()@,
                                emp));
                            assert(pages_free_direct_match(
                                (*old(local)).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                                (*old(local)).heap.pages.value()@[pq as int].first,
                                emp));
                            if local_before_count.heap.pages.value()@[pq as int].first.addr() == 0 {
                                assert(pages_free_direct_match(
                                    local_before_count.heap.pages_free_direct.value()@[wsize],
                                    local_before_count.heap.pages.value()@[pq as int].first,
                                    emp));
                            } else {
                                assert(local_before_count.heap.pages_free_direct.value()@[wsize] as int == emp as int);
                                assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int == emp as int);
                                assert(local_before_count.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int] as int
                                    == local_before_count.heap.pages.value()@[pq as int].first as int);
                                assert(local_before_count.heap.pages.value()@[pq as int].first as int == emp as int);
                                assert(pages_free_direct_match(
                                    local_before_count.heap.pages_free_direct.value()@[wsize],
                                    local_before_count.heap.pages.value()@[pq as int].first,
                                    emp));
                            }
                        }
                    } else {
                        assert(local.heap.pages.value()@[pq as int].first == (*old(local)).heap.pages.value()@[pq as int].first);
                        assert(local.heap.pages_free_direct.value()@[wsize] == (*old(local)).heap.pages_free_direct.value()@[wsize]);
                        assert(pages_free_direct_match(
                            (*old(local)).heap.pages_free_direct.value()@[wsize],
                            (*old(local)).heap.pages.value()@[pq as int].first,
                            emp));
                    }
                } else {
                    if last_in_queue.addr() == 0 && valid_bin_idx(pq as int) {
                        if pfd_lower(pq as int) <= wsize <= pfd_upper(pq as int) {
                            pfd_range_has_bin_size(pq as int, wsize);
                            assert(false);
                        }
                    }
                    assert(local.heap.pages.value()@[bin_idx].first == (*old(local)).heap.pages.value()@[bin_idx].first);
                    assert(local.heap.pages_free_direct.value()@[wsize] == (*old(local)).heap.pages_free_direct.value()@[wsize]);
                    assert(pages_free_direct_match(
                        (*old(local)).heap.pages_free_direct.value()@[wsize],
                        (*old(local)).heap.pages.value()@[bin_idx].first,
                        emp));
                }
            };
        };
        assert(local.heap.wf(
            local.heap_id,
            local.thread_token.value().heap,
            local.tld_id,
            local.instance.id(),
            local.page_empty_global@.s.points_to.ptr()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            (local.unused_pages.dom().contains(pid) <==> !local.thread_token.value().pages.dom().contains(pid))
        by { };
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by { };
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by { };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid)
        by {
            assert((*old(local)).segments.dom().contains(sid));
            assert((*old(local)).mem_chunk_good(sid));
            assert(local.segments == (*old(local)).segments);
            assert(local.page_organization.pages.dom() == (*old(local)).page_organization.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.is_used_primary(pid) == (*old(local)).is_used_primary(pid)
            by {
                if pid == page_id {
                    reveal(Local::is_used_primary);
                    assert(local.page_organization.pages[pid].is_used == (*old(local)).page_organization.pages[pid].is_used);
                    assert(local.page_organization.pages[pid].offset == (*old(local)).page_organization.pages[pid].offset);
                } else {
                    reveal(Local::is_used_primary);
                    assert(local.page_organization.pages[pid].is_used == (*old(local)).page_organization.pages[pid].is_used);
                    assert(local.page_organization.pages[pid].offset == (*old(local)).page_organization.pages[pid].offset);
                }
            };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_count(pid) == (*old(local)).page_count(pid)
            by { };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.page_capacity(pid) == (*old(local)).page_capacity(pid)
            by { };
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                local.block_size(pid) == (*old(local)).block_size(pid)
            by { };
            local.used_queue_update_preserves_mem_chunk_good(*old(local), sid);
        };
        assert(local.wf_main());
        assert(local.wf());
        assert(page.is_used_and_primary(*local));
    }
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

}

verus!{
#[cfg(any())]
#[verus_verify]
fn heap_queue_first_update(heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>, Ghost(old_p): Ghost<*mut Page>)
    requires
        old(local).wf_basic(),
        heap.wf(),
        heap.is_in(*old(local)),
        0 <= pq < BIN_FULL + 1,
    ensures
        final(local).wf_basic(),
        common_preserves(*old(local), *final(local)),
        heap.wf(),
        heap.is_in(*final(local)),
        *final(local) == (Local { heap: final(local).heap, ..*old(local) }),
        final(local).heap == (HeapLocalAccess { pages_free_direct: final(local).heap.pages_free_direct, ..old(local).heap }),
        old(local).heap.pages_free_direct.id() == final(local).heap.pages_free_direct.id(),
        old(local).heap.pages.value()@[pq as int].block_size > SMALL_SIZE_MAX ==> *final(local) == *old(local),
        valid_bin_idx(pq as int)
            && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX
            ==> local_direct_update(
                *old(local),
                *final(local),
                pfd_lower(pq as int) as int,
                pfd_upper(pq as int) as int + 1,
                pq as int)
                || *final(local) == *old(local),
        valid_bin_idx(pq as int)
            && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX
            && *final(local) == *old(local)
            ==> pages_free_direct_match(
                final(local).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                final(local).heap.pages.value()@[pq as int].first,
                final(local).page_empty_global@.s.points_to.ptr()),
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

}

#[cfg(not(any()))]
verus!{
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn heap_queue_first_update(heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>, Ghost(old_p): Ghost<*mut Page>)
    requires
        old(local).wf_basic(),
        heap.wf(),
        heap.is_in(*old(local)),
        0 <= pq < BIN_FULL + 1,
    ensures
        final(local).wf_basic(),
        common_preserves(*old(local), *final(local)),
        heap.wf(),
        heap.is_in(*final(local)),
        *final(local) == (Local { heap: final(local).heap, ..*old(local) }),
        final(local).heap == (HeapLocalAccess { pages_free_direct: final(local).heap.pages_free_direct, ..old(local).heap }),
        old(local).heap.pages_free_direct.id() == final(local).heap.pages_free_direct.id(),
        old(local).heap.pages.value()@[pq as int].block_size > SMALL_SIZE_MAX ==> *final(local) == *old(local),
        valid_bin_idx(pq as int)
            && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX
            ==> local_direct_update(
                *old(local),
                *final(local),
                pfd_lower(pq as int) as int,
                pfd_upper(pq as int) as int + 1,
                pq as int)
                || *final(local) == *old(local),
        valid_bin_idx(pq as int)
            && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX
            && *final(local) == *old(local)
            ==> pages_free_direct_match(
                final(local).heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                final(local).heap.pages.value()@[pq as int].first,
                final(local).page_empty_global@.s.points_to.ptr()),
{

    let size = heap.get_pages(Tracked(&*local))[pq].block_size;
    if size > SMALL_SIZE_MAX {
        proof {
            assert(*local == *old(local));
            assert(local.wf_basic());
            assert(common_preserves(*old(local), *local));
            assert(heap.is_in(*local));
            assert(*local == (Local { heap: local.heap, ..*old(local) }));
            assert(local.heap == (HeapLocalAccess { pages_free_direct: local.heap.pages_free_direct, ..old(local).heap }));
            assert(old(local).heap.pages_free_direct.id() == local.heap.pages_free_direct.id());
        }
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
        proof {
            assert(*local == *old(local));
            assert(local.wf_basic());
            assert(common_preserves(*old(local), *local));
            assert(heap.is_in(*local));
            assert(*local == (Local { heap: local.heap, ..*old(local) }));
            assert(local.heap == (HeapLocalAccess { pages_free_direct: local.heap.pages_free_direct, ..old(local).heap }));
            assert(old(local).heap.pages_free_direct.id() == local.heap.pages_free_direct.id());
            if valid_bin_idx(pq as int) && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX {
                assert(size as int == old(local).heap.pages.value()@[pq as int].block_size);
                assert(idx as int == pfd_upper(pq as int));
                assert(pages_free_direct_match(
                    local.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                    local.heap.pages.value()@[pq as int].first,
                    local.page_empty_global@.s.points_to.ptr())) by {
                    assert(local.heap.pages_free_direct.value()@[idx as int].addr() == page_ptr.addr());
                    if local.heap.pages.value()@[pq as int].first.addr() == 0 {
                        assert(page_ptr == local.page_empty_global@.s.points_to.ptr());
                        assert(local.heap.pages.value()@[pq as int].first as int == 0);
                        assert(local.heap.pages_free_direct.value()@[idx as int] as int
                            == local.page_empty_global@.s.points_to.ptr() as int);
                    } else {
                        assert(page_ptr == local.heap.pages.value()@[pq as int].first);
                        assert(local.heap.pages_free_direct.value()@[idx as int] as int
                            == local.heap.pages.value()@[pq as int].first as int);
                    }
                    reveal(pages_free_direct_match);
                };
            }
        }
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

    proof {
        if valid_bin_idx(pq as int) && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX {
            assert(local.heap.pages.value()@[pq as int].block_size == old(local).heap.pages.value()@[pq as int].block_size);
            assert(size as int == old(local).heap.pages.value()@[pq as int].block_size);
            assert(idx as int == pfd_upper(pq as int));
            if idx <= 1 {
                assert(start as int == 0);
                pfd_upper_le1_implies_bin1(pq as int);
                assert(pq as int == 1);
                assert(start as int == pfd_lower(pq as int));
            } else {
                if !(1 < pq as int) {
                    assert(pq as int == 1);
                    reveal(size_of_bin);
                    assert(size_of_bin(1) == 8);
                    assert(INTPTR_SIZE as int == 8) by(compute_only);
                    assert(pfd_upper(1) == 1) by(nonlinear_arith)
                        requires
                            size_of_bin(1) == 8,
                            INTPTR_SIZE as int == 8;
                    assert(idx as int == 1);
                    assert(false);
                }
                assert(1 < pq as int);
                assert(valid_bin_idx(pq as int - 1));
                assert(old(local).heap.pages.value()@[(pq as int) - 1].block_size == size_of_bin((pq as int) - 1));
                assert(start as int == pfd_lower(pq as int));
            }
        }
    }

    proof {
        assert(pages_free_direct_match(
            page_ptr,
            old(local).heap.pages.value()@[pq as int].first,
            old(local).page_empty_global@.s.points_to.ptr())) by {
            if old(local).heap.pages.value()@[pq as int].first.addr() == 0 {
                assert(page_ptr == old(local).page_empty_global@.s.points_to.ptr());
                assert(old(local).heap.pages.value()@[pq as int].first as int == 0);
            } else {
                assert(page_ptr == old(local).heap.pages.value()@[pq as int].first);
            }
            reveal(pages_free_direct_match);
        };
    }

    let mut sz = start;
    while sz <= idx
        invariant
            local.wf_basic(),
            heap.wf(),
            heap.is_in(*local),
            common_preserves(*old(local), *local),
            *local == (Local { heap: local.heap, ..*old(local) }),
            local.heap == (HeapLocalAccess { pages_free_direct: local.heap.pages_free_direct, ..old(local).heap }),
            old(local).heap.pages_free_direct.id() == local.heap.pages_free_direct.id(),
            start <= sz,
            sz <= idx + 1 || sz == start,
            idx < PAGES_DIRECT,
            pages_free_direct_match(
                page_ptr,
                old(local).heap.pages.value()@[pq as int].first,
                old(local).page_empty_global@.s.points_to.ptr()),
            pfd_direct_update(
                old(local).heap.pages_free_direct.value()@,
                local.heap.pages_free_direct.value()@,
                start as int,
                sz as int,
                old(local).page_empty_global@.s.points_to.ptr(),
                old(local).heap.pages.value()@[pq as int].first),
    {
        let ghost prev_local = *local;
        proof {
            assert(pages_free_direct_match(
                page_ptr,
                old(local).heap.pages.value()@[pq as int].first,
                old(local).page_empty_global@.s.points_to.ptr()));
        }
        heap_get_pages_free_direct!(heap, local, pages_free_direct => {
            pages_free_direct[sz] = page_ptr;
        });
        proof {
            let old_pfd = old(local).heap.pages_free_direct.value()@;
            let prev_pfd = prev_local.heap.pages_free_direct.value()@;
            let new_pfd = local.heap.pages_free_direct.value()@;
            let emp = old(local).page_empty_global@.s.points_to.ptr();
            let p = old(local).heap.pages.value()@[pq as int].first;
            assert(new_pfd[sz as int] == page_ptr);
            assert forall |k: int|
                0 <= k < new_pfd.len() && k != sz as int implies
                    #[trigger] new_pfd[k] == prev_pfd[k]
            by { };
            assert forall |k: int|
                0 <= k < old_pfd.len() && !(start as int <= k < (sz + 1) as int) implies
                    #[trigger] old_pfd[k] == new_pfd[k]
            by {
                assert(k != sz as int);
                assert(new_pfd[k] == prev_pfd[k]);
                assert(old_pfd[k] == prev_pfd[k]);
            };
            assert forall |k: int|
                0 <= k < new_pfd.len() && start as int <= k < (sz + 1) as int implies
                    pages_free_direct_match(#[trigger] new_pfd[k], p, emp)
            by {
                if k == sz as int {
                    assert(new_pfd[k] == page_ptr);
                    assert(pages_free_direct_match(page_ptr, p, emp));
                } else {
                    assert(start as int <= k < sz as int);
                    assert(new_pfd[k] == prev_pfd[k]);
                    assert(pages_free_direct_match(prev_pfd[k], p, emp));
                }
            };
            assert(pfd_direct_update(
                old(local).heap.pages_free_direct.value()@,
                local.heap.pages_free_direct.value()@,
                start as int,
                (sz + 1) as int,
                old(local).page_empty_global@.s.points_to.ptr(),
                old(local).heap.pages.value()@[pq as int].first));
        }

        sz += 1;
    }
    proof {
        assert(local.wf_basic());
        assert(common_preserves(*old(local), *local));
        assert(heap.is_in(*local));
        assert(*local == (Local { heap: local.heap, ..*old(local) }));
        assert(local.heap == (HeapLocalAccess { pages_free_direct: local.heap.pages_free_direct, ..old(local).heap }));
        assert(old(local).heap.pages_free_direct.id() == local.heap.pages_free_direct.id());
        if valid_bin_idx(pq as int) && old(local).heap.pages.value()@[pq as int].block_size <= SMALL_SIZE_MAX {
            assert(start as int == pfd_lower(pq as int));
            assert(idx as int == pfd_upper(pq as int));
            assert(local_direct_update(
                *old(local),
                *local,
                pfd_lower(pq as int) as int,
                pfd_upper(pq as int) as int + 1,
                pq as int));
            small_bin_pfd_range_nonempty(pq as int);
            assert(0 <= pfd_upper(pq as int) < local.heap.pages_free_direct.value()@.len());
            assert((pfd_lower(pq as int) as int) <= (pfd_upper(pq as int) as int));
            assert((pfd_upper(pq as int) as int) < (pfd_upper(pq as int) as int) + 1);
            assert(pages_free_direct_match(
                local.heap.pages_free_direct.value()@[pfd_upper(pq as int) as int],
                local.heap.pages.value()@[pq as int].first,
                local.page_empty_global@.s.points_to.ptr()));
        }
    }
}

}

verus!{
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
