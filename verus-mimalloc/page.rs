#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::pervasive::*;
use vstd::atomic_ghost::*;
use vstd::arithmetic::div_mod::{lemma_div_pos_is_pos, lemma_fundamental_div_mod};

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
use crate::queues::*;

verus!{

#[verifier::rlimit(200)]
proof fn valid_used_page_ptr_facts(page: PagePtr, local: Local, pq: int, list_idx: int)
    requires
        local.wf(),
        page.wf(),
        valid_bin_idx(pq),
        local.page_organization.valid_used_page(page.page_id@, pq, list_idx),
    ensures
        page.is_in(local),
        page.is_used_and_primary(local),
        local.block_size(page.page_id@) == size_of_bin(pq),
{
    let ghost page_id = page.page_id@;
    reveal(Local::wf);
    reveal(Local::wf_main);
    reveal(Local::page_organization_valid);
    reveal(PageOrg::State::valid_used_page);
    assert(local.page_organization.pages.dom().contains(page_id));
    assert(local.page_organization.pages[page_id].is_used);
    assert(local.page_organization.pages[page_id].offset == Some(0nat));
    assert(page_organization_pages_match(
        local.page_organization.pages,
        local.pages,
        local.psa,
        local.page_organization.popped));
    assert(local.pages.dom().contains(page_id));
    assert(local.thread_token.value().pages.dom().contains(page_id));
    assert(page_organization_matches_token_page(
        local.page_organization.pages[page_id],
        local.thread_token.value().pages[page_id]));
    assert(local.thread_token.value().pages[page_id].offset == 0);
    assert(page.is_in(local));
    assert(page.is_used_and_primary(local));
    assert(page_organization_pages_match_data(
        local.page_organization.pages[page_id],
        local.pages[page_id],
        local.psa[page_id],
        page_id,
        local.page_organization.popped));
    match local.page_organization.pages[page_id].page_header_kind {
        Some(PageHeaderKind::Normal(bin_idx, bsize)) => {
            assert(bin_idx == pq);
            assert(bsize == size_of_bin(pq));
            assert(local.pages[page_id].inner.value().xblock_size == bsize);
            assert(local.block_size(page_id) == size_of_bin(pq));
        }
        None => { assert(false); }
    }
}

#[verifier::rlimit(200)]
pub fn find_page(heap_ptr: HeapPtr, size: usize, huge_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> size as int <= final(local).block_size(page.page_id@),
{

    let req_size = size;
    if unlikely(req_size > MEDIUM_OBJ_SIZE_MAX as usize || huge_alignment > 0) {
        if unlikely(req_size > MAX_ALLOC_SIZE) {
            return PagePtr::null();
        } else {
            todo(); loop { }
        }
    } else {
        return find_free_page(heap_ptr, size, Tracked(&mut *local));
    }
}

#[verifier::rlimit(200)]
fn find_free_page(heap_ptr: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        size <= MEDIUM_OBJ_SIZE_MAX as usize,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> size as int <= final(local).block_size(page.page_id@),
{
    proof {
        assert(MEDIUM_OBJ_SIZE_MAX as int == 131072) by(compute_only);
        assert(size <= 131072) by(nonlinear_arith)
            requires size <= MEDIUM_OBJ_SIZE_MAX as usize, MEDIUM_OBJ_SIZE_MAX as int == 131072;
    }
    let pq = bin(size) as usize;
    proof {
        bounds_for_smallest_bin_fitting_size(size as int);
        assert(size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX);
    }

    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };

    proof {
        if page.page_ptr.addr() != 0 {
            reveal(Local::wf);
            reveal(Local::wf_main);
            reveal(Local::page_organization_valid);
            reveal(PageOrg::State::valid_used_page);
            assert(page_organization_used_queues_match(
                local.page_organization.used_dlist_headers,
                local.heap.pages.value()@));
            assert(is_page_ptr_opt(
                local.heap.pages.value()@[pq as int].first,
                local.page_organization.used_dlist_headers[pq as int].first));
            match local.page_organization.used_dlist_headers[pq as int].first {
                Some(id) => {
                    assert(page.page_id@ == id);
                }
                None => {
                    assert(local.heap.pages.value()@[pq as int].first.addr() == 0);
                    assert(false);
                }
            }
            local.page_organization.used_first_is_in(pq as int);
            assert(local.page_organization.valid_used_page(page.page_id@, pq as int, 0));
            assert(local.page_organization.pages[page.page_id@].is_used);
            assert(local.page_organization.pages[page.page_id@].offset == Some(0nat));
            assert(local.pages.dom().contains(page.page_id@));
            assert(!local.unused_pages.dom().contains(page.page_id@));
            assert(local.thread_token.value().pages.dom().contains(page.page_id@));
            assert(page_organization_matches_token_page(
                local.page_organization.pages[page.page_id@],
                local.thread_token.value().pages[page.page_id@]));
            assert(local.thread_token.value().pages[page.page_id@].offset == 0);
            assert(page.wf());
            assert(page.is_used_and_primary(*local));
        }
    }

    if page.page_ptr.addr() != 0 {
        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            proof {
                assert(page.wf());
                assert(page.is_in(*local));
                assert(page.is_used_and_primary(*local));
                match local.page_organization.pages[page.page_id@].page_header_kind {
                    Some(PageHeaderKind::Normal(bin_idx, bsize)) => {
                        assert(bin_idx == pq as int);
                        assert(bsize == size_of_bin(pq as int));
                        assert(local.pages[page.page_id@].inner.value().xblock_size == bsize);
                        assert(local.block_size(page.page_id@) == size_of_bin(pq as int));
                    }
                    None => { assert(false); }
                }
                assert(size_of_bin(pq as int) >= size);
                assert(size as int <= local.block_size(page.page_id@));
            }
            return page;
        }
    }

    page_queue_find_free_ex(heap_ptr, pq, true, Tracked(&mut *local))
}

#[verifier::rlimit(200)]
fn page_queue_find_free_ex(heap_ptr: HeapPtr, pq: usize, first_try: bool, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> final(local).block_size(page.page_id@) == size_of_bin(pq as int),
{
    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };
    let ghost mut list_idx = 0;
    proof {
        assert(0 <= pq as int <= BIN_HUGE);
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(Local::page_organization_valid);
        if page.page_ptr.addr() != 0 {
            assert(page_organization_used_queues_match(
                local.page_organization.used_dlist_headers,
                local.heap.pages.value()@));
            assert(is_page_ptr_opt(
                local.heap.pages.value()@[pq as int].first,
                local.page_organization.used_dlist_headers[pq as int].first));
            match local.page_organization.used_dlist_headers[pq as int].first {
                Some(id) => {
                    assert(page.page_id@ == id);
                }
                None => {
                    assert(local.heap.pages.value()@[pq as int].first.addr() == 0);
                    assert(false);
                }
            }
            local.page_organization.used_first_is_in(pq as int);
            assert(local.page_organization.valid_used_page(page.page_id@, pq as int, 0));
            reveal(PageOrg::State::valid_used_page);
            assert(is_page_ptr(local.heap.pages.value()@[pq as int].first, page.page_id@));
            assert(page.page_ptr as int == local.heap.pages.value()@[pq as int].first as int);
            assert(page.page_ptr@.provenance == page.page_id@.segment_id.provenance);
            assert(page.wf());
            valid_used_page_ptr_facts(page, *local, pq as int, 0);
        }
    }

    loop
        invariant
            local.wf(),
            heap_ptr.wf(),
            heap_ptr.is_in(*local),
            common_preserves(*old(local), *local),
            0 <= pq <= BIN_HUGE,
            size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
            page.page_ptr.addr() != 0 ==>
                page.wf()
                && local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    {
        if page.page_ptr.addr() == 0 {
            break;
        }

        let next_ptr = page.get_next(Tracked(&*local));
        let ghost page_id = page.page_id@;
        let ghost next_id = local.page_organization.pages[page_id].dlist_entry.unwrap().next.unwrap();

        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));
        proof {
            assert(local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx));
            valid_used_page_ptr_facts(page, *local, pq as int, list_idx);
            assert(common_preserves(*old(local), *local));
        }

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            break;
        }

        if page.get_inner_ref(Tracked(&*local)).capacity < page.get_inner_ref(Tracked(&*local)).reserved {
            //let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
            //assert(local.is_used_primary(page.page_id@));
            proof {
                local.used_primary_page_reserved_available(page.page_id@);
            }
            crate::alloc_generic::page_extend_free(page, Tracked(&mut *local));
            proof {
                assert(local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx));
                valid_used_page_ptr_facts(page, *local, pq as int, list_idx);
            }
            break;
        }

        proof {
            local.page_organization.used_next_is_in(page.page_id@, pq as int, list_idx);
        }
        page_to_full(page, heap_ptr, pq, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));

        page = PagePtr { page_ptr: next_ptr, page_id: Ghost(next_id) };

    }

    if page.page_ptr.addr() == 0 {
        let page = page_fresh(heap_ptr, pq, Tracked(&mut *local));
        if page.page_ptr.addr() == 0 && first_try {
            return page_queue_find_free_ex(heap_ptr, pq, false, Tracked(&mut *local))
        } else {
            return page;
        }
    } else {
        let ghost old_local = *local;
        page_get_mut_inner!(page, local, inner => {
            inner.set_retire_expire(0);
        });
        proof {
            reveal(Local::wf);
            reveal(Local::wf_main);
            reveal(Local::page_organization_valid);
            reveal(HeapLocalAccess::wf);
            reveal(HeapLocalAccess::wf_basic);
            reveal(PageLocalAccess::wf);
            reveal(PageInner::wf);
            reveal(page_organization_pages_match);
            reveal(page_organization_pages_match_data);
            assert(local.page_organization.popped == Popped::No);
            assert(is_tld_ptr(local.tld.ptr(), local.tld_id));
            assert(local.thread_token.instance_id() == local.instance.id());
            assert(local.thread_token.key() == local.thread_id);
            assert(local.thread_id == local.is_thread@);
            assert(local.thread_token.value().segments.dom() == local.segments.dom());
            assert(local.thread_token.value().heap_id == local.heap_id);
            assert(local.heap.wf(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id(), local.page_empty_global@.s.points_to.ptr()));
            assert forall |page_id| #[trigger] local.pages.dom().contains(page_id) implies
                (local.unused_pages.dom().contains(page_id) <==> !local.thread_token.value().pages.dom().contains(page_id)) by { };
            assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
            assert(page_organization_queues_match(
                local.page_organization.unused_dlist_headers,
                local.tld.value().segments.span_queue_headers@));
            assert(page_organization_used_queues_match(
                local.page_organization.used_dlist_headers,
                local.heap.pages.value()@));
            assert(page_organization_segments_match(local.page_organization.segments, local.segments));
            assert(local.page_organization == old_local.page_organization);
            assert(local.psa == old_local.psa);
            assert(local.pages.dom() == old_local.pages.dom());
            assert(local.page_organization.pages.dom() == local.pages.dom());
            assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                page_organization_pages_match_data(
                    local.page_organization.pages[pid],
                    local.pages[pid],
                    local.psa[pid],
                    pid,
                    local.page_organization.popped)
            by {
                if pid == page.page_id@ {
                    assert(page_organization_pages_match_data(
                        old_local.page_organization.pages[pid],
                        old_local.pages[pid],
                        old_local.psa[pid],
                        pid,
                        old_local.page_organization.popped));
                    assert(local.pages[pid].count == old_local.pages[pid].count);
                    assert(local.pages[pid].prev == old_local.pages[pid].prev);
                    assert(local.pages[pid].next == old_local.pages[pid].next);
                    assert(local.pages[pid].inner.id() == old_local.pages[pid].inner.id());
                    assert(local.pages[pid].inner.value().flags0 == old_local.pages[pid].inner.value().flags0);
                    assert(local.pages[pid].inner.value().flags1 == old_local.pages[pid].inner.value().flags1);
                    assert(local.pages[pid].inner.value().capacity == old_local.pages[pid].inner.value().capacity);
                    assert(local.pages[pid].inner.value().reserved == old_local.pages[pid].inner.value().reserved);
                    assert(local.pages[pid].inner.value().free == old_local.pages[pid].inner.value().free);
                    assert(local.pages[pid].inner.value().used == old_local.pages[pid].inner.value().used);
                    assert(local.pages[pid].inner.value().xblock_size == old_local.pages[pid].inner.value().xblock_size);
                    assert(local.pages[pid].inner.value().local_free == old_local.pages[pid].inner.value().local_free);
                    assert(page_organization_pages_match_data(
                        local.page_organization.pages[pid],
                        local.pages[pid],
                        local.psa[pid],
                        pid,
                        local.page_organization.popped));
                } else {
                    assert(local.pages[pid] == old_local.pages[pid]);
                    assert(page_organization_pages_match_data(
                        old_local.page_organization.pages[pid],
                        old_local.pages[pid],
                        old_local.psa[pid],
                        pid,
                        old_local.page_organization.popped));
                }
            };
            assert(page_organization_pages_match(
                local.page_organization.pages,
                local.pages,
                local.psa,
                local.page_organization.popped));
            assert(local.page_organization_valid());
            assert(local.tld.is_init());
            assert forall |pid: PageId| (#[trigger] local.pages.dom().contains(pid))
                && local.thread_token.value().pages.dom().contains(pid) implies
                    local.pages.index(pid).wf(
                        pid,
                        local.thread_token.value().pages.index(pid),
                        local.instance,
                    ) by {
                if pid == page.page_id@ {
                    assert(local.pages[pid].wf(pid, local.thread_token.value().pages[pid], local.instance));
                } else {
                    assert(local.pages[pid] == old_local.pages[pid]);
                }
            };
            assert forall |pid: PageId| (#[trigger] local.pages.dom().contains(pid))
                && local.unused_pages.dom().contains(pid) implies
                    local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance) by {
                if pid == page.page_id@ {
                    assert(local.thread_token.value().pages.dom().contains(page.page_id@));
                    assert(!local.unused_pages.dom().contains(page.page_id@));
                } else {
                    assert(local.pages[pid] == old_local.pages[pid]);
                }
            };
            assert forall |sid| #[trigger] local.segments.dom().contains(sid) implies
                local.segments[sid].wf(
                    sid,
                    local.thread_token.value().segments.index(sid),
                    local.instance,
                ) by {
                assert(local.segments[sid] == old_local.segments[sid]);
            };
            assert forall |sid| #[trigger] local.segments.dom().contains(sid) implies
                local.mem_chunk_good(sid) by {
                assert(old_local.segments.dom().contains(sid));
                assert(old_local.mem_chunk_good(sid));
                assert(local.segments == old_local.segments);
                assert(local.page_organization == old_local.page_organization);
                assert(local.pages.dom() == old_local.pages.dom());
                assert forall |pid: PageId| local.page_organization.pages.dom().contains(pid) && pid != page.page_id@ implies
                    local.pages[pid] == old_local.pages[pid] by {
                    assert(local.pages[pid] == old_local.pages[pid]);
                };
                assert(local.page_count(page.page_id@) == old_local.page_count(page.page_id@));
                assert(local.page_capacity(page.page_id@) == old_local.page_capacity(page.page_id@));
                assert(local.block_size(page.page_id@) == old_local.block_size(page.page_id@));
                local.page_inner_update_preserves_mem_chunk_good(old_local, sid, page.page_id@);
            };
            assert(local.checked_token.instance_id() == local.instance.id());
            assert(local.checked_token.key() == local.thread_id);
            assert(local.my_inst.instance_id() == local.instance.id());
            assert(local.my_inst.value() == local.instance.id());
            assert(local.page_empty_global@.wf_empty_page_global());
            assert(local.wf_main());
            assert(local.wf());
            assert(local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx));
            valid_used_page_ptr_facts(page, *local, pq as int, list_idx);
            assert(local.inst() == old_local.inst());
            assert(common_preserves(old_local, *local));
            assert(common_preserves(*old(local), *local));
            assert forall |heap: HeapPtr| heap.is_in(*old(local)) implies heap.is_in(*local) by {
                assert(heap.is_in(old_local));
            };
        }
        return page;
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn page_fresh(heap_ptr: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        size_of_bin(pq as int) <= MEDIUM_OBJ_SIZE_MAX,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> final(local).block_size(page.page_id@) == size_of_bin(pq as int),
{
    let block_size = heap_ptr.get_pages(Tracked(&*local))[pq].block_size;
    proof {
        smallest_bin_fitting_size_size_of_bin(pq as int);
        assert(block_size as int == size_of_bin(pq as int));
        assert(block_size as int <= MEDIUM_OBJ_SIZE_MAX);
        assert(INTPTR_SIZE as usize <= block_size) by(nonlinear_arith)
            requires
                size_of_bin(pq as int) >= INTPTR_SIZE as nat,
                block_size as int == size_of_bin(pq as int);
    }
    page_fresh_alloc(heap_ptr, pq, block_size, 0, Tracked(&mut *local))
}

fn page_fresh_alloc(heap_ptr: HeapPtr, pq: usize, block_size: usize, page_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
    requires
        old(local).wf(),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        valid_bin_idx(pq as int),
        block_size > 0,
        INTPTR_SIZE as usize <= block_size,
        block_size as int == size_of_bin(pq as int),
        block_size as int <= MEDIUM_OBJ_SIZE_MAX,
        page_alignment == 0,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.wf() && page.is_in(*final(local)),
        page.page_ptr.addr() != 0 ==> page.is_used_and_primary(*final(local)),
        page.page_ptr.addr() != 0 ==> final(local).block_size(page.page_id@) == block_size as int,
{
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
    let page_ptr = crate::segment::segment_page_alloc(heap_ptr, block_size, page_alignment, tld_ptr, Tracked(&mut *local));
    if page_ptr.page_ptr.addr() == 0 {
        return page_ptr;
    }

    let full_block_size: usize = block_size; // TODO handle pq == NULL or huge pages
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;


    proof {
        smallest_bin_fitting_size_size_of_bin(pq as int);
        assert(pq as int == smallest_bin_fitting_size(block_size as int));

        let page_id = page_ptr.page_id@;
        let count = local.page_organization.pages[page_id].count.unwrap();
        let reserved = page_init_reserved(*local, page_id, block_size);
        local.page_organization.ready_popped_range_facts();
        page_init_reserved_ready_facts(*local, page_id, block_size);
        assert(0 <= reserved);
        assert(reserved <= u16::MAX as int);
        assert(block_start_at(page_id, block_size as int, reserved)
            <= segment_start(page_id.segment_id) + SEGMENT_SIZE);
        assert(local.segments[page_id.segment_id].mem.pointsto_has_range(
            page_start(page_id), count as int * SLICE_SIZE as int));
        assert(local.segments[page_id.segment_id].mem.pointsto_has_range(
            block_start_at(page_id, block_size as int, 0),
            reserved * block_size as int)) by {
            assert forall |addr: int|
                #[trigger] set_int_range(
                    block_start_at(page_id, block_size as int, 0),
                    block_start_at(page_id, block_size as int, 0) + reserved * block_size as int).contains(addr)
            implies
                set_int_range(page_start(page_id), page_start(page_id) + count as int * SLICE_SIZE as int).contains(addr)
            by {
                reveal(page_init_reserved);
                lemma_start_offset_bounds(block_size as int);
                assert(0 <= start_offset(block_size as int));
                assert(block_start_at(page_id, block_size as int, 0) <= addr);
                assert(addr < block_start_at(page_id, block_size as int, 0) + reserved * block_size as int);
                assert(page_start(page_id) <= addr) by(nonlinear_arith)
                    requires
                        block_start_at(page_id, block_size as int, 0) <= addr,
                        block_start_at(page_id, block_size as int, 0)
                            == page_start(page_id) + start_offset(block_size as int),
                        0 <= start_offset(block_size as int);
                assert(addr < block_start_at(page_id, block_size as int, reserved)) by(nonlinear_arith)
                    requires
                        addr < block_start_at(page_id, block_size as int, 0) + reserved * block_size as int,
                        block_start_at(page_id, block_size as int, reserved)
                            == block_start_at(page_id, block_size as int, 0) + reserved * block_size as int;
                assert(block_start_at(page_id, block_size as int, reserved)
                    <= page_start(page_id) + count as int * SLICE_SIZE as int) by {
                    page_init_reserved_ready_facts(*local, page_id, block_size);
                    let total = count as int * SLICE_SIZE as int - start_offset(block_size as int);
                    lemma_fundamental_div_mod(total, block_size as int);
                    assert(reserved == total / block_size as int);
                    assert(0 <= total % block_size as int);
                    assert(reserved * block_size as int <= total) by(nonlinear_arith)
                        requires total == reserved * block_size as int + total % block_size as int,
                            0 <= total % block_size as int;
                    assert(block_start_at(page_id, block_size as int, reserved)
                        <= page_start(page_id) + count as int * SLICE_SIZE as int) by(nonlinear_arith)
                        requires
                            block_start_at(page_id, block_size as int, reserved)
                                == page_start(page_id) + start_offset(block_size as int) + reserved * block_size as int,
                            reserved * block_size as int <= total,
                            total == count as int * SLICE_SIZE as int - start_offset(block_size as int);
                }
                assert(addr < page_start(page_id) + count as int * SLICE_SIZE as int);
            };
        };
        assert forall |idx: nat| (idx as int) < reserved implies
            page_id.range_from(0, local.page_organization.pages[page_id].count.unwrap() as int).contains(
                PageId {
                    segment_id: page_id.segment_id,
                    idx: BlockId::get_slice_idx(page_id, idx, block_size as nat),
                }) by {
            page_init_reserved_ready_facts(*local, page_id, block_size);
        };
        assert(set_int_range(
            page_start(page_id),
            page_start(page_id) + local.page_organization.pages[page_id].count.unwrap() as int * SLICE_SIZE as int)
            <= local.commit_mask(page_id.segment_id).bytes(page_id.segment_id)
                - local.decommit_mask(page_id.segment_id).bytes(page_id.segment_id));
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by { };
    }
    page_init(heap_ptr, page_ptr, full_block_size, tld_ptr, Tracked(&mut *local), Ghost(pq as int));
    proof {
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid) by { };
    }
    page_queue_push(heap_ptr, pq, page_ptr, Tracked(&mut *local));

    return page_ptr;
}

// READY --> USED
closed spec fn page_init_reserved(local: Local, page_id: PageId, block_size: usize) -> int
    recommends
        block_size > 0,
        local.page_organization.pages[page_id].count.is_some(),
{
    (local.page_organization.pages[page_id].count.unwrap() * (SLICE_SIZE as int)
        - start_offset(block_size as int)) / block_size as int
}

#[verifier::rlimit(200)]
proof fn page_init_reserved_ready_facts(local: Local, page_id: PageId, block_size: usize)
    requires
        local.wf_main_for_page_access(),
        local.page_organization.popped == Popped::Ready(page_id, true),
        local.page_organization.pages[page_id].count.is_some(),
        block_size > 0,
        INTPTR_SIZE as usize <= block_size,
        good_count_for_block_size(
            block_size as int,
            local.page_organization.pages[page_id].count.unwrap() as int),
    ensures
        0 <= page_init_reserved(local, page_id, block_size),
        page_init_reserved(local, page_id, block_size) <= u16::MAX as int,
        block_start_at(page_id, block_size as int, page_init_reserved(local, page_id, block_size))
            <= segment_start(page_id.segment_id) + SEGMENT_SIZE,
        forall |idx: nat| (idx as int) < page_init_reserved(local, page_id, block_size) ==>
            page_id.range_from(0, local.page_organization.pages[page_id].count.unwrap() as int).contains(
                PageId {
                    segment_id: page_id.segment_id,
                    idx: BlockId::get_slice_idx(page_id, idx, block_size as nat),
                }),
{
    reveal(page_init_reserved);
    reveal(good_count_for_block_size);
    reveal(Local::wf_main_for_page_access);
    reveal(Local::page_organization_valid);
    let count = local.page_organization.pages[page_id].count.unwrap();
    let bs = block_size as int;
    let total = count * (SLICE_SIZE as int) - start_offset(bs);
    let reserved = page_init_reserved(local, page_id, block_size);

    local.page_organization.ready_popped_range_facts();
    lemma_start_offset_bounds(bs);
    assert(0 <= start_offset(bs));
    assert(start_offset(bs) <= 3 * MAX_ALIGN_GUARANTEE as int);
    assert(SLICE_SIZE as int == 65536) by(compute_only);
    assert(MAX_ALIGN_GUARANTEE as int == 128) by(compute_only);
    assert(count > 0);
    assert(count * (SLICE_SIZE as int) >= SLICE_SIZE as int) by(nonlinear_arith)
        requires count > 0, SLICE_SIZE as int == 65536;
    assert(total >= 0) by(nonlinear_arith)
        requires
            total == count * (SLICE_SIZE as int) - start_offset(bs),
            count * (SLICE_SIZE as int) >= SLICE_SIZE as int,
            start_offset(bs) <= 3 * MAX_ALIGN_GUARANTEE as int,
            MAX_ALIGN_GUARANTEE as int == 128,
            SLICE_SIZE as int == 65536;
    lemma_div_pos_is_pos(total, bs);
    assert(reserved == total / bs);
    assert(0 <= reserved);

    assert(total < bs * 0x10000) by(nonlinear_arith)
        requires
            total == count * (SLICE_SIZE as int) - start_offset(bs),
            count * (SLICE_SIZE as int) < bs * 0x10000,
            0 <= start_offset(bs);
    lemma_fundamental_div_mod(total, bs);
    assert(0 <= total % bs);
    if !(reserved < 0x10000) {
        assert(0x10000 * bs <= reserved * bs) by(nonlinear_arith)
            requires 0x10000 <= reserved, 0 < bs;
        assert(total >= reserved * bs) by(nonlinear_arith)
            requires total == reserved * bs + total % bs, 0 <= total % bs;
        assert(total >= 0x10000 * bs) by(nonlinear_arith)
            requires 0x10000 * bs <= reserved * bs, reserved * bs <= total;
        assert(false);
    }
    assert(u16::MAX as int == 65535) by(compute_only);
    assert(0x10000 == 65536) by(compute_only);
    assert(reserved <= u16::MAX as int) by(nonlinear_arith)
        requires reserved < 0x10000, u16::MAX as int == 65535, 0x10000 == 65536;

    assert(reserved * bs <= total) by(nonlinear_arith)
        requires total == reserved * bs + total % bs, 0 <= total % bs;
    assert(block_start_at(page_id, bs, reserved) <= page_start(page_id) + count * (SLICE_SIZE as int))
        by(nonlinear_arith)
        requires
            block_start_at(page_id, bs, reserved) == page_start(page_id) + start_offset(bs) + reserved * bs,
            reserved * bs <= total,
            total == count * (SLICE_SIZE as int) - start_offset(bs);
    assert((SLICES_PER_SEGMENT as int) * (SLICE_SIZE as int) == SEGMENT_SIZE as int) by(compute_only);
    assert(page_id.idx + count <= SLICES_PER_SEGMENT);
    assert(page_start(page_id) + count * (SLICE_SIZE as int)
        <= segment_start(page_id.segment_id) + SEGMENT_SIZE) by(nonlinear_arith)
        requires
            page_start(page_id) == segment_start(page_id.segment_id) + SLICE_SIZE as int * page_id.idx,
            page_id.idx + count <= SLICES_PER_SEGMENT,
            (SLICES_PER_SEGMENT as int) * (SLICE_SIZE as int) == SEGMENT_SIZE as int;
    assert(block_start_at(page_id, bs, reserved)
        <= segment_start(page_id.segment_id) + SEGMENT_SIZE);

    assert forall |idx0: nat| (idx0 as int) < reserved implies
        page_id.range_from(0, count as int).contains(
            PageId {
                segment_id: page_id.segment_id,
                idx: BlockId::get_slice_idx(page_id, idx0, block_size as nat),
            })
    by {
        let offset = start_offset(bs) + idx0 as int * bs;
        assert((idx0 as int) * bs < reserved * bs) by(nonlinear_arith)
            requires (idx0 as int) < reserved, 0 < bs;
        assert(offset < count * (SLICE_SIZE as int)) by(nonlinear_arith)
            requires
                offset == start_offset(bs) + idx0 as int * bs,
                (idx0 as int) * bs < reserved * bs,
                reserved * bs <= total,
                total == count * (SLICE_SIZE as int) - start_offset(bs);
        assert(0 <= idx0 as int * bs) by(nonlinear_arith)
            requires 0 <= idx0 as int, 0 < bs;
        assert(0 <= offset) by(nonlinear_arith)
            requires offset == start_offset(bs) + idx0 as int * bs,
                0 <= start_offset(bs), 0 <= idx0 as int * bs;
        lemma_fundamental_div_mod(offset, SLICE_SIZE as int);
        let q = offset / (SLICE_SIZE as int);
        assert(0 <= q);
        assert(q < count) by {
            if !(q < count) {
                assert(offset >= count * (SLICE_SIZE as int)) by(nonlinear_arith)
                    requires
                        offset == q * (SLICE_SIZE as int) + offset % (SLICE_SIZE as int),
                        0 <= offset % (SLICE_SIZE as int),
                        count <= q,
                        0 < SLICE_SIZE as int;
                assert(false);
            }
        };
        let slice_id = PageId {
            segment_id: page_id.segment_id,
            idx: BlockId::get_slice_idx(page_id, idx0, block_size as nat),
        };
        assert((block_size as nat) as int == bs);
        assert(0 <= idx0 as int * bs) by(nonlinear_arith)
            requires 0 <= idx0 as int, 0 < bs;
        assert(idx0 * (block_size as nat) == (idx0 as int * bs) as nat) by(nonlinear_arith)
            requires (block_size as nat) as int == bs, 0 <= idx0 as int * bs;
        assert((idx0 * (block_size as nat)) as int == idx0 as int * bs);
        assert(BlockId::get_slice_idx(page_id, idx0, block_size as nat)
            == (page_id.idx + (start_offset((block_size as nat) as int)
                + idx0 * (block_size as nat)) / (SLICE_SIZE as int)) as nat);
        assert(start_offset((block_size as nat) as int) == start_offset(bs));
        assert((start_offset((block_size as nat) as int) + idx0 * (block_size as nat)) == offset);
        assert(slice_id.idx as int == page_id.idx + q);
        assert(page_id.idx <= slice_id.idx);
        assert(slice_id.idx < page_id.idx + count) by(nonlinear_arith)
            requires slice_id.idx as int == page_id.idx + q, q < count;
    };
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
    requires
        old(local).wf_main_for_page_access(),
        old(local).mem_chunk_good(page_ptr.page_id@.segment_id),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        page_ptr.wf(),
        page_ptr.is_in(*old(local)),
        page_ptr.is_in_unused(*old(local)),
        old(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        valid_bin_idx(pq),
        block_size > 0,
        block_size as int == size_of_bin(pq),
        pq == smallest_bin_fitting_size(block_size as int),
        block_size as int <= MEDIUM_OBJ_SIZE_MAX,
        0 <= page_init_reserved(*old(local), page_ptr.page_id@, block_size),
        page_init_reserved(*old(local), page_ptr.page_id@, block_size) <= u16::MAX as int,
        old(local).segments[page_ptr.page_id@.segment_id].mem.pointsto_has_range(
            block_start_at(page_ptr.page_id@, block_size as int, 0),
            page_init_reserved(*old(local), page_ptr.page_id@, block_size) * block_size as int),
        block_start_at(page_ptr.page_id@, block_size as int,
            page_init_reserved(*old(local), page_ptr.page_id@, block_size))
            <= segment_start(page_ptr.page_id@.segment_id) + SEGMENT_SIZE,
        set_int_range(
            page_start(page_ptr.page_id@),
            page_start(page_ptr.page_id@)
                + old(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int * SLICE_SIZE as int)
            <= old(local).commit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id)
                - old(local).decommit_mask(page_ptr.page_id@.segment_id).bytes(page_ptr.page_id@.segment_id),
        forall |idx: nat| (idx as int) < page_init_reserved(*old(local), page_ptr.page_id@, block_size) ==>
            page_ptr.page_id@.range_from(0, old(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int).contains(
                PageId {
                    segment_id: page_ptr.page_id@.segment_id,
                    idx: BlockId::get_slice_idx(page_ptr.page_id@, idx, block_size as nat),
                }),
    ensures
        common_preserves(*old(local), *final(local)),
        final(local).wf_main_for_page_access(),
        final(local).segments.dom() == old(local).segments.dom(),
        forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) && old(local).mem_chunk_good(sid) ==>
            final(local).mem_chunk_good(sid),
        heap_ptr.wf(),
        heap_ptr.is_in(*final(local)),
        page_ptr.wf(),
        page_ptr.is_in(*final(local)),
        page_ptr.is_used_and_primary(*final(local)),
        final(local).block_size(page_ptr.page_id@) == block_size as int,
        final(local).page_organization.popped == Popped::Used(page_ptr.page_id@, true),
        final(local).page_organization.pages[page_ptr.page_id@].page_header_kind
            == Some(PageHeaderKind::Normal(pq, block_size as int)),
{
    let ghost page_id = page_ptr.page_id@;
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost reserved_blocks = page_init_reserved(*old(local), page_id, block_size);
    let ghost range = page_id.range_from(0, n_slices as int);

    proof! {
        reveal(Local::wf_main_for_page_access);
        reveal(Local::page_organization_valid);
        local.page_organization.ready_popped_range_facts();
        assert(local.unused_pages.dom().contains(page_id));
        assert(local.thread_token.value().segments.dom().contains(page_id.segment_id));
        assert(local.thread_token.value().segments[page_id.segment_id].is_enabled);
        assert(!local.thread_token.value().pages.dom().contains(page_id));
        assert(local.thread_token.value().heap_id == local.heap_id);
    }

    let ghost new_page_state_map = Map::new(
            range,
            |pid: PageId| PageState {
                offset: pid.idx - page_id.idx,
                block_size: block_size as nat,
                num_blocks: 0,
                shared_access: arbitrary(),
                is_enabled: false,
            });

    proof! {
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies pid.segment_id == page_id.segment_id
                && page_id.idx <= pid.idx < page_id.idx + n_slices by {
            assert(range.contains(pid));
        };
        assert forall |pid: PageId| pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + n_slices
            implies #[trigger] new_page_state_map.dom().contains(pid) by {
            assert(range.contains(pid));
        };
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies new_page_state_map[pid].offset + page_id.idx == pid.idx by {
        };
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies !new_page_state_map[pid].is_enabled by {
        };
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies new_page_state_map[pid].num_blocks == 0 by {
        };
        assert(new_page_state_map.dom().contains(page_id));
        assert(new_page_state_map[page_id].block_size == block_size as nat);
        assert(new_page_state_map.dom().disjoint(local.thread_token.value().pages.dom())) by {
            assert forall |pid: PageId| new_page_state_map.dom().contains(pid)
                implies !local.thread_token.value().pages.dom().contains(pid) by {
                assert(local.page_organization.pages.dom().contains(pid));
                assert(!local.page_organization.pages[pid].is_used);
                assert(local.unused_pages.dom().contains(pid));
            };
        };
    }

    let count = page_ptr.get_count(Tracked(&*local));

    let tracked thread_token = local.take_thread_token();
    let tracked (
        Tracked(thread_token),
        Tracked(delay_token),
        Tracked(heap_of_page_token),
    ) = local.instance.create_page_mk_tokens(
            // params
            local.thread_id,
            page_id,
            n_slices as nat,
            block_size as nat,
            new_page_state_map,
            // input ghost state
            thread_token,
        );

    unused_page_get_mut!(page_ptr, local, page => {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(false);
        let ghost g = (Ghost(local.instance), Ghost(page_ptr.page_id@), Tracked(emp_x), Tracked(emp_inst));
        page.xheap = AtomicHeapPtr {
            atomic: AtomicPtr::new(Ghost(g), heap_ptr.heap_ptr, Tracked((emp_y, Some(heap_of_page_token)))),
            instance: Ghost(local.instance), page_id: Ghost(page_ptr.page_id@), emp: Tracked(emp_x), emp_inst: Tracked(emp_inst), };
        page.xthread_free.enable(Ghost(block_size as nat), Ghost(page_ptr.page_id@),
            Tracked(local.instance.clone()), Tracked(delay_token));
    });

    let ghost local_before_inner = *local;
    proof! {
        assert(count as int == n_slices);
        assert(1 <= n_slices <= SLICES_PER_SEGMENT);
        lemma_start_offset_bounds(block_size as int);
        assert(SLICES_PER_SEGMENT as int == 512) by(compute_only);
        assert(SLICE_SIZE as u32 == 65536) by(compute_only);
        assert(MAX_ALIGN_GUARANTEE as int == 128) by(compute_only);
        assert(count <= 512) by(nonlinear_arith)
            requires count as int == n_slices, n_slices <= SLICES_PER_SEGMENT, SLICES_PER_SEGMENT as int == 512;
        assert(count >= 1) by(nonlinear_arith)
            requires count as int == n_slices, 1 <= n_slices;
        assert(count * SLICE_SIZE as u32 <= u32::MAX) by(bit_vector)
            requires count <= 512, SLICE_SIZE as u32 == 65536;
        assert forall |start_offs: u32| #[trigger] (start_offs as int + 0) == start_offset(block_size as int)
            implies start_offs <= count * SLICE_SIZE as u32 by {
            assert(start_offs as int == start_offset(block_size as int)) by(nonlinear_arith)
                requires start_offs as int + 0 == start_offset(block_size as int);
            assert(start_offs <= 384) by(nonlinear_arith)
                requires start_offs as int == start_offset(block_size as int),
                    start_offset(block_size as int) <= 3 * (MAX_ALIGN_GUARANTEE as int),
                    MAX_ALIGN_GUARANTEE as int == 128;
            assert(start_offs <= count * SLICE_SIZE as u32) by(bit_vector)
                requires count >= 1, start_offs <= 384, SLICE_SIZE as u32 == 65536;
        };
        assert(MEDIUM_OBJ_SIZE_MAX as int == 131072) by(compute_only);
        assert(block_size as int <= 131072);
        assert(131072 <= u32::MAX as int) by(compute_only);
        assert(block_size <= u32::MAX as usize) by(nonlinear_arith)
            requires block_size as int <= 131072, 131072 <= u32::MAX as int;
        assert(block_size as u32 > 0) by(bit_vector)
            requires block_size > 0, block_size <= u32::MAX as usize;
    }
    unused_page_get_mut_inner!(page_ptr, local, inner => {

        inner.xblock_size = block_size as u32;
        let start_offs = calculate_start_offset(block_size);
        let page_size = count * SLICE_SIZE as u32 - start_offs;
        inner.reserved = (page_size / block_size as u32) as u16;

        inner.free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
        inner.local_free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
    });

    proof! {
        assert(local.pages[page_id].inner.value().capacity == 0);
        assert(local.pages[page_id].inner.value().used == 0);
        assert(local.pages[page_id].inner.value().xblock_size == block_size as u32);
        assert(local.pages[page_id].inner.value().free.wf());
        assert(local.pages[page_id].inner.value().local_free.wf());
        assert(local.pages[page_id].inner.value().free.len() == 0);
        assert(local.pages[page_id].inner.value().local_free.len() == 0);
        assert(local.pages[page_id].inner.value().free.fixed_page());
        assert(local.pages[page_id].inner.value().local_free.fixed_page());
        assert(local.pages[page_id].inner.value().free.page_id() == page_id);
        assert(local.pages[page_id].inner.value().local_free.page_id() == page_id);
        assert(local.pages[page_id].inner.value().free.block_size() == block_size as nat);
        assert(local.pages[page_id].inner.value().local_free.block_size() == block_size as nat);
        assert(local.pages[page_id].inner.value().free.instance() == local.instance);
        assert(local.pages[page_id].inner.value().local_free.instance() == local.instance);
    }

    let ghost page_header_kind = PageHeaderKind::Normal(pq, block_size as int);
    proof! {
        local.page_organization = PageOrg::take_step::set_range_to_used(
            local.page_organization,
            page_header_kind);
    }

    let ghost enabled_page_state_map = Map::new(
        range,
        |pid: PageId| PageState {
            is_enabled: true,
            shared_access: local.unused_pages[pid],
            .. new_page_state_map[pid]
        });
    let ghost psa_map = Map::new(range, |pid: PageId| local.unused_pages[pid]);

    proof! {
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies pid.segment_id == page_id.segment_id
                && page_id.idx <= pid.idx < page_id.idx + n_slices by {
            assert(range.contains(pid));
        };
        assert forall |pid: PageId| pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + n_slices
            implies #[trigger] enabled_page_state_map.dom().contains(pid) by {
            assert(range.contains(pid));
        };
        assert(enabled_page_state_map.dom() =~= psa_map.dom());
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies psa_map[pid] == enabled_page_state_map[pid].shared_access by {
        };
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies enabled_page_state_map[pid].offset + page_id.idx == pid.idx by {
        };
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies thread_token.value().pages.dom().contains(pid)
                && !thread_token.value().pages[pid].is_enabled by {
            assert(new_page_state_map.dom().contains(pid));
        };
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies enabled_page_state_map[pid] == PageState {
                is_enabled: true,
                shared_access: psa_map[pid],
                .. thread_token.value().pages[pid]
            } by {
            assert(new_page_state_map.dom().contains(pid));
        };
    }

    let ghost unused_before_enable = local.unused_pages;
    proof! {
        assert(local.unused_pages.dom() == local_before_inner.unused_pages.dom());
        assert(local_before_inner.page_organization.popped == Popped::Ready(page_id, true));
        local_before_inner.page_organization.ready_popped_range_facts();
        assert forall |pid: PageId| #[trigger] range.contains(pid) implies
            local.unused_pages.dom().contains(pid)
        by {
            assert(local_before_inner.page_organization.pages.dom().contains(pid));
            assert(!local_before_inner.page_organization.pages[pid].is_used);
            assert(local_before_inner.unused_pages.dom().contains(pid));
        };
        assert(range.subset_of(local.unused_pages.dom()));
    }
    proof! {
        let tracked page_shared_access = local.unused_pages.tracked_remove_keys(range);
        assert(page_shared_access == unused_before_enable.restrict(range));
        assert(psa_map == unused_before_enable.restrict(range)) by {
            assert(psa_map.dom() =~= range);
            assert forall |pid: PageId| #[trigger] psa_map.dom().contains(pid) implies
                psa_map[pid] == unused_before_enable.restrict(range)[pid]
            by {
                assert(range.contains(pid));
            };
            assert forall |pid: PageId| #[trigger] unused_before_enable.restrict(range).dom().contains(pid) implies
                unused_before_enable.restrict(range)[pid] == psa_map[pid]
            by {
                assert(range.contains(pid));
            };
        };
        assert(page_shared_access == psa_map);
        let tracked thread_token = local.instance.page_enable(
            local.thread_id,
            page_id,
            n_slices as nat,
            enabled_page_state_map,
            psa_map,
            thread_token,
            page_shared_access,
        );
        local.thread_token = thread_token;
        local.psa = local.psa.union_prefer_right(psa_map);
    }

    proof! {
        assert(local.page_organization.popped == Popped::Used(page_id, true));
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by {
            if range.contains(pid) {
                assert(!local.unused_pages.dom().contains(pid));
                assert(local.page_organization.pages[pid].is_used);
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
        by {
            if range.contains(pid) {
                assert(psa_map.dom().contains(pid));
                assert(local.thread_token.value().pages[pid].shared_access == psa_map[pid]);
            }
        };
        assert(local.page_organization_valid());
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by {
            if range.contains(pid) {
                if pid == page_id {
                    let page_state = local.thread_token.value().pages[pid];
                    let page_inner = local.pages[pid].inner.value();
                    reveal(PageLocalAccess::wf);
                    reveal(PageInner::wf);
                    reveal(Page::wf);
                    assert(page_state.offset == 0);
                    assert(page_state.block_size == block_size as nat);
                    assert(page_state.num_blocks == 0);
                    assert(page_state.is_enabled);
                    assert(page_state.shared_access == local.psa[pid]);
                    assert(local.psa[pid] == psa_map[pid]);
                    assert(page_inner.capacity == 0);
                    assert(page_inner.used == 0);
                    assert(page_inner.xblock_size == block_size as u32);
                    assert(page_inner.free.wf());
                    assert(page_inner.local_free.wf());
                    assert(page_inner.free.len() == 0);
                    assert(page_inner.local_free.len() == 0);
                    assert(page_inner.free.fixed_page());
                    assert(page_inner.local_free.fixed_page());
                    assert(page_inner.free.page_id() == pid);
                    assert(page_inner.local_free.page_id() == pid);
                    assert(page_inner.free.block_size() == page_state.block_size);
                    assert(page_inner.local_free.block_size() == page_state.block_size);
                    assert(page_inner.free.instance() == local.instance);
                    assert(page_inner.local_free.instance() == local.instance);
                    assert(page_inner.capacity == page_state.num_blocks);
                    assert(page_inner.used + page_inner.free.len() + page_inner.local_free.len() == page_state.num_blocks);
                    assert(page_inner.xblock_size > 0);
                    assert(page_inner.wf(pid, page_state, local.instance));
                    assert(page_state.shared_access.wf(pid, page_state.block_size, local.instance));
                    assert(page_state.shared_access.points_to.value().count.id() == local.pages[pid].count.id());
                    assert(page_state.shared_access.points_to.value().inner.id() == local.pages[pid].inner.id());
                    assert(page_state.shared_access.points_to.value().prev.id() == local.pages[pid].prev.id());
                    assert(page_state.shared_access.points_to.value().next.id() == local.pages[pid].next.id());
                    assert(page_state.shared_access.points_to.is_init());
                    assert(local.page_count(pid) == count as int);
                    assert(page_inner.reserved as int == reserved_blocks);
                    assert(page_state.block_size as int == block_size as int);
                    reveal(page_init_reserved);
                    let ghost total = n_slices * (SLICE_SIZE as int) - start_offset(block_size as int);
                    assert(reserved_blocks == total / block_size as int);
                    lemma_fundamental_div_mod(total, block_size as int);
                    assert(0 <= total % block_size as int);
                    assert(reserved_blocks * block_size as int <= total) by(nonlinear_arith)
                        requires
                            reserved_blocks == total / block_size as int,
                            total == (total / block_size as int) * (block_size as int) + total % block_size as int,
                            0 <= total % block_size as int;
                    assert(wf_reserved(page_state.block_size as int, page_inner.reserved as int, local.page_count(pid))) by(nonlinear_arith)
                        requires
                            page_state.block_size as int == block_size as int,
                            page_inner.reserved as int == reserved_blocks,
                            local.page_count(pid) == n_slices,
                            reserved_blocks * block_size as int <= total,
                            total == n_slices * (SLICE_SIZE as int) - start_offset(block_size as int);
                    assert(local.pages[pid].wf(pid, page_state, local.instance));
                } else {
                    assert(local.pages[pid] == local_before_inner.pages[pid]);
                }
            }
        };
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by {
            assert(local_before_inner.pages[pid] == local.pages[pid] || pid == page_id);
        };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { };
        assert(local.wf_main_for_page_access());
    }

    let ghost local_before_extend = *local;
    proof! {
        assert(common_preserves(*old(local), local_before_extend));
        assert(local_before_extend.segments == old(local).segments);
        assert(local_before_extend.block_size(page_id) == block_size as int);
        assert(local_before_extend.page_capacity(page_id) == 0);
        assert(local_before_extend.page_reserved(page_id) == reserved_blocks);
        assert(block_start_at(
            page_id,
            local_before_extend.block_size(page_id),
            local_before_extend.page_reserved(page_id))
            == block_start_at(page_id, block_size as int, reserved_blocks));
        assert(block_start_at(page_id, block_size as int, reserved_blocks)
            <= segment_start(page_id.segment_id) + SEGMENT_SIZE);
        assert(block_start_at(
            page_id,
            local_before_extend.block_size(page_id),
            local_before_extend.page_capacity(page_id))
            == block_start_at(page_id, block_size as int, 0));
        assert((local_before_extend.page_reserved(page_id) - local_before_extend.page_capacity(page_id))
            * local_before_extend.block_size(page_id)
            == reserved_blocks * block_size as int) by(nonlinear_arith)
            requires
                local_before_extend.page_reserved(page_id) == reserved_blocks,
                local_before_extend.page_capacity(page_id) == 0,
                local_before_extend.block_size(page_id) == block_size as int;
        assert(local_before_extend.segments[page_id.segment_id].mem.pointsto_has_range(
            block_start_at(
                page_id,
                local_before_extend.block_size(page_id),
                local_before_extend.page_capacity(page_id)),
            (local_before_extend.page_reserved(page_id) - local_before_extend.page_capacity(page_id))
                * local_before_extend.block_size(page_id)));
        assert forall |sid: SegmentId| #[trigger] old(local).segments.dom().contains(sid) && old(local).mem_chunk_good(sid) implies
            local.mem_chunk_good(sid) by {
            if sid == page_id.segment_id {
                let count = old(local).page_organization.pages[page_id].count.unwrap();
                let range = page_id.range_from(0, count as int);
                assert(local.segments == old(local).segments);
                assert(local.page_organization.pages[page_id].count == old(local).page_organization.pages[page_id].count);
                assert(local.page_count(page_id) == count as int);
                assert(local.page_capacity(page_id) == 0);
                assert forall |pid: PageId| #[trigger] old(local).page_organization.pages.dom().contains(pid)
                    && !range.contains(pid) implies
                        local.page_organization.pages[pid] == old(local).page_organization.pages[pid]
                        && local.pages[pid] == old(local).pages[pid] by {
                    assert(local.page_organization.pages[pid] == old(local).page_organization.pages[pid]);
                    assert(local.pages[pid] == old(local).pages[pid]);
                };
                assert(set_int_range(
                    page_start(page_id),
                    page_start(page_id) + count as int * SLICE_SIZE as int)
                    <= local.commit_mask(page_id.segment_id).bytes(page_id.segment_id)
                        - local.decommit_mask(page_id.segment_id).bytes(page_id.segment_id)) by {
                    assert(local.commit_mask(page_id.segment_id) == old(local).commit_mask(page_id.segment_id));
                    assert(local.decommit_mask(page_id.segment_id) == old(local).decommit_mask(page_id.segment_id));
                };
                local.ready_to_used_zero_capacity_preserves_mem_chunk_good(*old(local), page_id);
            } else {
                assert(local.segments.dom().contains(sid));
                assert(local.segments[sid] == old(local).segments[sid]);
                assert(local.commit_mask(sid) == old(local).commit_mask(sid));
                assert(local.decommit_mask(sid) == old(local).decommit_mask(sid));
                assert forall |pid: PageId| #[trigger] old(local).page_organization.pages.dom().contains(pid)
                    && pid.segment_id == sid implies
                    local.page_organization.pages.dom().contains(pid) by {
                    assert(pid.segment_id != page_id.segment_id);
                    assert(local.page_organization.pages[pid] == old(local).page_organization.pages[pid]);
                }
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid)
                    && pid.segment_id == sid implies
                    old(local).page_organization.pages.dom().contains(pid) by {
                    assert(pid.segment_id != page_id.segment_id);
                }
                assert forall |pid: PageId| #[trigger] old(local).page_organization.pages.dom().contains(pid)
                    && pid.segment_id == sid implies
                    local.is_used_primary(pid) == old(local).is_used_primary(pid) by {
                    assert(pid.segment_id != page_id.segment_id);
                    assert(local.page_organization.pages[pid] == old(local).page_organization.pages[pid]);
                }
                assert forall |pid: PageId| #[trigger] old(local).page_organization.pages.dom().contains(pid)
                    && pid.segment_id == sid && old(local).is_used_primary(pid) implies
                    local.page_count(pid) == old(local).page_count(pid)
                    && local.page_capacity(pid) == old(local).page_capacity(pid)
                    && local.block_size(pid) == old(local).block_size(pid) by {
                    assert(pid.segment_id != page_id.segment_id);
                    assert(local.pages[pid] == old(local).pages[pid]);
                }
                local.mem_chunk_good_preserved_when_segment_pages_unchanged(*old(local), sid);
            }
        }
    }
    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local))
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn page_queue_of(page: PagePtr, Tracked(local): Tracked<&Local>) -> (res: (HeapPtr, usize, Ghost<int>))
    requires
        local.wf(),
        page.wf(),
        page.is_used_and_primary(*local),
    ensures
        res.0.wf(),
        res.0.is_in(*local),
        0 <= res.1 as int <= BIN_FULL as int,
        local.page_organization.valid_used_page(page.page_id@, res.1 as int, res.2@),
{
    let is_in_full = page.get_inner_ref(Tracked(&*local)).get_in_full();

    let ghost mut list_idx;

    proof! {
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(Local::page_organization_valid);
        reveal(page_organization_pages_match);
        reveal(page_organization_pages_match_data);
        assert(local.page_organization.pages.dom().contains(page.page_id@));
        assert(local.thread_token.value().pages.dom().contains(page.page_id@));
        assert(!local.unused_pages.dom().contains(page.page_id@));
        assert(local.page_organization.pages[page.page_id@].is_used);
        assert(local.page_organization.pages[page.page_id@].offset == Some(0nat));
        assert(local.page_organization.pages[page.page_id@].full == Some(is_in_full));
        if is_in_full {
            list_idx = local.page_organization.marked_full_is_in(page.page_id@);
        } else {
            list_idx = local.page_organization.marked_unfull_is_in(page.page_id@);
            match local.page_organization.pages[page.page_id@].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) => {
                    assert(size <= MEDIUM_OBJ_SIZE_MAX);
                    assert(MEDIUM_OBJ_SIZE_MAX == 131072) by(compute_only);
                    assert(local.pages[page.page_id@].inner.value().xblock_size as int == size);
                    assert(local.pages[page.page_id@].inner.value().xblock_size as int <= 131072);
                }
                None => { assert(false); }
            }
        }
    }

    let bin = if is_in_full {
        BIN_FULL as usize
    } else {
        bin(page.get_inner_ref(Tracked(&*local)).xblock_size as usize) as usize
    };

    let heap = page.get_heap(Tracked(&*local));
    proof! {
        if is_in_full {
            assert(bin == BIN_FULL as usize);
            assert(local.page_organization.valid_used_page(page.page_id@, bin as int, list_idx));
        } else {
            assert(valid_bin_idx(bin as int));
            assert(bin as int <= BIN_HUGE as int);
            assert(BIN_HUGE < BIN_FULL) by(compute_only);
            assert(local.page_organization.valid_used_page(page.page_id@, bin as int, list_idx));
        }
    }
    (heap, bin, Ghost(list_idx))
}

const MAX_RETIRE_SIZE: u32 = MEDIUM_OBJ_SIZE_MAX as u32;

}

verus!{
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
pub fn page_retire(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        page.wf(),
        page.is_used_and_primary(*old(local)),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    let (heap, pq, Ghost(list_idx)) = page_queue_of(page, Tracked(&*local));
    if likely(
        page.get_inner_ref(Tracked(&*local)).xblock_size <= MAX_RETIRE_SIZE
          && !(heap.get_pages(Tracked(&*local))[pq].block_size > MEDIUM_OBJ_SIZE_MAX as usize)
    )
    {
        if heap.get_pages(Tracked(&*local))[pq].last.addr() == page.page_ptr.addr() &&
            heap.get_pages(Tracked(&*local))[pq].first.addr() == page.page_ptr.addr()
        {
            let RETIRE_CYCLES = 8;
            let ghost local_before_retire_expire = *local;
            page_get_mut_inner!(page, local, inner => {
                let xb = inner.xblock_size as u64;
                inner.set_retire_expire(1 + (if xb <= SMALL_OBJ_SIZE_MAX { RETIRE_CYCLES } else { RETIRE_CYCLES/4 }));
            });

            if pq < heap.get_page_retired_min(Tracked(&*local)) {
                heap.set_page_retired_min(Tracked(&mut *local), pq);
            }
            if pq > heap.get_page_retired_max(Tracked(&*local)) {
                heap.set_page_retired_max(Tracked(&mut *local), pq);
            }

            proof! {
                reveal(Local::wf);
                reveal(Local::wf_main);
                reveal(Local::page_organization_valid);
                reveal(HeapLocalAccess::wf);
                reveal(HeapLocalAccess::wf_basic);
                reveal(PageLocalAccess::wf);
                reveal(PageInner::wf);
                reveal(page_organization_pages_match);
                reveal(page_organization_pages_match_data);
                assert(local.page_organization.popped == Popped::No);
                assert(is_tld_ptr(local.tld.ptr(), local.tld_id));
                assert(local.thread_token.instance_id() == local.instance.id());
                assert(local.thread_token.key() == local.thread_id);
                assert(local.thread_id == local.is_thread@);
                assert(local.thread_token.value().segments.dom() == local.segments.dom());
                assert(local.thread_token.value().heap_id == local.heap_id);
                assert(local.heap.wf(local.heap_id, local.thread_token.value().heap, local.tld_id, local.instance.id(), local.page_empty_global@.s.points_to.ptr()));
                assert forall |page_id| #[trigger] local.pages.dom().contains(page_id) implies
                    (local.unused_pages.dom().contains(page_id) <==> !local.thread_token.value().pages.dom().contains(page_id)) by { };
                assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
                assert(page_organization_queues_match(
                    local.page_organization.unused_dlist_headers,
                    local.tld.value().segments.span_queue_headers@));
                assert(page_organization_used_queues_match(
                    local.page_organization.used_dlist_headers,
                    local.heap.pages.value()@));
                assert(page_organization_segments_match(local.page_organization.segments, local.segments));
                assert(local.page_organization == local_before_retire_expire.page_organization);
                assert(local.psa == local_before_retire_expire.psa);
                assert(local.pages.dom() == local_before_retire_expire.pages.dom());
                assert(local.page_organization.pages.dom() == local.pages.dom());
                assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
                    page_organization_pages_match_data(
                        local.page_organization.pages[pid],
                        local.pages[pid],
                        local.psa[pid],
                        pid,
                        local.page_organization.popped)
                by {
                    if pid == page.page_id@ {
                        assert(page_organization_pages_match_data(
                            local_before_retire_expire.page_organization.pages[pid],
                            local_before_retire_expire.pages[pid],
                            local_before_retire_expire.psa[pid],
                            pid,
                            local_before_retire_expire.page_organization.popped));
                        assert(local.pages[pid].count == local_before_retire_expire.pages[pid].count);
                        assert(local.pages[pid].prev == local_before_retire_expire.pages[pid].prev);
                        assert(local.pages[pid].next == local_before_retire_expire.pages[pid].next);
                        assert(local.pages[pid].inner.id() == local_before_retire_expire.pages[pid].inner.id());
                        assert(local.pages[pid].inner.value().flags0 == local_before_retire_expire.pages[pid].inner.value().flags0);
                        assert(local.pages[pid].inner.value().flags1 == local_before_retire_expire.pages[pid].inner.value().flags1);
                        assert(local.pages[pid].inner.value().capacity == local_before_retire_expire.pages[pid].inner.value().capacity);
                        assert(local.pages[pid].inner.value().reserved == local_before_retire_expire.pages[pid].inner.value().reserved);
                        assert(local.pages[pid].inner.value().free == local_before_retire_expire.pages[pid].inner.value().free);
                        assert(local.pages[pid].inner.value().used == local_before_retire_expire.pages[pid].inner.value().used);
                        assert(local.pages[pid].inner.value().xblock_size == local_before_retire_expire.pages[pid].inner.value().xblock_size);
                        assert(local.pages[pid].inner.value().local_free == local_before_retire_expire.pages[pid].inner.value().local_free);
                        assert(page_organization_pages_match_data(
                            local.page_organization.pages[pid],
                            local.pages[pid],
                            local.psa[pid],
                            pid,
                            local.page_organization.popped));
                    } else {
                        assert(local.pages[pid] == local_before_retire_expire.pages[pid]);
                        assert(page_organization_pages_match_data(
                            local_before_retire_expire.page_organization.pages[pid],
                            local_before_retire_expire.pages[pid],
                            local_before_retire_expire.psa[pid],
                            pid,
                            local_before_retire_expire.page_organization.popped));
                    }
                };
                assert(page_organization_pages_match(
                    local.page_organization.pages,
                    local.pages,
                    local.psa,
                    local.page_organization.popped));
                assert(local.page_organization_valid());
                assert(local.tld.is_init());
                assert forall |pid: PageId| (#[trigger] local.pages.dom().contains(pid))
                    && local.thread_token.value().pages.dom().contains(pid) implies
                        local.pages.index(pid).wf(
                            pid,
                            local.thread_token.value().pages.index(pid),
                            local.instance,
                        ) by {
                    if pid == page.page_id@ {
                        assert(local.pages[pid].wf(pid, local.thread_token.value().pages[pid], local.instance));
                    } else {
                        assert(local.pages[pid] == local_before_retire_expire.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] local.pages.dom().contains(pid))
                    && local.unused_pages.dom().contains(pid) implies
                        local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance) by {
                    if pid == page.page_id@ {
                        assert(local.thread_token.value().pages.dom().contains(page.page_id@));
                        assert(!local.unused_pages.dom().contains(page.page_id@));
                    } else {
                        assert(local.pages[pid] == local_before_retire_expire.pages[pid]);
                    }
                };
                assert forall |sid| #[trigger] local.segments.dom().contains(sid) implies
                    local.segments[sid].wf(
                        sid,
                        local.thread_token.value().segments.index(sid),
                        local.instance,
                    ) by {
                    assert(local.segments[sid] == local_before_retire_expire.segments[sid]);
                };
                assert forall |sid| #[trigger] local.segments.dom().contains(sid) implies
                    local.mem_chunk_good(sid) by {
                    assert(local_before_retire_expire.segments.dom().contains(sid));
                    assert(local_before_retire_expire.mem_chunk_good(sid));
                    assert(local.segments == local_before_retire_expire.segments);
                    assert(local.page_organization == local_before_retire_expire.page_organization);
                    assert(local.pages.dom() == local_before_retire_expire.pages.dom());
                    assert forall |pid: PageId| local.page_organization.pages.dom().contains(pid) && pid != page.page_id@ implies
                        local.pages[pid] == local_before_retire_expire.pages[pid] by {
                        assert(local.pages[pid] == local_before_retire_expire.pages[pid]);
                    };
                    assert(local.page_count(page.page_id@) == local_before_retire_expire.page_count(page.page_id@));
                    assert(local.page_capacity(page.page_id@) == local_before_retire_expire.page_capacity(page.page_id@));
                    assert(local.block_size(page.page_id@) == local_before_retire_expire.block_size(page.page_id@));
                    local.page_inner_update_preserves_mem_chunk_good(local_before_retire_expire, sid, page.page_id@);
                };
                assert(local.checked_token.instance_id() == local.instance.id());
                assert(local.checked_token.key() == local.thread_id);
                assert(local.my_inst.instance_id() == local.instance.id());
                assert(local.my_inst.value() == local.instance.id());
                assert(local.page_empty_global@.wf_empty_page_global());
                assert(local.wf_main());
                assert(local.wf());
                assert(local.inst() == old(local).inst());
                assert(common_preserves(*old(local), local_before_retire_expire));
                assert(common_preserves(local_before_retire_expire, *local));
                assert(common_preserves(*old(local), *local));
                assert forall |heap: HeapPtr| heap.is_in(*old(local)) implies heap.is_in(*local) by {
                    assert((*old(local)).heap_id == (*local).heap_id);
                };
            }

            return;
        }
    }

    page_free(page, pq, false, Tracked(&mut *local), Ghost(list_idx));
}
}

verus!{

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn page_free(page: PagePtr, pq: usize, force: bool, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>)
    requires
        old(local).wf(),
        page.wf(),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    let ghost local_before_aligned = *local;
    proof! {
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(Local::page_organization_valid);
        assert(local.page_organization.popped == Popped::No);
        assert(page.is_used_and_primary(*local));
        assert(page.is_in(*local));
    }
    page_get_mut_inner!(page, local, inner => {
        inner.set_has_aligned(false);
    });
    proof! {
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(Local::page_organization_valid);
        reveal(HeapLocalAccess::wf);
        reveal(HeapLocalAccess::wf_basic);
        reveal(PageLocalAccess::wf);
        reveal(PageInner::wf);
        reveal(page_organization_pages_match);
        reveal(page_organization_pages_match_data);
        assert(local.page_organization == local_before_aligned.page_organization);
        assert(local.psa == local_before_aligned.psa);
        assert(local.pages.dom() == local_before_aligned.pages.dom());
        assert(page_organization_pages_match(
            local_before_aligned.page_organization.pages,
            local_before_aligned.pages,
            local_before_aligned.psa,
            local_before_aligned.page_organization.popped));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            page_organization_pages_match_data(
                local.page_organization.pages[pid],
                local.pages[pid],
                local.psa[pid],
                pid,
                local.page_organization.popped)
        by {
            if pid == page.page_id@ {
                assert(page_organization_pages_match_data(
                    local_before_aligned.page_organization.pages[pid],
                    local_before_aligned.pages[pid],
                    local_before_aligned.psa[pid],
                    pid,
                    local_before_aligned.page_organization.popped));
                assert(local.pages[pid].count == local_before_aligned.pages[pid].count);
                assert(local.pages[pid].prev == local_before_aligned.pages[pid].prev);
                assert(local.pages[pid].next == local_before_aligned.pages[pid].next);
                assert(local.pages[pid].inner.id() == local_before_aligned.pages[pid].inner.id());
                assert(local.pages[pid].inner.value().capacity == local_before_aligned.pages[pid].inner.value().capacity);
                assert(local.pages[pid].inner.value().reserved == local_before_aligned.pages[pid].inner.value().reserved);
                assert(local.pages[pid].inner.value().free == local_before_aligned.pages[pid].inner.value().free);
                assert(local.pages[pid].inner.value().used == local_before_aligned.pages[pid].inner.value().used);
                assert(local.pages[pid].inner.value().xblock_size == local_before_aligned.pages[pid].inner.value().xblock_size);
                assert(local.pages[pid].inner.value().local_free == local_before_aligned.pages[pid].inner.value().local_free);
                assert(local.pages[pid].inner.value().in_full() == local_before_aligned.pages[pid].inner.value().in_full());
            } else {
                assert(local.pages[pid] == local_before_aligned.pages[pid]);
                assert(page_organization_pages_match_data(
                    local_before_aligned.page_organization.pages[pid],
                    local_before_aligned.pages[pid],
                    local_before_aligned.psa[pid],
                    pid,
                    local_before_aligned.page_organization.popped));
            }
        };
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by {
            if pid == page.page_id@ {
                assert(local.thread_token.value().pages.dom().contains(page.page_id@));
                assert(!local.unused_pages.dom().contains(page.page_id@));
            } else {
                assert(local.pages[pid] == local_before_aligned.pages[pid]);
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
        assert(local.page_organization_valid());
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| (#[trigger] local.pages.dom().contains(pid))
            && local.thread_token.value().pages.dom().contains(pid) implies
                local.pages.index(pid).wf(
                    pid,
                    local.thread_token.value().pages.index(pid),
                    local.instance,
                )
        by {
            if pid == page.page_id@ {
                assert(local.pages[pid].wf(pid, local.thread_token.value().pages[pid], local.instance));
            } else {
                assert(local.pages[pid] == local_before_aligned.pages[pid]);
            }
        };
        assert forall |pid: PageId| (#[trigger] local.pages.dom().contains(pid))
            && local.unused_pages.dom().contains(pid) implies
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by {
            if pid == page.page_id@ {
                assert(local.thread_token.value().pages.dom().contains(page.page_id@));
                assert(!local.unused_pages.dom().contains(page.page_id@));
            } else {
                assert(local.pages[pid] == local_before_aligned.pages[pid]);
            }
        };
        assert forall |sid| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(
                sid,
                local.thread_token.value().segments.index(sid),
                local.instance,
            )
        by {
            assert(local.segments[sid] == local_before_aligned.segments[sid]);
        };
        assert forall |sid| #[trigger] local.segments.dom().contains(sid) implies
            local.mem_chunk_good(sid)
        by {
            assert(local_before_aligned.segments.dom().contains(sid));
            assert(local_before_aligned.mem_chunk_good(sid));
            assert(local.segments == local_before_aligned.segments);
            assert(local.page_organization == local_before_aligned.page_organization);
            assert(local.pages.dom() == local_before_aligned.pages.dom());
            assert forall |pid: PageId| local.page_organization.pages.dom().contains(pid) && pid != page.page_id@ implies
                local.pages[pid] == local_before_aligned.pages[pid]
            by {
                assert(local.pages[pid] == local_before_aligned.pages[pid]);
            };
            assert(local.page_count(page.page_id@) == local_before_aligned.page_count(page.page_id@));
            assert(local.page_capacity(page.page_id@) == local_before_aligned.page_capacity(page.page_id@));
            assert(local.block_size(page.page_id@) == local_before_aligned.block_size(page.page_id@));
            local.page_inner_update_preserves_mem_chunk_good(local_before_aligned, sid, page.page_id@);
        };
        assert(local.wf_main());
        assert(local.wf());
        assert(local.inst() == old(local).inst());
        assert(page.is_used_and_primary(*local));
        assert(page.is_in(*local));
        assert(local.page_organization.valid_used_page(page.page_id@, pq as int, list_idx));
        assert forall |heap: HeapPtr| heap.is_in(*old(local)) implies heap.is_in(*local) by {
            assert((*old(local)).heap_id == (*local).heap_id);
        };
    }
    let heap = page.get_heap(Tracked(&*local));

    page_queue_remove(heap, pq, page, Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));
    let ghost local_after_remove = *local;

    let tld = heap.get_ref(Tracked(&*local)).tld_ptr;
    crate::segment::segment_page_free(page, force, tld, Tracked(&mut *local));
    proof {
        assert(common_preserves(*old(local), local_after_remove));
        assert(common_preserves(local_after_remove, *local));
        assert(common_preserves(*old(local), *local));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn page_to_full(page: PagePtr, heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>,
      Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
        valid_bin_idx(pq as int),
        old(local).page_organization.valid_used_page(page.page_id@, pq as int, list_idx),
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
        final(local).inst() == old(local).inst(),
        heap.wf(),
        heap.is_in(*final(local)),
        page.wf(),
        page.is_used_and_primary(*final(local)),
        common_preserves(*old(local), *final(local)),
        old(local).page_organization.pages[page.page_id@].dlist_entry.unwrap().next == Some(next_id) ==>
            final(local).page_organization.valid_used_page(next_id, pq as int, list_idx),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    let ghost had_next = old(local).page_organization.pages[page.page_id@].dlist_entry.unwrap().next == Some(next_id);
    page_queue_enqueue_from(heap, BIN_FULL as usize, pq, page, Tracked(&mut *local),
        Ghost(list_idx), Ghost(next_id));
    let ghost local_before_collect = *local;
    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));
    proof! {
        if had_next {
            assert(local_before_collect.page_organization.valid_used_page(next_id, pq as int, list_idx));
            assert(local.page_organization == local_before_collect.page_organization);
            assert(local.page_organization.valid_used_page(next_id, pq as int, list_idx));
        }
        assert(heap.is_in(local_before_collect));
        assert(heap.is_in(*local));
        assert forall |heap0: HeapPtr| heap0.is_in(*old(local)) implies heap0.is_in(*local) by {
            assert(heap0.is_in(local_before_collect));
        };
    }
}

}

verus!{
#[cfg(any())]
#[verus_verify]
pub fn page_unfull(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        page.wf(),
        page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.pages[page.page_id@].offset == Some(0nat),
        old(local).page_organization.pages[page.page_id@].full != Some(false),
        old(local).page_organization.pages[page.page_id@].is_used,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    let heap = page.get_heap(Tracked(&*local));
    let pq = bin(page.get_inner_ref(Tracked(&mut *local)).xblock_size as usize);
    let ghost list_idx = local.page_organization.marked_full_is_in(page.page_id@);
    page_queue_enqueue_from(heap, pq as usize, BIN_FULL as usize, page,
        Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));
}

}

#[cfg(not(any()))]
verus!{
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
pub fn page_unfull(page: PagePtr, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        page.wf(),
        page.is_in(*old(local)),
        page.is_used_and_primary(*old(local)),
        old(local).page_organization.pages[page.page_id@].offset == Some(0nat),
        old(local).page_organization.pages[page.page_id@].full != Some(false),
        old(local).page_organization.pages[page.page_id@].is_used,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    let heap = page.get_heap(Tracked(&*local));
    let ghost list_idx = local.page_organization.marked_full_is_in(page.page_id@);
    let page_inner = page.get_inner_ref(Tracked(&*local));
    proof! {
        reveal(Local::page_organization_valid);
        assert(page_inner.xblock_size == local.page_inner(page.page_id@).xblock_size);
        match local.page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(_, size)) => {
                assert(page_organization_pages_match(
                    local.page_organization.pages,
                    local.pages,
                    local.psa,
                    local.page_organization.popped));
                assert(page_organization_pages_match_data(
                    local.page_organization.pages[page.page_id@],
                    local.pages[page.page_id@],
                    local.psa[page.page_id@],
                    page.page_id@,
                    local.page_organization.popped));
                assert(page_inner.xblock_size == size);
                assert(size <= MEDIUM_OBJ_SIZE_MAX);
                assert(MEDIUM_OBJ_SIZE_MAX as int == 131072) by(compute_only);
                assert(page_inner.xblock_size as int <= 131072);
            }
            None => { assert(false); }
        }
    }
    let pq = bin(page_inner.xblock_size as usize);
    proof! {
        reveal(Local::page_organization_valid);
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        match local.page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(bin_idx, size)) => {
                assert(page_organization_pages_match_data(
                    local.page_organization.pages[page.page_id@],
                    local.pages[page.page_id@],
                    local.psa[page.page_id@],
                    page.page_id@,
                    local.page_organization.popped));
                assert(local.page_inner(page.page_id@).xblock_size == size);
                assert(pq as int == smallest_bin_fitting_size(size));
                assert(pq as int == bin_idx);
            }
            None => { assert(false); }
        }
    }
    page_queue_enqueue_from(heap, pq as usize, BIN_FULL as usize, page,
        Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));
}

}

verus!{
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
fn page_queue_enqueue_from(heap: HeapPtr, to: usize, from: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        page.wf(),
        valid_bin_idx(from as int) || from == BIN_FULL as usize,
        valid_bin_idx(to as int) || to == BIN_FULL as usize,
        old(local).page_organization.valid_used_page(page.page_id@, from as int, list_idx),
        match old(local).page_organization.pages[page.page_id@].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) =>
                (to as int != BIN_FULL ==> to as int == bin)
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
        old(local).page_organization.pages[page.page_id@].dlist_entry.unwrap().next == Some(next_id) ==>
            final(local).page_organization.valid_used_page(next_id, from as int, list_idx),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    let ghost local_before_remove = *local;
    let ghost had_next = local_before_remove.page_organization.pages[page.page_id@].dlist_entry.unwrap().next == Some(next_id);
    proof! {
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(Local::page_organization_valid);
        reveal(page_organization_pages_match);
        assert(local.page_organization.pages.dom().contains(page.page_id@));
        assert(local.pages.dom().contains(page.page_id@));
        assert(page.is_in(*local));
    }
    page_queue_remove(heap, from, page, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));
    let ghost local_after_remove = *local;
    proof! {
        if had_next {
            assert(local.page_organization.valid_used_page(next_id, from as int, list_idx));
            reveal(PageOrg::State::valid_used_page);
            assert(next_id != page.page_id@);
        }
        assert(local.page_organization.pages[page.page_id@].page_header_kind
            == local_before_remove.page_organization.pages[page.page_id@].page_header_kind);
    }
    page_queue_push_back(heap, to, page, Tracked(&mut *local), Ghost(next_id), Ghost(from as int), Ghost(list_idx));
    proof! {
        assert(common_preserves(local_before_remove, local_after_remove));
        assert(common_preserves(local_after_remove, *local));
        assert(common_preserves(*old(local), *local));
        assert forall |heap0: HeapPtr| heap0.is_in(*old(local)) implies heap0.is_in(*local) by {
            assert(heap0.is_in(local_before_remove));
        };
    }
}

pub fn page_try_use_delayed_free(page: PagePtr, delay: usize, override_never: bool, Tracked(local): Tracked<&Local>) -> bool
    requires
        local.wf(),
        page.wf(),
        page.is_used_and_primary(*local),
        delay == 0,
        !override_never,
    ensures
        local.wf(),
        page.wf(),
        page.is_used_and_primary(*local),
{
    proof! {
        assert(local.wf_main());
        assert(local.thread_token.value().pages.dom().contains(page.page_id@));
        assert(!local.unused_pages.dom().contains(page.page_id@));
        assert(!page.is_in_unused(*local));
        assert(local.pages[page.page_id@].wf(
            page.page_id@,
            local.thread_token.value().pages.index(page.page_id@),
            local.instance,
        ));
        assert(local.thread_token.value().pages[page.page_id@].offset == 0);
        assert(local.thread_token.value().pages.index(page.page_id@).shared_access.wf(
            page.page_id@,
            local.thread_token.value().pages[page.page_id@].block_size,
            local.instance,
        ));
    }
    page.get_ref(Tracked(&*local)).xthread_free.try_use_delayed_free(delay, override_never)
}

}
