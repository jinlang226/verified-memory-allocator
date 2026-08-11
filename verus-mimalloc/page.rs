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

#[verifier::external_body]
fn find_free_page(heap_ptr: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
{
    let pq = bin(size) as usize;


    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };

    if page.page_ptr.addr() != 0 {
        crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            return page;
        }
    }

    page_queue_find_free_ex(heap_ptr, pq, true, Tracked(&mut *local))
}

#[verifier::external_body]
fn page_queue_find_free_ex(heap_ptr: HeapPtr, pq: usize, first_try: bool, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
{
    let mut page = PagePtr { page_ptr: heap_ptr.get_pages(Tracked(&*local))[pq].first, page_id: Ghost(local.page_organization.used_dlist_headers[pq as int].first.unwrap()) };
    let ghost mut list_idx = 0;

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

        if !page.get_inner_ref(Tracked(&*local)).free.is_empty() {
            break;
        }

        if page.get_inner_ref(Tracked(&*local)).capacity < page.get_inner_ref(Tracked(&*local)).reserved {
            //let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
            //assert(local.is_used_primary(page.page_id@));
            crate::alloc_generic::page_extend_free(page, Tracked(&mut *local));
            break;
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
        return page;
    }
}

#[verifier::external_body]
fn page_fresh(heap_ptr: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
{
    let block_size = heap_ptr.get_pages(Tracked(&*local))[pq].block_size;
    page_fresh_alloc(heap_ptr, pq, block_size, 0, Tracked(&mut *local))
}

#[verifier::external_body]
fn page_fresh_alloc(heap_ptr: HeapPtr, pq: usize, block_size: usize, page_alignment: usize, Tracked(local): Tracked<&mut Local>) -> (page: PagePtr)
{
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;
    let page_ptr = crate::segment::segment_page_alloc(heap_ptr, block_size, page_alignment, tld_ptr, Tracked(&mut *local));
    if page_ptr.page_ptr.addr() == 0 {
        return page_ptr;
    }

    let full_block_size: usize = block_size; // TODO handle pq == NULL or huge pages
    let tld_ptr = heap_ptr.get_ref(Tracked(&*local)).tld_ptr;


    page_init(heap_ptr, page_ptr, full_block_size, tld_ptr, Tracked(&mut *local), Ghost(pq as int));
    page_queue_push(heap_ptr, pq, page_ptr, Tracked(&mut *local));

    return page_ptr;
}

// READY --> USED
#[verifier::external_body]
fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
{
    let ghost page_id = page_ptr.page_id@;
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost n_blocks = n_slices * SLICE_SIZE / block_size as int;
    let ghost range = page_id.range_from(0, n_slices as int);

    let ghost new_page_state_map = Map::new(
            range,
            |pid: PageId| PageState {
                offset: pid.idx - page_id.idx,
                block_size: block_size as nat,
                num_blocks: 0,
                shared_access: arbitrary(),
                is_enabled: false,
            });

    

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
        //assert(page.xheap.wf(local.instance, page_ptr.page_id@));
    });

    unused_page_get_mut_inner!(page_ptr, local, inner => {

        inner.xblock_size = block_size as u32;
        let start_offs = calculate_start_offset(block_size);
        //proof {
        //    assert(count * SLICE_SIZE as u32 >= start_offs);
        //}
        let page_size = count * SLICE_SIZE as u32 - start_offs;
        inner.reserved = (page_size / block_size as u32) as u16;

        inner.free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
        inner.local_free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));

        /*assert(inner.capacity == 0);
        assert(inner.free.wf());
        assert(inner.local_free.wf());
        assert(inner.free.block_size() == block_size);
        assert(inner.local_free.block_size() == block_size);
        assert(inner.free.len() == 0);
        assert(inner.local_free.len() == 0);
        assert(inner.free.fixed_page());
        assert(inner.local_free.fixed_page());
        assert(inner.free.page_id() == page_id);
        assert(inner.local_free.page_id() == page_id);
        assert(inner.free.instance() == local.instance);
        assert(inner.local_free.instance() == local.instance);
        assert(inner.used == 0);

        assert(inner.reserved == page_size as int / block_size as int);*/

    });


    //assert(local.is_used_primary(page_ptr.page_id@));
    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local))
}

#[verifier::external_body]
fn page_queue_of(page: PagePtr, Tracked(local): Tracked<&Local>) -> (res: (HeapPtr, usize, Ghost<int>))
{
    let is_in_full = page.get_inner_ref(Tracked(&*local)).get_in_full();

    let ghost mut list_idx;

    let bin = if is_in_full {
        BIN_FULL as usize
    } else {
        bin(page.get_inner_ref(Tracked(&*local)).xblock_size as usize) as usize
    };

    let heap = page.get_heap(Tracked(&*local));
    (heap, bin, Ghost(list_idx))
}

const MAX_RETIRE_SIZE: u32 = MEDIUM_OBJ_SIZE_MAX as u32;

#[verifier::external_body]
pub fn page_retire(page: PagePtr, Tracked(local): Tracked<&mut Local>)
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

            return;
        }
    }

    page_free(page, pq, false, Tracked(&mut *local), Ghost(list_idx));
}

#[verifier::external_body]
fn page_free(page: PagePtr, pq: usize, force: bool, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>)
{
    page_get_mut_inner!(page, local, inner => {
        inner.set_has_aligned(false);
    });
    let heap = page.get_heap(Tracked(&*local));

    page_queue_remove(heap, pq, page, Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));

    let tld = heap.get_ref(Tracked(&*local)).tld_ptr;
    crate::segment::segment_page_free(page, force, tld, Tracked(&mut *local));
}

#[verifier::external_body]
fn page_to_full(page: PagePtr, heap: HeapPtr, pq: usize, Tracked(local): Tracked<&mut Local>,
      Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
{
    page_queue_enqueue_from(heap, BIN_FULL as usize, pq, page, Tracked(&mut *local),
        Ghost(list_idx), Ghost(next_id));
    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));
}

#[verifier::external_body]
pub fn page_unfull(page: PagePtr, Tracked(local): Tracked<&mut Local>)
{
    let heap = page.get_heap(Tracked(&*local));
    let pq = bin(page.get_inner_ref(Tracked(&mut *local)).xblock_size as usize);
    let ghost list_idx = local.page_organization.marked_full_is_in(page.page_id@);
    page_queue_enqueue_from(heap, pq as usize, BIN_FULL as usize, page,
        Tracked(&mut *local), Ghost(list_idx), Ghost(arbitrary()));
}

#[verifier::external_body]
fn page_queue_enqueue_from(heap: HeapPtr, to: usize, from: usize, page: PagePtr, Tracked(local): Tracked<&mut Local>, Ghost(list_idx): Ghost<int>, Ghost(next_id): Ghost<PageId>)
{
    page_queue_remove(heap, from, page, Tracked(&mut *local), Ghost(list_idx), Ghost(next_id));
    page_queue_push_back(heap, to, page, Tracked(&mut *local), Ghost(next_id), Ghost(from as int), Ghost(list_idx));
}

#[verifier::external_body]
pub fn page_try_use_delayed_free(page: PagePtr, delay: usize, override_never: bool, Tracked(local): Tracked<&Local>) -> bool
{
    page.get_ref(Tracked(&*local)).xthread_free.try_use_delayed_free(delay, override_never)
}

}
