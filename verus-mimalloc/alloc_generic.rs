#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId};
use crate::types::*;
use crate::config::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::os_mem_util::*;

verus!{

#[verifier::external_body]
pub fn malloc_generic(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    huge_alignment: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
{
    // TODO heap initialization

    // TODO deferred free?

    heap_delayed_free_partial(heap, Tracked(&mut *local));

    let page = crate::page::find_page(heap, size, huge_alignment, Tracked(&mut *local));
    if unlikely(page.is_null()) {
        todo();
    }

    if unlikely(zero && page.get_block_size(Tracked(&*local)) == 0) {
        todo(); loop{}
    } else {
        crate::alloc_fast::page_malloc(heap, page, size, zero, Tracked(&mut *local))
    }
}

#[verifier::external_body]
pub fn page_free_collect(
    page_ptr: PagePtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>
)
{
    if force || page_ptr.get_ref(Tracked(&*local)).xthread_free.atomic.load().addr() != 0 {
        page_thread_free_collect(page_ptr, Tracked(&mut *local));
    }

    let ghost old_local = *local;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        if !page_inner.local_free.is_empty() {
            if likely(page_inner.free.is_empty()) {
                // Move local_free to free
                let mut ll = LL::new(Ghost(page_inner.local_free.page_id()), Ghost(page_inner.local_free.fixed_page()), Ghost(page_inner.local_free.instance()), Ghost(page_inner.local_free.block_size()), Ghost(None));
                core::mem::swap(&mut ll, &mut page_inner.local_free);
                page_inner.free = ll;
            } else if force {
                page_inner.free.append(&mut page_inner.local_free);
            }
        }
    });

}

#[verifier::external_body]
fn page_thread_free_collect(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
{
    let mut ll = page_ptr.get_ref(Tracked(&*local)).xthread_free.take();

    if ll.is_empty() { return; }

    page_get_mut_inner!(page_ptr, local, page_inner => {
        let count = page_inner.local_free.append(&mut ll);

        // this relies on counting the block tokens
        //assert(page_inner.used >= count);

        page_inner.used = page_inner.used - count;
    });

}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn page_free_list_extend(
    page_ptr: PagePtr,
    bsize: usize,
    extend: usize,
    Tracked(local): Tracked<&mut Local>
)
{
    let ghost page_id = page_ptr.page_id@;

    let capacity = page_ptr.get_inner_ref(Tracked(&*local)).capacity;

    let pag_start = calculate_page_start(page_ptr, bsize);
    let start = calculate_page_block_at(pag_start, bsize, capacity as usize,
        Ghost(page_ptr.page_id@));
    let start = page_ptr.page_ptr.with_addr(start) as *mut u8;

    //assert((capacity + extend) as usize as int == capacity + extend);
    let x = capacity as usize + extend - 1;

    let last = calculate_page_block_at(pag_start, bsize, x,
        Ghost(page_ptr.page_id@));
    let last = page_ptr.page_ptr.with_addr(last) as *mut u8;

    let ghost rng_start = block_start_at(page_id, bsize as int, capacity as int);
    let ghost rng_size = extend * bsize;
    let ghost segment_id = page_id.segment_id;
    let tracked mut seg = local.segments.tracked_remove(segment_id);
    let tracked mut pt = seg.mem.take_points_to_range(rng_start, rng_size);

    let tracked mut thread_token = local.take_thread_token();
    let tracked mut checked_token = local.take_checked_token();

    let ghost mut cap_nat;
    let ghost mut extend_nat;

    //assert(page_inner.wf(page_ptr.page_id@,
    //    local.thread_token.value().pages.index(page_ptr.page_id@),
    //    local.instance));


    let tracked (Tracked(_thread_token), Tracked(block_tokens), Ghost(_s), Tracked(_checked_token)) = local.instance.page_mk_block_tokens(
        // params
        local.thread_id,
        page_ptr.page_id@,
        cap_nat as nat,
        cap_nat as nat + extend_nat as nat,
        bsize as nat,
        // input ghost state
        thread_token,
        checked_token,
    );
    let tracked block_tokens = block_tokens.into_map();
    let tracked mut block_tokens = Map::tracked_map_keys(block_tokens,
        Map::<int, BlockId>::new(
          Set::range(cap_nat as int, cap_nat as int + extend_nat),
          |i: int| BlockId {
              page_id: page_ptr.page_id@,
              idx: i as nat,
              slice_idx: BlockId::get_slice_idx(page_ptr.page_id@, i as nat, bsize as nat),
              block_size: bsize as nat
          }
        ));

    // TODO


    page_get_mut_inner!(page_ptr, local, page_inner => {
        page_inner.free.prepend_contiguous_blocks(
            start, last, bsize,
            // ghost args:
            Ghost(cap_nat), Ghost(extend_nat),
            // tracked args:
            Tracked(&mut pt),
            Tracked(&mut block_tokens));

        // note: mimalloc has this line in the parent function, mi_page_extend_free,
        // but it's easier to just do it here to preserve local.wf()
        page_inner.capacity = page_inner.capacity + extend as u16;
    });


}

const MIN_EXTEND: usize = 4;
const MAX_EXTEND_SIZE: u32 = 4096;

#[verifier::external_body]
pub fn page_extend_free(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
{
    let page_inner = page_ptr.get_inner_ref(Tracked(&*local));

    /*proof {
        assert(page_inner.wf(page_ptr.page_id@,
            local.thread_token.value().pages.index(page_ptr.page_id@),
            local.instance));
    }*/

    let reserved = page_inner.reserved;
    let capacity = page_inner.capacity;

    if capacity >= reserved { return; }

    // Calculate the block size
    // TODO should have special handling for huge blocks
    let bsize: usize = page_ptr.get_inner_ref(Tracked(&*local)).xblock_size as usize;

    /*proof {
        let ghost page_id = page_ptr.page_id@;
        assert(local.page_organization.pages.dom().contains(page_id));
        assert(page_organization_matches_token_page(
            local.page_organization.pages[page_id],
            local.thread_token.value().pages[page_id]));
        assert(local.is_used_primary(page_id));
        assert(bsize != 0);
    }*/

    // Calculate extend amount

    let mut max_extend: usize = if bsize >= MAX_EXTEND_SIZE as usize {
        MIN_EXTEND
    } else {
        (MAX_EXTEND_SIZE / bsize as u32) as usize
    };
    if max_extend < MIN_EXTEND {
        max_extend = MIN_EXTEND;
    }

    let mut extend: usize = (reserved - capacity) as usize;
    if extend > max_extend {
        extend = max_extend;
    }

    page_free_list_extend(page_ptr, bsize, extend, Tracked(local));

    // page capacity is modified in page_free_list_extend, no need to do it here
}

#[verifier::external_body]
fn heap_delayed_free_partial(heap: HeapPtr, Tracked(local): Tracked<&mut Local>) -> (b: bool)
{
    let mut ll = heap.get_ref(Tracked(&*local)).thread_delayed_free.take();
    let mut all_freed = true;
    while !ll.is_empty()
        invariant
            local.wf(),
            heap.wf(), heap.is_in(*local),
            ll.wf(), common_preserves(*old(local), *local),
            ll.instance().id() == local.instance.id(),
            ll.heap_id() == Some(local.thread_token.value().heap_id)
    {
        let (ptr, Tracked(perm), Tracked(block)) = ll.pop_block();
        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block,
            ptr: ptr,
        };
        let (success, Tracked(p_opt), Tracked(d_opt)) =
                crate::free::free_delayed_block(ptr, Tracked(perm),
                    Tracked(dealloc_inner), Tracked(&mut *local));
        if !success {
            all_freed = false;
            let tracked perm = p_opt.tracked_unwrap();
            let tracked dealloc = d_opt.tracked_unwrap();
            let tracked block = dealloc.mim_block;

            heap.get_ref(Tracked(&*local)).thread_delayed_free
                .atomic_insert_block(ptr as *mut Node, Tracked(perm), Tracked(block));
        }
    }
    return all_freed;
}

}
