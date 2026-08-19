#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;

use core::intrinsics::{likely, unlikely};

use crate::tokens::{Mim, BlockId, DelayState, PageId, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::page_organization::Popped;

verus!{

// The algorithm for `free` is this:
//
//  1. Given the ptr, compute the segment and page it is on.
//
//  2. Check the 'thread_id' on the page. If it matches the thread we're on, then
//      this is a 'local' transition (the common case).
//      Otherwise, it's a 'thread' transition.
//
// If it's a LOCAL transition:
//
//   Update the local_free list.
//
// If it's a THREAD transition:
//
//   Attempt to update the thread_free list by first reading the atomic, then performing
//   a CAS (repeating if necessary). The thread_free contains both the linked_list pointer
//   and a 'delay' state.
//
//   If the 'delay' state is NOT in 'UseDelayedFree' (the usual case):
//
//     Update the thread_free atomically by inserting the new block to the front of the list.
//
//   If the 'delay' state is in 'UseDelayedFree' (the unusual case):
//
//     Set 'delay' to Freeing
//     Follow the heap pointer to access the Heap
//     Atomically add to the delayed free list.
//     Set 'delay' to NoDelaying
//
//     (The purpose of setting the 'Freeing' state is to ensure that the Heap remains
//     valid while we perform this operation.)
//
//     (Also note that setting the 'Freeing' state does not prevent the next thread that
//     comes along from adding to the thread_free list.)


proof fn block_token_idx_lt_num_blocks(
    tracked inst: &Mim::Instance,
    tracked thread_token: &Mim::thread_local_state,
    thread_id: ThreadId,
    tracked block: &Mim::block,
    num_blocks: nat,
)
    requires
        block.instance_id() == inst.id(),
        inst.id() == thread_token.instance_id(),
        thread_token.key() == thread_id,
        thread_token.value().pages.dom().contains(block.key().page_id),
        thread_token.value().pages[block.key().page_id].num_blocks == num_blocks,
    ensures
        block.key().idx < num_blocks,
{
    inst.get_block_properties(thread_id, block.key(), thread_token, block);
}

proof fn live_block_implies_page_used(tracked mim_block: &Mim::block, local: Local)
    requires
        local.wf(),
        local.thread_token.value().pages.dom().contains(mim_block.key().page_id),
        local.thread_token.value().pages[mim_block.key().page_id].offset == 0,
        local.pages.dom().contains(mim_block.key().page_id),
        local.page_inner(mim_block.key().page_id).free.len()
            + local.page_inner(mim_block.key().page_id).local_free.len()
            < local.thread_token.value().pages[mim_block.key().page_id].num_blocks,
    ensures
        local.page_inner(mim_block.key().page_id).used >= 1,
{
    reveal(Local::wf);
    reveal(Local::wf_main);
    reveal(PageLocalAccess::wf);
    reveal(PageInner::wf);

    let page_id = mim_block.key().page_id;
    let page_inner = local.page_inner(page_id);
    let page_state = local.thread_token.value().pages[page_id];

    assert(local.wf_main());
    assert(local.pages.index(page_id).wf(page_id, page_state, local.instance));
    assert(page_state.offset == 0);
    assert(page_inner.wf(page_id, page_state, local.instance));
    assert(page_inner.used + page_inner.free.len() + page_inner.local_free.len()
        == page_state.num_blocks);
    assert(page_inner.used >= 1) by(nonlinear_arith)
        requires
            page_inner.used + page_inner.free.len() + page_inner.local_free.len()
                == page_state.num_blocks,
            page_inner.free.len() + page_inner.local_free.len() < page_state.num_blocks;
}
}

macro_rules! atomic_with_ghost { (&$segment:ident . thread_id => load(); returning $ret:ident; ghost $g:ident => { if $g2:ident . value() == $local:ident . thread_id { $local2:ident . instance . block_on_the_local_thread( $local3:ident . thread_token . key(), $dealloc:ident . mim_block . key(), & $local4:ident . thread_token, & $dealloc2:ident . mim_block, & $g3:ident, ); } }) => { ::vstd::prelude::verus_exec_expr!{ { let ghost __argus_block_id = $dealloc.block_id(); let ghost mut __argus_loaded_thread = $local.thread_id; let ghost mut __argus_page_in_local = false; let ghost mut __argus_page_primary = false; let ghost mut __argus_block_size_matches = false; let ghost mut __argus_idx_lt_num_blocks = false; let __argus_ret = ::vstd::atomic_ghost::atomic_with_ghost!(&$segment.thread_id => load(); returning $ret; ghost $g => { __argus_loaded_thread = $g.value(); if $g.value() == $local.thread_id { $local.instance.block_on_the_local_thread($local.thread_token.key(), $dealloc.mim_block.key(), &$local.thread_token, &$dealloc.mim_block, &$g); assert($local.thread_token.value().pages.dom().contains(__argus_block_id.page_id)); assert($local.thread_token.value().pages[__argus_block_id.page_id].offset == 0); assert($local.thread_token.value().pages[__argus_block_id.page_id].block_size == __argus_block_id.block_size); assert(__argus_block_id.idx < $local.thread_token.value().pages[__argus_block_id.page_id].num_blocks); __argus_page_in_local = true; __argus_page_primary = true; __argus_block_size_matches = true; __argus_idx_lt_num_blocks = true; } }); proof { assert(__argus_loaded_thread.thread_id == __argus_ret); assert(__argus_ret == $local.thread_id.thread_id ==> __argus_page_in_local); assert(__argus_ret == $local.thread_id.thread_id ==> __argus_page_primary); assert(__argus_ret == $local.thread_id.thread_id ==> __argus_block_size_matches); assert(__argus_ret == $local.thread_id.thread_id ==> __argus_idx_lt_num_blocks); assert(__argus_ret == $local.thread_id.thread_id ==> $local.thread_token.value().pages.dom().contains(__argus_block_id.page_id)); assert(__argus_ret == $local.thread_id.thread_id ==> $local.thread_token.value().pages[__argus_block_id.page_id].offset == 0); assert(__argus_ret == $local.thread_id.thread_id ==> $local.thread_token.value().pages[__argus_block_id.page_id].block_size == __argus_block_id.block_size); assert(__argus_ret == $local.thread_id.thread_id ==> __argus_block_id.idx < $local.thread_token.value().pages[__argus_block_id.page_id].num_blocks); } __argus_ret } } }; ($($tokens:tt)*) => { ::vstd::atomic_ghost::atomic_with_ghost!($($tokens)*) }; }
verus!{ #[verus_verify]
pub fn free(ptr: *mut u8, Tracked(user_perm): Tracked<PointsToRaw>, Tracked(user_dealloc): Tracked<Option<MimDealloc>>, Tracked(local): Tracked<&mut Local>)
    // According to the Linux man pages, `ptr` is allowed to be NULL,
    // in which case no operation is performed.
    requires
        old(local).wf(),
        ptr.addr() != 0 ==> user_dealloc.is_some(),
        ptr.addr() != 0 ==> user_perm.is_range(ptr as int, user_dealloc.unwrap().size()),
        ptr.addr() != 0 ==> user_perm.provenance() == ptr@.provenance,
        ptr.addr() != 0 ==> ptr == user_dealloc.unwrap().ptr(),
        ptr.addr() != 0 ==> old(local).inst() == user_dealloc.unwrap().inst()
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    if ptr.addr() == 0 {
        return;
    }

    let tracked user_dealloc = user_dealloc.tracked_unwrap();

    let tracked (dealloc, perm) = user_dealloc.into_internal(user_perm);

    // Calculate the pointer to the segment this block is in.

    let segment_ptr = calculate_segment_ptr_from_block(ptr, Ghost(dealloc.block_id()));

    let tracked segment_shared_access: &SegmentSharedAccess =
        dealloc.mim_instance.alloc_guards_segment_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let segment: &SegmentHeader = ptr_ref(segment_ptr,
        Tracked(&segment_shared_access.points_to));

    // Determine if this operation is thread local or not

    let ghost page_id = dealloc.block_id().page_id;

    let segment_thread_id_u64 = atomic_with_ghost!(
        &segment.thread_id => load();
        returning thread_id_u64;
        ghost g => {
            if g.value() == local.thread_id {
                local.instance.block_on_the_local_thread(
                    local.thread_token.key(),
                    dealloc.mim_block.key(),
                    &local.thread_token,
                    &dealloc.mim_block,
                    &g,
                    );
            }
        }
    );

    let (thread_id, Tracked(is_thread)) = crate::thread::thread_id();
    let is_local = thread_id.thread_id == segment_thread_id_u64;
    proof {
        is_thread.agrees(local.is_thread);
        assert(is_thread@ == thread_id);
        assert(local.thread_id == local.is_thread@);
        assert(thread_id == local.thread_id);
        if is_local {
            assert(segment_thread_id_u64 == local.thread_id.thread_id);
            assert(local.thread_token.value().pages.dom().contains(page_id));
            assert(local.thread_token.value().pages[page_id].offset == 0);
            assert(local.thread_token.value().pages[page_id].block_size == dealloc.block_id().block_size);
            assert(dealloc.block_id().idx < local.thread_token.value().pages[page_id].num_blocks);
        }
    }

    // Calculate the pointer to the PageHeader for the *slice* that this block is in.
    // Remember this might not be the "main" PageHeader for this Page.

    let slice_page_ptr = calculate_slice_page_ptr_from_block(ptr, segment_ptr, Ghost(dealloc.block_id()));

    let tracked page_slice_shared_access: &PageSharedAccess =
        dealloc.mim_instance.alloc_guards_page_slice_shared_access(
            dealloc.block_id(),
            &dealloc.mim_block,
        );

    let slice_page: &Page = ptr_ref(slice_page_ptr,
        Tracked(&page_slice_shared_access.points_to));

    // Use the 'offset' to calculate a pointer to the main PageHeader for this page.

    let offset = slice_page.offset;

    let page_ptr = calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(dealloc.block_id().page_id_for_slice()),
        Ghost(dealloc.block_id().page_id),
    );

    //assert(is_page_ptr(page_ptr, dealloc.block_id().page_id));

    /*
    let tracked page_shared_access: &PageSharedAccess;
    proof {
        page_shared_access = dealloc.mim_instance.alloc_guards_page_shared_access(
            dealloc.block_id(), &dealloc.mim_block);
    }
    let page: &Page = page_ptr.borrow(Tracked(&page_shared_access.points_to));
    */

    let page = PagePtr {
        page_ptr,
        page_id: Ghost(page_id),
    };


    // Case based on whether this is thread local or not

    if likely(is_local) {
        proof {
            assert(local.thread_token.value().pages.dom().contains(page_id));
            assert(local.thread_token.value().pages[page_id].offset == 0);
            assert(local.thread_token.value().pages[page_id].block_size == dealloc.block_id().block_size);
            assert(dealloc.block_id().idx < local.thread_token.value().pages[page_id].num_blocks);
            assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
            assert(local.pages.dom().contains(page_id));
            assert(page.wf());
            assert(page.is_in(*local));
        }
        if likely(page.get_inner_ref(Tracked(&*local)).not_full_nor_aligned()) {
            let used;
            page_get_mut_inner!(page, local, page_inner => {
                let tracked mim_block = dealloc.mim_block;

                //proof {
                    //assert(mim_block.key().page_id == page_inner.free.page_id());
                    //assert(mim_block.key().block_size == page_inner.free.block_size());
                //}

                page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));

                //assert(page_inner.used >= 1);

                used = page_inner.used - 1;
                page_inner.used = used;
            });


            if unlikely(used == 0) {
                crate::page::page_retire(page, Tracked(&mut *local));
            }
        } else {
            free_generic(segment_ptr, page, true, ptr,
                Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
        }
    } else {
        free_generic(segment_ptr, page, false, ptr,
            Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
    }
}
}

verus!{
fn free_generic(segment: *mut SegmentHeader, page: PagePtr, is_local: bool, p: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        dealloc.mim_instance == old(local).inst(),
        perm.is_range(p as int, dealloc.block_id().block_size as int),
        perm.provenance() == p@.provenance,
        p == dealloc.ptr,
        page.page_id@ == dealloc.block_id().page_id,
        is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
        is_local ==> page.is_used_and_primary(*old(local)),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        is_local ==> dealloc.block_id().idx < old(local).thread_token.value().pages[page.page_id@].num_blocks,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    // this has_aligned check could be a data race??
    //if page.get_inner_ref(Tracked(&*local)).get_has_aligned() {
    //    todo();
    //}

    free_block(page, is_local, p, Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
}
}

verus!{

#[verus_verify]
fn free_block(page: PagePtr, is_local: bool, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        dealloc.mim_instance == old(local).inst(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        page.page_id@ == dealloc.block_id().page_id,
        is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
        is_local ==> page.is_used_and_primary(*old(local)),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        is_local ==> dealloc.block_id().idx < old(local).thread_token.value().pages[page.page_id@].num_blocks,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    if likely(is_local) {
        let used;
        page_get_mut_inner!(page, local, page_inner => {
            let tracked mim_block = dealloc.mim_block;

            //proof {
            //    assert(mim_block.key().page_id == page_inner.free.page_id());
            //    assert(mim_block.key().block_size == page_inner.free.block_size());
            //}

            page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));

            //assert(page_inner.used >= 1);

            used = page_inner.used - 1;
            page_inner.used = used;
        });


        if unlikely(used == 0) {
            crate::page::page_retire(page, Tracked(&mut *local));
        } else if unlikely(page.get_inner_ref(Tracked(&*local)).get_in_full()) {
            crate::page::page_unfull(page, Tracked(&mut *local));
        }
    } else {
        free_block_mt(page, ptr, Tracked(perm), Tracked(dealloc), Tracked(&mut *local));
    }
}

}

verus!{
#[cfg(any())]
#[verus_verify]
fn free_block_mt(page: PagePtr, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        dealloc.mim_instance == old(local).inst(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    // Based on _mi_free_block_mt

    // TODO check the segment kind

    let tracked mut perm = perm;
    let tracked mut delay_actor_token_opt: Option<Mim::delay_actor> = None;
    let tracked MimDeallocInner { mim_block, mim_instance, .. } = dealloc;
    let tracked mut mim_block_opt = Some(mim_block);
    let ptr = ptr as *mut Node;
    let mut use_delayed;

    loop
        invariant
            dealloc.wf(),
            mim_block_opt == Some(dealloc.mim_block),
            mim_instance == dealloc.mim_instance,
            mim_instance == local.instance,
            perm.is_range(ptr as int, dealloc.block_id().block_size as int),
            perm.provenance() == ptr@.provenance,
            ptr as *mut u8 == dealloc.ptr,
            is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
            local.wf(),
            common_preserves(*old(local), *local),

            //*page ==
            //    dealloc.mim_block.value().page_shared_access.points_to@.value.get_Some_0(),
        //ensures
        //    use_delayed ==> (match delay_actor_token_opt {
        //        None => false,
        //        Some(tok) => tok@.instance == dealloc.mim_instance
        //            && tok@.key == dealloc.block_id().page_id
        //    }),
    {
        let tracked page_shared_access: &PageSharedAccess =
            mim_instance.alloc_guards_page_shared_access(
                dealloc.block_id(), mim_block_opt.tracked_borrow());
        let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));


        let ghost mut next_ptr;
        let ghost mut delay;
        let mask = atomic_with_ghost!(&pag.xthread_free.atomic => load(); ghost g => {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            next_ptr = g.1.unwrap().1.ptr();
            delay = g.1.unwrap().0.value(); // TODO fix macro syntax in atomic_with_ghost
        });

        use_delayed = masked_ptr_delay_get_is_use_delayed(mask, Ghost(delay), Ghost(next_ptr));
        let mask1;

        let tracked mut ptr_mem = None;
        let tracked mut raw_mem = None;
        let tracked mut exposed = None;

        if unlikely(use_delayed) {
            mask1 = masked_ptr_delay_set_freeing(mask, Ghost(delay), Ghost(next_ptr));
        } else {

            // *ptr = mask.next_ptr
            let (ptr_mem0, raw_mem0) = LL::block_write_ptr(
                ptr,
                Tracked(perm),
                masked_ptr_delay_get_ptr(mask, Ghost(delay), Ghost(next_ptr)));
            //assert(ptr_mem0@.ptr() == ptr);

            let Tracked(exposed0) = expose_provenance(ptr);


            //assert(ptr_mem.unwrap().ptr() == ptr);

            // mask1 = mask (set next_ptr to ptr)
            mask1 = masked_ptr_delay_set_ptr(mask, ptr, Ghost(delay), Ghost(next_ptr));
        }

        //assert(pag.xthread_free.instance == mim_instance);

        let cas_result = atomic_with_ghost!(
            &pag.xthread_free.atomic => compare_exchange_weak(mask, mask1);
            update v_old -> v_new;
            returning cas_result;
            ghost g =>
        {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            let tracked (emp_token, pair_opt) = g;
            let tracked pair = pair_opt.tracked_unwrap();
            let tracked (mut delay_token, mut ghost_ll) = pair;

            let ghost ok = cas_result.is_ok();
            if use_delayed {
                if ok {
                    let tracked (Tracked(delay_token0), Tracked(delay_actor_token)) =
                        mim_instance.delay_enter_freeing(
                            dealloc.block_id().page_id,
                            dealloc.block_id(),
                            mim_block_opt.tracked_borrow(),
                            delay_token);
                    delay_token = delay_token0;
                    delay_actor_token_opt = Some(delay_actor_token);
                } else {
                    // do nothing
                }
            } else {
                if ok {
                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    //assert(ptr_mem.unwrap().ptr() == ptr);
                    LL::ghost_insert_block(mut_ref_tracked(&mut ghost_ll), ptr, ptr_mem.tracked_unwrap(),
                        raw_mem.tracked_unwrap(), mim_block, exposed.tracked_unwrap());

                    mim_block_opt = None;

                    is_block_ptr_mult4(ptr as *mut u8, dealloc.block_id());
                } else {
                    // do nothing

                    // okay, actually do 1 thing: reset the 'perm' variable
                    // for the next loop.
                    let tracked mut ptr_mem = ptr_mem.tracked_unwrap();
                    let tracked raw_mem = raw_mem.tracked_unwrap();
                    ptr_mem.leak_contents();
                    perm = ptr_mem.into_raw().join(raw_mem);
                }
            }

            g = (emp_token, Some((delay_token, ghost_ll)));

            //assert(ghost_ll.wf());
            //assert(ghost_ll.block_size() == pag.xthread_free.block_size());
            //assert(ghost_ll.instance() == pag.xthread_free.instance@);
            //assert(ghost_ll.page_id() == pag.xthread_free.page_id());
            //assert(ghost_ll.fixed_page());
            //assert(delay_token@.instance == pag.xthread_free.instance@);
            //assert(delay_token@.key == pag.xthread_free.page_id());
            //assert(v_new as int == ghost_ll.ptr() as int + delay_token@.value.to_int());
            //assert(ghost_ll.ptr() as int % 4 == 0);
        });

        match cas_result {
            Result::Err(_) => { }
            Result::Ok(_) => {
                if unlikely(use_delayed) {
                    // Lookup the heap ptr

                    let tracked mut delay_actor_token;
                    let ghost mut heap_id;

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.alloc_guards_page_shared_access(
                            dealloc.block_id(), mim_block_opt.tracked_borrow());
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    let heap_ptr = atomic_with_ghost!(
                        &pag.xheap.atomic => load();
                        ghost g =>
                    {
                        delay_actor_token = delay_actor_token_opt.tracked_unwrap();
                        //assert(!pag.xheap.is_empty());
                        //assert(pag.xheap.wf(pag.xheap.instance@, pag.xheap.page_id@));
                        pag.xheap.emp_inst.borrow().agree(pag.xheap.emp.borrow(), &g.0);
                        //assert(g.0@.value == false);
                        let tracked (Tracked(tok), _) = mim_instance.delay_lookup_heap(
                            dealloc.block_id(),
                            &local.my_inst,
                            mim_block_opt.tracked_borrow(),
                            g.1.tracked_borrow(),
                            delay_actor_token);
                        delay_actor_token = tok;
                        heap_id = g.1.unwrap().value();
                    });

                    let tracked heap_shared_access: &HeapSharedAccess;
                    let heap: &Heap = ptr_ref(heap_ptr,
                        Tracked(&heap_shared_access.points_to));

                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    let tracked mim_block = local.instance.block_set_heap_id(mim_block.key(),
                        mim_block, &delay_actor_token);
                    heap.thread_delayed_free.atomic_insert_block(ptr, Tracked(perm), Tracked(mim_block));

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.delay_guards_page_shared_access(
                            dealloc.block_id().page_id, &delay_actor_token);
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    //pag.xthread_free.exit_delaying_state(Tracked(delay_actor_token));

                    // have to inline this bc of lifetimes
                    atomic_with_ghost!(
                        &pag.xthread_free.atomic => fetch_xor(3);
                        update v_old -> v_new;
                        ghost g => {
                            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (mut delay_token, mut ll) = pair;

                            delay_token = mim_instance.delay_leave_freeing(dealloc.block_id().page_id,
                                delay_token, delay_actor_token);

                            // TODO right now this only works for fixed-width architecture
                            //verus_proof_expr!{ { // TODO fix atomic_with_ghost
                            //    assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1)) by (bit_vector);
                            //} }

                            g = (emp_token, Some((delay_token, ll)));

                            let v_old = v_old as usize;


                        }
                    );
                }
                return;
            }
        }
    }
}

}

#[cfg(not(any()))]
verus!{
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
fn free_block_mt(page: PagePtr, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        dealloc.mim_instance == old(local).inst(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
{
    // Based on _mi_free_block_mt

    // TODO check the segment kind

    let tracked mut perm_opt = Some(perm);
    let tracked mut delay_actor_token_opt: Option<Mim::delay_actor> = None;
    let tracked MimDeallocInner { mim_block, mim_instance, .. } = dealloc;
    let tracked mut mim_block_opt = Some(mim_block);
    let ptr = ptr as *mut Node;
    let mut use_delayed;

    proof {
        assert(dealloc.wf());
        assert(match perm_opt {
            Some(perm) =>
                perm.is_range(ptr as int, dealloc.block_id().block_size as int)
                && perm.provenance() == ptr@.provenance,
            None => false,
        });
    }

    loop
        invariant
            dealloc.wf(),
            mim_block_opt == Some(dealloc.mim_block),
            mim_instance == dealloc.mim_instance,
            mim_instance == local.instance,
            match perm_opt {
                Some(perm) =>
                    perm.is_range(ptr as int, dealloc.block_id().block_size as int)
                    && perm.provenance() == ptr@.provenance,
                None => false,
            },
            ptr as *mut u8 == dealloc.ptr,
            is_page_ptr(page.page_ptr, dealloc.block_id().page_id),
            local.wf(),
            common_preserves(*old(local), *local),

            //*page ==
            //    dealloc.mim_block.value().page_shared_access.points_to@.value.get_Some_0(),
        //ensures
        //    use_delayed ==> (match delay_actor_token_opt {
        //        None => false,
        //        Some(tok) => tok@.instance == dealloc.mim_instance
        //            && tok@.key == dealloc.block_id().page_id
        //    }),
    {
        let tracked page_shared_access: &PageSharedAccess =
            mim_instance.alloc_guards_page_shared_access(
                dealloc.block_id(), mim_block_opt.tracked_borrow());
        let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));
        proof {
            reveal(MimDeallocInner::wf);
            reveal(valid_block_token);
            assert(page_shared_access.wf(dealloc.block_id().page_id, dealloc.block_id().block_size, mim_instance));
            assert(pag.xthread_free.wf());
            pag.xthread_free.wf_emp_instance_ids();
            assert(!pag.xthread_free.is_empty());
        }


        let ghost mut next_ptr;
        let ghost mut delay;
        let mask = atomic_with_ghost!(&pag.xthread_free.atomic => load(); ghost g => {
            assert(pag.xthread_free.wf());
            assert(pag.xthread_free.emp@.instance_id() == pag.xthread_free.emp_inst@.id());
            assert(g.0.instance_id() == pag.xthread_free.emp_inst@.id());
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            next_ptr = g.1.unwrap().1.ptr();
            delay = g.1.unwrap().0.value(); // TODO fix macro syntax in atomic_with_ghost
        });

        proof {
            assert(masked_ptr_delay_wf(mask, delay, next_ptr));
        }
        use_delayed = masked_ptr_delay_get_is_use_delayed(mask, Ghost(delay), Ghost(next_ptr));
        proof {
            assert(use_delayed == (delay == DelayState::UseDelayedFree));
        }
        let mask1;

        let tracked mut ptr_mem = None;
        let tracked mut raw_mem = None;
        let tracked mut exposed = None;

        if unlikely(use_delayed) {
            mask1 = masked_ptr_delay_set_freeing(mask, Ghost(delay), Ghost(next_ptr));
        } else {

            // *ptr = mask.next_ptr
            let tracked perm = perm_opt.tracked_unwrap();
            proof { perm_opt = None; }
            let (Tracked(ptr_mem0), Tracked(raw_mem0)) = LL::block_write_ptr(
                ptr,
                Tracked(perm),
                masked_ptr_delay_get_ptr(mask, Ghost(delay), Ghost(next_ptr)));
            //assert(ptr_mem0@.ptr() == ptr);

            let Tracked(exposed0) = expose_provenance(ptr);
            proof {
                ptr_mem = Some(ptr_mem0);
                raw_mem = Some(raw_mem0);
                exposed = Some(exposed0);
            }


            //assert(ptr_mem.unwrap().ptr() == ptr);

            // mask1 = mask (set next_ptr to ptr)
            mask1 = masked_ptr_delay_set_ptr(mask, ptr, Ghost(delay), Ghost(next_ptr));
            vstd::layout::layout_for_type_is_valid::<Node>();
            proof {
                node_layout_facts();
                lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, dealloc.block_id());
                assert(ptr.addr() % 4 == 0);
            }
        }

        //assert(pag.xthread_free.instance == mim_instance);

        let cas_result = atomic_with_ghost!(
            &pag.xthread_free.atomic => compare_exchange_weak(mask, mask1);
            update v_old -> v_new;
            returning cas_result;
            ghost g =>
        {
            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
            let tracked (emp_token, pair_opt) = g;
            let tracked pair = pair_opt.tracked_unwrap();
            let tracked (mut delay_token, mut ghost_ll) = pair;
            let ghost old_delay = delay_token.value();
            let ghost old_ll_ptr = ghost_ll.ptr();
            assert(ghost_ll.wf());
            assert(ghost_ll.fixed_page());
            assert(ghost_ll.block_size() == pag.xthread_free.block_size());
            assert(ghost_ll.instance() == pag.xthread_free.instance@);
            assert(ghost_ll.page_id() == pag.xthread_free.page_id());
            assert(delay_token.instance_id() == pag.xthread_free.instance@.id());
            assert(delay_token.key() == pag.xthread_free.page_id());
            assert(masked_ptr_delay_wf(v_old, old_delay, old_ll_ptr));

            let ghost ok = cas_result.is_Ok();
            if use_delayed {
                if ok {
                    assert(v_old.addr() == mask.addr());
                    assert(v_new == mask1);
                    assert(masked_ptr_delay_wf(mask, old_delay, old_ll_ptr));
                    masked_ptr_delay_wf_unique(mask, delay, next_ptr, old_delay, old_ll_ptr);
                    assert(old_delay == DelayState::UseDelayedFree);
                    assert(old_ll_ptr.addr() == next_ptr.addr());
                    let tracked (Tracked(delay_token0), Tracked(delay_actor_token)) =
                        mim_instance.delay_enter_freeing(
                            dealloc.block_id().page_id,
                            dealloc.block_id(),
                            mim_block_opt.tracked_borrow(),
                            delay_token);
                    delay_token = delay_token0;
                    assert(delay_token.value() == DelayState::Freeing);
                    assert(masked_ptr_delay_wf(mask1, DelayState::Freeing, next_ptr));
                    delay_actor_token_opt = Some(delay_actor_token);
                } else {
                    // do nothing
                }
            } else {
                if ok {
                    assert(v_old.addr() == mask.addr());
                    assert(v_new == mask1);
                    assert(masked_ptr_delay_wf(mask, old_delay, old_ll_ptr));
                    masked_ptr_delay_wf_unique(mask, delay, next_ptr, old_delay, old_ll_ptr);
                    assert(old_delay == delay);
                    assert(old_ll_ptr.addr() == next_ptr.addr());
                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    assert(pag.xthread_free.instance == mim_instance);
                    assert(ghost_ll.instance() == mim_instance);
                    assert(ghost_ll.page_id() == dealloc.block_id().page_id);
                    assert(mim_block.instance_id() == mim_instance.id());
                    assert(mim_block.key() == dealloc.block_id());
                    let tracked (ghost_ll0, mim_block0) =
                        LL::block_token_fresh_for_ll(&mim_instance, ghost_ll, mim_block);
                    ghost_ll = ghost_ll0;
                    let tracked mim_block = mim_block0;
                    //assert(ptr_mem.unwrap().ptr() == ptr);
                    ghost_ll = LL::ghost_insert_block(ghost_ll, ptr, ptr_mem.tracked_unwrap(),
                        raw_mem.tracked_unwrap(), mim_block, exposed.tracked_unwrap());
                    assert(ghost_ll.ptr() == ptr);
                    assert(delay_token.value() == delay);
                    assert(masked_ptr_delay_wf(mask1, delay, ptr));

                    mim_block_opt = None;

                    is_block_ptr_mult4(ptr as *mut u8, dealloc.block_id());
                } else {
                    assert(v_new == v_old);
                    // do nothing

                    // okay, actually do 1 thing: reset the 'perm' variable
                    // for the next loop.
                    let tracked mut ptr_mem = ptr_mem.tracked_unwrap();
                    let tracked raw_mem = raw_mem.tracked_unwrap();
                    ptr_mem.leak_contents();
                    let tracked ptr_raw = ptr_mem.into_raw();
                    let tracked joined = LL::block_write_ptr_rejoin(ptr_raw, raw_mem, ptr, dealloc.block_id());
                    perm_opt = Some(joined);
                }
            }

            if !ok {
                assert(v_new == v_old);
                assert(masked_ptr_delay_wf(v_new, delay_token.value(), ghost_ll.ptr()));
            } else if use_delayed {
                assert(delay_token.value() == DelayState::Freeing);
                assert(masked_ptr_delay_wf(v_new, delay_token.value(), ghost_ll.ptr()));
            } else {
                assert(delay_token.value() == delay);
                assert(masked_ptr_delay_wf(v_new, delay_token.value(), ghost_ll.ptr()));
            }
            g = (emp_token, Some((delay_token, ghost_ll)));

            //assert(ghost_ll.wf());
            //assert(ghost_ll.block_size() == pag.xthread_free.block_size());
            //assert(ghost_ll.instance() == pag.xthread_free.instance@);
            //assert(ghost_ll.page_id() == pag.xthread_free.page_id());
            //assert(ghost_ll.fixed_page());
            //assert(delay_token@.instance == pag.xthread_free.instance@);
            //assert(delay_token@.key == pag.xthread_free.page_id());
            //assert(v_new as int == ghost_ll.ptr() as int + delay_token@.value.to_int());
            //assert(ghost_ll.ptr() as int % 4 == 0);
        });

        match cas_result {
            Result::Err(_) => { }
            Result::Ok(_) => {
                if unlikely(use_delayed) {
                    // Lookup the heap ptr

                    let tracked mut delay_actor_token;
                    let ghost mut heap_id;

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.alloc_guards_page_shared_access(
                            dealloc.block_id(), mim_block_opt.tracked_borrow());
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    let heap_ptr = atomic_with_ghost!(
                        &pag.xheap.atomic => load();
                        ghost g =>
                    {
                        delay_actor_token = delay_actor_token_opt.tracked_unwrap();
                        //assert(!pag.xheap.is_empty());
                        //assert(pag.xheap.wf(pag.xheap.instance@, pag.xheap.page_id@));
                        pag.xheap.emp_inst.borrow().agree(pag.xheap.emp.borrow(), &g.0);
                        //assert(g.0@.value == false);
                        let tracked (Tracked(tok), _) = mim_instance.delay_lookup_heap(
                            dealloc.block_id(),
                            &local.my_inst,
                            mim_block_opt.tracked_borrow(),
                            g.1.tracked_borrow(),
                            delay_actor_token);
                        delay_actor_token = tok;
                        heap_id = g.1.unwrap().value();
                    });

                    let tracked heap_shared_access: &HeapSharedAccess =
                        mim_instance.delay_guards_heap_shared_access(
                            dealloc.block_id().page_id, &delay_actor_token);
                    let heap: &Heap = ptr_ref(heap_ptr,
                        Tracked(&heap_shared_access.points_to));

                    let tracked mim_block = mim_block_opt.tracked_unwrap();
                    let tracked mim_block = local.instance.block_set_heap_id(mim_block.key(),
                        mim_block, &delay_actor_token);
                    let tracked perm = perm_opt.tracked_unwrap();
                    proof { perm_opt = None; }
                    heap.thread_delayed_free.atomic_insert_block(ptr, Tracked(perm), Tracked(mim_block));

                    let tracked page_shared_access: &PageSharedAccess =
                        mim_instance.delay_guards_page_shared_access(
                            dealloc.block_id().page_id, &delay_actor_token);
                    let pag: &Page = ptr_ref(page.page_ptr, Tracked(&page_shared_access.points_to));

                    //pag.xthread_free.exit_delaying_state(Tracked(delay_actor_token));

                    // have to inline this bc of lifetimes
                    atomic_with_ghost!(
                        &pag.xthread_free.atomic => fetch_xor(3);
                        update v_old -> v_new;
                        ghost g => {
                            pag.xthread_free.emp_inst.borrow().agree(pag.xthread_free.emp.borrow(), &g.0);
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (mut delay_token, mut ll) = pair;
                            let ghost old_delay = delay_token.value();
                            let ghost old_ll_ptr = ll.ptr();
                            assert(ll.wf());
                            assert(ll.fixed_page());
                            assert(ll.block_size() == pag.xthread_free.block_size());
                            assert(ll.instance() == pag.xthread_free.instance@);
                            assert(ll.page_id() == pag.xthread_free.page_id());
                            assert(delay_token.instance_id() == pag.xthread_free.instance@.id());
                            assert(delay_token.key() == pag.xthread_free.page_id());
                            assert(masked_ptr_delay_wf(v_old, old_delay, old_ll_ptr));

                            delay_token = mim_instance.delay_leave_freeing(dealloc.block_id().page_id,
                                delay_token, delay_actor_token);
                            assert(old_delay == DelayState::Freeing);
                            assert(delay_token.value() == DelayState::NoDelayedFree);
                            assert(v_new.addr() == (v_old.addr() ^ 3usize));
                            masked_ptr_delay_xor3_freeing_to_no_delayed(v_old, v_new, old_ll_ptr);
                            assert(masked_ptr_delay_wf(v_new, delay_token.value(), ll.ptr()));

                            // TODO right now this only works for fixed-width architecture
                            //verus_proof_expr!{ { // TODO fix atomic_with_ghost
                            //    assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1)) by (bit_vector);
                            //} }

                            g = (emp_token, Some((delay_token, ll)));

                            let v_old = v_old as usize;


                        }
                    );
                }
                return;
            }
        }
    }
}

}

verus!{
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
#[verus_verify]
pub fn free_delayed_block(ptr: *mut u8,
    Tracked(perm): Tracked<PointsToRaw>,
    Tracked(dealloc): Tracked<MimDeallocInner>,
    Tracked(local): Tracked<&mut Local>,
) -> (res: (bool, Tracked<Option<PointsToRaw>>, Tracked<Option<MimDeallocInner>>))
    requires
        old(local).wf(),
        dealloc.wf(),
        dealloc.mim_instance == old(local).inst(),
        dealloc.mim_block.value().heap_id == Some(old(local).heap_id),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        common_preserves(*old(local), *final(local)),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        res.0 ==> res.1@.is_none() && res.2@.is_none(),
        !res.0 ==> res.1@.is_some() && res.2@.is_some(),
{
    let ghost block_id = dealloc.mim_block.key();
    proof {
        reveal(Local::wf);
        reveal(Local::wf_main);
        reveal(MimDeallocInner::wf);
        reveal(valid_block_token);
        assert(dealloc.block_id() == block_id);
        assert(dealloc.mim_instance == local.instance);
        assert(local.thread_token.value().heap_id == local.heap_id);
        dealloc.mim_instance.block_in_heap_has_valid_page(
            local.thread_id,
            block_id,
            &local.thread_token,
            &dealloc.mim_block,
        );
        assert(local.thread_token.value().pages.dom().contains(block_id.page_id));
        dealloc.mim_instance.get_block_properties(
            local.thread_id,
            block_id,
            &local.thread_token,
            &dealloc.mim_block,
        );
        assert(local.thread_token.value().pages[block_id.page_id].offset == 0);
        assert(local.thread_token.value().pages[block_id.page_id].block_size == block_id.block_size);
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert(local.pages.dom().contains(block_id.page_id));
    }
    let segment = crate::layout::calculate_segment_ptr_from_block(ptr, Ghost(block_id));

    let slice_page_ptr = crate::layout::calculate_slice_page_ptr_from_block(ptr, segment, Ghost(block_id));
    let tracked page_slice_shared_access: &PageSharedAccess =
        local.instance.alloc_guards_page_slice_shared_access(
            block_id,
            &dealloc.mim_block,
        );
    let slice_page: &Page = ptr_ref(slice_page_ptr,
        Tracked(&page_slice_shared_access.points_to));
    let offset = slice_page.offset;
    proof {
        assert(block_id.page_id_for_slice().segment_id == block_id.page_id.segment_id);
        assert(offset as int == (block_id.page_id_for_slice().idx as int - block_id.page_id.idx as int)
            * (crate::config::SIZEOF_PAGE_HEADER as int));
    }
    let page_ptr = crate::layout::calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(block_id.page_id_for_slice()),
        Ghost(block_id.page_id),
    );
    //assert(crate::layout::is_page_ptr(page_ptr, block_id.page_id));
    let ghost page_id = dealloc.block_id().page_id;


    let page = PagePtr { page_ptr: page_ptr, page_id: Ghost(block_id.page_id) };
    proof {
        assert(page.wf());
        assert(page.is_in(*local));
        assert(page.is_used_and_primary(*local));
        assert(local.thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size);
        assert(dealloc.block_id().idx < local.thread_token.value().pages[page.page_id@].num_blocks);
    }

    if !crate::page::page_try_use_delayed_free(page, 0, false, Tracked(&*local)) {
        proof {
            assert(*local == *old(local));
            assert forall |heap: HeapPtr| heap.is_in(*old(local)) implies heap.is_in(*local) by { };
        }
        return (false, Tracked(Some(perm)), Tracked(Some(dealloc)));
    }

    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

    proof {
        assert(local.thread_token.value() == old(local).thread_token.value());
        assert(local.thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size);
        assert(dealloc.block_id().idx < local.thread_token.value().pages[page.page_id@].num_blocks);
    }

    crate::free::free_block(page, true, ptr,
        Tracked(perm), Tracked(dealloc), Tracked(&mut *local));

    return (true, Tracked(None), Tracked(None));
}

}
