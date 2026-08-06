#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;

use core::intrinsics::{likely, unlikely};

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;

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

#[verifier::external_body]
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
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn free_generic(segment: *mut SegmentHeader, page: PagePtr, is_local: bool, p: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(p as int, dealloc.block_id().block_size as int),
        perm.provenance() == p@.provenance,
        p == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.wf(),
        is_local ==> page.is_in(*old(local)),
        is_local ==> old(local).is_used_primary(page.page_id@),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        page.page_id@ == dealloc.block_id().page_id,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn free_block(page: PagePtr, is_local: bool, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.wf(),
        is_local ==> page.is_in(*old(local)),
        is_local ==> old(local).is_used_primary(page.page_id@),
        is_local ==> old(local).thread_token.value().pages[page.page_id@].block_size == dealloc.block_id().block_size,
        page.page_id@ == dealloc.block_id().page_id,
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn free_block_mt(page: PagePtr, ptr: *mut u8, Tracked(perm): Tracked<PointsToRaw>, Tracked(dealloc): Tracked<MimDeallocInner>, Tracked(local): Tracked<&mut Local>)
    requires
        old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        page.page_id@ == dealloc.block_id().page_id,
        page.wf(),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
pub fn free_delayed_block(ptr: *mut u8,
    Tracked(perm): Tracked<PointsToRaw>,
    Tracked(dealloc): Tracked<MimDeallocInner>,
    Tracked(local): Tracked<&mut Local>,
) -> (res: (bool, Tracked<Option<PointsToRaw>>, Tracked<Option<MimDeallocInner>>))
    requires old(local).wf(),
        dealloc.wf(),
        perm.is_range(ptr as int, dealloc.block_id().block_size as int),
        perm.provenance() == ptr@.provenance,
        ptr == dealloc.ptr,
        old(local).instance == dealloc.mim_instance,
        dealloc.mim_block.value().heap_id == Some(old(local).thread_token.value().heap_id),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local)),
        !res.0 ==> res.1@ == Some(perm),
        !res.0 ==> res.2@ == Some(dealloc)
{
    unimplemented!()
}

}
