#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;

use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;

verus!{

// Implements the "fast path"

// malloc -> heap_malloc -> heap_malloc_zero -> heap_malloc_zero_ex
//  -> heap_malloc_small_zero
//  -> heap_get_free_small_page & page_malloc

#[inline]
#[verifier::external_body]
pub fn heap_malloc(heap: HeapPtr, size: usize, Tracked(local): Tracked<&mut Local>)  // $line_count$Trusted$
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>)) // $line_count$Trusted$
    requires // $line_count$Trusted$
        old(local).wf(), // $line_count$Trusted$
        heap.wf(), // $line_count$Trusted$
        heap.is_in(*old(local)), // $line_count$Trusted$
    ensures // $line_count$Trusted$
        final(local).wf(), // $line_count$Trusted$
        final(local).inst() == old(local).inst(), // $line_count$Trusted$
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)), // $line_count$Trusted$
        ({ // $line_count$Trusted$
            let (ptr, points_to_raw, dealloc) = t; // $line_count$Trusted$

            points_to_raw@.is_range(ptr as int, size as int)  // $line_count$Trusted$
              && points_to_raw@.provenance() == ptr@.provenance  // $line_count$Trusted$
              && ptr == dealloc@.ptr()  // $line_count$Trusted$
              && dealloc@.inst() == final(local).inst()  // $line_count$Trusted$
              && dealloc@.size() == size  // $line_count$Trusted$
        })  // $line_count$Trusted$
{
    heap_malloc_zero(heap, size, false, Tracked(&mut *local))
}

#[inline]
#[verifier::external_body]
pub fn heap_malloc_zero(heap: HeapPtr, size: usize, zero: bool, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
{
    heap_malloc_zero_ex(heap, size, zero, 0, Tracked(&mut *local))
}

#[inline]
#[verifier::external_body]
pub fn heap_malloc_zero_ex(heap: HeapPtr, size: usize, zero: bool, huge_alignment: usize, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
{
    if likely(size <= SMALL_SIZE_MAX) {
        heap_malloc_small_zero(heap, size, zero, Tracked(&mut *local))
    } else {
        malloc_generic(heap, size, zero, huge_alignment, Tracked(&mut *local))
    }
}

#[inline]
#[verifier::external_body]
pub fn heap_get_free_small_page(heap: HeapPtr, size: usize, Tracked(local): Tracked<&Local>) -> (page: PagePtr)
{
    let idx = (size + 7) / 8;
    let ptr = heap.get_pages_free_direct(Tracked(local))[idx];

    let ghost bin_idx = smallest_bin_fitting_size((size + 7) / 8 * 8);
    let ghost page_id =
        local.page_organization.used_dlist_headers[bin_idx].first.unwrap();
    let ptr = with_exposed_provenance(ptr.addr(), Tracked(if ptr as int == local.page_empty_global@.s.points_to.ptr() as int { local.page_empty_global.borrow().s.exposed } else { local.instance.thread_local_state_guards_page(local.thread_id, page_id, &local.thread_token).exposed }));
    let page_ptr = PagePtr { page_ptr: ptr, page_id: Ghost(page_id) };

    return page_ptr;
}

#[inline]
#[verifier::external_body]
pub fn heap_malloc_small_zero(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
{
    /*let mut size = size;
    if PADDING {
        if size == 0 {
            size = INTPTR_SIZE;
        }
    }*/

    let page = heap_get_free_small_page(heap, size, Tracked(&*local));


    let (p, Tracked(points_to_raw), Tracked(mim_dealloc)) = page_malloc(heap, page, size, zero, Tracked(&mut *local));

    (p, Tracked(points_to_raw), Tracked(mim_dealloc))
}

#[verifier::external_body]
pub fn page_malloc(
    heap: HeapPtr,
    page_ptr: PagePtr,
    size: usize,
    zero: bool,

    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
{
    if unlikely(page_ptr.get_inner_ref_maybe_empty(Tracked(&*local)).free.is_empty()) {
        return malloc_generic(heap, size, zero, 0, Tracked(&mut *local));
    }
    //assert(!page_ptr.is_empty_global(*local));

    let popped;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        popped = page_inner.free.pop_block();

        //assert(page_inner.used < 1000000);
        page_inner.used = page_inner.used + 1;
    });

    let ptr = popped.0;

    let tracked dealloc;
    let tracked points_to_raw;

    (ptr, Tracked(points_to_raw), Tracked(dealloc))
}


}
