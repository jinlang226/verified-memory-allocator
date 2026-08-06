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

#[verifier::external_body]
#[inline]
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
    unimplemented!()
}

#[verifier::external_body]
#[inline]
pub fn heap_malloc_zero(heap: HeapPtr, size: usize, zero: bool, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;
            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
#[inline]
pub fn heap_malloc_zero_ex(heap: HeapPtr, size: usize, zero: bool, huge_alignment: usize, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;
            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
#[inline]
pub fn heap_get_free_small_page(heap: HeapPtr, size: usize, Tracked(local): Tracked<&Local>) -> (page: PagePtr)
    requires 0 <= size <= SMALL_SIZE_MAX,
        local.wf_main(), heap.is_in(*local), heap.wf(),
    ensures
        page.is_empty_global(*local) || ({
          &&& page.wf()
          &&& Some(page.page_id@) == 
            local.page_organization.used_dlist_headers[smallest_bin_fitting_size((size + 7) / 8 * 8)].first
        })
{
    unimplemented!()
}

#[verifier::external_body]
#[inline]
pub fn heap_malloc_small_zero(
    heap: HeapPtr,
    size: usize,
    zero: bool,
    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        size <= SMALL_SIZE_MAX,
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;
            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
pub fn page_malloc(
    heap: HeapPtr,
    page_ptr: PagePtr,
    size: usize,
    zero: bool,

    Tracked(local): Tracked<&mut Local>,
) -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
        page_ptr.is_empty_global(*old(local)) || ({
            &&& page_ptr.wf()
            &&& page_ptr.is_used_and_primary(*old(local))
            &&& size <= old(local).page_state(page_ptr.page_id@).block_size
        })
    ensures
        final(local).wf(),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).instance
              && dealloc@.size() == size
        }),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}


}
