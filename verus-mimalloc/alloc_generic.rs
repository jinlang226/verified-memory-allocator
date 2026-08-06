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
pub fn page_free_collect(
    page_ptr: PagePtr,
    force: bool, 
    Tracked(local): Tracked<&mut Local>
)
    requires
        old(local).wf(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),
        old(local).page_organization.pages[page_ptr.page_id@].is_used == true,
    ensures final(local).wf(),
        page_ptr.is_used_and_primary(*final(local)),
        old(local).page_organization == final(local).page_organization,
        common_preserves(*old(local), *final(local)),
        old(local).thread_token == final(local).thread_token
{
    unimplemented!()
}

#[verifier::external_body]
fn page_thread_free_collect(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),
    ensures final(local).wf(),
        final(local).pages.dom() == old(local).pages.dom(),
        page_ptr.is_used_and_primary(*final(local)),
        old(local).page_organization == final(local).page_organization,
        common_preserves(*old(local), *final(local)),
        old(local).thread_token == final(local).thread_token
{
    unimplemented!()
}

#[verifier::external_body]
fn page_free_list_extend(
    page_ptr: PagePtr,
    bsize: usize,
    extend: usize,
    Tracked(local): Tracked<&mut Local>
)
    requires
        old(local).wf_main(),
        page_ptr.wf(),
        page_ptr.is_used_and_primary(*old(local)),

        old(local).page_capacity(page_ptr.page_id@) + extend as int
            <= old(local).page_reserved(page_ptr.page_id@),
        // TODO this should have a special case for huge-page handling:
        bsize == old(local).page_inner(page_ptr.page_id@).xblock_size,
        bsize % 8 == 0,
        extend >= 1,
    ensures
        final(local).wf_main(),
        page_ptr.is_used_and_primary(*final(local)),
        final(local).page_organization == old(local).page_organization,
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

const MIN_EXTEND: usize = 4;
const MAX_EXTEND_SIZE: u32 = 4096;

#[verifier::external_body]
pub fn page_extend_free(
    page_ptr: PagePtr,
    Tracked(local): Tracked<&mut Local>,
)
    requires
        old(local).wf_main(),
        page_ptr.wf(),
        old(local).is_used_primary(page_ptr.page_id@),
        old(local).pages[page_ptr.page_id@].inner.value().xblock_size % 8 == 0,
    ensures
        final(local).wf_main(),
        final(local).is_used_primary(page_ptr.page_id@),
        final(local).page_organization == old(local).page_organization,
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

#[verifier::external_body]
fn heap_delayed_free_partial(heap: HeapPtr, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    requires
        old(local).wf(),
        heap.wf(), heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        common_preserves(*old(local), *final(local))
{
    unimplemented!()
}

}
