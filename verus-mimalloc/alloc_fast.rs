#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_multiply_divide_lt, lemma_remainder};
use vstd::modes::*;
use vstd::set_lib::*;

use crate::tokens::{Mim, BlockId, DelayState, PageId};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;
use crate::page_organization::{PageHeaderKind, PageOrg, Popped};

verus!{

// Implements the "fast path"

// malloc -> heap_malloc -> heap_malloc_zero -> heap_malloc_zero_ex
//  -> heap_malloc_small_zero
//  -> heap_get_free_small_page & page_malloc

#[inline]
#[verus_verify]
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
#[verus_verify]
pub fn heap_malloc_zero(heap: HeapPtr, size: usize, zero: bool, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        })
{
    heap_malloc_zero_ex(heap, size, zero, 0, Tracked(&mut *local))
}

#[inline]
pub fn heap_malloc_zero_ex(heap: HeapPtr, size: usize, zero: bool, huge_alignment: usize, Tracked(local): Tracked<&mut Local>)
    -> (t: (*mut u8, Tracked<PointsToRaw>, Tracked<MimDealloc>))
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        })
{
    if likely(size <= SMALL_SIZE_MAX) {
        proof { assert(size <= SMALL_SIZE_MAX); }
        heap_malloc_small_zero(heap, size, zero, Tracked(&mut *local))
    } else {
        malloc_generic(heap, size, zero, huge_alignment, Tracked(&mut *local))
    }
}

#[inline]
#[verifier::rlimit(200)]
pub fn heap_get_free_small_page(heap: HeapPtr, size: usize, Tracked(local): Tracked<&Local>) -> (page: PagePtr)
    requires
        heap.wf(),
        heap.is_in(*local),
        local.wf(),
        size <= SMALL_SIZE_MAX,
    ensures
        page.page_ptr.addr() == local.heap.pages_free_direct.value()@[((size as int + 7) / 8)].addr(),
        local.heap.pages_free_direct.value()@[((size as int + 7) / 8)].addr()
            != local.page_empty_global@.s.points_to.ptr().addr() ==> page.is_in(*local),
        page.is_empty_global(*local) || (
            page.wf()
            && page.is_used_and_primary(*local)
            && size as int <= local.block_size(page.page_id@)
        ),
{
    proof {
        assert(SMALL_SIZE_MAX == 1024) by(compute_only);
        assert(PAGES_DIRECT == 129) by(compute_only);
        assert(SMALL_SIZE_MAX + 7 <= usize::MAX) by(compute_only);
        assert(size <= usize::MAX - 7) by(nonlinear_arith)
            requires
                size <= SMALL_SIZE_MAX,
                SMALL_SIZE_MAX + 7 <= usize::MAX;
    }
    let idx = (size + 7) / 8;
    proof {
        assert((size + 7) as int == size as int + 7) by(nonlinear_arith)
            requires size <= usize::MAX - 7;
        assert(size as int + 7 < 8 * (PAGES_DIRECT as int)) by(nonlinear_arith)
            requires
                size <= SMALL_SIZE_MAX,
                SMALL_SIZE_MAX == 1024,
                PAGES_DIRECT == 129;
        lemma_multiply_divide_lt((size + 7) as int, 8, PAGES_DIRECT as int);
        assert(((size + 7) / 8) as int == ((size + 7) as int) / 8) by(nonlinear_arith);
        assert(idx as int == ((size + 7) / 8) as int);
        assert(idx as int == (size as int + 7) / 8) by(nonlinear_arith)
            requires
                idx as int == ((size + 7) / 8) as int,
                ((size + 7) / 8) as int == ((size + 7) as int) / 8,
                (size + 7) as int == size as int + 7;
        assert((idx as int) < (PAGES_DIRECT as int));
        assert(idx < PAGES_DIRECT);
    }
    let ptr = heap.get_pages_free_direct(Tracked(local))[idx];
    let ghost empty_page_ptr = local.page_empty_global@.s.points_to.ptr();
    let ghost direct_addr = ptr.addr();
    let ghost direct_nonempty = ptr as int != empty_page_ptr as int;
    proof {
        assert(ptr.addr() as int == ptr as int);
        assert(empty_page_ptr.addr() as int == empty_page_ptr as int);
        assert(direct_nonempty == (direct_addr != empty_page_ptr.addr()));
    }

    let ghost bin_idx = smallest_bin_fitting_size(idx as int * INTPTR_SIZE);
    proof {
        direct_wsize_bin_bounds(idx as int);
        bounds_for_smallest_bin_fitting_size(idx as int * INTPTR_SIZE as int);
        assert(0 <= bin_idx < (BIN_FULL as int));
        assert(BIN_FULL == BIN_HUGE + 1) by(compute_only);
        assert(bin_idx <= (BIN_HUGE as int)) by(nonlinear_arith)
            requires
                bin_idx < (BIN_FULL as int),
                BIN_FULL == BIN_HUGE + 1;

        reveal(HeapLocalAccess::wf);
        reveal(pages_free_direct_is_correct);
        reveal(pages_free_direct_match);
        assert(local.heap.wf(
            local.heap_id,
            local.thread_token.value().heap,
            local.tld_id,
            local.instance.id(),
            local.page_empty_global@.s.points_to.ptr()));
        assert(pages_free_direct_is_correct(
            local.heap.pages_free_direct.value()@,
            local.heap.pages.value()@,
            local.page_empty_global@.s.points_to.ptr()));
        assert(local.heap.pages_free_direct.value()@.len() == PAGES_DIRECT);
        assert(local.heap.pages.value()@.len() == BIN_FULL + 1);
        assert(ptr == local.heap.pages_free_direct.value()@[idx as int]);
        assert(pages_free_direct_match(
            local.heap.pages_free_direct.value()@[idx as int],
            local.heap.pages.value()@[bin_idx].first,
            local.page_empty_global@.s.points_to.ptr()));

        reveal(Local::page_organization_valid);
        assert(local.page_organization_valid());
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(is_page_ptr_opt(
            local.heap.pages.value()@[bin_idx].first,
            local.page_organization.used_dlist_headers[bin_idx].first));
    }
    let ghost first_page_id = local.page_organization.used_dlist_headers[bin_idx].first;
    let ghost page_id = match first_page_id {
        Some(page_id) => page_id,
        None => arbitrary(),
    };
    proof {
        if direct_nonempty {
            assert(local.heap.pages.value()@[bin_idx].first as int != 0) by {
                if local.heap.pages.value()@[bin_idx].first as int == 0 {
                    assert(ptr as int == local.page_empty_global@.s.points_to.ptr() as int);
                }
            }
            match first_page_id {
                Some(id) => {
                    assert(page_id == id);
                }
                None => {
                    assert(local.heap.pages.value()@[bin_idx].first.addr() == 0);
                    assert(local.heap.pages.value()@[bin_idx].first as int == 0);
                    assert(false);
                }
            }
            local.page_organization.used_first_is_in(bin_idx);
            assert(local.page_organization.valid_used_page(page_id, bin_idx, 0));
            assert(local.page_organization.pages.dom().contains(page_id));
            assert(local.page_organization.pages[page_id].is_used == true);
            assert(page_organization_pages_match(
                local.page_organization.pages,
                local.pages,
                local.psa,
                local.page_organization.popped));
            assert(local.pages.dom().contains(page_id));
            assert(!local.unused_pages.dom().contains(page_id));
            assert(local.thread_token.value().pages.dom().contains(page_id));
            assert(local.pages[page_id].wf(
                page_id,
                local.thread_token.value().pages[page_id],
                local.instance));
            assert(local.thread_token.value().pages[page_id].is_enabled);
        }
        assert(direct_nonempty ==> local.pages.dom().contains(page_id));
    }
    let ptr = with_exposed_provenance(ptr.addr(), Tracked(if ptr as int == local.page_empty_global@.s.points_to.ptr() as int { local.page_empty_global.borrow().s.exposed } else { local.instance.thread_local_state_guards_page(local.thread_id, page_id, &local.thread_token).exposed }));
    let page_ptr = PagePtr { page_ptr: ptr, page_id: Ghost(page_id) };
    proof {
        assert(page_ptr.page_ptr.addr() == direct_addr);
        assert(direct_addr == local.heap.pages_free_direct.value()@[idx as int].addr());
        assert(idx as int == (size as int + 7) / 8);
        assert(page_ptr.page_ptr.addr()
            == local.heap.pages_free_direct.value()@[((size as int + 7) / 8)].addr());
        if local.heap.pages_free_direct.value()@[((size as int + 7) / 8)].addr()
            != empty_page_ptr.addr()
        {
            assert(direct_addr != empty_page_ptr.addr());
            assert(direct_nonempty);
            assert(local.pages.dom().contains(page_id));
            assert(page_ptr.is_in(*local));
            reveal(PageOrg::State::valid_used_page);
            assert(local.page_organization.valid_used_page(page_id, bin_idx, 0));
            assert(is_page_ptr(local.heap.pages.value()@[bin_idx].first, page_id));
            assert(page_ptr.page_ptr as int == local.heap.pages.value()@[bin_idx].first as int);
            assert(page_ptr.page_ptr@.provenance == page_id.segment_id.provenance);
            assert(page_ptr.wf());
            reveal(Local::wf_main);
            reveal(Local::page_organization_valid);
            assert(local.page_organization.pages[page_id].is_used);
            assert(local.page_organization.pages[page_id].offset == Some(0nat));
            assert(!local.unused_pages.dom().contains(page_id));
            assert(local.thread_token.value().pages.dom().contains(page_id));
            assert(page_organization_matches_token_page(
                local.page_organization.pages[page_id],
                local.thread_token.value().pages[page_id]));
            assert(local.thread_token.value().pages[page_id].offset == 0);
            assert(page_ptr.is_used_and_primary(*local));
            match local.page_organization.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, bsize)) => {
                    assert(bin == bin_idx);
                    assert(bsize == size_of_bin(bin_idx));
                    assert(local.pages[page_id].inner.value().xblock_size == bsize);
                    assert(local.block_size(page_id) == size_of_bin(bin_idx));
                }
                None => {
                    assert(false);
                }
            }
            assert(size as int <= idx as int * INTPTR_SIZE as int) by(nonlinear_arith)
                requires
                    idx as int == (size as int + 7) / 8,
                    size as int + 7 == 8 * ((size as int + 7) / 8) + ((size as int + 7) % 8),
                    0 <= ((size as int + 7) % 8) < 8;
            lemma_remainder(size as int + 7, 8);
            lemma_fundamental_div_mod(size as int + 7, 8);
            assert(size as int <= idx as int * INTPTR_SIZE as int);
            assert(size_of_bin(bin_idx) >= idx as int * INTPTR_SIZE as int);
            assert(size as int <= local.block_size(page_id));
        } else {
            assert(!direct_nonempty);
            assert(page_ptr.page_ptr == empty_page_ptr);
            assert(page_ptr.is_empty_global(*local));
        }
    }

    return page_ptr;
}

#[inline]
#[verifier::rlimit(200)]
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
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        })
{
    /*let mut size = size;
    if PADDING {
        if size == 0 {
            size = INTPTR_SIZE;
        }
    }*/

    let page = heap_get_free_small_page(heap, size, Tracked(&*local));

    proof {
        assert(page.is_empty_global(*local) || (
            page.wf()
            && page.is_used_and_primary(*local)
            && size as int <= local.block_size(page.page_id@)
        ));
    }

    let (p, Tracked(points_to_raw), Tracked(mim_dealloc)) = page_malloc(heap, page, size, zero, Tracked(&mut *local));

    (p, Tracked(points_to_raw), Tracked(mim_dealloc))
}

#[verifier::rlimit(200)]
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
        page_ptr.is_empty_global(*old(local)) || (
            page_ptr.wf()
            && page_ptr.is_used_and_primary(*old(local))
            && size as int <= old(local).block_size(page_ptr.page_id@)
        ),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
        ({
            let (ptr, points_to_raw, dealloc) = t;

            points_to_raw@.is_range(ptr as int, size as int)
              && points_to_raw@.provenance() == ptr@.provenance
              && ptr == dealloc@.ptr()
              && dealloc@.inst() == final(local).inst()
              && dealloc@.size() == size
        })
{
    if unlikely(page_ptr.get_inner_ref_maybe_empty(Tracked(&*local)).free.is_empty()) {
        return malloc_generic(heap, size, zero, 0, Tracked(&mut *local));
    }
    //assert(!page_ptr.is_empty_global(*local));

    proof {
        assert(!page_ptr.is_empty_global(*local));
        assert(page_ptr.wf());
        assert(page_ptr.is_used_and_primary(*local));
        assert(page_ptr.is_in(*local));
        assert(local.page_inner(page_ptr.page_id@).free.first_addr() != 0);
    }

    let ghost old_local = *local;
    let ghost page_id = page_ptr.page_id@;
    let popped;

    page_get_mut_inner!(page_ptr, local, page_inner => {
        popped = page_inner.free.pop_block();
        page_inner.used = page_inner.used + 1;
    });

    let ptr = popped.0;

    let tracked dealloc;
    let tracked points_to_raw;

    proof {
        let tracked block_raw = popped.1.get();
        let tracked block_token = popped.2.get();
        let ghost block_id = block_token.key();

        assert(local.wf());
        assert(local.inst() == old_local.inst());
        assert(block_id.page_id == page_id);
        assert(block_id.block_size as int == old_local.block_size(page_id));
        assert(size as int <= block_id.block_size as int);
        assert(block_token.instance_id() == local.instance.id());
        local.instance.get_block_properties(local.thread_id, block_id, &local.thread_token, &block_token);
        assert(local.thread_token.value().pages.dom().contains(block_id.page_id));
        assert(local.pages.dom().contains(block_id.page_id));
        assert(local.thread_token.value().segments.dom().contains(block_id.page_id.segment_id));
        assert(local.segments.dom().contains(block_id.page_id.segment_id));
        reveal(Local::wf);
        reveal(Local::wf_main);
        assert(local.pages[block_id.page_id].wf(
            block_id.page_id,
            local.thread_token.value().pages[block_id.page_id],
            local.instance));
        assert(local.segments[block_id.page_id.segment_id].wf(
            block_id.page_id.segment_id,
            local.thread_token.value().segments[block_id.page_id.segment_id],
            local.instance));
        assert(block_raw.is_range(ptr as int, block_id.block_size as int));
        assert(block_raw.provenance() == ptr@.provenance);

        let tracked (points_to_raw0, padding) =
            block_raw.split(set_int_range(ptr as int, ptr as int + size as int));

        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block_token,
            ptr,
        };

        reveal(MimDeallocInner::wf);
        reveal(valid_block_token);
        assert(dealloc_inner.mim_instance == local.instance);
        assert(dealloc_inner.mim_block.instance_id() == local.instance.id());
        assert(dealloc_inner.block_id() == block_id);
        assert(dealloc_inner.ptr == ptr);
        assert(is_block_ptr(ptr, dealloc_inner.block_id()));
        assert(valid_block_token(dealloc_inner.mim_block, dealloc_inner.mim_instance));
        assert(dealloc_inner.wf());
        assert(points_to_raw0.is_range(ptr as int, size as int));
        assert(points_to_raw0.provenance() == ptr@.provenance);
        assert(padding.is_range(ptr as int + size as int, block_id.block_size as int - size as int));
        assert(padding.provenance() == ptr@.provenance);

        let tracked dealloc0 = MimDealloc::new(padding, size as int, dealloc_inner);

        assert(dealloc0.ptr() == ptr);
        assert(dealloc0.inst() == local.inst());
        assert(dealloc0.size() == size);

        points_to_raw = points_to_raw0;
        dealloc = dealloc0;
    }

    (ptr, Tracked(points_to_raw), Tracked(dealloc))
}


}
