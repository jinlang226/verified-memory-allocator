#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::commit_mask::*;
use crate::types::*;
use crate::layout::*;
use crate::config::*;
use crate::segment::*;
use crate::os_mem_util::*;
use crate::tokens::*;
use crate::os_mem::*;

verus!{

#[verifier::external_body]
fn clock_now() -> i64
{
    unimplemented!()
}

#[verifier::external_body]
// Should not be called for huge segments, I think? TODO can probably optimize out some checks
fn segment_commit_mask(
    segment_ptr: *mut u8,
    conservative: bool,
    p: usize,
    size: usize,
    cm: &mut CommitMask)
 -> (res: (*mut u8, usize)) // start_p, full_size
    requires
        segment_ptr as int % SEGMENT_SIZE as int == 0,
        segment_ptr as int + SEGMENT_SIZE <= usize::MAX,
        p >= segment_ptr as int,
        p + size <= segment_ptr as int + SEGMENT_SIZE,
        old(cm)@ == Set::<int>::empty(),
    ensures ({ let (start_p, full_size) = res; {
        (final(cm)@ == Set::<int>::empty() ==> !conservative ==> size == 0)
        && (final(cm)@ != Set::<int>::empty() ==>
            (conservative ==> p <= start_p as int <= start_p as int + full_size <= p + size)
            && (!conservative ==> start_p as int <= p <= p + size <= start_p as int + full_size)
            && start_p as int >= segment_ptr as int
            && start_p as int + full_size <= segment_ptr as int + SEGMENT_SIZE
            //&& (!conservative ==> set_int_range((p - segment_ptr) / COMMIT_SIZE as int,
            //    (((p + size - 1 - segment_ptr as int) / COMMIT_SIZE as int) + 1)).subset_of(cm@))
            //&& (conservative ==> cm@ <= set_int_range((p - segment_ptr) / COMMIT_SIZE as int,
            //    (((p + size - 1 - segment_ptr as int) / COMMIT_SIZE as int) + 1)))
            && start_p as int % COMMIT_SIZE as int == 0
            && full_size as int % COMMIT_SIZE as int == 0
            && final(cm)@ =~= 
                set_int_range((start_p as int - segment_ptr as int) / COMMIT_SIZE as int,
                    (((start_p as int + full_size - segment_ptr as int) / COMMIT_SIZE as int)))
            && start_p@.provenance == segment_ptr@.provenance
        )
        && (!conservative ==> forall |i| #[trigger] final(cm)@.contains(i) ==>
            start_p as int <= segment_ptr as int + i * SLICE_SIZE
            && start_p as int + full_size >= segment_ptr as int + (i + 1) * SLICE_SIZE
        )
        //&& start_p as int % SLICE_SIZE as int == 0
        //&& full_size as int % SLICE_SIZE as int == 0
    }})
{
    unimplemented!()
}

#[verifier::external_body]
fn segment_commitx(
    segment: SegmentPtr,
    commit: bool,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
        // !commit ==> old(local).segments[segment.segment_id@]
        //    .mem.os_has_range_read_write(p as int, size as int),
        // !commit ==> old(local).segments[segment.segment_id@]
        //    .mem.pointsto_has_range(p as int, size as int),
        !commit ==> 
            set_int_range(p as int, p + size)
             <= old(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        commit ==> success ==> final(local).segments[segment.segment_id@]
            .mem.os_has_range_read_write(p as int, size as int),
        commit ==> success ==> set_int_range(p as int, p + size) <=
            final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
             - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),

        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa
{
    unimplemented!()
}

#[verifier::external_body]
pub fn segment_ensure_committed(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>
) -> (success: bool)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        success ==> set_int_range(p as int, p + size) <=
            final(local).commit_mask(segment.segment_id@).bytes(segment.segment_id@)
            - final(local).decommit_mask(segment.segment_id@).bytes(segment.segment_id@),

        final(local).page_organization == old(local).page_organization
{
    unimplemented!()
}

#[verifier::external_body]
pub fn segment_perhaps_decommit(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
        p >= segment.segment_ptr.addr(),
        p + size <= segment.segment_ptr.addr() + SEGMENT_SIZE,
        set_int_range(p as int, p + size).disjoint(
            segment_info_range(segment.segment_id@)
                + old(local).segment_pages_used_total(segment.segment_id@)
        )
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa
{
    unimplemented!()
}

#[verifier::external_body]
pub fn segment_delayed_decommit(
    segment: SegmentPtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>,
)
    requires old(local).wf_main(),
        segment.wf(),
        segment.is_in(*old(local)),
    ensures
        final(local).wf_main(),
        common_preserves(*old(local), *final(local)),
        final(local).page_organization == old(local).page_organization,
        final(local).pages == old(local).pages,
        final(local).psa == old(local).psa
{
    unimplemented!()
}

}
