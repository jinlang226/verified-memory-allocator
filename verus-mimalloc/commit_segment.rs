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
fn clock_now() -> i64 {
    let t = clock_gettime_monotonic();
    t.tv_sec.wrapping_mul(1000).wrapping_add( (((t.tv_nsec as u64) / 1000000) as i64) )
}

// Should not be called for huge segments, I think? TODO can probably optimize out some checks
#[verifier::external_body]
fn segment_commit_mask(
    segment_ptr: *mut u8,
    conservative: bool,
    p: usize,
    size: usize,
    cm: &mut CommitMask)
 -> (res: (*mut u8, usize)) // start_p, full_size
{

    if size == 0 || size > SEGMENT_SIZE as usize {
        return (core::ptr::null_mut(), 0);
    }

    let segstart: usize = SLICE_SIZE as usize;
    let segsize: usize = SEGMENT_SIZE as usize;

    if p >= segment_ptr.addr() + segsize {
        return (core::ptr::null_mut(), 0);
    }

    let pstart: usize = p - segment_ptr.addr();

    let mut start: usize;
    let mut end: usize;
    if conservative {
        start = align_up(pstart, COMMIT_SIZE as usize);
        end = align_down(pstart + size, COMMIT_SIZE as usize);
    } else {
        start = align_down(pstart, COMMIT_SIZE as usize);
        end = align_up(pstart + size, COMMIT_SIZE as usize);
    }

    if pstart >= segstart && start < segstart {
        start = segstart;
    }

    if end > segsize {
        end = segsize;
    }

    let start_p = segment_ptr.with_addr(segment_ptr.addr() + start);
    let full_size = if end > start { end - start } else { 0 };
    if full_size == 0 {
        return (start_p, full_size);
    }

    let bitidx = start / COMMIT_SIZE as usize;
    let bitcount = full_size / COMMIT_SIZE as usize;
    cm.create(bitidx, bitcount);


    return (start_p, full_size);
}

#[verifier::spinoff_prover]
#[verifier::external_body]
fn segment_commitx(
    segment: SegmentPtr,
    commit: bool,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
) -> (success: bool)
{
    let ghost sid = segment.segment_id@;

    let mut mask: CommitMask = CommitMask::empty();
    let (start, full_size) = segment_commit_mask(
        segment.segment_ptr as *mut u8, !commit, p, size, &mut mask);

    if mask.is_empty() || full_size == 0 {
        return true;
    }

    if commit && !segment.get_commit_mask(Tracked(&*local)).all_set(&mask) {

        let mut is_zero = false;
        let mut cmask = CommitMask::empty();
        segment.get_commit_mask(Tracked(&*local)).create_intersect(&mask, &mut cmask);

        let success;
        segment_get_mut_local!(segment, local, l => {
            let (_success, _is_zero) =
                crate::os_commit::os_commit(start, full_size, Tracked(&mut l.mem));
            success = _success;
        });
        if (!success) {
            return false;
        }

        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.set(&mask);
        });
    }
    else if !commit && segment.get_commit_mask(Tracked(&*local)).any_set(&mask) {
        let mut cmask = CommitMask::empty();
        segment.get_commit_mask(Tracked(&*local)).create_intersect(&mask, &mut cmask);
        if segment.get_allow_decommit(Tracked(&*local)) {
            segment_get_mut_local!(segment, local, l => {
                crate::os_commit::os_decommit(start, full_size, Tracked(&mut l.mem));
            });
        }
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.clear(&mask);
        });
    }

    if commit && segment.get_main_ref(Tracked(&*local)).decommit_mask.any_set(&mask) {
        segment_get_mut_main!(segment, local, main => {
            main.decommit_expire = clock_now().wrapping_add(option_decommit_delay());
        });
    }

    segment_get_mut_main!(segment, local, main => {
        main.decommit_mask.clear(&mask);
    });


    return true;
}

#[verifier::external_body]
pub fn segment_ensure_committed(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>
) -> (success: bool)
{
    if segment.get_commit_mask(Tracked(&*local)).is_full()
        && segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {

        return true;
    }

    segment_commitx(segment, true, p, size, Tracked(local))
}

#[verifier::external_body]
pub fn segment_perhaps_decommit(
    segment: SegmentPtr,
    p: usize,
    size: usize,
    Tracked(local): Tracked<&mut Local>,
)
{
    if !segment.get_allow_decommit(Tracked(&*local)) {
        return;
    }

    if option_decommit_delay() == 0 {
        todo();
    } else {

        let mut mask: CommitMask = CommitMask::empty();
        let (start, full_size) =
            segment_commit_mask(segment.segment_ptr as *mut u8, true, p, size, &mut mask);

        if mask.is_empty() || full_size == 0 {
            return;
        }

        let mut cmask = CommitMask::empty();
        segment_get_mut_main!(segment, local, main => {
            main.commit_mask.create_intersect(&mask, &mut cmask);
            main.decommit_mask.set(&cmask);
        });

        let ghost local_snap = *local;

        let now = clock_now();
        if segment.get_decommit_expire(Tracked(&*local)) == 0 {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire = now.wrapping_add(option_decommit_delay());
            });
        } else if segment.get_decommit_expire(Tracked(&*local)) <= now {
            let ded = option_decommit_extend_delay();
            if segment.get_decommit_expire(Tracked(&*local)).wrapping_add(option_decommit_extend_delay()) <= now {
                segment_delayed_decommit(segment, true, Tracked(&mut *local));
            } else {
                segment_get_mut_main!(segment, local, main => {
                    main.decommit_expire = now.wrapping_add(option_decommit_extend_delay());
                });
            }
        } else {
            segment_get_mut_main!(segment, local, main => {
                main.decommit_expire =
                    main.decommit_expire.wrapping_add(option_decommit_extend_delay());
            });
        }
    }

    assert(local.unused_pages === old(local).unused_pages);
    assert(local.page_organization === old(local).page_organization);
}

#[verifier::external_body]
pub fn segment_delayed_decommit(
    segment: SegmentPtr,
    force: bool,
    Tracked(local): Tracked<&mut Local>,
)
{
    if !segment.get_allow_decommit(Tracked(&*local))
        || segment.get_decommit_mask(Tracked(&*local)).is_empty()
    {
        return;
    }

    let now = clock_now();
    if !force && now < segment.get_decommit_expire(Tracked(&*local)) {
        return;
    }


    let mut idx = 0;
    loop
        invariant_except_break
            local.wf_main(),
            segment.wf(),
            segment.is_in(*local),
            0 <= idx < COMMIT_MASK_BITS,
        invariant
            local.wf_main(),
            common_preserves(*old(local), *local),
            local.page_organization == old(local).page_organization,
            local.pages == old(local).pages,
            local.psa == old(local).psa,
    {

        let mask = segment.get_decommit_mask(Tracked(&*local));
        let (next_idx, count) = mask.next_run(idx);
        if count == 0 {
            break;
        }
        idx = next_idx;

        let p = segment.segment_ptr.addr() + idx * COMMIT_SIZE as usize;
        let size = count * COMMIT_SIZE as usize;
        segment_commitx(segment, false, p, size, Tracked(&mut *local));
    }
}

}
