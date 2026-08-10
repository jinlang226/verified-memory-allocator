use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::raw_ptr::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;
use vstd::set_lib::set_int_range;


verus!{

#[verifier::external_body]
pub fn os_commit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (res: (bool, bool))
{
    os_commitx(addr, size, true, false, Tracked(&mut *mem))
}

#[verifier::external_body]
pub fn os_decommit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (success: bool)
{
    let tracked mut t = mem.split(addr as int, size as int);
    let ghost t1 = t;
    let (success, _) = os_commitx(addr, size, false, true, Tracked(&mut t));
    success
}

#[verifier::external_body]
fn os_page_align_areax(conservative: bool, addr: usize, size: usize)
    -> (res: (usize, usize))
{
    if size == 0 || addr == 0 {
        return (0, 0);
    }

    let start = if conservative {
        align_up(addr, get_page_size())
    } else {
        align_down(addr, get_page_size())
    };
    let end = if conservative {
        align_down(addr + size, get_page_size())
    } else {
        align_up(addr + size, get_page_size())
    };

    let diff = end - start;
    if diff <= 0 {
        return (0, 0);
    }
    (start, diff)
}

#[verifier::external_body]
fn os_commitx(
    addr: *mut u8, size: usize, commit: bool, conservative: bool,
    Tracked(mem): Tracked<&mut MemChunk>
) -> (res: (bool, bool))
{
    let is_zero = false;
    let (start, csize) = os_page_align_areax(conservative, addr.addr(), size);
    if csize == 0 {
        return (true, is_zero);
    }
    let err = 0;

    let p = addr.with_addr(start);

    let tracked weird_extra = mem.take_points_to_set(
          mem.points_to.dom() - mem.os_rw_bytes());
    let tracked mut exact_mem = mem.split(addr as int, size as int);
    let ghost em = exact_mem;

    if commit {
        mprotect_prot_read_write(p, csize, Tracked(&mut exact_mem));
    } else {
        // TODO madvise?
        mprotect_prot_none(p, csize, Tracked(&mut exact_mem));
    }


    // TODO bubble up error instead of panicking
    return (true, is_zero);
}

}

