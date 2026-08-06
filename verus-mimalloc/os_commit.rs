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
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        addr@.provenance == old(mem).points_to.provenance(),
        //old(mem).has_pointsto_for_all_read_write(),
    ensures ({
        let (success, is_zero) = res;
        final(mem).wf()
        //&& final(mem).has_pointsto_for_all_read_write()
        //&& (success ==> final(mem).os_has_range_read_write(addr as int, size as int))
        && final(mem).has_new_pointsto(&*old(mem))
        && final(mem).os.dom() == old(mem).os.dom()
        && final(mem).points_to.provenance() == old(mem).points_to.provenance()
        && (success ==> final(mem).os_has_range_read_write(addr as int, size as int))
    })
{
    unimplemented!()
}

#[verifier::external_body]
pub fn os_decommit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (success: bool)
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        old(mem).pointsto_has_range(addr as int, size as int),
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        addr@.provenance == old(mem).points_to.provenance(),
    ensures
        final(mem).wf(),
        final(mem).os.dom() =~= old(mem).os.dom(),

        final(mem).points_to.dom().subset_of(old(mem).points_to.dom()),
        final(mem).os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        final(mem).points_to.provenance() == old(mem).points_to.provenance(),

        old(mem).points_to.dom() - final(mem).points_to.dom()
            =~= old(mem).os_rw_bytes() - final(mem).os_rw_bytes(),
        old(mem).os_rw_bytes() - final(mem).os_rw_bytes()
            <= set_int_range(addr as int, addr as int + size)
{
    unimplemented!()
}

#[verifier::external_body]
fn os_page_align_areax(conservative: bool, addr: usize, size: usize)
    -> (res: (usize, usize))
    requires
        addr as int % page_size() == 0,
        size as int % page_size() == 0,
        addr != 0,
        addr + size <= usize::MAX,
    ensures
        ({ let (start, csize) = res;
            start as int % page_size() == 0
            && csize as int % page_size() == 0
            && (size != 0 ==> start == addr)
            && (size != 0 ==> csize == size)
            && (size == 0 ==> start == 0 && csize == 0)
        })
{
    unimplemented!()
}

#[verifier::external_body]
fn os_commitx(
    addr: *mut u8, size: usize, commit: bool, conservative: bool,
    Tracked(mem): Tracked<&mut MemChunk>
) -> (res: (bool, bool))
    requires old(mem).wf(), 
        old(mem).os_has_range(addr as int, size as int),
        addr as int % page_size() as int == 0,
        size as int % page_size() as int == 0,
        addr as int != 0,
        addr as int + size <= usize::MAX,
        !commit ==> old(mem).pointsto_has_range(addr as int, size as int),
        addr@.provenance == old(mem).points_to.provenance()
    ensures
        final(mem).wf(),
        final(mem).os.dom() =~= old(mem).os.dom(),
        commit ==> final(mem).has_new_pointsto(&*old(mem)),
        commit ==> res.0 ==> final(mem).os_has_range_read_write(addr as int, size as int),
        !commit ==> final(mem).points_to.dom().subset_of(old(mem).points_to.dom()),
        !commit ==> final(mem).os_rw_bytes().subset_of(old(mem).os_rw_bytes()),
        !commit ==> old(mem).points_to.dom() - final(mem).points_to.dom()
                    =~= old(mem).os_rw_bytes() - final(mem).os_rw_bytes(),
        final(mem).points_to.provenance() == old(mem).points_to.provenance()
{
    unimplemented!()
}

}

