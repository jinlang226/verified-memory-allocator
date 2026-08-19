use core::intrinsics::{unlikely, likely};
use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::raw_ptr::*;
use crate::config::*;
use crate::os_mem::*;
use crate::layout::*;
use crate::types::todo;
use vstd::arithmetic::div_mod::{lemma_add_mod_noop, lemma_fundamental_div_mod};
use vstd::set_lib::set_int_range;


verus!{

#[verifier::rlimit(200)]
pub fn os_commit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (res: (bool, bool))
    requires
        size != 0 ==> addr as int % page_size() == 0,
        size != 0 ==> size as int % page_size() == 0,
        size != 0 ==>
            addr as int + size as int + page_size() - 1 <= usize::MAX as int,
        size != 0 ==> old(mem).wf(),
        size != 0 ==> old(mem).os_has_range(addr as int, size as int),
        size != 0 ==> old(mem).points_to.provenance() == addr@.provenance,
    ensures
        res.0 == true,
        res.1 == false,
        size != 0 ==> final(mem).wf(),
        size != 0 ==> final(mem).range_os() =~= old(mem).range_os(),
        size != 0 ==> final(mem).points_to.provenance() == old(mem).points_to.provenance(),
        size != 0 ==> old(mem).os_rw_bytes() <= final(mem).os_rw_bytes(),
        size != 0 ==> final(mem).os_rw_bytes() <= old(mem).os_rw_bytes() + set_int_range(addr as int, addr as int + size as int),
        size != 0 ==> final(mem).has_new_pointsto(&*old(mem)),
        size != 0 && old(mem).has_pointsto_for_all_read_write() ==> final(mem).has_pointsto_for_all_read_write(),
        size != 0 && addr.addr() != 0 ==> final(mem).os_has_range_read_write(addr as int, size as int),
        size != 0 && addr.addr() != 0 &&
            (old(mem).os_rw_bytes().intersect(set_int_range(addr as int, addr as int + size as int)) <= old(mem).points_to.dom()) ==>
                final(mem).pointsto_has_range(addr as int, size as int),
{
    os_commitx(addr, size, true, false, Tracked(&mut *mem))
}

pub fn os_decommit(addr: *mut u8, size: usize, Tracked(mem): Tracked<&mut MemChunk>)
    -> (success: bool)
    requires
        size != 0,
        old(mem).wf(),
        old(mem).os_has_range(addr as int, size as int),
        old(mem).points_to.provenance() == addr@.provenance,
        old(mem).committed_pointsto_has_range(addr as int, size as int),
        old(mem).os_has_range_read_write(addr as int, size as int),
        size != 0 ==> addr as int % page_size() == 0,
        size != 0 ==> size as int % page_size() == 0,
        size != 0 ==>
            addr as int + size as int + page_size() - 1 <= usize::MAX as int,
        size != 0 ==> old(mem).wf(),
        size != 0 ==> old(mem).os_has_range(addr as int, size as int),
        size != 0 ==> old(mem).points_to.provenance() == addr@.provenance,
    ensures
        success == true,
        size != 0 ==> final(mem).wf(),
        size != 0 ==> final(mem).range_os() =~= old(mem).range_os(),
        size != 0 ==> final(mem).points_to.provenance() == old(mem).points_to.provenance(),
        size != 0 ==>
            old(mem).os_rw_bytes() - set_int_range(addr as int, addr as int + size as int)
                <= final(mem).os_rw_bytes(),
        size != 0 ==>
            final(mem).os_rw_bytes() <=
                (old(mem).os_rw_bytes() - set_int_range(addr as int, addr as int + size as int))
                    + final(mem).points_to.dom(),
        size != 0 ==>
            old(mem).points_to.dom() - set_int_range(addr as int, addr as int + size as int)
                <= final(mem).points_to.dom(),
{
    let tracked mut t = mem.split(addr as int, size as int);
    let ghost t1 = t;
    proof {
        assert(t.os_has_range_read_write(addr as int, size as int)) by {
            assert forall |a: int| #[trigger] set_int_range(addr as int, addr as int + size as int).contains(a) implies
                t.os_rw_bytes().contains(a) by {
                assert(old(mem).range_os_rw().contains(a));
                assert(t.os.dom().contains(a));
                assert(t.os[a] == old(mem).os[a]);
            }
        }
        assert(t.has_pointsto_for_all_read_write()) by {
            assert forall |a: int| #[trigger] t.os.dom().contains(a)
                && t.os[a]@.mem_protect == MemProtect { read: true, write: true }
                implies t.points_to.dom().contains(a) by {
                assert(set_int_range(addr as int, addr as int + size as int).contains(a));
                assert(old(mem).points_to.dom().contains(a));
            }
        }
    }
    let (success, _) = os_commitx(addr, size, false, true, Tracked(&mut t));
    proof {
        let ghost range = set_int_range(addr as int, addr as int + size as int);
        let ghost rest = *mem;
        let ghost t_after = t;
        assert(rest.os_rw_bytes() =~= old(mem).os_rw_bytes() - range) by {
            assert forall |a: int| #[trigger] rest.os_rw_bytes().contains(a) ==
                (old(mem).os_rw_bytes() - range).contains(a) by {
                if rest.os_rw_bytes().contains(a) {
                    assert(rest.os.dom().contains(a));
                    assert(old(mem).os.dom().contains(a));
                    assert(!range.contains(a));
                    assert(rest.os[a] == old(mem).os[a]);
                    assert(old(mem).os_rw_bytes().contains(a));
                }
                if (old(mem).os_rw_bytes() - range).contains(a) {
                    assert(old(mem).os.dom().contains(a));
                    assert(!range.contains(a));
                    assert(rest.os.dom().contains(a));
                    assert(rest.os[a] == old(mem).os[a]);
                    assert(rest.os_rw_bytes().contains(a));
                }
            }
        }
        mem.join(t);
        assert forall |a: int| #[trigger] mem.os_rw_bytes().contains(a) implies
            ((old(mem).os_rw_bytes() - range) + mem.points_to.dom()).contains(a) by {
            if rest.os.dom().contains(a) {
                assert(mem.os[a] == rest.os[a]);
                assert(rest.os_rw_bytes().contains(a));
                assert((old(mem).os_rw_bytes() - range).contains(a));
            } else {
                assert(t_after.os.dom().contains(a));
                assert(mem.os[a] == t_after.os[a]);
                assert(t_after.os_rw_bytes().contains(a));
                assert(t_after.os_rw_bytes() <= (t1.os_rw_bytes() - range) + t_after.points_to.dom());
                assert((t1.os_rw_bytes() - range) =~= Set::<int>::empty()) by {
                    assert forall |b: int| #[trigger] (t1.os_rw_bytes() - range).contains(b) implies false by {
                        assert(t1.os.dom().contains(b));
                        assert(range.contains(b));
                    }
                }
                assert(t_after.points_to.dom().contains(a));
                assert(mem.points_to.dom().contains(a));
            }
        }
    }
    success
}

#[verifier::rlimit(200)]
proof fn lemma_aligned_in_same_page(x: int, aligned: int, unit: int)
    requires
        0 < unit,
        x % unit == 0,
        aligned % unit == 0,
        aligned <= x,
        x < aligned + unit,
    ensures
        x == aligned,
{
    if aligned < x {
        lemma_fundamental_div_mod(aligned, unit);
        lemma_fundamental_div_mod(x, unit);
        assert(aligned == unit * (aligned / unit));
        assert(x == unit * (x / unit));
        assert(aligned / unit < x / unit) by(nonlinear_arith)
            requires
                aligned == unit * (aligned / unit),
                x == unit * (x / unit),
                aligned < x,
                0 < unit;
        assert(aligned / unit + 1 <= x / unit);
        assert(aligned + unit <= x) by(nonlinear_arith)
            requires
                aligned == unit * (aligned / unit),
                x == unit * (x / unit),
                aligned / unit + 1 <= x / unit,
                0 < unit;
        assert(false) by(nonlinear_arith)
            requires
                aligned + unit <= x,
                x < aligned + unit;
    }
}

#[verus_verify]
fn os_page_align_areax(conservative: bool, addr: usize, size: usize)
    -> (res: (usize, usize))
    requires
        size != 0 && addr != 0 ==> addr as int % page_size() == 0,
        size != 0 && addr != 0 ==> size as int % page_size() == 0,
        size != 0 && addr != 0 ==>
            addr as int + size as int + page_size() - 1 <= usize::MAX as int,
    ensures
        size == 0 || addr == 0 ==> res.0 == 0 && res.1 == 0,
        size != 0 && addr != 0 ==> res.0 == addr && res.1 == size,
{
    if size == 0 || addr == 0 {
        return (0, 0);
    }

    proof {
        assert(page_size() == 4096) by(compute_only);
        assert(page_size() > 0);
        assert(addr as int + page_size() - 1 <= usize::MAX as int) by(nonlinear_arith)
            requires
                addr as int + size as int + page_size() - 1 <= usize::MAX as int,
                0 <= size as int;
        assert(addr as int + size as int <= usize::MAX as int) by(nonlinear_arith)
            requires
                addr as int + size as int + page_size() - 1 <= usize::MAX as int,
                page_size() > 0;
    }

    let start = if conservative {
        align_up(addr, get_page_size())
    } else {
        align_down(addr, get_page_size())
    };
    proof {
        lemma_aligned_in_same_page(start as int, addr as int, page_size());
        assert(start == addr);
        assert((addr + size) as int == addr as int + size as int) by(bit_vector)
            requires addr as int + size as int <= usize::MAX as int;
        lemma_add_mod_noop(addr as int, size as int, page_size());
        assert((addr as int + size as int) % page_size() == 0);
        assert(((addr + size) as int) % page_size() == 0);
        assert((addr + size) as int + page_size() - 1 <= usize::MAX as int) by(nonlinear_arith)
            requires
                (addr + size) as int == addr as int + size as int,
                addr as int + size as int + page_size() - 1 <= usize::MAX as int;
    }
    let end = if conservative {
        align_down(addr + size, get_page_size())
    } else {
        align_up(addr + size, get_page_size())
    };
    proof {
        lemma_aligned_in_same_page((addr + size) as int, end as int, page_size());
        assert(end == addr + size);
        assert(start <= end) by(nonlinear_arith)
            requires
                start == addr,
                end == addr + size;
    }

    let diff = end - start;
    proof {
        assert(diff == sub(end, start));
        assert(diff as int == end as int - start as int) by(bit_vector)
            requires
                diff == sub(end, start),
                start <= end;
        assert(diff as int == size as int) by(nonlinear_arith)
            requires
                diff as int == end as int - start as int,
                start == addr,
                end == addr + size,
                (addr + size) as int == addr as int + size as int;
        assert(diff == size);
        assert(diff > 0);
    }
    if diff <= 0 {
        return (0, 0);
    }
    (start, diff)
}

#[verifier::rlimit(200)]
fn os_commitx(
    addr: *mut u8, size: usize, commit: bool, conservative: bool,
    Tracked(mem): Tracked<&mut MemChunk>
) -> (res: (bool, bool))
    requires
        size != 0 ==> addr as int % page_size() == 0,
        size != 0 ==> size as int % page_size() == 0,
        size != 0 ==>
            addr as int + size as int + page_size() - 1 <= usize::MAX as int,
        size != 0 ==> old(mem).wf(),
        size != 0 ==> old(mem).os_has_range(addr as int, size as int),
        size != 0 ==> old(mem).points_to.provenance() == addr@.provenance,
        size != 0 && !commit ==> old(mem).committed_pointsto_has_range(addr as int, size as int),
    ensures
        res.0 == true,
        res.1 == false,
        size != 0 && commit ==> final(mem).wf(),
        size != 0 && commit ==> final(mem).range_os() =~= old(mem).range_os(),
        size != 0 && commit ==> final(mem).points_to.provenance() == old(mem).points_to.provenance(),
        size != 0 && commit ==> old(mem).os_rw_bytes() <= final(mem).os_rw_bytes(),
        size != 0 && commit ==> final(mem).os_rw_bytes() <= old(mem).os_rw_bytes() + set_int_range(addr as int, addr as int + size as int),
        size != 0 && commit ==> final(mem).has_new_pointsto(&*old(mem)),
        size != 0 && commit && old(mem).has_pointsto_for_all_read_write() ==> final(mem).has_pointsto_for_all_read_write(),
        size != 0 && commit && addr.addr() != 0 ==> final(mem).os_has_range_read_write(addr as int, size as int),
        size != 0 && commit && addr.addr() != 0 &&
            (old(mem).os_rw_bytes().intersect(set_int_range(addr as int, addr as int + size as int)) <= old(mem).points_to.dom()) ==>
                final(mem).pointsto_has_range(addr as int, size as int),
        size != 0 && !commit ==> final(mem).wf(),
        size != 0 && !commit ==> final(mem).range_os() =~= old(mem).range_os(),
        size != 0 && !commit ==> final(mem).points_to.provenance() == old(mem).points_to.provenance(),
        size != 0 && !commit ==>
            old(mem).os_rw_bytes() - set_int_range(addr as int, addr as int + size as int)
                <= final(mem).os_rw_bytes(),
        size != 0 && !commit ==>
            final(mem).os_rw_bytes() <=
                (old(mem).os_rw_bytes() - set_int_range(addr as int, addr as int + size as int))
                    + final(mem).points_to.dom(),
        size != 0 && !commit ==>
            old(mem).points_to.dom() - set_int_range(addr as int, addr as int + size as int)
                <= final(mem).points_to.dom(),
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

    proof {
        if !commit {
            assert(exact_mem.os_has_range_read_write(addr as int, size as int)) by {
                assert forall |a: int| #[trigger] set_int_range(addr as int, addr as int + size as int).contains(a) implies
                    exact_mem.os_rw_bytes().contains(a) by {
                    assert(old(mem).range_os_rw().contains(a));
                    assert(exact_mem.os.dom().contains(a));
                    assert(exact_mem.os[a] == old(mem).os[a]);
                }
            }
            assert(exact_mem.has_pointsto_for_all_read_write()) by {
                assert forall |a: int| #[trigger] exact_mem.os.dom().contains(a)
                    && exact_mem.os[a]@.mem_protect == MemProtect { read: true, write: true }
                    implies exact_mem.points_to.dom().contains(a) by {
                    assert(set_int_range(addr as int, addr as int + size as int).contains(a));
                    assert(old(mem).points_to.dom().contains(a));
                }
            }
        }
    }

    if commit {
        mprotect_prot_read_write(p, csize, Tracked(&mut exact_mem));
    } else {
        // TODO madvise?
        mprotect_prot_none(p, csize, Tracked(&mut exact_mem));
    }

    proof {
        if commit {
            mem.join(exact_mem);
            let tracked empty_os = Map::<int, OsMem>::tracked_empty();
            let tracked extra_mem = MemChunk { os: empty_os, points_to: weird_extra };
            mem.join(extra_mem);
        } else {
            mem.join(exact_mem);
            let tracked empty_os = Map::<int, OsMem>::tracked_empty();
            let tracked extra_mem = MemChunk { os: empty_os, points_to: weird_extra };
            mem.join(extra_mem);
        }
    }

    // TODO bubble up error instead of panicking
    return (true, is_zero);
}

}

