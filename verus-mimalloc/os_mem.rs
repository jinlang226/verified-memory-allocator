use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::set_lib::*;
use libc::{PROT_NONE, PROT_READ, PROT_WRITE, MAP_PRIVATE, MAP_ANONYMOUS, MAP_NORESERVE};

verus!{

#[verus::trusted]
pub open spec fn page_size() -> int { 4096 }

#[verifier::external_body]
#[verus::trusted]
pub fn get_page_size() -> (u: usize)
    ensures u == page_size()
{
    unimplemented!()
}

#[verus::trusted]
#[verifier(external_body)]
pub tracked struct OsMem {
    no_copy: NoCopy,
}

#[verus::trusted]
pub ghost struct MemProtect {
    pub read: bool,
    pub write: bool,
}

#[verus::trusted]
pub ghost struct OsMemData {
    pub byte_addr: int,
    pub mem_protect: MemProtect,
}

#[verus::trusted]
pub tracked struct MemChunk {
    pub os: Map<int, OsMem>,
    pub points_to: PointsToRaw,
}

#[verus::trusted]
impl MemChunk {
    pub open spec fn wf(&self) -> bool {
        self.wf_os()
    }

    pub open spec fn wf_os(&self) -> bool {
        forall |addr: int|
            #[trigger] self.os.dom().contains(addr)
             ==> self.os[addr]@.byte_addr == addr
    }

    #[verifier::inline]
    pub open spec fn range_os(&self) -> Set<int> {
        self.os.dom()
    }

    pub open spec fn range_os_rw(&self) -> Set<int> {
        self.os.dom().filter(|addr| self.os[addr]@.mem_protect == MemProtect { read: true, write: true })
    }

    pub open spec fn range_os_none(&self) -> Set<int> {
        self.os.dom().filter(|addr| self.os[addr]@.mem_protect == MemProtect { read: false, write: false })
    }

    #[verifier::inline]
    pub open spec fn range_points_to(&self) -> Set<int> {
        self.points_to.dom()
    }

    pub open spec fn has_pointsto_for_all_read_write(&self) -> bool {
        self.range_os_rw() <= self.range_points_to()
    }

    pub open spec fn os_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os()
    }

    pub open spec fn os_exact_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) =~= self.range_os()
    }

    pub open spec fn os_has_range_read_write(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os_rw()
    }

    pub open spec fn os_has_range_no_read_write(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_os_none()
    }

    pub open spec fn has_new_pointsto(&self, the_old: &MemChunk) -> bool {
        // Same domain for OS permissions knowledge
        self.os.dom() == the_old.os.dom()
        // points_to grew monotonically
        && the_old.points_to.dom().subset_of(self.points_to.dom())
        // stuff with rw permission grew monotonically
        && (forall |addr: int|
            #[trigger] the_old.os.dom().contains(addr)
              ==> the_old.os[addr]@.mem_protect == MemProtect { read: true, write: true }
              ==> self.os[addr]@.mem_protect == MemProtect { read: true, write: true }
        )
        // Anything that became rw, we now have the points_to for it
        && (forall |addr: int|
              self.os.dom().contains(addr)
              && self.os[addr]@.mem_protect == MemProtect { read: true, write: true }
              && the_old.os[addr]@.mem_protect != MemProtect { read: true, write: true }
              ==> #[trigger] self.points_to.dom().contains(addr)
        )
    }
}

#[verus::trusted]
impl OsMem {
    pub uninterp spec fn view(self) -> OsMemData;
}

#[verus::trusted]
pub const MAP_FAILED: usize = usize::MAX;

//// Wrappers

// TODO should allow these to return 0 for error case

#[verus::trusted]
#[verifier::external_body]
pub fn mmap_prot_none(hint: *mut u8, len: usize) -> (pt: (*mut u8, Tracked<MemChunk>))
    requires
        hint as int % page_size() == 0,
        len as int % page_size() == 0,
    ensures
        pt.0.addr() != MAP_FAILED ==> pt.1@.wf(),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_exact_range(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_has_range_no_read_write(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.0.addr() + len < usize::MAX,
        pt.0.addr() != MAP_FAILED ==> pt.0@.provenance == pt.1@.points_to.provenance()
{
    unimplemented!()
}

#[verus::trusted]
#[verifier::external_body]
pub fn mmap_prot_read_write(hint: *mut u8, len: usize) -> (pt: (*mut u8, Tracked<MemChunk>))
    requires
        hint as int % page_size() == 0,
        len as int % page_size() == 0,
    ensures
        pt.0.addr() != MAP_FAILED ==> pt.1@.wf(),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_exact_range(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.1@.os_has_range_read_write(pt.0 as int, len as int),
        pt.0.addr() != MAP_FAILED ==> pt.1@.has_pointsto_for_all_read_write(),
        pt.0.addr() != MAP_FAILED ==> pt.0.addr() + len < usize::MAX,
        pt.0.addr() != MAP_FAILED ==> pt.0 as int % page_size() == 0,
        pt.0.addr() != MAP_FAILED ==> pt.0@.provenance == pt.1@.points_to.provenance()
{
    unimplemented!()
}

#[verus::trusted]
#[verifier::external_body]
pub fn mprotect_prot_none(addr: *mut u8, len: usize, Tracked(mem): Tracked<&mut MemChunk>) 
    requires
        addr as int % page_size() == 0,
        len as int % page_size() == 0,

        old(mem).wf(),
        old(mem).os_exact_range(addr as int, len as int),
        old(mem).has_pointsto_for_all_read_write(),
        old(mem).points_to.provenance() == addr@.provenance,
    ensures
        final(mem).wf(),
        final(mem).os_exact_range(addr as int, len as int),
        final(mem).os_has_range_no_read_write(addr as int, len as int),
        final(mem).points_to.dom() === Set::empty(),
        final(mem).points_to.provenance() == old(mem).points_to.provenance()
{
    unimplemented!()
}

#[verus::trusted]
#[verifier::external_body]
pub fn mprotect_prot_read_write(addr: *mut u8, len: usize, Tracked(mem): Tracked<&mut MemChunk>)
    requires
        addr as int % page_size() == 0,
        len as int % page_size() == 0,
        old(mem).wf(),
        old(mem).os_exact_range(addr as int, len as int),
        old(mem).points_to.provenance() == addr@.provenance,
    ensures
        final(mem).wf(),
        final(mem).os_exact_range(addr as int, len as int),
        final(mem).os_has_range_read_write(addr as int, len as int),
        final(mem).has_new_pointsto(&*old(mem)),
        old(mem).has_pointsto_for_all_read_write() ==>
             final(mem).has_pointsto_for_all_read_write(),
        final(mem).points_to.provenance() == old(mem).points_to.provenance()
{
    unimplemented!()
}

//// Tested for macOS / Linux

#[verus::trusted]
#[verifier::external]
fn _mmap_prot_read_write(hint_addr: *mut libc::c_void, len: usize) -> *mut libc::c_void
{
    unimplemented!()
}

#[verifier::external]
fn _mmap_prot_none(hint_addr: *mut libc::c_void, len: usize) -> *mut libc::c_void
{
    unimplemented!()
}

#[verus::trusted]
#[verifier::external]
fn _mprotect_prot_read_write(addr: *mut libc::c_void, len: usize)
{
    unimplemented!()
}

#[verus::trusted]
#[verifier::external]
fn _mprotect_prot_none(addr: *mut libc::c_void, len: usize)
{
    unimplemented!()
}

//// Misc utilities

#[verus::trusted]
#[verifier::external_type_specification]
pub struct ExTimespec(libc::timespec);

#[verus::trusted]
#[inline(always)]
#[verifier::external_body]
pub fn clock_gettime_monotonic() -> libc::timespec
{
    unimplemented!()
}


}
