#![allow(unused_imports)]

use core::intrinsics::{unlikely, likely};

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::*;
use vstd::modes::*;
use vstd::set_lib::*;
use vstd::cell::pcell::*;
use vstd::shared::Shared;

use crate::tokens::{Mim, BlockId, DelayState, ThreadState, HeapState, HeapId, TldId, ThreadId};
use crate::types::*;
use crate::layout::*;
use crate::linked_list::*;
use crate::dealloc_token::*;
use crate::alloc_generic::*;
use crate::os_mem_util::*;
use crate::config::*;
use crate::bin_sizes::*;
use crate::page_organization::*;
use crate::os_mem::*;
use crate::thread::*;

verus!{

pub tracked struct Global {
    pub(crate) tracked instance: Mim::Instance,
    pub(crate) tracked my_inst: Mim::my_inst,
}

impl Global {
    #[verifier::type_invariant]
    pub(crate) closed spec fn wf(&self) -> bool {
        self.my_inst.instance_id() == self.instance.id()
        && self.my_inst.value() == self.instance.id()
    }

    pub open(crate) spec fn wf_right_to_use_thread(&self, right: RightToUseThread, tid: ThreadId) -> bool {
        right.instance_id() == self.instance.id() && right.element() == tid
    }

    pub open(crate) spec fn inst(&self) -> MimInst {
        self.instance
    }
}

type RightToUseThread = Mim::right_to_use_thread;
type MimInst = Mim::Instance;


/*
impl RightToUseThread {
    pub open spec fn wf(tid: ThreadId) { true } // TODO
}
*/

//impl Copy for Global { }

#[verifier::external_body]
pub proof fn global_init() -> (tracked res: (Global, Map<ThreadId, Mim::right_to_use_thread>))    // $line_count$Trusted$
    ensures // $line_count$Trusted$
        forall |tid: ThreadId| #[trigger] res.1.dom().contains(tid) // $line_count$Trusted$
          && res.0.wf_right_to_use_thread(res.1[tid], tid) // $line_count$Trusted$
{
    unimplemented!()
}

#[verifier::external_body]
pub fn heap_init(Tracked(global): Tracked<Global>, // $line_count$Trusted$
      Tracked(right): Tracked<Mim::right_to_use_thread>, // $line_count$Trusted$
      Tracked(cur_thread): Tracked<IsThread> // $line_count$Trusted$
) -> (res: (HeapPtr, Tracked<Option<Local>>)) // $line_count$Trusted$
    requires global.wf_right_to_use_thread(right, cur_thread@), // $line_count$Trusted$
    ensures ({ let (heap, local_opt) = res; { // $line_count$Trusted$
        heap.heap_ptr.addr() != 0 ==> // $line_count$Trusted$
            local_opt@.is_some() // $line_count$Trusted$
            && local_opt@.unwrap().wf() // $line_count$Trusted$
            && local_opt@.unwrap().inst() == global.inst() // $line_count$Trusted$
            && heap.wf() // $line_count$Trusted$
            && heap.is_in(local_opt@.unwrap()) // $line_count$Trusted$
    }}) // $line_count$Trusted$
{
    unimplemented!()
}


impl PageQueue {
    #[verifier::external_body]
    #[inline]
    fn empty(wsize: usize) -> (pq: PageQueue)
        requires wsize < 0x1_0000_0000_0000,
        ensures
          pq.first.addr() == 0,
          pq.last.addr() == 0,
          pq.block_size == wsize * INTPTR_SIZE
    {
        unimplemented!()
    }
}

#[verifier::external_body]
#[inline]
fn pages_tmp() -> (pages: [PageQueue; 75])
    ensures pages@.len() == BIN_FULL + 1,
      forall |p| 0 <= p < pages@.len() ==> (#[trigger] pages[p]).first.addr() == 0
          && pages[p].last.addr() == 0
          && (valid_bin_idx(p) ==> pages[p].block_size == size_of_bin(p)),
      pages[0].block_size == 8,
      pages[BIN_FULL as int].block_size == 8 * (524288 + 2), //8 * (MEDIUM_OBJ_WSIZE_MAX + 2)
{
    unimplemented!()
}

#[verifier::external_body]
fn pages_free_direct_tmp() -> [*mut Page; 129]
{
    unimplemented!()
}

#[verifier::external_body]
fn span_queue_headers_tmp() -> [SpanQueueHeader; 32]
{
    unimplemented!()
}

#[verifier::external_body]
fn thread_data_alloc()
    -> (res: (*mut u8, Tracked<MemChunk>))
    ensures ({ let (p, mc) = res; {
        p.addr() != 0 ==> (
            mc@.pointsto_has_range(p as int, SIZEOF_HEAP + SIZEOF_TLD)
            && p as int + page_size() <= usize::MAX
            && p as int % 4096 == 0
            && p@.provenance == mc@.points_to.provenance()
        )
    }})
{
    unimplemented!()
}

///// The global 'empty page'

/*
pub fn get_page_empty()
    -> (res: (PPtr<Page>, Tracked<Shared<PageFullAccess>>))
    ensures ({ let (page_ptr, pfa) = res; {
        pfa@@.wf_empty_page_global()
        && pfa@@.s.points_to@.pptr == page_ptr.id()
        && page_ptr.id() != 0
    }})
{
    let e = get_empty_page_stuff();
    (e.ptr, Tracked(e.pfa.borrow().clone()))
}
*/

struct EmptyPageStuff {
    ptr: *mut Page,
    pfa: Tracked<Shared<PageFullAccess>>,
}

impl EmptyPageStuff {
    pub closed spec fn wf(&self) -> bool {
        self.pfa@@.wf_empty_page_global()
        && self.pfa@@.s.points_to.ptr() == self.ptr
        && self.ptr.addr() != 0
    }
}

/*
#[verifier::external]
static EMPTY_PAGE_PTR: std::sync::LazyLock<EmptyPageStuff> =
    std::sync::LazyLock::new(init_empty_page_ptr);
*/

#[verifier::external_body]
fn init_empty_page_ptr() -> (e: EmptyPageStuff)
    ensures e.wf()
{
    unimplemented!()
}

/*
#[verifier::external_body]
fn get_empty_page_stuff() -> (e: &'static EmptyPageStuff)
    ensures e.wf()
{
    &*EMPTY_PAGE_PTR
}
*/

//// Current thread count

/*
struct_with_invariants!{
    pub struct ThreadCountAtomic {
        pub atomic: AtomicUsize<_, (), _>,
    }

    pub open spec fn wf(&self) -> bool {
        invariant
            on atomic
            is (v: usize, g: ())
        {
            true
        }
    }
}

impl ThreadCountAtomic {
    #[inline]
    pub get(&self) -> usize {
        self.atomic.load()
    }

    #[inline]
    pub new(&self) -> usize {
        self.atomic.load()
    }
}
*/

exec static THREAD_COUNT: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

//exec static THREAD_COUNT: core::sync::atomic::AtomicUsize
//  ensures true
//  { core::sync::atomic::AtomicUsize::new(0) }

#[verifier::external_body]
#[inline]
fn increment_thread_count()
{
    unimplemented!()
}

#[verifier::external_body]
#[inline]
pub fn current_thread_count() -> usize
{
    unimplemented!()
}


}
