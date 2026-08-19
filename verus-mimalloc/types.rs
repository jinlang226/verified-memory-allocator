#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::arithmetic::div_mod::lemma_div_by_multiple;
use vstd::cell::pcell::*;
use vstd::cell::pcell;
use vstd::atomic_ghost::*;
use vstd::shared::Shared;
use verus_state_machines_macros::*;

use crate::config::*;
use crate::tokens::{Mim, BlockId, PageId, ThreadId, SegmentId, HeapId, PageState, HeapState, SegmentState, TldId};
use crate::linked_list::{LL, ThreadLLSimple, ThreadLLWithDelayBits};
use crate::layout::{is_page_ptr, is_page_ptr_opt, is_heap_ptr, is_tld_ptr, block_start_at, is_segment_ptr, page_header_start, page_start, segment_start, lemma_segment_start_basics};
use crate::page_organization::*;
use crate::os_mem::MemChunk;
use crate::commit_mask::CommitMask;
use crate::bin_sizes::{valid_bin_idx, size_of_bin, smallest_bin_fitting_size};
use crate::arena::{ArenaId, MemId};

verus!{

//// Page header data

#[repr(C)]
pub struct PageInner {
    pub flags0: u8,   // is_reset, is_committed, is_zero_init,

    pub capacity: u16,
    pub reserved: u16,

    pub flags1: u8,       // in_full, has_aligned
    pub flags2: u8,       // is_zero, retire_expire

    pub free: LL,

    // number of blocks that are allocated, or in `xthread_free`
    // In other words, this is the "complement" of the number
    // of blocks in `free` and `local_free`.
    pub used: u32,

    pub xblock_size: u32,
    pub local_free: LL,
}

impl PageInner {
    pub open spec fn wf(&self, page_id: PageId, page_state: PageState, mim_instance: Mim::Instance) -> bool {
        &&& page_state.block_size == self.xblock_size as nat

        &&& self.free.wf()
        &&& self.free.fixed_page()
        &&& self.free.page_id() == page_id
        &&& self.free.block_size() == page_state.block_size
        &&& self.free.instance() == mim_instance
        &&& self.free.heap_id().is_none()

        &&& self.local_free.wf()
        &&& self.local_free.fixed_page()
        &&& self.local_free.page_id() == page_id
        &&& self.local_free.block_size() == page_state.block_size
        &&& self.local_free.instance() == mim_instance
        &&& self.local_free.heap_id().is_none()

        &&& self.used + self.free.len() + self.local_free.len() == page_state.num_blocks

        &&& self.local_free.fixed_page()
        &&& self.free.fixed_page()

        &&& self.local_free.block_size() == page_state.block_size
        &&& self.free.block_size() == page_state.block_size

        &&& self.capacity <= self.reserved
        &&& self.capacity == page_state.num_blocks

        &&& self.xblock_size > 0
    }

    pub open spec fn zeroed(&self) -> bool {
        &&& self.capacity == 0
        &&& self.reserved == 0
        &&& self.free.wf() && self.free.len() == 0
        &&& self.used == 0
        &&& self.xblock_size == 0
        &&& self.local_free.wf() && self.local_free.len() == 0
    }

    pub open spec fn zeroed_except_block_size(&self) -> bool {
        &&& self.capacity == 0
        &&& self.reserved == 0
        &&& self.free.wf() && self.free.len() == 0
        &&& self.used == 0
        &&& self.local_free.wf() && self.local_free.len() == 0
    }
}

tokenized_state_machine!{ BoolAgree {
    fields {
        #[sharding(variable)] pub x: bool,
        #[sharding(variable)] pub y: bool,
    }
    init!{
        initialize(b: bool) {
            init x = b;
            init y = b;
        }
    }
    transition!{
        set(b: bool) {
            assert(pre.x == pre.y);
            update x = b;
            update y = b;
        }
    }
    property!{
        agree() {
            assert(pre.x == pre.y);
        }
    }
    #[invariant]
    pub spec fn inv_eq(&self) -> bool {
        self.x == self.y
    }
    #[inductive(initialize)] fn initialize_inductive(post: Self, b: bool) { }
    #[inductive(set)] fn set_inductive(pre: Self, post: Self, b: bool) { }
}}

struct_with_invariants!{
    pub struct AtomicHeapPtr {
        pub atomic: AtomicPtr<Heap, _, (BoolAgree::y, Option<Mim::heap_of_page>), _>,

        pub instance: Ghost<Mim::Instance>,
        pub page_id: Ghost<PageId>,
        pub emp: Tracked<BoolAgree::x>,
        pub emp_inst: Tracked<BoolAgree::Instance>,
    }

    pub open spec fn wf(&self, instance: Mim::Instance, page_id: PageId) -> bool {
        predicate {
            self.instance == instance
            && self.page_id == page_id
            && self.emp@.instance_id() == self.emp_inst@.id()
        }
        invariant
            on atomic
            with (instance, page_id, emp, emp_inst)
            is (v: *mut Heap, all_g: (BoolAgree::y, Option<Mim::heap_of_page>))
        {
            let (is_emp, g_opt) = all_g;
            is_emp.instance_id() == emp_inst@.id()
            && (match g_opt {
                None => is_emp.value(),
                Some(g) => {
                    &&& !is_emp.value()
                    &&& g.instance_id() == instance@.id()
                    &&& g.key() == page_id
                    &&& is_heap_ptr(v, g.value())
                }
            })
        }
    }
}

impl AtomicHeapPtr {
    pub open spec fn is_empty(&self) -> bool { self.emp@.value() }

    pub fn empty() -> (ahp: AtomicHeapPtr)
        ensures
            ahp.is_empty(),
    {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(true);
        let ghost g = (Ghost(arbitrary()), Ghost(arbitrary()), Tracked(emp_x), Tracked(emp_inst));
        AtomicHeapPtr {
            page_id: Ghost(arbitrary()),
            instance: Ghost(arbitrary()),
            emp: Tracked(emp_x),
            emp_inst: Tracked(emp_inst),
            atomic: AtomicPtr::new(Ghost(g), core::ptr::null_mut(), Tracked((emp_y, None))),
        }
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn disable(&mut self) -> (hop: Tracked<Mim::heap_of_page>)
        ensures
            final(self).wf(old(self).instance@, old(self).page_id@),
            final(self).is_empty(),
            hop@.instance_id() == old(self).instance@.id(),
            hop@.key() == old(self).page_id@,
    {
        let tracked mut heap_of_page;
        atomic_with_ghost!(
            &self.atomic => no_op();
            ghost g => {
                let tracked (mut y, heap_of_page_opt) = g;
                self.emp_inst.borrow().set(true, self.emp.borrow_mut(), &mut y);
                heap_of_page = heap_of_page_opt.tracked_unwrap();
                g = (y, None);
            }
        );
        Tracked(heap_of_page)
    }
}

#[repr(C)]
pub struct Page {
    pub count: PCell<u32>,
    pub offset: u32, // this value is read-only while the Page is shared

    pub inner: PCell<PageInner>,
    pub xthread_free: ThreadLLWithDelayBits,
    pub xheap: AtomicHeapPtr,
    pub prev: PCell<*mut Page>,
    pub next: PCell<*mut Page>,

    pub padding: usize,
}

pub tracked struct PageSharedAccess {
    pub tracked points_to: raw_ptr::PointsTo<Page>,
    pub tracked exposed: raw_ptr::IsExposed,
}

pub tracked struct PageLocalAccess {
    pub tracked count: pcell::PointsTo<u32>,
    pub tracked inner: pcell::PointsTo<PageInner>,
    pub tracked prev: pcell::PointsTo<*mut Page>,
    pub tracked next: pcell::PointsTo<*mut Page>,
}

pub tracked struct PageFullAccess {
    pub tracked s: PageSharedAccess,
    pub tracked l: PageLocalAccess,
}

impl Page {
    pub open spec fn wf(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && !self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
          && self.xthread_free.page_id() == page_id
          && self.xthread_free.block_size() == block_size

          && self.xheap.wf(mim_instance, page_id)
          && !self.xheap.is_empty()
    }

    pub open spec fn wf_secondary(&self, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
    }

    pub open spec fn wf_unused(&self, mim_instance: Mim::Instance) -> bool {
        self.xthread_free.wf()
          && self.xthread_free.is_empty()
          && self.xthread_free.instance == mim_instance
    }
}

pub open spec fn page_differ_only_in_offset(page1: Page, page2: Page) -> bool {
    page2 == Page { offset: page2.offset, .. page1 }
}

pub open spec fn psa_differ_only_in_offset(psa1: PageSharedAccess, psa2: PageSharedAccess) -> bool {
    psa1.points_to.is_init()
    && psa2.points_to.is_init()
    && page_differ_only_in_offset(
        psa1.points_to.value(),
        psa2.points_to.value())
    && psa1.points_to.ptr() == psa2.points_to.ptr()
}

impl PageSharedAccess {
    pub open spec fn wf(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf(page_id, block_size, mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }

    pub open spec fn wf_secondary(&self, page_id: PageId, block_size: nat, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf_secondary(mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }

    pub open spec fn wf_unused(&self, page_id: PageId, mim_instance: Mim::Instance) -> bool {
        &&& is_page_ptr(self.points_to.ptr(), page_id)
        &&& self.points_to.is_init()
        &&& self.points_to.value().wf_unused(mim_instance)
        &&& self.exposed.provenance() == self.points_to.ptr()@.provenance
    }
}

pub open spec fn wf_reserved(block_size: int, reserved: int, count: int) -> bool {
    reserved * block_size + crate::layout::start_offset(block_size) <= count * SLICE_SIZE
}

impl PageLocalAccess {
    pub open spec fn wf(&self, page_id: PageId, page_state: PageState, mim_instance: Mim::Instance) -> bool {
        (page_state.offset == 0 ==> page_state.shared_access.wf(page_id, page_state.block_size, mim_instance))
        && (page_state.offset != 0 ==> page_state.shared_access.wf_secondary(page_id, page_state.block_size, mim_instance))
        && page_state.is_enabled

        && match page_state.shared_access.points_to.opt_value() {
            MemContents::Init(page) => {
                &&& self.inner.id() == page.inner.id()
                &&& self.count.id() == page.count.id()
                &&& self.prev.id() == page.prev.id()
                &&& self.next.id() == page.next.id()

                &&& match (self.count.value(), self.inner.value(), self.prev.value(), self.next.value()) {
                    (count, page_inner, prev, next) => {
                        //&&& is_page_ptr_opt(prev, page_state.prev)
                        //&&& is_page_ptr_opt(next, page_state.next)

                        &&& (page_state.offset == 0 ==>
                            page_inner.wf(page_id, page_state, mim_instance)
                            && wf_reserved(page_state.block_size as int,
                                page_inner.reserved as int, count as int)
                        )
                        &&& (page_state.offset != 0 ==> page_inner.zeroed_except_block_size())
                    }
                }
            }
            MemContents::Uninit => false,
        }
    }

    pub open spec fn wf_unused(&self, page_id: PageId, shared_access: PageSharedAccess, popped: Popped, mim_instance: Mim::Instance) -> bool {
        shared_access.wf_unused(page_id, mim_instance)

        && match shared_access.points_to.opt_value() {
            MemContents::Init(page) => {
                &&& self.count.id() == page.count.id()
                &&& self.inner.id() == page.inner.id()
                &&& self.prev.id() == page.prev.id()
                &&& self.next.id() == page.next.id()

                &&& self.inner.value().zeroed_except_block_size()
                // TODO move PageData comparison in here?
            }
            MemContents::Uninit => false,
        }
    }
}

impl PageFullAccess {
    pub open spec fn wf_empty_page_global(&self) -> bool {
        &&& self.s.points_to.is_init()
        &&& self.s.points_to.value().inner.id() == self.l.inner.id()
        &&& self.s.exposed.provenance() == self.s.points_to.ptr()@.provenance
        &&& self.l.inner.value().zeroed()
    }
}

/////////////////////////////////////////////
///////////////////////////////////////////// Segments
/////////////////////////////////////////////

#[derive(Clone, Copy)]
pub enum SegmentKind {
    Normal,
    Huge,
}

pub open spec fn segment_kind_is_huge(kind: SegmentKind) -> bool {
    matches!(kind, SegmentKind::Huge)
}

#[repr(C)]
pub struct SegmentHeaderMain {
    pub memid: usize,
    pub mem_is_pinned: bool,
    pub mem_is_large: bool,
    pub mem_is_committed: bool,
    pub mem_alignment: usize,
    pub mem_align_offset: usize,
    pub allow_decommit: bool,
    pub decommit_expire: i64,
    pub decommit_mask: CommitMask,
    pub commit_mask: CommitMask,
}

#[repr(C)]
pub struct SegmentHeaderMain2 {
    pub next: *mut SegmentHeader,
    pub abandoned: usize,
    pub abandoned_visits: usize,
    pub used: usize,
    pub cookie: usize,
    pub segment_slices: usize,
    pub segment_info_slices: usize,
    pub kind: SegmentKind,
    pub slice_entries: usize,
}

struct_with_invariants!{
    #[repr(C)]
    pub struct SegmentHeader {
        pub main: PCell<SegmentHeaderMain>,
        pub abandoned_next: usize, // TODO should be atomic
        pub main2: PCell<SegmentHeaderMain2>,

        // Note: thread_id is 0 if the segment is abandoned
        pub thread_id: AtomicU64<_, Mim::thread_of_segment, _>,

        pub instance: Ghost<Mim::Instance>,
        pub segment_id: Ghost<SegmentId>,
    }

    pub open spec fn wf(&self, instance: Mim::Instance, segment_id: SegmentId) -> bool {
        predicate {
            self.instance == instance
            && self.segment_id == segment_id
        }
        invariant
            on thread_id
            with (instance, segment_id)
            is (v: u64, g: Mim::thread_of_segment)
        {
            &&& g.instance_id() == instance@.id()
            &&& g.key() == segment_id
            &&& g.value() == ThreadId { thread_id: v }
        }
    }
}

pub tracked struct SegmentSharedAccess {
    pub points_to: raw_ptr::PointsTo<SegmentHeader>,
}

impl SegmentSharedAccess {
    pub open spec fn wf(&self, segment_id: SegmentId, mim_instance: Mim::Instance) -> bool {
        &&& is_segment_ptr(self.points_to.ptr(), segment_id)
        &&& (match self.points_to.opt_value() {
            MemContents::Init(segment_header) => segment_header.wf(mim_instance, segment_id),
            MemContents::Uninit => false,
        })
    }
}

pub tracked struct SegmentLocalAccess {
    pub mem: MemChunk,
    pub main: pcell::PointsTo<SegmentHeaderMain>,
    pub main2: pcell::PointsTo<SegmentHeaderMain2>,
}

impl SegmentLocalAccess {
    pub open spec fn wf(&self, segment_id: SegmentId, segment_state: SegmentState, mim_instance: Mim::Instance) -> bool {
        &&& segment_state.shared_access.wf(segment_id, mim_instance)
        &&& segment_state.shared_access.points_to.value().main.id() == self.main.id()

        &&& segment_state.shared_access.points_to.value().main2.id() == self.main2.id()

        &&& segment_state.is_enabled
    }
}

/////////////////////////////////////////////
///////////////////////////////////////////// Heaps
/////////////////////////////////////////////

pub struct PageQueue {
    pub first: *mut Page,
    pub last: *mut Page,
    pub block_size: usize,
}

impl Clone for PageQueue {
    fn clone(&self) -> (s: Self)
        ensures
            s.first == self.first,
            s.last == self.last,
            s.block_size == self.block_size,
    {
        PageQueue { first: self.first, last: self.last, block_size: self.block_size }
    }
}
impl Copy for PageQueue { }

#[repr(C)]
pub struct Heap {
    pub tld_ptr: TldPtr,

    pub pages_free_direct: PCell<[*mut Page; 129]>, // length PAGES_DIRECT
    pub pages: PCell<[PageQueue; 75]>, // length BIN_FULL + 1

    pub thread_delayed_free: ThreadLLSimple,
    pub thread_id: ThreadId,
    pub arena_id: ArenaId,
    //pub cookie: usize,
    //pub keys: usize,
    //pub random:
    pub page_count: PCell<usize>,
    pub page_retired_min: PCell<usize>,
    pub page_retired_max: PCell<usize>,
    //pub next: HeapPtr,
    pub no_reclaim: bool,

    // TODO should be a global, but right now we don't support pointers to globals
    pub page_empty_ptr: *mut Page,
}

pub struct HeapSharedAccess {
    pub points_to: raw_ptr::PointsTo<Heap>,
}

pub struct HeapLocalAccess {
    pub pages_free_direct: pcell::PointsTo<[*mut Page; 129]>,
    pub pages: pcell::PointsTo<[PageQueue; 75]>,
    pub page_count: pcell::PointsTo<usize>,
    pub page_retired_min: pcell::PointsTo<usize>,
    pub page_retired_max: pcell::PointsTo<usize>,
}

impl Heap {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        &&& self.thread_delayed_free.wf()
        &&& self.thread_delayed_free.instance@.id() == mim_instance
        &&& self.thread_delayed_free.heap_id == heap_id
        &&& self.tld_ptr.wf()
        &&& self.tld_ptr.tld_id == tld_id
    }
}

impl HeapSharedAccess {
    pub open spec fn wf(&self, heap_id: HeapId, tld_id: TldId, mim_instance: InstanceId) -> bool {
        is_heap_ptr(self.points_to.ptr(), heap_id)
          && self.points_to.is_init()
          && self.points_to.value().wf(heap_id, tld_id, mim_instance)
    }

    pub open spec fn wf2(&self, heap_id: HeapId, mim_instance: InstanceId) -> bool {
        self.wf(heap_id, self.points_to.value().tld_ptr.tld_id@,
            mim_instance)
    }
}

pub open spec fn pages_free_direct_match(pfd_val: *mut Page, p_val: *mut Page, emp: *mut Page) -> bool {
    (p_val as int == 0 ==> pfd_val as int == emp as int)
    && (p_val as int != 0 ==> pfd_val as int == p_val as int)
}

pub open spec fn pages_free_direct_is_correct(pfd: Seq<*mut Page>, pages: Seq<PageQueue>, emp: *mut Page) -> bool {
    &&& pfd.len() == PAGES_DIRECT
    &&& pages.len() == BIN_FULL + 1
    &&& (forall |wsize|
      0 <= wsize < pfd.len() ==>
        pages_free_direct_match(
            #[trigger] pfd[wsize],
            pages[smallest_bin_fitting_size(wsize * INTPTR_SIZE)].first,
            emp)
    )
}

impl HeapLocalAccess {
    pub open spec fn wf(&self, heap_id: HeapId, heap_state: HeapState, tld_id: TldId, mim_instance: InstanceId, emp: *mut Page) -> bool {

        self.wf_basic(heap_id, heap_state, tld_id, mim_instance)
          && pages_free_direct_is_correct(
                self.pages_free_direct.value()@,
                self.pages.value()@,
                emp)
          && heap_state.shared_access.points_to.value().page_empty_ptr == emp
    }

    pub open spec fn wf_basic(&self, heap_id: HeapId, heap_state: HeapState, tld_id: TldId, mim_instance: InstanceId) -> bool {
      heap_state.shared_access.wf(heap_id, tld_id, mim_instance)
        && {
            let heap = heap_state.shared_access.points_to.value();
              heap.pages_free_direct.id() == self.pages_free_direct.id()
              && heap.pages.id() == self.pages.id()
              && heap.page_count.id() == self.page_count.id()
              && heap.page_retired_min.id() == self.page_retired_min.id()
              && heap.page_retired_max.id() == self.page_retired_max.id()

              && (forall |i: int| #[trigger] valid_bin_idx(i) ==>
                  self.pages.value()[i].block_size == size_of_bin(i))
              // 0 isn't a valid_bin_idx
              && self.pages.value()[0].block_size == 8
              && self.pages.value()[BIN_FULL as int].block_size ==
                    8 * (524288 + 2) //MEDIUM_OBJ_WSIZE_MAX + 2

              && self.pages_free_direct.value()@.len() == PAGES_DIRECT
              && self.pages.value()@.len() == BIN_FULL + 1
        }
    }
}

/////////////////////////////////////////////
///////////////////////////////////////////// Thread local data
/////////////////////////////////////////////

//pub struct OsTld {
//    pub region_idx: usize,
//}

pub struct SegmentsTld {
    pub span_queue_headers: [SpanQueueHeader; 32], // len = SEGMENT_BIN_MAX + 1
    pub count: usize,
    pub peak_count: usize,
    pub current_size: usize,
    pub peak_size: usize,
}

pub struct SpanQueueHeader {
    pub first: *mut Page,
    pub last: *mut Page,
}

impl Clone for SpanQueueHeader {
    fn clone(&self) -> (s: Self)
        ensures
            s.first == self.first,
            s.last == self.last,
    {
        SpanQueueHeader { first: self.first, last: self.last }
    }
}
impl Copy for SpanQueueHeader { }

pub struct Tld {
    // TODO mimalloc allows multiple heaps per thread
    pub heap_backing: *mut Heap,

    pub segments: SegmentsTld,
}

pub tracked struct Local {
    pub ghost thread_id: ThreadId,

    pub tracked my_inst: Mim::my_inst,
    pub tracked instance: Mim::Instance,
    pub tracked thread_token: Mim::thread_local_state,
    pub tracked checked_token: Mim::thread_checked_state,
    pub tracked is_thread: crate::thread::IsThread,

    pub ghost heap_id: HeapId,
    pub tracked heap: HeapLocalAccess,

    pub ghost tld_id: TldId,
    pub tracked tld: raw_ptr::PointsTo<Tld>,

    pub tracked segments: Map<SegmentId, SegmentLocalAccess>,

    // All pages, used and unused
    pub tracked pages: Map<PageId, PageLocalAccess>,
    pub ghost psa: Map<PageId, PageSharedAccess>,

    // All unused pages
    // (used pages are in the token system)
    pub tracked unused_pages: Map<PageId, PageSharedAccess>,

    pub ghost page_organization: PageOrg::State,

    pub tracked page_empty_global: Shared<PageFullAccess>,
}

pub open spec fn common_preserves(l1: Local, l2: Local) -> bool {
    l1.heap_id == l2.heap_id
    && l1.tld_id == l2.tld_id
    && l1.instance == l2.instance
}

impl Local {
    pub open(crate) spec fn inst(&self) -> Mim::Instance {
        self.instance
    }

    pub open(crate) spec fn wf(&self) -> bool {
        self.wf_main()
          && self.page_organization.popped == Popped::No
    }

    pub open spec fn wf_basic(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id

        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf_basic(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id())

        &&& self.thread_token.value().heap.shared_access.points_to.value().page_empty_ptr == self.page_empty_global@.s.points_to.ptr()
        &&& self.page_empty_global@.wf_empty_page_global()
    }

    pub open spec fn wf_main_for_page_access(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id
        &&& self.thread_id == self.is_thread@

        &&& self.checked_token.instance_id() == self.instance.id()
        &&& self.checked_token.key() == self.thread_id

        &&& self.my_inst.instance_id() == self.instance.id()
        &&& self.my_inst.value() == self.instance.id()

        //&&& (forall |page_id|
        //    self.thread_token.value().pages.dom().contains(page_id) <==>
        //    self.pages.dom().contains(page_id))
        //&&& self.thread_token.value().pages.dom() == self.pages.dom()
        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id(), self.page_empty_global@.s.points_to.ptr())

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
            // Page is either 'used' or 'unused'
              (self.unused_pages.dom().contains(page_id) <==>
                !self.thread_token.value().pages.dom().contains(page_id)))

        &&& self.thread_token.value().pages.dom().subset_of(self.pages.dom())
        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.thread_token.value().pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf(
                  page_id,
                  self.thread_token.value().pages.index(page_id),
                  self.instance,
                )
            )

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.unused_pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf_unused(page_id, self.unused_pages[page_id], self.page_organization.popped, self.instance))

        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.segments[segment_id].wf(
                segment_id,
                self.thread_token.value().segments.index(segment_id),
                self.instance,
              )
            )

        &&& self.tld.is_init()

        &&& self.page_organization_valid()

        &&& self.page_empty_global@.wf_empty_page_global()
        }

    pub open spec fn wf_main(&self) -> bool {
        &&& is_tld_ptr(self.tld.ptr(), self.tld_id)

        &&& self.thread_token.instance_id() == self.instance.id()
        &&& self.thread_token.key() == self.thread_id
        &&& self.thread_id == self.is_thread@

        &&& self.checked_token.instance_id() == self.instance.id()
        &&& self.checked_token.key() == self.thread_id

        &&& self.my_inst.instance_id() == self.instance.id()
        &&& self.my_inst.value() == self.instance.id()

        //&&& (forall |page_id|
        //    self.thread_token.value().pages.dom().contains(page_id) <==>
        //    self.pages.dom().contains(page_id))
        //&&& self.thread_token.value().pages.dom() == self.pages.dom()
        &&& self.thread_token.value().segments.dom() == self.segments.dom()

        &&& self.thread_token.value().heap_id == self.heap_id
        &&& self.heap.wf(self.heap_id, self.thread_token.value().heap, self.tld_id, self.instance.id(), self.page_empty_global@.s.points_to.ptr())

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
            // Page is either 'used' or 'unused'
              (self.unused_pages.dom().contains(page_id) <==>
                !self.thread_token.value().pages.dom().contains(page_id)))

        &&& self.thread_token.value().pages.dom().subset_of(self.pages.dom())
        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.thread_token.value().pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf(
                  page_id,
                  self.thread_token.value().pages.index(page_id),
                  self.instance,
                )
            )

        &&& (forall |page_id|
            #[trigger] self.pages.dom().contains(page_id) ==>
              self.unused_pages.dom().contains(page_id) ==>
                self.pages.index(page_id).wf_unused(page_id, self.unused_pages[page_id], self.page_organization.popped, self.instance))

        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.segments[segment_id].wf(
                segment_id,
                self.thread_token.value().segments.index(segment_id),
                self.instance,
              )
            )
        &&& (forall |segment_id|
            #[trigger] self.segments.dom().contains(segment_id) ==>
              self.mem_chunk_good(segment_id)
            )

        &&& self.tld.is_init()

        &&& self.page_organization_valid()

        &&& self.page_empty_global@.wf_empty_page_global()
    }

    pub proof fn wf_main_implies_page_access(&self)
        requires self.wf_main(),
        ensures self.wf_main_for_page_access(),
    {
    }

    pub open spec fn page_organization_valid(&self) -> bool
    {
        &&& self.page_organization.invariant()
        &&& self.tld.is_init()

        &&& page_organization_queues_match(self.page_organization.unused_dlist_headers,
                self.tld.value().segments.span_queue_headers@)

        &&& page_organization_used_queues_match(self.page_organization.used_dlist_headers,
                self.heap.pages.value()@)

        &&& page_organization_pages_match(self.page_organization.pages,
                self.pages, self.psa, self.page_organization.popped)

        &&& page_organization_segments_match(self.page_organization.segments, self.segments)

        &&& (forall |page_id: PageId| #[trigger] self.page_organization.pages.dom().contains(page_id) ==>
            (!self.page_organization.pages[page_id].is_used <==> self.unused_pages.dom().contains(page_id)))

        //&&& (forall |page_id: PageId|
        //  #[trigger] self.page_organization.pages.dom().contains(page_id)
        //    ==> self.page_organization.pages[page_id].is_used
        //    ==> self.page_organization.pages[page_id].offset == Some(0nat)
        //    ==> self.thread_token.value().pages[page_id].offset == 0)

        &&& (forall |page_id|
          #[trigger] self.page_organization.pages.dom().contains(page_id)
            ==> self.page_organization.pages[page_id].is_used
            ==> page_organization_matches_token_page(
                    self.page_organization.pages[page_id],
                    self.thread_token.value().pages[page_id]))

        &&& (forall |page_id: PageId| (#[trigger] self.unused_pages.dom().contains(page_id)) ==>
            self.page_organization.pages.dom().contains(page_id))

        &&& (forall |page_id: PageId| #[trigger] self.unused_pages.dom().contains(page_id) ==>
            self.unused_pages[page_id] == self.psa[page_id])

        &&& (forall |page_id: PageId| #[trigger] self.thread_token.value().pages.dom().contains(page_id) ==>
            self.thread_token.value().pages[page_id].shared_access == self.psa[page_id])
    }

    pub open spec fn page_state(&self, page_id: PageId) -> PageState
        recommends self.thread_token.value().pages.dom().contains(page_id)
    {
        self.thread_token.value().pages.index(page_id)
    }

    pub open spec fn page_inner(&self, page_id: PageId) -> PageInner
        recommends
            self.pages.dom().contains(page_id),
    {
        *self.pages.index(page_id).inner.value()
    }


    // This is for when we need to obtain ownership of the ThreadToken
    // but when we have a &mut reference to the Local

    #[verifier::external_body]
    pub proof fn take_thread_token(tracked &mut self) -> (tracked tt: Mim::thread_local_state)
        ensures
            *final(self) == *old(self),
            tt == old(self).thread_token,
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn take_checked_token(tracked &mut self) -> (tracked tt: Mim::thread_checked_state)
        ensures
            *final(self) == *old(self),
            tt == old(self).checked_token,
    {
        unimplemented!();
    }

    pub open spec fn commit_mask(&self, segment_id: SegmentId) -> CommitMask {
        self.segments[segment_id].main.value().commit_mask
    }

    pub open spec fn decommit_mask(&self, segment_id: SegmentId) -> CommitMask {
        self.segments[segment_id].main.value().decommit_mask
    }

    pub open spec fn is_used_primary(&self, page_id: PageId) -> bool {
        self.page_organization.pages.dom().contains(page_id)
          && self.page_organization.pages[page_id].is_used
          && self.page_organization.pages[page_id].offset == Some(0nat)
    }

    pub open spec fn page_reserved(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().reserved as int
    }

    pub open spec fn page_count(&self, page_id: PageId) -> int {
        self.pages[page_id].count.value() as int
    }

    pub open spec fn page_capacity(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().capacity as int
    }

    pub open spec fn block_size(&self, page_id: PageId) -> int {
        self.pages[page_id].inner.value().xblock_size as int
    }
}

pub open spec fn page_organization_queues_match(
    org_queues: Seq<DlistHeader>,
    queues: Seq<SpanQueueHeader>,
) -> bool {
    org_queues.len() == queues.len()
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).first, org_queues[i].first))
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).last, org_queues[i].last))
}

pub open spec fn page_organization_used_queues_match(
    org_queues: Seq<DlistHeader>,
    queues: Seq<PageQueue>,
) -> bool {
    org_queues.len() == queues.len()
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).first, org_queues[i].first))
    && (forall |i: int| 0 <= i < org_queues.len() ==>
        is_page_ptr_opt((#[trigger] queues[i]).last, org_queues[i].last))
}


pub open spec fn page_organization_pages_match(
    org_pages: Map<PageId, PageData>,
    pages: Map<PageId, PageLocalAccess>,
    psa: Map<PageId, PageSharedAccess>,
    popped: Popped,
) -> bool {
    &&& org_pages.dom() =~= pages.dom()
    &&& org_pages.dom() =~= psa.dom()

    //&&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id)
    //    && !org_pages[page_id].is_used ==> unused_pages.dom().contains(page_id))
    //
    //&&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id)
    //    && !org_pages[page_id].is_used ==> unused_pages[page_id].wf_unused(page_id))

    &&& (forall |page_id| #[trigger] org_pages.dom().contains(page_id) ==>
        page_organization_pages_match_data(org_pages[page_id], pages[page_id], psa[page_id], page_id, popped))
}

pub open spec fn page_organization_pages_match_data(
    page_data: PageData,
    pla: PageLocalAccess,
    psa: PageSharedAccess,
    page_id: PageId,
    popped: Popped) -> bool
{
    psa.points_to.is_init() && (
    match (*pla.count.value(), *pla.inner.value(), *pla.prev.value(), *pla.next.value()) {
        (count, inner, prev, next) => {
            &&& (match page_data.count {
                None => true,
                Some(c) => count as int == c
            })
            &&& (match page_data.full {
                None => true,
                Some(b) => inner.in_full() == b,
            })
            &&& (match page_data.offset {
                None => true,
                Some(o) => psa.points_to.value().offset as int ==
                            o * SIZEOF_PAGE_HEADER
            })
            &&& (match page_data.dlist_entry {
                None => true,
                Some(page_queue_data) => {
                    &&& is_page_ptr_opt(prev, page_queue_data.prev)
                    &&& is_page_ptr_opt(next, page_queue_data.next)
                }
            })
            &&& (match page_data.page_header_kind {
                None => {
                    (page_id.idx == 0 ==> {
                      &&& !page_data.is_used
                      &&& (match popped {
                          Popped::SegmentCreating(sid) if sid == page_id.segment_id =>
                              true,
                          _ => inner.xblock_size != 0
                      })
                      &&& (!popped.is_SegmentCreating() ==> inner.xblock_size != 0)
                    })
                    && (page_id.idx != 0 ==> page_data.offset == Some(0nat) ==> (
                        (!(popped.is_Ready() && popped.get_Ready_0() == page_id) &&
                            !(popped.is_VeryUnready() && popped.get_VeryUnready_0() == page_id.segment_id && popped.get_VeryUnready_1() == page_id.idx))
                          ==>
                        (page_data.is_used <==> inner.xblock_size != 0)
                    ))
                }
                Some(PageHeaderKind::Normal(_, bsize)) => {
                    &&& page_id.idx != 0
                    &&& page_data.is_used
                    &&& inner.xblock_size != 0
                    &&& inner.xblock_size == bsize
                    &&& page_data.is_used
                    &&& page_data.offset == Some(0nat)
                }
            })
        }
    })
}

pub open spec fn page_organization_segments_match(
    org_segments: Map<SegmentId, SegmentData>,
    segments: Map<SegmentId, SegmentLocalAccess>,
) -> bool {
    org_segments.dom() =~= segments.dom()
    && (forall |segment_id: SegmentId| segments.dom().contains(segment_id) ==>
        org_segments[segment_id].used == segments[segment_id].main2.value().used)
}

pub open spec fn page_organization_matches_token_page(
    page_data: PageData,
    page_state: PageState) -> bool
{
    page_data.offset.is_some()
    && page_data.offset.unwrap() == page_state.offset
    /*&& (match page_data.page_header_kind {
        Some(PageHeaderKind::Normal(bsize)) => bsize == page_state.block_size,
        _ => true,
    })*/
}


proof fn lemma_heap_ptr_unique(p1: *mut Heap, p2: *mut Heap, heap_id: HeapId)
    requires
        is_heap_ptr(p1, heap_id),
        is_heap_ptr(p2, heap_id),
    ensures
        p1 == p2,
{
    assert(p1@.addr == p2@.addr);
    assert(p1@.provenance == p2@.provenance);
}

proof fn lemma_tld_ptr_unique(p1: *mut Tld, p2: *mut Tld, tld_id: TldId)
    requires
        is_tld_ptr(p1, tld_id),
        is_tld_ptr(p2, tld_id),
    ensures
        p1 == p2,
{
    assert(p1@.addr == p2@.addr);
    assert(p1@.provenance == p2@.provenance);
}

proof fn lemma_segment_ptr_unique(p1: *mut SegmentHeader, p2: *mut SegmentHeader, segment_id: SegmentId)
    requires
        is_segment_ptr(p1, segment_id),
        is_segment_ptr(p2, segment_id),
    ensures
        p1 == p2,
{
    assert(p1.addr() as int == p1 as int);
    assert(p2.addr() as int == p2 as int);
    assert(p1@.addr == p2@.addr);
    assert(p1@.provenance == p2@.provenance);
}

proof fn lemma_page_ptr_unique(p1: *mut Page, p2: *mut Page, page_id: PageId)
    requires
        is_page_ptr(p1, page_id),
        is_page_ptr(p2, page_id),
    ensures
        p1 == p2,
{
    assert(p1.addr() as int == p1 as int);
    assert(p2.addr() as int == p2 as int);
    assert(p1@.addr == p2@.addr);
    assert(p1@.provenance == p2@.provenance);
}



/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
/////////////////////////////////////////////
////// Utilities for local access

pub struct HeapPtr {
    pub heap_ptr: *mut Heap,
    pub heap_id: Ghost<HeapId>,
}

impl Clone for HeapPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures
            s.heap_ptr == self.heap_ptr,
            s.heap_id@ == self.heap_id@,
    {
        HeapPtr { heap_ptr: self.heap_ptr, heap_id: Ghost(self.heap_id@) }
    }
}
impl Copy for HeapPtr { }

impl HeapPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_heap_ptr(self.heap_ptr, self.heap_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.heap_id == self.heap_id@
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (heap: &'a Heap)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            heap == local.thread_token.value().heap.shared_access.points_to.value(),
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        proof {
            assert(local.thread_token.value().heap_id == self.heap_id@);
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.wf(self.heap_id@, local.tld_id, local.instance.id()));
            lemma_heap_ptr_unique(self.heap_ptr, perm.ptr(), self.heap_id@);
            assert(perm.is_init());
        }
        ptr_ref(self.heap_ptr, Tracked(perm))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_pages<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (pages: &'a [PageQueue; 75])
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            pages == local.heap.pages.value(),
            pages@ == local.heap.pages.value()@,
    {
        proof {
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.points_to.value().pages.id() == local.heap.pages.id());
        }
        self.get_ref(Tracked(local)).pages.borrow(Tracked(&local.heap.pages))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_page_count<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_count: usize)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            page_count == *local.heap.page_count.value(),
    {
        proof {
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.points_to.value().page_count.id() == local.heap.page_count.id());
        }
        *self.get_ref(Tracked(local)).page_count.borrow(Tracked(&local.heap.page_count))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn set_page_count<'a>(&self, Tracked(local): Tracked<&mut Local>, page_count: usize)
        requires
            self.wf(),
            self.is_in(*old(local)),
            old(local).wf_basic(),
        ensures
            local_page_count_update(*old(local), *final(local)),
            *final(local).heap.page_count.value() == page_count,
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        proof {
            assert(local.thread_token.value().heap_id == self.heap_id@);
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.wf(self.heap_id@, local.tld_id, local.instance.id()));
            lemma_heap_ptr_unique(self.heap_ptr, perm.ptr(), self.heap_id@);
            assert(perm.is_init());
        }
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        proof {
            assert(heap == local.thread_token.value().heap.shared_access.points_to.value());
            assert(heap.page_count.id() == local.heap.page_count.id());
        }
        *heap.page_count.borrow_mut(Tracked(&mut local.heap.page_count)) = page_count;
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_page_retired_min<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_retired_min: usize)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            page_retired_min == *local.heap.page_retired_min.value(),
    {
        proof {
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.points_to.value().page_retired_min.id() == local.heap.page_retired_min.id());
        }
        *self.get_ref(Tracked(local)).page_retired_min.borrow(Tracked(&local.heap.page_retired_min))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn set_page_retired_min<'a>(&self, Tracked(local): Tracked<&mut Local>, page_retired_min: usize)
        requires
            self.wf(),
            self.is_in(*old(local)),
            old(local).wf_basic(),
        ensures
            local_page_retired_min_update(*old(local), *final(local)),
            *final(local).heap.page_retired_min.value() == page_retired_min,
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        proof {
            assert(local.thread_token.value().heap_id == self.heap_id@);
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.wf(self.heap_id@, local.tld_id, local.instance.id()));
            lemma_heap_ptr_unique(self.heap_ptr, perm.ptr(), self.heap_id@);
            assert(perm.is_init());
        }
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        proof {
            assert(heap == local.thread_token.value().heap.shared_access.points_to.value());
            assert(heap.page_retired_min.id() == local.heap.page_retired_min.id());
        }
        *heap.page_retired_min.borrow_mut(Tracked(&mut local.heap.page_retired_min)) = page_retired_min;
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_page_retired_max<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_retired_max: usize)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            page_retired_max == *local.heap.page_retired_max.value(),
    {
        proof {
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.points_to.value().page_retired_max.id() == local.heap.page_retired_max.id());
        }
        *self.get_ref(Tracked(local)).page_retired_max.borrow(Tracked(&local.heap.page_retired_max))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn set_page_retired_max<'a>(&self, Tracked(local): Tracked<&mut Local>, page_retired_max: usize)
        requires
            self.wf(),
            self.is_in(*old(local)),
            old(local).wf_basic(),
        ensures
            local_page_retired_max_update(*old(local), *final(local)),
            *final(local).heap.page_retired_max.value() == page_retired_max,
    {
        let tracked perm = &local.instance.thread_local_state_guards_heap(
            local.thread_id, &local.thread_token).points_to;
        proof {
            assert(local.thread_token.value().heap_id == self.heap_id@);
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.wf(self.heap_id@, local.tld_id, local.instance.id()));
            lemma_heap_ptr_unique(self.heap_ptr, perm.ptr(), self.heap_id@);
            assert(perm.is_init());
        }
        let heap = ptr_ref(self.heap_ptr, Tracked(perm));
        proof {
            assert(heap == local.thread_token.value().heap.shared_access.points_to.value());
            assert(heap.page_retired_max.id() == local.heap.page_retired_max.id());
        }
        *heap.page_retired_max.borrow_mut(Tracked(&mut local.heap.page_retired_max)) = page_retired_max;
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_pages_free_direct<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (pages: &'a [*mut Page; 129])
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            pages == local.heap.pages_free_direct.value(),
            pages@ == local.heap.pages_free_direct.value()@,
    {
        proof {
            assert(local.heap.wf_basic(self.heap_id@, local.thread_token.value().heap, local.tld_id, local.instance.id()));
            assert(local.thread_token.value().heap.shared_access.points_to.value().pages_free_direct.id() == local.heap.pages_free_direct.id());
        }
        self.get_ref(Tracked(local)).pages_free_direct.borrow(Tracked(&local.heap.pages_free_direct))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_arena_id<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (arena_id: ArenaId)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            arena_id == local.thread_token.value().heap.shared_access.points_to.value().arena_id,
    {
        self.get_ref(Tracked(local)).arena_id
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_page_empty(&self, Tracked(local): Tracked<&Local>)
        -> (res: (*mut Page, Tracked<Shared<PageFullAccess>>))
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_basic(),
        ensures
            res.0 == local.thread_token.value().heap.shared_access.points_to.value().page_empty_ptr,
            res.0 == local.page_empty_global@.s.points_to.ptr(),
            res.1@@ == local.page_empty_global@,
    {
        let page_ptr = self.get_ref(Tracked(local)).page_empty_ptr;
        let tracked pfa = local.page_empty_global.clone();
        (page_ptr, Tracked(pfa))
    }
}

pub open spec fn local_page_count_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_count: loc2.heap.page_count, .. loc1.heap }
    &&& loc1.heap.page_count.id() == loc2.heap.page_count.id()
}

pub open spec fn local_page_retired_min_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_retired_min: loc2.heap.page_retired_min, .. loc1.heap }
    &&& loc1.heap.page_retired_min.id() == loc2.heap.page_retired_min.id()
}

pub open spec fn local_page_retired_max_update(loc1: Local, loc2: Local) -> bool {
    &&& loc2 == Local { heap: loc2.heap, .. loc1 }
    &&& loc2.heap == HeapLocalAccess { page_retired_max: loc2.heap.page_retired_max, .. loc1.heap }
    &&& loc1.heap.page_retired_max.id() == loc2.heap.page_retired_max.id()
}



pub struct TldPtr {
    pub tld_ptr: *mut Tld,
    pub tld_id: Ghost<TldId>,
}

impl Clone for TldPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures
            s.tld_ptr == self.tld_ptr,
            s.tld_id@ == self.tld_id@,
    {
        TldPtr { tld_ptr: self.tld_ptr, tld_id: Ghost(self.tld_id@) }
    }
}
impl Copy for TldPtr { }


impl TldPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_tld_ptr(self.tld_ptr, self.tld_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.tld_id == self.tld_id@
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (tld: &'a Tld)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main(),
        ensures
            tld == local.tld.value(),
    {
        proof {
            lemma_tld_ptr_unique(self.tld_ptr, local.tld.ptr(), self.tld_id@);
            assert(local.tld.is_init());
        }
        ptr_ref(self.tld_ptr, Tracked(&local.tld))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_mut<'a>(&self, Tracked(local): Tracked<&'a mut Local>) -> (tld: &'a mut Tld)
        requires
            self.wf(),
            self.is_in(*old(local)),
            is_tld_ptr(old(local).tld.ptr(), old(local).tld_id),
            old(local).tld.is_init(),
        ensures
            *tld == old(local).tld.value(),
            final(local).page_organization == old(local).page_organization,
            final(local).pages == old(local).pages,
            final(local).unused_pages == old(local).unused_pages,
            final(local).psa == old(local).psa,
            final(local).segments == old(local).segments,
            final(local).heap == old(local).heap,
            final(local).thread_token == old(local).thread_token,
            final(local).checked_token == old(local).checked_token,
            final(local).my_inst == old(local).my_inst,
            final(local).is_thread == old(local).is_thread,
            final(local).thread_id == old(local).thread_id,
            final(local).heap_id == old(local).heap_id,
            final(local).instance == old(local).instance,
            final(local).page_empty_global == old(local).page_empty_global,
            final(local).tld_id == old(local).tld_id,
            final(local).tld.ptr() == self.tld_ptr,
            final(local).tld.is_init(),
            final(local).tld.value() == *final(tld),
    {
        proof {
            lemma_tld_ptr_unique(self.tld_ptr, local.tld.ptr(), self.tld_id@);
            assert(local.tld.is_init());
        }
        ptr_mut_ref(self.tld_ptr, Tracked(&mut local.tld))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_segments_count(&self, Tracked(local): Tracked<&Local>) -> (count: usize)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main(),
        ensures
            count == local.tld.value().segments.count,
    {
        self.get_ref(Tracked(local)).segments.count
    }
}

pub struct SegmentPtr {
    pub segment_ptr: *mut SegmentHeader,
    pub segment_id: Ghost<SegmentId>,
}

impl Clone for SegmentPtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures
            s.segment_ptr == self.segment_ptr,
            s.segment_id@ == self.segment_id@,
    {
        SegmentPtr { segment_ptr: self.segment_ptr, segment_id: Ghost(self.segment_id@) }
    }
}
impl Copy for SegmentPtr { }

impl SegmentPtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_segment_ptr(self.segment_ptr, self.segment_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.segments.dom().contains(self.segment_id@)
    }

    #[inline(always)]
    #[verus_verify]
    pub fn is_null(&self) -> (b: bool)
        ensures b == (self.segment_ptr.addr() == 0),
    {
        self.segment_ptr.addr() == 0
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn null() -> (s: Self)
        ensures
            s.segment_ptr.addr() == 0,
    {
        SegmentPtr { segment_ptr: core::ptr::null_mut(),
            segment_id: Ghost(arbitrary())
        }
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_page_header_ptr(&self, idx: usize) -> (page_ptr: PagePtr)
        requires
            self.wf(),
            idx <= SLICES_PER_SEGMENT as usize,
        ensures
            page_ptr.page_id@ == (PageId { segment_id: self.segment_id@, idx: idx as nat }),
            page_ptr.page_ptr as int == crate::layout::page_header_start(
                PageId { segment_id: self.segment_id@, idx: idx as nat }),
            page_ptr.wf(),
    {
        proof {
            let segment_id = self.segment_id@;
            assert(self.segment_ptr as int == crate::layout::segment_start(segment_id));
            assert(self.segment_ptr.addr() as int == self.segment_ptr as int);
            assert((SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int) by(compute_only);
            assert(idx as int <= SLICES_PER_SEGMENT as int) by(nonlinear_arith)
                requires
                    idx <= SLICES_PER_SEGMENT as usize,
                    (SLICES_PER_SEGMENT as usize) as int == SLICES_PER_SEGMENT as int;
            assert(0 <= SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= SEGMENT_SIZE as int) by(compute_only);
            assert((idx as int) * (SIZEOF_PAGE_HEADER as int)
                <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    idx as int <= SLICES_PER_SEGMENT as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert(SIZEOF_SEGMENT_HEADER as int
                + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    (idx as int) * (SIZEOF_PAGE_HEADER as int)
                        <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int),
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int;
            assert(self.segment_ptr.addr() as int
                + SIZEOF_SEGMENT_HEADER as int
                + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                <= crate::layout::segment_start(segment_id) + SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    self.segment_ptr.addr() as int == crate::layout::segment_start(segment_id),
                    SIZEOF_SEGMENT_HEADER as int
                        + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int;
            assert(self.segment_ptr.addr() as int
                + SIZEOF_SEGMENT_HEADER as int
                + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                <= usize::MAX as int) by(nonlinear_arith)
                requires
                    self.segment_ptr.addr() as int
                        + SIZEOF_SEGMENT_HEADER as int
                        + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                        <= crate::layout::segment_start(segment_id) + SEGMENT_SIZE as int,
                    crate::layout::segment_start(segment_id) + SEGMENT_SIZE < usize::MAX;
            assert((idx as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    0 <= self.segment_ptr.addr() as int,
                    0 <= SIZEOF_SEGMENT_HEADER as int,
                    0 <= (idx as int) * (SIZEOF_PAGE_HEADER as int),
                    self.segment_ptr.addr() as int
                        + SIZEOF_SEGMENT_HEADER as int
                        + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                        <= usize::MAX as int;
            assert(self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int <= usize::MAX as int) by(nonlinear_arith)
                requires
                    0 <= (idx as int) * (SIZEOF_PAGE_HEADER as int),
                    self.segment_ptr.addr() as int
                        + SIZEOF_SEGMENT_HEADER as int
                        + (idx as int) * (SIZEOF_PAGE_HEADER as int)
                        <= usize::MAX as int;
        }
        let j = self.segment_ptr.addr() + SIZEOF_SEGMENT_HEADER + idx * SIZEOF_PAGE_HEADER;
        proof {
            let segment_id = self.segment_id@;
            let page_id = PageId { segment_id, idx: idx as nat };
            let prod = mul(idx, SIZEOF_PAGE_HEADER);
            let partial = add(self.segment_ptr.addr(), SIZEOF_SEGMENT_HEADER);
            assert(j == add(partial, prod));
            assert(prod == mul(idx, SIZEOF_PAGE_HEADER));
            assert(partial == add(self.segment_ptr.addr(), SIZEOF_SEGMENT_HEADER));
            assert(prod as int == (idx as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    prod == mul(idx, SIZEOF_PAGE_HEADER),
                    (idx as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int;
            assert(partial as int == self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int) by(nonlinear_arith)
                requires
                    partial == add(self.segment_ptr.addr(), SIZEOF_SEGMENT_HEADER),
                    self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int <= usize::MAX as int;
            assert(j as int == partial as int + prod as int) by(nonlinear_arith)
                requires
                    j == add(partial, prod),
                    partial as int + prod as int <= usize::MAX as int;
            assert(j as int == self.segment_ptr.addr() as int
                + SIZEOF_SEGMENT_HEADER as int
                + (idx as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    j as int == partial as int + prod as int,
                    partial as int == self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int,
                    prod as int == (idx as int) * (SIZEOF_PAGE_HEADER as int);
            assert(self.segment_ptr.addr() as int == crate::layout::segment_start(segment_id));
            assert(j as int == crate::layout::page_header_start(page_id));
            assert((self.segment_ptr.with_addr(j) as *mut Page) as int == crate::layout::page_header_start(page_id));
            assert((self.segment_ptr.with_addr(j) as *mut Page)@.provenance == segment_id.provenance);
            assert(crate::layout::is_page_ptr(self.segment_ptr.with_addr(j) as *mut Page, page_id));
        }
        return PagePtr {
            page_ptr: self.segment_ptr.with_addr(j) as *mut Page,
            page_id: Ghost(PageId { segment_id: self.segment_id@, idx: idx as nat }),
        };
    }

    #[inline]
    #[verus_verify]
    pub fn get_page_after_end(&self) -> (page_ptr: *mut Page)
        requires
            self.wf(),
        ensures
            page_ptr as int == page_header_start(PageId {
                segment_id: self.segment_id@,
                idx: SLICES_PER_SEGMENT as nat,
            }),
            page_ptr@.provenance == self.segment_id@.provenance,
    {
        proof {
            let segment_id = self.segment_id@;
            assert(self.segment_ptr as int == crate::layout::segment_start(segment_id));
            assert(self.segment_ptr.addr() as int == self.segment_ptr as int);
            assert(SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= SEGMENT_SIZE as int) by(compute_only);
            assert(self.segment_ptr.addr() as int
                + SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= crate::layout::segment_start(segment_id) + SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    self.segment_ptr.addr() as int == crate::layout::segment_start(segment_id),
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int;
            assert(self.segment_ptr.addr() as int
                + SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= usize::MAX as int) by(nonlinear_arith)
                requires
                    self.segment_ptr.addr() as int
                        + SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= crate::layout::segment_start(segment_id) + SEGMENT_SIZE as int,
                    crate::layout::segment_start(segment_id) + SEGMENT_SIZE < usize::MAX;
        }
        let j = self.segment_ptr.addr()
          + SIZEOF_SEGMENT_HEADER
          + SLICES_PER_SEGMENT as usize * SIZEOF_PAGE_HEADER;
        proof {
            let segment_id = self.segment_id@;
            let page_id = PageId { segment_id, idx: SLICES_PER_SEGMENT as nat };
            let prod = mul(SLICES_PER_SEGMENT as usize, SIZEOF_PAGE_HEADER);
            let partial = add(self.segment_ptr.addr(), SIZEOF_SEGMENT_HEADER);
            assert(j == add(partial, prod));
            assert(prod == mul(SLICES_PER_SEGMENT as usize, SIZEOF_PAGE_HEADER));
            assert(mul(SLICES_PER_SEGMENT as usize, SIZEOF_PAGE_HEADER) == 40960usize) by(compute_only);
            assert(prod == 40960usize);
            assert(prod as int == 40960) by(nonlinear_arith)
                requires prod == 40960usize;
            assert((SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int) == 40960) by(compute_only);
            assert(prod as int == (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int));
            assert(partial as int == self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int) by(nonlinear_arith)
                requires
                    partial == add(self.segment_ptr.addr(), SIZEOF_SEGMENT_HEADER),
                    self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int <= usize::MAX as int;
            assert(j as int == partial as int + prod as int) by(nonlinear_arith)
                requires
                    j == add(partial, prod),
                    partial as int + prod as int <= usize::MAX as int;
            assert(j as int == self.segment_ptr.addr() as int
                + SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    j as int == partial as int + prod as int,
                    partial as int == self.segment_ptr.addr() as int + SIZEOF_SEGMENT_HEADER as int,
                    prod as int == (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int);
            assert(self.segment_ptr.addr() as int == crate::layout::segment_start(segment_id));
            assert(j as int == crate::layout::page_header_start(page_id));
            assert((self.segment_ptr.with_addr(j) as *mut Page) as int == crate::layout::page_header_start(page_id));
        }
        self.segment_ptr.with_addr(j) as *mut Page
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment: &'a SegmentHeader)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            segment == local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value(),
    {
        let tracked perm =
            &local.instance.thread_local_state_guards_segment(
                local.thread_id, self.segment_id@, &local.thread_token).points_to;
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.thread_token.value().segments.dom() == local.segments.dom());
            assert(local.thread_token.value().segments.dom().contains(self.segment_id@));
            assert(local.segments[self.segment_id@].wf(
                self.segment_id@,
                local.thread_token.value().segments.index(self.segment_id@),
                local.instance,
            ));
            assert(local.thread_token.value().segments[self.segment_id@].is_enabled);
            assert(local.thread_token.value().segments.index(self.segment_id@).shared_access.wf(self.segment_id@, local.instance));
            lemma_segment_ptr_unique(self.segment_ptr, perm.ptr(), self.segment_id@);
            assert(perm.is_init());
        }
        ptr_ref(self.segment_ptr, Tracked(perm))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_main_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment_header_main: &'a SegmentHeaderMain)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            segment_header_main == local.segments[self.segment_id@].main.value(),
    {
        let segment = self.get_ref(Tracked(local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.thread_token.value().segments.dom() == local.segments.dom());
            assert(local.segments.dom().contains(self.segment_id@));
            assert(local.segments[self.segment_id@].wf(
                self.segment_id@,
                local.thread_token.value().segments.index(self.segment_id@),
                local.instance,
            ));
            assert(segment == local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value());
            assert(segment.main.id() == local.segments[self.segment_id@].main.id());
        }
        segment.main.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_main2_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (segment_header_main2: &'a SegmentHeaderMain2)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            segment_header_main2 == local.segments[self.segment_id@].main2.value(),
    {
        let segment = self.get_ref(Tracked(local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.thread_token.value().segments.dom() == local.segments.dom());
            assert(local.segments.dom().contains(self.segment_id@));
            assert(local.segments[self.segment_id@].wf(
                self.segment_id@,
                local.thread_token.value().segments.index(self.segment_id@),
                local.instance,
            ));
            assert(segment == local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value());
            assert(segment.main2.id() == local.segments[self.segment_id@].main2.id());
        }
        segment.main2.borrow(Tracked(&local.segments.tracked_borrow(self.segment_id@).main2))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_commit_mask<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (cm: &'a CommitMask)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            *cm == local.commit_mask(self.segment_id@),
    {
        &self.get_main_ref(Tracked(local)).commit_mask
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_decommit_mask<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (cm: &'a CommitMask)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            *cm == local.decommit_mask(self.segment_id@),
    {
        &self.get_main_ref(Tracked(local)).decommit_mask
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_decommit_expire(&self, Tracked(local): Tracked<&Local>) -> (i: i64)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            i == local.segments[self.segment_id@].main.value().decommit_expire,
    {
        self.get_main_ref(Tracked(local)).decommit_expire
    }


    #[inline(always)]
    #[verus_verify]
    pub fn get_allow_decommit(&self, Tracked(local): Tracked<&Local>) -> (b: bool)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            b == local.segments[self.segment_id@].main.value().allow_decommit,
    {
        self.get_main_ref(Tracked(local)).allow_decommit
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_used(&self, Tracked(local): Tracked<&Local>) -> (used: usize)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            used == local.segments[self.segment_id@].main2.value().used,
    {
        self.get_main2_ref(Tracked(local)).used
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_abandoned(&self, Tracked(local): Tracked<&Local>) -> (abandoned: usize)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            abandoned == local.segments[self.segment_id@].main2.value().abandoned,
    {
        self.get_main2_ref(Tracked(local)).abandoned
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_mem_is_pinned(&self, Tracked(local): Tracked<&Local>) -> (mem_is_pinned: bool)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            mem_is_pinned == local.segments[self.segment_id@].main.value().mem_is_pinned,
    {
        self.get_main_ref(Tracked(local)).mem_is_pinned
    }

    #[inline(always)]
    pub fn is_abandoned(&self, Tracked(local): Tracked<&Local>) -> (is_ab: bool)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value().thread_id.well_formed(),
            is_ab ==> local.thread_token.value().segments.index(self.segment_id@).shared_access.points_to.value().thread_id.well_formed(),
    {
        self.get_ref(Tracked(local)).thread_id.load() == 0
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_segment_kind(&self, Tracked(local): Tracked<&Local>) -> (kind: SegmentKind)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            kind == local.segments[self.segment_id@].main2.value().kind,
    {
        self.get_main2_ref(Tracked(local)).kind
    }

    #[inline(always)]
    #[verus_verify]
    pub fn is_kind_huge(&self, Tracked(local): Tracked<&Local>) -> (b: bool)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            b == segment_kind_is_huge(local.segments[self.segment_id@].main2.value().kind),
    {
        let kind = self.get_main2_ref(Tracked(local)).kind;
        matches!(kind, SegmentKind::Huge)
    }
}

pub struct PagePtr {
    pub page_ptr: *mut Page,
    pub page_id: Ghost<PageId>,
}

impl Clone for PagePtr {
    #[inline(always)]
    fn clone(&self) -> (s: Self)
        ensures
            s.page_ptr == self.page_ptr,
            s.page_id@ == self.page_id@,
    {
        PagePtr { page_ptr: self.page_ptr, page_id: Ghost(self.page_id@) }
    }
}
impl Copy for PagePtr { }

impl PagePtr {
    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool {
        is_page_ptr(self.page_ptr, self.page_id@)
          && self.page_ptr.addr() != 0
    }

    #[verifier(inline)]
    pub open spec fn is_in(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
    }

    pub open spec fn is_empty_global(&self, local: Local) -> bool {
        self.page_ptr == local.page_empty_global@.s.points_to.ptr()
    }

    #[verifier(inline)]
    pub open spec fn is_used_and_primary(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages[self.page_id@].offset == 0
    }

    #[verifier(inline)]
    pub open spec fn is_in_unused(&self, local: Local) -> bool {
        local.unused_pages.dom().contains(self.page_id@)
    }

    #[verifier(inline)]
    pub open spec fn is_used(&self, local: Local) -> bool {
        local.pages.dom().contains(self.page_id@)
          && local.thread_token.value().pages.dom().contains(self.page_id@)
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn null() -> (s: Self)
        ensures
            s.page_ptr.addr() == 0,
    {
        PagePtr { page_ptr: core::ptr::null_mut(),
            page_id: Ghost(arbitrary())
        }
    }

    #[inline(always)]
    #[verus_verify]
    pub fn is_null(&self) -> (b: bool)
        ensures b == (self.page_ptr.addr() == 0),
    {
        self.page_ptr.addr() == 0
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page: &'a Page)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            self.is_in_unused(*local) ==> page == local.unused_pages[self.page_id@].points_to.value(),
            !self.is_in_unused(*local) ==> page == local.thread_token.value().pages.index(self.page_id@).shared_access.points_to.value(),
    {
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            if self.is_in_unused(*local) {
                assert(local.unused_pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf_unused(
                    self.page_id@,
                    local.unused_pages[self.page_id@],
                    local.page_organization.popped,
                    local.instance,
                ));
                assert(local.unused_pages[self.page_id@].wf_unused(self.page_id@, local.instance));
                lemma_page_ptr_unique(self.page_ptr, local.unused_pages[self.page_id@].points_to.ptr(), self.page_id@);
                assert(local.unused_pages[self.page_id@].points_to.is_init());
            } else {
                assert(!local.unused_pages.dom().contains(self.page_id@));
                assert(local.thread_token.value().pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf(
                    self.page_id@,
                    local.thread_token.value().pages.index(self.page_id@),
                    local.instance,
                ));
                assert(local.thread_token.value().pages[self.page_id@].is_enabled);
                if local.thread_token.value().pages[self.page_id@].offset == 0 {
                    assert(local.thread_token.value().pages.index(self.page_id@).shared_access.wf(
                        self.page_id@,
                        local.thread_token.value().pages[self.page_id@].block_size,
                        local.instance,
                    ));
                } else {
                    assert(local.thread_token.value().pages.index(self.page_id@).shared_access.wf_secondary(
                        self.page_id@,
                        local.thread_token.value().pages[self.page_id@].block_size,
                        local.instance,
                    ));
                }
            }
        }
        let tracked perm = if self.is_in_unused(*local) {
            &local.unused_pages.tracked_borrow(self.page_id@).points_to
        } else {
            &local.instance.thread_local_state_guards_page(
                local.thread_id, self.page_id@, &local.thread_token).points_to
        };
        proof {
            lemma_page_ptr_unique(self.page_ptr, perm.ptr(), self.page_id@);
            assert(perm.is_init());
        }

        ptr_ref(self.page_ptr, Tracked(perm))
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_inner_ref<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_inner: &'a PageInner)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            page_inner == local.pages[self.page_id@].inner.value(),
            *page_inner == local.page_inner(self.page_id@),
    {
        let page = self.get_ref(Tracked(local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.pages.dom().contains(self.page_id@));
            if self.is_in_unused(*local) {
                assert(local.unused_pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf_unused(
                    self.page_id@,
                    local.unused_pages[self.page_id@],
                    local.page_organization.popped,
                    local.instance,
                ));
                assert(local.unused_pages[self.page_id@].wf_unused(self.page_id@, local.instance));
                assert(page == local.unused_pages[self.page_id@].points_to.value());
                assert(page.inner.id() == local.pages[self.page_id@].inner.id());
            } else {
                assert(local.thread_token.value().pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf(
                    self.page_id@,
                    local.thread_token.value().pages[self.page_id@],
                    local.instance,
                ));
                assert(page == local.thread_token.value().pages[self.page_id@].shared_access.points_to.value());
                assert(page.inner.id() == local.pages[self.page_id@].inner.id());
            }
        }
        page.inner.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).inner
            ))
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn get_inner_ref_maybe_empty<'a>(&self, Tracked(local): Tracked<&'a Local>) -> (page_inner: &'a PageInner)
        requires
            local.wf_main() || local.wf_main_for_page_access(),
            self.is_empty_global(*local) || (self.wf() && self.is_in(*local)),
        ensures
            self.is_empty_global(*local) ==> page_inner == local.page_empty_global@.l.inner.value(),
            self.is_empty_global(*local) ==> page_inner.free.first_addr() == 0,
            !self.is_empty_global(*local) ==> page_inner == local.pages[self.page_id@].inner.value(),
    {
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            if !self.is_empty_global(*local) {
                assert(self.is_in(*local));
            }
        }
        let tracked perm = if self.is_empty_global(*local) {
            &local.page_empty_global.borrow().s.points_to
        } else if self.is_in_unused(*local) {
            &local.unused_pages.tracked_borrow(self.page_id@).points_to
        } else {
            &local.instance.thread_local_state_guards_page(
                local.thread_id, self.page_id@, &local.thread_token).points_to
        };
        proof {
            if self.is_empty_global(*local) {
                let tracked pfa = local.page_empty_global.borrow();
                assert(*pfa == local.page_empty_global@);
                assert(pfa.wf_empty_page_global());
                assert(pfa.s.points_to.ptr() == self.page_ptr);
                assert(pfa.s.points_to.is_init());
                assert(perm.ptr() == self.page_ptr);
                assert(perm.is_init());
            } else if self.is_in_unused(*local) {
                assert(local.unused_pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf_unused(
                    self.page_id@,
                    local.unused_pages[self.page_id@],
                    local.page_organization.popped,
                    local.instance,
                ));
                assert(local.unused_pages[self.page_id@].wf_unused(self.page_id@, local.instance));
                lemma_page_ptr_unique(self.page_ptr, local.unused_pages[self.page_id@].points_to.ptr(), self.page_id@);
                assert(local.unused_pages[self.page_id@].points_to.is_init());
                assert(perm.ptr() == self.page_ptr);
                assert(perm.is_init());
            } else {
                assert(self.is_in(*local));
                assert(local.pages.dom().contains(self.page_id@));
                assert(!local.unused_pages.dom().contains(self.page_id@));
                assert(local.thread_token.value().pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf(
                    self.page_id@,
                    local.thread_token.value().pages.index(self.page_id@),
                    local.instance,
                ));
                assert(local.thread_token.value().pages[self.page_id@].is_enabled);
                if local.thread_token.value().pages[self.page_id@].offset == 0 {
                    assert(local.thread_token.value().pages.index(self.page_id@).shared_access.wf(
                        self.page_id@,
                        local.thread_token.value().pages[self.page_id@].block_size,
                        local.instance,
                    ));
                } else {
                    assert(local.thread_token.value().pages.index(self.page_id@).shared_access.wf_secondary(
                        self.page_id@,
                        local.thread_token.value().pages[self.page_id@].block_size,
                        local.instance,
                    ));
                }
                lemma_page_ptr_unique(self.page_ptr, perm.ptr(), self.page_id@);
                assert(perm.is_init());
            }
        }
        let page = ptr_ref(self.page_ptr, Tracked(perm));
        proof {
            if self.is_empty_global(*local) {
                let tracked pfa = local.page_empty_global.borrow();
                assert(*pfa == local.page_empty_global@);
                assert(pfa.wf_empty_page_global());
                assert(page == local.page_empty_global@.s.points_to.value());
                assert(page.inner.id() == local.page_empty_global@.l.inner.id());
                assert(local.page_empty_global@.l.inner.value().zeroed());
                assert(local.page_empty_global@.l.inner.value().free.len() == 0);
                local.page_empty_global@.l.inner.value().free.len_zero_implies_first_addr_zero();
            } else if self.is_in_unused(*local) {
                assert(page == local.unused_pages[self.page_id@].points_to.value());
                assert(local.pages[self.page_id@].wf_unused(
                    self.page_id@,
                    local.unused_pages[self.page_id@],
                    local.page_organization.popped,
                    local.instance,
                ));
                assert(local.unused_pages[self.page_id@].wf_unused(self.page_id@, local.instance));
                assert(page.inner.id() == local.pages[self.page_id@].inner.id());
            } else {
                assert(local.thread_token.value().pages.dom().contains(self.page_id@));
                assert(local.pages[self.page_id@].wf(
                    self.page_id@,
                    local.thread_token.value().pages[self.page_id@],
                    local.instance,
                ));
                assert(page == local.thread_token.value().pages[self.page_id@].shared_access.points_to.value());
                assert(page.inner.id() == local.pages[self.page_id@].inner.id());
            }
        }
        page.inner.borrow(Tracked(
            if self.is_empty_global(*local) {
                &local.page_empty_global.borrow().l.inner
            } else {
                &local.pages.tracked_borrow(self.page_id@).inner
            }
            ))
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn get_count<'a>(&self, Tracked(local): Tracked<&Local>) -> (count: u32)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            local.page_organization.pages.dom().contains(self.page_id@),
            count as int == local.page_count(self.page_id@),
            local.page_organization.pages[self.page_id@].count.is_some() ==>
                count as int == local.page_organization.pages[self.page_id@].count.unwrap(),
    {
        let page = self.get_ref(Tracked(local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.page_organization_valid());
            assert(local.pages.dom().contains(self.page_id@));
            assert(local.page_organization.pages.dom().contains(self.page_id@));
            assert(page == local.unused_pages[self.page_id@].points_to.value() ||
                page == local.thread_token.value().pages.index(self.page_id@).shared_access.points_to.value());
            assert(page_organization_pages_match(
                local.page_organization.pages,
                local.pages,
                local.psa,
                local.page_organization.popped));
            assert(page_organization_pages_match_data(
                local.page_organization.pages[self.page_id@],
                local.pages[self.page_id@],
                local.psa[self.page_id@],
                self.page_id@,
                local.page_organization.popped));
        }
        *page.count.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).count
            ))
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn get_next<'a>(&self, Tracked(local): Tracked<&Local>) -> (next: *mut Page)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            local.page_organization.pages.dom().contains(self.page_id@),
            local.page_organization.pages[self.page_id@].dlist_entry.is_some() ==>
                is_page_ptr_opt(next, local.page_organization.pages[self.page_id@].dlist_entry.unwrap().next),
    {
        let page = self.get_ref(Tracked(local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.page_organization_valid());
            assert(local.pages.dom().contains(self.page_id@));
            assert(local.page_organization.pages.dom().contains(self.page_id@));
            assert(page_organization_pages_match(
                local.page_organization.pages,
                local.pages,
                local.psa,
                local.page_organization.popped));
            assert(page_organization_pages_match_data(
                local.page_organization.pages[self.page_id@],
                local.pages[self.page_id@],
                local.psa[self.page_id@],
                self.page_id@,
                local.page_organization.popped));
        }
        *page.next.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).next
            ))
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn get_prev<'a>(&self, Tracked(local): Tracked<&Local>) -> (prev: *mut Page)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            local.page_organization.pages.dom().contains(self.page_id@),
            local.page_organization.pages[self.page_id@].dlist_entry.is_some() ==>
                is_page_ptr_opt(prev, local.page_organization.pages[self.page_id@].dlist_entry.unwrap().prev),
    {
        let page = self.get_ref(Tracked(local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.page_organization_valid());
            assert(local.pages.dom().contains(self.page_id@));
            assert(local.page_organization.pages.dom().contains(self.page_id@));
            assert(page_organization_pages_match(
                local.page_organization.pages,
                local.pages,
                local.psa,
                local.page_organization.popped));
            assert(page_organization_pages_match_data(
                local.page_organization.pages[self.page_id@],
                local.pages[self.page_id@],
                local.psa[self.page_id@],
                self.page_id@,
                local.page_organization.popped));
        }
        *page.prev.borrow(Tracked(
            &local.pages.tracked_borrow(self.page_id@).prev
            ))
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn add_offset(&self, count: usize) -> (p: Self)
        requires
            self.wf(),
            self.page_id@.idx + count <= SLICES_PER_SEGMENT,
        ensures
            p.page_id@ == (PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            }),
            p.page_ptr as int == page_header_start(p.page_id@),
            p.wf(),
    {
        let p = self.page_ptr.addr();
        proof {
            const_facts();
            let page_id = self.page_id@;
            lemma_segment_start_basics(page_id.segment_id);
            assert(self.page_ptr as int == page_header_start(page_id));
            assert(p as int == self.page_ptr as int);
            assert(0 <= SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(0 < SIZEOF_SEGMENT_HEADER as int) by(compute_only);
            assert(SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= SEGMENT_SIZE as int) by(compute_only);
            assert(count as int <= SLICES_PER_SEGMENT as int) by(nonlinear_arith)
                requires
                    0 <= page_id.idx,
                    page_id.idx + count <= SLICES_PER_SEGMENT;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int)
                <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    count as int <= SLICES_PER_SEGMENT as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    (count as int) * (SIZEOF_PAGE_HEADER as int)
                        <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int),
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int,
                    0 <= SIZEOF_SEGMENT_HEADER as int;
            assert(SEGMENT_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
                requires
                    SEGMENT_SIZE as int + SEGMENT_SIZE as int - 1 <= usize::MAX as int,
                    0 <= SEGMENT_SIZE as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= SEGMENT_SIZE as int,
                    SEGMENT_SIZE as int <= usize::MAX as int;
            assert(p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                == segment_start(page_id.segment_id)
                    + SIZEOF_SEGMENT_HEADER as int
                    + (page_id.idx as int + count as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    p as int == page_header_start(page_id);
            assert(p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                <= segment_start(page_id.segment_id) + SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                        == segment_start(page_id.segment_id)
                            + SIZEOF_SEGMENT_HEADER as int
                            + (page_id.idx as int + count as int) * (SIZEOF_PAGE_HEADER as int),
                    page_id.idx + count <= SLICES_PER_SEGMENT,
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert(p as int + (count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                        <= segment_start(page_id.segment_id) + SEGMENT_SIZE as int,
                    segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX;
        }
        let q = p + count * SIZEOF_PAGE_HEADER;
        proof {
            let page_id = self.page_id@;
            let new_page_id = PageId {
                segment_id: page_id.segment_id,
                idx: (page_id.idx + count) as nat,
            };
            assert(new_page_id.segment_id == page_id.segment_id);
            assert(0 <= page_id.idx + count);
            assert(new_page_id.idx == page_id.idx + count);
            let prod = mul(count, SIZEOF_PAGE_HEADER);
            assert(q == add(p, prod));
            assert(prod == mul(count, SIZEOF_PAGE_HEADER));
            assert(prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    prod == mul(count, SIZEOF_PAGE_HEADER),
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int;
            assert(q as int == p as int + prod as int) by(nonlinear_arith)
                requires
                    q == add(p, prod),
                    p as int + prod as int <= usize::MAX as int;
            assert(q as int == page_header_start(new_page_id)) by(nonlinear_arith)
                requires
                    q as int == p as int + prod as int,
                    prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int),
                    p as int == page_header_start(page_id),
                    new_page_id.segment_id == page_id.segment_id,
                    new_page_id.idx == page_id.idx + count;
            assert(0 <= new_page_id.idx <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    0 <= page_id.idx,
                    page_id.idx + count <= SLICES_PER_SEGMENT,
                    new_page_id.idx == page_id.idx + count;
            assert(segment_start(new_page_id.segment_id) + SEGMENT_SIZE < usize::MAX);
            assert(q as int != 0) by(nonlinear_arith)
                requires
                    q as int == page_header_start(new_page_id),
                    0 <= segment_start(new_page_id.segment_id),
                    0 < SIZEOF_SEGMENT_HEADER as int,
                    0 <= new_page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((self.page_ptr.with_addr(q) as *mut Page) as int == page_header_start(new_page_id));
            assert((self.page_ptr.with_addr(q) as *mut Page)@.provenance == new_page_id.segment_id.provenance);
            assert(is_page_ptr(self.page_ptr.with_addr(q) as *mut Page, new_page_id));
        }
        PagePtr {
            page_ptr: self.page_ptr.with_addr(q),
            page_id: Ghost(PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            })
        }
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn sub_offset(&self, count: usize) -> (p: Self)
        requires
            self.wf(),
            count <= self.page_id@.idx,
        ensures
            p.page_id@ == (PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx - count) as nat,
            }),
            p.page_ptr as int == page_header_start(p.page_id@),
            p.wf(),
    {
        let p = self.page_ptr.addr();
        proof {
            const_facts();
            let page_id = self.page_id@;
            lemma_segment_start_basics(page_id.segment_id);
            assert(self.page_ptr as int == page_header_start(page_id));
            assert(p as int == self.page_ptr as int);
            assert(0 <= SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(0 < SIZEOF_SEGMENT_HEADER as int) by(compute_only);
            assert(SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= SEGMENT_SIZE as int) by(compute_only);
            assert(count as int <= SLICES_PER_SEGMENT as int) by(nonlinear_arith)
                requires
                    count <= page_id.idx,
                    page_id.idx <= SLICES_PER_SEGMENT;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int)
                <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    count as int <= SLICES_PER_SEGMENT as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    (count as int) * (SIZEOF_PAGE_HEADER as int)
                        <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int),
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int,
                    0 <= SIZEOF_SEGMENT_HEADER as int;
            assert(SEGMENT_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
                requires
                    SEGMENT_SIZE as int + SEGMENT_SIZE as int - 1 <= usize::MAX as int,
                    0 <= SEGMENT_SIZE as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= SEGMENT_SIZE as int,
                    SEGMENT_SIZE as int <= usize::MAX as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= p as int) by(nonlinear_arith)
                requires
                    p as int == page_header_start(page_id),
                    count <= page_id.idx,
                    0 <= segment_start(page_id.segment_id),
                    0 <= SIZEOF_SEGMENT_HEADER as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
        }
        let q = p - count * SIZEOF_PAGE_HEADER;
        let ghost page_id = PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx - count) as nat,
            };
        proof {
            let old_page_id = self.page_id@;
            assert(page_id.segment_id == old_page_id.segment_id);
            assert(0 <= old_page_id.idx - count) by(nonlinear_arith)
                requires
                    count <= old_page_id.idx;
            assert(page_id.idx == old_page_id.idx - count);
            let prod = mul(count, SIZEOF_PAGE_HEADER);
            assert(q == sub(p, prod));
            assert(prod == mul(count, SIZEOF_PAGE_HEADER));
            assert(prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    prod == mul(count, SIZEOF_PAGE_HEADER),
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int;
            assert(prod <= p) by(nonlinear_arith)
                requires
                    prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int),
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= p as int;
            assert(q as int == p as int - prod as int) by(bit_vector)
                requires
                    q == sub(p, prod),
                    prod <= p;
            assert(q as int == page_header_start(page_id)) by(nonlinear_arith)
                requires
                    q as int == p as int - prod as int,
                    prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int),
                    p as int == page_header_start(old_page_id),
                    page_id.segment_id == old_page_id.segment_id,
                    page_id.idx == old_page_id.idx - count;
            assert(0 <= page_id.idx <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    count <= old_page_id.idx,
                    old_page_id.idx <= SLICES_PER_SEGMENT,
                    page_id.idx == old_page_id.idx - count;
            assert(segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX);
            assert(q as int != 0) by(nonlinear_arith)
                requires
                    q as int == page_header_start(page_id),
                    0 <= segment_start(page_id.segment_id),
                    0 < SIZEOF_SEGMENT_HEADER as int,
                    0 <= page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
        }
        let q = self.page_ptr.with_addr(q);
        proof {
            assert(q as int == page_header_start(page_id));
            assert(q@.provenance == page_id.segment_id.provenance);
            assert(is_page_ptr(q, page_id));
        }
        PagePtr {
            page_ptr: q,
            page_id: Ghost(page_id)
        }
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn is_gt_0th_slice(&self, segment: SegmentPtr) -> (res: bool)
        requires
            self.wf(),
            segment.wf(),
            self.page_id@.segment_id == segment.segment_id@,
        ensures
            res == (self.page_id@.idx > 0),
    {
        proof {
            let page_id = self.page_id@;
            assert(self.page_ptr.addr() as int == page_header_start(page_id));
            assert(SIZEOF_PAGE_HEADER as int > 0) by(compute_only);
            assert(0 <= page_id.idx <= SLICES_PER_SEGMENT);
        }
        self.page_ptr.addr() > segment.get_page_header_ptr(0).page_ptr.addr()
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn get_index(&self) -> (idx: usize)
        requires
            self.wf(),
        ensures
            idx as int == self.page_id@.idx,
    {
        let segment = SegmentPtr::ptr_segment(*self);
        proof {
            let page_id = self.page_id@;
            assert(segment.wf());
            assert(segment.segment_id@ == page_id.segment_id);
            lemma_segment_start_basics(page_id.segment_id);
            let page_addr = self.page_ptr.addr();
            let seg_addr = segment.segment_ptr.addr();
            assert(page_addr as int == self.page_ptr as int);
            assert(seg_addr as int == segment.segment_ptr as int);
            assert(page_addr as int == page_header_start(page_id));
            assert(seg_addr as int == segment_start(page_id.segment_id));
            assert(0 <= SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(SIZEOF_PAGE_HEADER as int > 0) by(compute_only);
            assert(seg_addr <= page_addr) by(nonlinear_arith)
                requires
                    page_addr as int == page_header_start(page_id),
                    seg_addr as int == segment_start(page_id.segment_id),
                    0 <= SIZEOF_SEGMENT_HEADER as int,
                    0 <= page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((page_addr - seg_addr) as int == page_addr as int - seg_addr as int) by(bit_vector)
                requires
                    seg_addr <= page_addr;
            assert(SIZEOF_SEGMENT_HEADER <= page_addr - seg_addr) by(nonlinear_arith)
                requires
                    (page_addr - seg_addr) as int == page_addr as int - seg_addr as int,
                    page_addr as int == page_header_start(page_id),
                    seg_addr as int == segment_start(page_id.segment_id),
                    0 <= page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
            let diff = sub(page_addr, seg_addr);
            assert(diff == page_addr - seg_addr);
            let idxx = sub(diff, SIZEOF_SEGMENT_HEADER);
            assert(idxx == diff - SIZEOF_SEGMENT_HEADER);
            assert(idxx as int == diff as int - SIZEOF_SEGMENT_HEADER as int) by(bit_vector)
                requires
                    idxx == sub(diff, SIZEOF_SEGMENT_HEADER),
                    SIZEOF_SEGMENT_HEADER <= diff;
            assert(idxx as int == page_id.idx * SIZEOF_PAGE_HEADER) by(nonlinear_arith)
                requires
                    idxx as int == diff as int - SIZEOF_SEGMENT_HEADER as int,
                    diff as int == page_addr as int - seg_addr as int,
                    page_addr as int == page_header_start(page_id),
                    seg_addr as int == segment_start(page_id.segment_id);
            lemma_div_by_multiple(page_id.idx as int, SIZEOF_PAGE_HEADER as int);
            assert((idxx / SIZEOF_PAGE_HEADER) as int == page_id.idx) by(nonlinear_arith)
                requires
                    idxx as int == page_id.idx * SIZEOF_PAGE_HEADER,
                    SIZEOF_PAGE_HEADER as int > 0;
        }
        (self.page_ptr.addr() - segment.segment_ptr.addr() - SIZEOF_SEGMENT_HEADER)
            / SIZEOF_PAGE_HEADER
    }

    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn slice_start(&self) -> (p: usize)
        requires
            self.wf(),
        ensures
            p as int == page_start(self.page_id@),
    {
        let segment = SegmentPtr::ptr_segment(*self);
        let s = segment.segment_ptr.addr();
        proof {
            const_facts();
            let page_id = self.page_id@;
            assert(segment.wf());
            assert(segment.segment_id@ == page_id.segment_id);
            lemma_segment_start_basics(page_id.segment_id);
            let page_addr = self.page_ptr.addr();
            assert(page_addr as int == self.page_ptr as int);
            assert(segment.segment_ptr.addr() as int == segment.segment_ptr as int);
            assert(page_addr as int == page_header_start(page_id));
            assert(s as int == segment_start(page_id.segment_id));
            assert(0 <= SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(SIZEOF_PAGE_HEADER as int > 0) by(compute_only);
            assert(SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int) by(compute_only);
            assert(s <= page_addr) by(nonlinear_arith)
                requires
                    page_addr as int == page_header_start(page_id),
                    s as int == segment_start(page_id.segment_id),
                    0 <= SIZEOF_SEGMENT_HEADER as int,
                    0 <= page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((page_addr - s) as int == page_addr as int - s as int) by(bit_vector)
                requires
                    s <= page_addr;
            assert(SIZEOF_SEGMENT_HEADER <= page_addr - s) by(nonlinear_arith)
                requires
                    (page_addr - s) as int == page_addr as int - s as int,
                    page_addr as int == page_header_start(page_id),
                    s as int == segment_start(page_id.segment_id),
                    0 <= page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
            let diff = sub(page_addr, s);
            assert(diff == page_addr - s);
            let idxx = sub(diff, SIZEOF_SEGMENT_HEADER);
            assert(idxx == diff - SIZEOF_SEGMENT_HEADER);
            assert(idxx as int == diff as int - SIZEOF_SEGMENT_HEADER as int) by(bit_vector)
                requires
                    idxx == sub(diff, SIZEOF_SEGMENT_HEADER),
                    SIZEOF_SEGMENT_HEADER <= diff;
            assert(idxx as int == page_id.idx * SIZEOF_PAGE_HEADER) by(nonlinear_arith)
                requires
                    idxx as int == diff as int - SIZEOF_SEGMENT_HEADER as int,
                    diff as int == page_addr as int - s as int,
                    page_addr as int == page_header_start(page_id),
                    s as int == segment_start(page_id.segment_id);
            lemma_div_by_multiple(page_id.idx as int, SIZEOF_PAGE_HEADER as int);
            assert((idxx / SIZEOF_PAGE_HEADER) as int == page_id.idx) by(nonlinear_arith)
                requires
                    idxx as int == page_id.idx * SIZEOF_PAGE_HEADER,
                    SIZEOF_PAGE_HEADER as int > 0;
            assert(((idxx / SIZEOF_PAGE_HEADER) as int) * (SLICE_SIZE as int)
                <= usize::MAX as int) by(nonlinear_arith)
                requires
                    (idxx / SIZEOF_PAGE_HEADER) as int == page_id.idx,
                    page_id.idx <= SLICES_PER_SEGMENT,
                    SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int,
                    SEGMENT_SIZE as int <= usize::MAX as int;
            assert(s as int + ((idxx / SIZEOF_PAGE_HEADER) as int) * (SLICE_SIZE as int)
                <= usize::MAX as int) by(nonlinear_arith)
                requires
                    s as int == segment_start(page_id.segment_id),
                    (idxx / SIZEOF_PAGE_HEADER) as int == page_id.idx,
                    page_id.idx <= SLICES_PER_SEGMENT,
                    SLICES_PER_SEGMENT as int * SLICE_SIZE as int == SEGMENT_SIZE as int,
                    segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX;
        }
        s +
          ((self.page_ptr.addr() - s - SIZEOF_SEGMENT_HEADER) / SIZEOF_PAGE_HEADER)
            * SLICE_SIZE as usize
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn add_offset_and_check(&self, count: usize, segment: SegmentPtr) -> (res: (Self, bool))
        requires
            self.wf(),
            segment.wf(),
            self.page_id@.segment_id == segment.segment_id@,
            self.page_id@.idx + count <= SLICES_PER_SEGMENT,
        ensures
            res.0.page_id@ == (PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            }),
            res.0.page_ptr as int == page_header_start(res.0.page_id@),
            res.0.wf(),
            res.1 == (res.0.page_id@.idx < SLICES_PER_SEGMENT),
    {
        let p = self.page_ptr.addr();
        proof {
            const_facts();
            let page_id = self.page_id@;
            lemma_segment_start_basics(page_id.segment_id);
            assert(self.page_ptr as int == page_header_start(page_id));
            assert(p as int == self.page_ptr as int);
            assert(0 <= SIZEOF_PAGE_HEADER as int) by(compute_only);
            assert(0 < SIZEOF_SEGMENT_HEADER as int) by(compute_only);
            assert(SIZEOF_SEGMENT_HEADER as int
                + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                <= SEGMENT_SIZE as int) by(compute_only);
            assert(count as int <= SLICES_PER_SEGMENT as int) by(nonlinear_arith)
                requires
                    0 <= page_id.idx,
                    page_id.idx + count <= SLICES_PER_SEGMENT;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int)
                <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    count as int <= SLICES_PER_SEGMENT as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    (count as int) * (SIZEOF_PAGE_HEADER as int)
                        <= (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int),
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int,
                    0 <= SIZEOF_SEGMENT_HEADER as int;
            assert(SEGMENT_SIZE as int <= usize::MAX as int) by(nonlinear_arith)
                requires
                    SEGMENT_SIZE as int + SEGMENT_SIZE as int - 1 <= usize::MAX as int,
                    0 <= SEGMENT_SIZE as int;
            assert((count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= SEGMENT_SIZE as int,
                    SEGMENT_SIZE as int <= usize::MAX as int;
            assert(p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                == segment_start(page_id.segment_id)
                    + SIZEOF_SEGMENT_HEADER as int
                    + (page_id.idx as int + count as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    p as int == page_header_start(page_id);
            assert(p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                <= segment_start(page_id.segment_id) + SEGMENT_SIZE as int) by(nonlinear_arith)
                requires
                    p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                        == segment_start(page_id.segment_id)
                            + SIZEOF_SEGMENT_HEADER as int
                            + (page_id.idx as int + count as int) * (SIZEOF_PAGE_HEADER as int),
                    page_id.idx + count <= SLICES_PER_SEGMENT,
                    SIZEOF_SEGMENT_HEADER as int
                        + (SLICES_PER_SEGMENT as int) * (SIZEOF_PAGE_HEADER as int)
                        <= SEGMENT_SIZE as int,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert(p as int + (count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int) by(nonlinear_arith)
                requires
                    p as int + (count as int) * (SIZEOF_PAGE_HEADER as int)
                        <= segment_start(page_id.segment_id) + SEGMENT_SIZE as int,
                    segment_start(page_id.segment_id) + SEGMENT_SIZE < usize::MAX;
        }
        let q = p + count * SIZEOF_PAGE_HEADER;
        proof {
            let page_id = self.page_id@;
            let new_page_id = PageId {
                segment_id: page_id.segment_id,
                idx: (page_id.idx + count) as nat,
            };
            assert(new_page_id.segment_id == page_id.segment_id);
            assert(0 <= page_id.idx + count);
            assert(new_page_id.idx == page_id.idx + count);
            let prod = mul(count, SIZEOF_PAGE_HEADER);
            assert(q == add(p, prod));
            assert(prod == mul(count, SIZEOF_PAGE_HEADER));
            assert(prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int)) by(nonlinear_arith)
                requires
                    prod == mul(count, SIZEOF_PAGE_HEADER),
                    (count as int) * (SIZEOF_PAGE_HEADER as int) <= usize::MAX as int;
            assert(q as int == p as int + prod as int) by(nonlinear_arith)
                requires
                    q == add(p, prod),
                    p as int + prod as int <= usize::MAX as int;
            assert(q as int == page_header_start(new_page_id)) by(nonlinear_arith)
                requires
                    q as int == p as int + prod as int,
                    prod as int == (count as int) * (SIZEOF_PAGE_HEADER as int),
                    p as int == page_header_start(page_id),
                    new_page_id.segment_id == page_id.segment_id,
                    new_page_id.idx == page_id.idx + count;
            assert(0 <= new_page_id.idx <= SLICES_PER_SEGMENT) by(nonlinear_arith)
                requires
                    0 <= page_id.idx,
                    page_id.idx + count <= SLICES_PER_SEGMENT,
                    new_page_id.idx == page_id.idx + count;
            assert(segment_start(new_page_id.segment_id) + SEGMENT_SIZE < usize::MAX);
            assert(q as int != 0) by(nonlinear_arith)
                requires
                    q as int == page_header_start(new_page_id),
                    0 <= segment_start(new_page_id.segment_id),
                    0 < SIZEOF_SEGMENT_HEADER as int,
                    0 <= new_page_id.idx,
                    0 <= SIZEOF_PAGE_HEADER as int;
            assert((self.page_ptr.with_addr(q) as *mut Page) as int == page_header_start(new_page_id));
            assert((self.page_ptr.with_addr(q) as *mut Page)@.provenance == new_page_id.segment_id.provenance);
            assert(is_page_ptr(self.page_ptr.with_addr(q) as *mut Page, new_page_id));
        }
        let page_ptr = PagePtr {
            page_ptr: self.page_ptr.with_addr(q),
            page_id: Ghost(PageId {
                segment_id: self.page_id@.segment_id,
                idx: (self.page_id@.idx + count) as nat,
            })
        };
        let last = segment.get_page_after_end();
        proof {
            let new_page_id = page_ptr.page_id@;
            assert(page_ptr.wf());
            assert(new_page_id.segment_id == segment.segment_id@);
            assert(last as int == page_header_start(PageId {
                segment_id: segment.segment_id@,
                idx: SLICES_PER_SEGMENT as nat,
            }));
            assert(page_ptr.page_ptr.addr() as int == page_ptr.page_ptr as int);
            assert(last.addr() as int == last as int);
            assert(SIZEOF_PAGE_HEADER as int > 0) by(compute_only);
            if new_page_id.idx < SLICES_PER_SEGMENT {
                assert(page_ptr.page_ptr.addr() < last.addr()) by(nonlinear_arith)
                    requires
                        page_ptr.page_ptr.addr() as int == page_header_start(new_page_id),
                        last.addr() as int == page_header_start(PageId {
                            segment_id: segment.segment_id@,
                            idx: SLICES_PER_SEGMENT as nat,
                        }),
                        new_page_id.segment_id == segment.segment_id@,
                        new_page_id.idx < SLICES_PER_SEGMENT,
                        0 < SIZEOF_PAGE_HEADER as int;
            } else {
                assert(new_page_id.idx == SLICES_PER_SEGMENT) by(nonlinear_arith)
                    requires
                        new_page_id.idx <= SLICES_PER_SEGMENT,
                        !(new_page_id.idx < SLICES_PER_SEGMENT);
                assert(!(page_ptr.page_ptr.addr() < last.addr())) by(nonlinear_arith)
                    requires
                        page_ptr.page_ptr.addr() as int == page_header_start(new_page_id),
                        last.addr() as int == page_header_start(PageId {
                            segment_id: segment.segment_id@,
                            idx: SLICES_PER_SEGMENT as nat,
                        }),
                        new_page_id.segment_id == segment.segment_id@,
                        new_page_id.idx == SLICES_PER_SEGMENT;
            }
        }
        (page_ptr, page_ptr.page_ptr.addr() < last.addr())
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_block_size(&self, Tracked(local): Tracked<&Local>) -> (bsize: u32)
        requires
            self.wf(),
            self.is_in(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            bsize == local.pages[self.page_id@].inner.value().xblock_size,
            bsize as int == local.block_size(self.page_id@),
    {
        self.get_inner_ref(Tracked(local)).xblock_size
    }


    #[inline(always)]
    #[verifier::rlimit(200)]
    #[verus_verify]
    pub fn get_heap(&self, Tracked(local): Tracked<&Local>) -> (heap: HeapPtr)
        requires
            self.wf(),
            self.is_in(*local),
            self.is_used_and_primary(*local),
            local.wf_main() || local.wf_main_for_page_access(),
        ensures
            heap.wf(),
            heap.is_in(*local),
    {
        let page_ref = self.get_ref(Tracked(&*local));
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.thread_token.value().pages.dom().contains(self.page_id@));
            assert(!local.unused_pages.dom().contains(self.page_id@));
            assert(local.pages[self.page_id@].wf(
                self.page_id@,
                local.thread_token.value().pages[self.page_id@],
                local.instance));
            assert(local.thread_token.value().pages[self.page_id@].offset == 0 ==> page_ref.xheap.wf(local.instance, self.page_id@));
            assert(page_ref.xheap.wf(local.instance, self.page_id@));
            assert(!page_ref.xheap.is_empty());
        }
        let ghost mut loaded_heap_id = local.heap_id;
        let h = atomic_with_ghost!(
            &page_ref.xheap.atomic => load();
            ghost g => {
                page_ref.xheap.emp_inst.borrow().agree(page_ref.xheap.emp.borrow(), &g.0);
                let tracked heap_of_page = g.1.tracked_borrow();
                local.instance.heap_of_page_agree_with_thread_state(
                    self.page_id@,
                    local.thread_id,
                    &local.thread_token,
                    heap_of_page);
            }
        );
        proof {
            if local.wf_main() {
                local.wf_main_implies_page_access();
            }
            assert(local.wf_main_for_page_access());
            assert(local.thread_token.value().pages.dom().contains(self.page_id@));
            assert(loaded_heap_id == local.heap_id);
            assert(is_heap_ptr(h, local.heap_id));
        }
        HeapPtr {
            heap_ptr: h,
            heap_id: Ghost(local.heap_id),
        }
    }
}



pub(crate) proof fn free_fast_block_token_idx_lt_num_blocks(
    tracked inst: &Mim::Instance,
    tracked thread_token: &Mim::thread_local_state,
    thread_id: ThreadId,
    tracked block: &Mim::block,
    num_blocks: nat,
)
    requires
        block.instance_id() == inst.id(),
        inst.id() == thread_token.instance_id(),
        thread_token.key() == thread_id,
        thread_token.value().pages.dom().contains(block.key().page_id),
        thread_token.value().pages[block.key().page_id].num_blocks == num_blocks,
    ensures
        block.key().idx < num_blocks,
{
    inst.get_block_properties(thread_id, block.key(), thread_token, block);
}

pub(crate) proof fn free_fast_live_block_implies_page_used(tracked mim_block: &Mim::block, local: Local)
    requires
        local.wf(),
        local.thread_token.value().pages.dom().contains(mim_block.key().page_id),
        local.thread_token.value().pages[mim_block.key().page_id].offset == 0,
        local.pages.dom().contains(mim_block.key().page_id),
        local.page_inner(mim_block.key().page_id).free.len()
            + local.page_inner(mim_block.key().page_id).local_free.len()
            < local.thread_token.value().pages[mim_block.key().page_id].num_blocks,
    ensures
        local.page_inner(mim_block.key().page_id).used >= 1,
{
    reveal(Local::wf);
    reveal(Local::wf_main);
    reveal(PageLocalAccess::wf);
    reveal(PageInner::wf);

    let page_id = mim_block.key().page_id;
    let page_inner = local.page_inner(page_id);
    let page_state = local.thread_token.value().pages[page_id];

    assert(local.wf_main());
    assert(local.pages.index(page_id).wf(page_id, page_state, local.instance));
    assert(page_state.offset == 0);
    assert(page_inner.wf(page_id, page_state, local.instance));
    assert(page_inner.used + page_inner.free.len() + page_inner.local_free.len()
        == page_state.num_blocks);
    assert(page_inner.used >= 1) by(nonlinear_arith)
        requires
            page_inner.used + page_inner.free.len() + page_inner.local_free.len()
                == page_state.num_blocks,
            page_inner.free.len() + page_inner.local_free.len() < page_state.num_blocks;
}

// Use macro as a work-arounds for not supporting functions that return &mut
// (note: not necessary anymore now that &mut is supported)

#[macro_export]
macro_rules! page_get_mut_inner {
    ($ptr:expr, $local:ident, $page_inner:ident => {
        let tracked mim_block = $dealloc:ident . mim_block;
        $receiver:ident . free . insert_block($block_ptr:expr, Tracked($perm:ident), Tracked(mim_block));
        $used:ident = $receiver2:ident . used - 1;
        $receiver3:ident . used = $used_again:ident;
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = $ptr;
            let ghost page_id = page_ptr.page_id@;
            let ghost local_before_inner = *$local;
            let ghost page_state_before = $local.thread_token.value().pages[page_id];

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

                let tracked $crate::dealloc_token::MimDeallocInner { mim_instance: dealloc_mim_instance, mim_block: mut live_block, ptr: dealloc_ptr } = $dealloc;
                let ghost dealloc_block_id = live_block.key();
                proof {
                    reveal(PageInner::wf);
                    assert($crate::dealloc_token::valid_block_token(live_block, dealloc_mim_instance));

                    assert(local_before_inner.wf());
                    assert(page_state_before == local_before_inner.thread_token.value().pages[page_id]);
                    assert(local_before_inner.page_inner(page_id).used == $page_inner.used);
                    assert(local_before_inner.page_inner(page_id).free.len() == $page_inner.free.len());
                    assert(local_before_inner.page_inner(page_id).local_free.len() == $page_inner.local_free.len());
                    assert($page_inner.wf(page_id, page_state_before, $local.instance));
                    assert($page_inner.free.wf());
                    assert($page_inner.local_free.wf());

                    assert(dealloc_block_id.page_id == page_id);
                    assert(dealloc_block_id.idx < page_state_before.num_blocks);
                    assert(live_block.instance_id() == $local.instance.id());

                    if exists |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                        && !(block_id.idx < page_state_before.num_blocks) {
                        let bad_id = choose |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                            && !(block_id.idx < page_state_before.num_blocks);
                        $page_inner.free.block_ids_contains_witness(bad_id);
                        let i = choose |i: nat| i < $page_inner.free.len()
                            && $page_inner.free.perms@.dom().contains(i)
                            && $page_inner.free.perms@[i].2.key() == bad_id;
                        $page_inner.free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == bad_id);
                        assert(entry_block.instance_id() == $local.instance.id());
                        free_fast_block_token_idx_lt_num_blocks(
                            &$local.instance,
                            &$local.thread_token,
                            $local.thread_id,
                            &entry_block,
                            page_state_before.num_blocks,
                        );
                        $page_inner.free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.free.block_ids().contains(block_id) implies
                        block_id.idx < page_state_before.num_blocks by {
                        if !(block_id.idx < page_state_before.num_blocks) {
                            assert(exists |bad_id: BlockId| $page_inner.free.block_ids().contains(bad_id)
                                && !(bad_id.idx < page_state_before.num_blocks));
                            assert(false);
                        }
                    };
                    if exists |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                        && !(block_id.idx < page_state_before.num_blocks) {
                        let bad_id = choose |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                            && !(block_id.idx < page_state_before.num_blocks);
                        $page_inner.local_free.block_ids_contains_witness(bad_id);
                        let i = choose |i: nat| i < $page_inner.local_free.len()
                            && $page_inner.local_free.perms@.dom().contains(i)
                            && $page_inner.local_free.perms@[i].2.key() == bad_id;
                        $page_inner.local_free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.local_free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == bad_id);
                        assert(entry_block.instance_id() == $local.instance.id());
                        free_fast_block_token_idx_lt_num_blocks(
                            &$local.instance,
                            &$local.thread_token,
                            $local.thread_id,
                            &entry_block,
                            page_state_before.num_blocks,
                        );
                        $page_inner.local_free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.local_free.block_ids().contains(block_id) implies
                        block_id.idx < page_state_before.num_blocks by {
                        if !(block_id.idx < page_state_before.num_blocks) {
                            assert(exists |bad_id: BlockId| $page_inner.local_free.block_ids().contains(bad_id)
                                && !(bad_id.idx < page_state_before.num_blocks));
                            assert(false);
                        }
                    };

                    if exists |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                        && block_id.idx == dealloc_block_id.idx {
                        let collision_id = choose |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                            && block_id.idx == dealloc_block_id.idx;
                        $page_inner.free.block_ids_contains_witness(collision_id);
                        let i = choose |i: nat| i < $page_inner.free.len()
                            && $page_inner.free.perms@.dom().contains(i)
                            && $page_inner.free.perms@[i].2.key() == collision_id;
                        $page_inner.free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == collision_id);
                        assert(entry_block.key().page_id == dealloc_block_id.page_id);
                        assert(entry_block.key().idx == dealloc_block_id.idx);
                        assert(entry_block.instance_id() == $local.instance.id());
                        let tracked (Tracked(entry_block), Tracked(returned_live_block)) =
                            LL::owned_block_tokens_same_page_idx_impossible_retain(&$local.instance, entry_block, live_block);
                        $page_inner.free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        live_block = returned_live_block;
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.free.block_ids().contains(block_id) implies
                        block_id.idx != dealloc_block_id.idx by {
                        if block_id.idx == dealloc_block_id.idx {
                            assert(exists |collision_id: BlockId| $page_inner.free.block_ids().contains(collision_id)
                                && collision_id.idx == dealloc_block_id.idx);
                            assert(false);
                        }
                    };
                    assert(!$page_inner.free.block_ids().contains(dealloc_block_id));

                    if exists |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                        && block_id.idx == dealloc_block_id.idx {
                        let collision_id = choose |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                            && block_id.idx == dealloc_block_id.idx;
                        $page_inner.local_free.block_ids_contains_witness(collision_id);
                        let i = choose |i: nat| i < $page_inner.local_free.len()
                            && $page_inner.local_free.perms@.dom().contains(i)
                            && $page_inner.local_free.perms@[i].2.key() == collision_id;
                        $page_inner.local_free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.local_free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == collision_id);
                        assert(entry_block.key().page_id == dealloc_block_id.page_id);
                        assert(entry_block.key().idx == dealloc_block_id.idx);
                        assert(entry_block.instance_id() == $local.instance.id());
                        let tracked (Tracked(entry_block), Tracked(returned_live_block)) =
                            LL::owned_block_tokens_same_page_idx_impossible_retain(&$local.instance, entry_block, live_block);
                        $page_inner.local_free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        live_block = returned_live_block;
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.local_free.block_ids().contains(block_id) implies
                        block_id.idx != dealloc_block_id.idx by {
                        if block_id.idx == dealloc_block_id.idx {
                            assert(exists |collision_id: BlockId| $page_inner.local_free.block_ids().contains(collision_id)
                                && collision_id.idx == dealloc_block_id.idx);
                            assert(false);
                        }
                    };
                    assert(!$page_inner.local_free.block_ids().contains(dealloc_block_id));

                    if exists |free_id: BlockId, local_id: BlockId|
                        #[trigger] $page_inner.free.block_ids().contains(free_id)
                            && #[trigger] $page_inner.local_free.block_ids().contains(local_id)
                            && free_id.idx == local_id.idx {
                        let free_id = choose |free_id: BlockId| exists |local_id: BlockId|
                            #[trigger] $page_inner.free.block_ids().contains(free_id)
                                && #[trigger] $page_inner.local_free.block_ids().contains(local_id)
                                && free_id.idx == local_id.idx;
                        let local_id = choose |local_id: BlockId|
                            $page_inner.free.block_ids().contains(free_id)
                                && $page_inner.local_free.block_ids().contains(local_id)
                                && free_id.idx == local_id.idx;
                        $page_inner.free.block_ids_contains_witness(free_id);
                        let i = choose |i: nat| i < $page_inner.free.len()
                            && $page_inner.free.perms@.dom().contains(i)
                            && $page_inner.free.perms@[i].2.key() == free_id;
                        $page_inner.free.entry_token_matches_metadata(i);
                        $page_inner.local_free.block_ids_contains_witness(local_id);
                        let j = choose |j: nat| j < $page_inner.local_free.len()
                            && $page_inner.local_free.perms@.dom().contains(j)
                            && $page_inner.local_free.perms@[j].2.key() == local_id;
                        $page_inner.local_free.entry_token_matches_metadata(j);
                        let tracked (free_node, free_raw, free_block, free_exposed) =
                            $page_inner.free.perms.borrow_mut().tracked_remove(i);
                        let tracked (local_node, local_raw, local_block, local_exposed) =
                            $page_inner.local_free.perms.borrow_mut().tracked_remove(j);
                        assert(free_block.key() == free_id);
                        assert(local_block.key() == local_id);
                        assert(free_block.key().page_id == local_block.key().page_id);
                        assert(free_block.key().idx == local_block.key().idx);
                        assert(free_block.instance_id() == $local.instance.id());
                        assert(local_block.instance_id() == $local.instance.id());
                        let tracked (Tracked(free_block), Tracked(local_block)) =
                            LL::owned_block_tokens_same_page_idx_impossible_retain(&$local.instance, free_block, local_block);
                        $page_inner.free.perms.borrow_mut().tracked_insert(i, (
                            free_node,
                            free_raw,
                            free_block,
                            free_exposed,
                        ));
                        $page_inner.local_free.perms.borrow_mut().tracked_insert(j, (
                            local_node,
                            local_raw,
                            local_block,
                            local_exposed,
                        ));
                        assert(false);
                    }
                    assert forall |free_id: BlockId, local_id: BlockId|
                        #[trigger] $page_inner.free.block_ids().contains(free_id)
                            && #[trigger] $page_inner.local_free.block_ids().contains(local_id)
                            && free_id.idx == local_id.idx implies false by {
                        assert(exists |free_id0: BlockId, local_id0: BlockId|
                            $page_inner.free.block_ids().contains(free_id0)
                                && $page_inner.local_free.block_ids().contains(local_id0)
                                && free_id0.idx == local_id0.idx);
                        assert(false);
                    };
                    assert($page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids())) by {
                        if !$page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids()) {
                            let block_id = choose |block_id: BlockId|
                                $page_inner.free.block_ids().contains(block_id)
                                    && $page_inner.local_free.block_ids().contains(block_id);
                            assert(false);
                        }
                    };

                    LL::two_lists_with_live_cardinality_gap(
                        &$page_inner.free,
                        &$page_inner.local_free,
                        dealloc_block_id,
                        page_state_before.num_blocks,
                    );
                    assert(local_before_inner.page_inner(page_id).free.len()
                        + local_before_inner.page_inner(page_id).local_free.len()
                        < page_state_before.num_blocks);
                    free_fast_live_block_implies_page_used(&live_block, local_before_inner);
                    assert($page_inner.used >= 1);
                }
                let ghost used_before_free = $page_inner.used;
                let ghost free_len_before = $page_inner.free.len();
                let ghost local_free_len_before = $page_inner.local_free.len();
                let ghost local_free_block_ids_before = $page_inner.local_free.block_ids();
                let ghost freed_block_id = dealloc_block_id;
                let tracked mim_block = live_block;
                proof {
                    assert(mim_block.key() == dealloc_block_id);
                    assert(!$page_inner.free.block_ids().contains(mim_block.key()));
                    assert forall |block_id: BlockId| #[trigger] $page_inner.free.block_ids().contains(block_id) implies
                        block_id.idx != mim_block.key().idx by {
                        assert(block_id.idx != dealloc_block_id.idx);
                    };
                    assert($page_inner.used >= 1);
                }

                $page_inner.free.insert_block($block_ptr, Tracked($perm), Tracked(mim_block));
                proof {
                    assert($page_inner.used == used_before_free);
                    assert($page_inner.used >= 1);
                }

                $used = $page_inner.used - 1;
                $page_inner.used = $used;

                proof {
                    reveal(PageInner::wf);
                    assert($page_inner.used == used_before_free - 1);
                    assert($page_inner.free.len() == free_len_before + 1);
                    assert($page_inner.local_free.len() == local_free_len_before);
                    assert($page_inner.local_free.block_ids() == local_free_block_ids_before);
                    assert($page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids())) by {
                        if !$page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids()) {
                            let block_id = choose |block_id: BlockId|
                                $page_inner.free.block_ids().contains(block_id)
                                    && $page_inner.local_free.block_ids().contains(block_id);
                            if block_id == freed_block_id {
                                assert(!$page_inner.local_free.block_ids().contains(freed_block_id));
                            } else {
                                assert(local_before_inner.page_inner(page_id).free.block_ids().contains(block_id));
                                assert(local_before_inner.page_inner(page_id).local_free.block_ids().contains(block_id));
                                assert(false);
                            }
                        }
                    };
                    assert($page_inner.used + $page_inner.free.len() + $page_inner.local_free.len()
                        == page_state_before.num_blocks) by(nonlinear_arith)
                        requires
                            $page_inner.used == used_before_free - 1,
                            $page_inner.free.len() == free_len_before + 1,
                            $page_inner.local_free.len() == local_free_len_before,
                            used_before_free + free_len_before + local_free_len_before
                                == page_state_before.num_blocks,
                            used_before_free >= 1;
                    assert($page_inner.wf(page_id, page_state_before, $local.instance));
                }

            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }

            proof {
                assert($local.wf_basic());
                assert($local.page_organization.popped == Popped::No);
                assert($local.thread_token.value().pages.dom().subset_of($local.pages.dom()));
                assert forall |pid: PageId| #[trigger] $local.pages.dom().contains(pid) implies
                    ($local.unused_pages.dom().contains(pid) <==>
                        !$local.thread_token.value().pages.dom().contains(pid)) by {
                    if pid == page_id {
                        assert($local.thread_token.value().pages.dom().contains(page_id));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] $local.pages.dom().contains(pid))
                    && $local.thread_token.value().pages.dom().contains(pid) implies
                        $local.pages.index(pid).wf(
                            pid,
                            $local.thread_token.value().pages.index(pid),
                            $local.instance,
                        ) by {
                    if pid == page_id {
                        assert($local.pages[pid].wf(pid, $local.thread_token.value().pages[pid], $local.instance));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] $local.pages.dom().contains(pid))
                    && $local.unused_pages.dom().contains(pid) implies
                        $local.pages.index(pid).wf_unused(pid, $local.unused_pages[pid], $local.page_organization.popped, $local.instance) by {
                    if pid == page_id {
                        assert($local.thread_token.value().pages.dom().contains(page_id));
                        assert(!$local.unused_pages.dom().contains(page_id));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |sid| #[trigger] $local.segments.dom().contains(sid) implies
                    $local.segments[sid].wf(
                        sid,
                        $local.thread_token.value().segments.index(sid),
                        $local.instance,
                    ) by {
                    assert($local.segments[sid] == local_before_inner.segments[sid]);
                };
                assert forall |sid| #[trigger] $local.segments.dom().contains(sid) implies
                    $local.mem_chunk_good(sid) by {
                    assert(local_before_inner.segments.dom().contains(sid));
                    assert(local_before_inner.mem_chunk_good(sid));
                    assert($local.segments == local_before_inner.segments);
                    assert($local.page_organization == local_before_inner.page_organization);
                    assert($local.pages.dom() == local_before_inner.pages.dom());
                    assert forall |pid: PageId| $local.page_organization.pages.dom().contains(pid) && pid != page_id implies
                        $local.pages[pid] == local_before_inner.pages[pid] by {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    };
                    assert($local.page_count(page_id) == local_before_inner.page_count(page_id));
                    assert($local.page_capacity(page_id) == local_before_inner.page_capacity(page_id));
                    assert($local.block_size(page_id) == local_before_inner.block_size(page_id));
                    $local.page_inner_update_preserves_mem_chunk_good(local_before_inner, sid, page_id);
                };
                assert($local.thread_id == $local.is_thread@);
                assert($local.checked_token.instance_id() == $local.instance.id());
                assert($local.checked_token.key() == $local.thread_id);
                assert($local.my_inst.instance_id() == $local.instance.id());
                assert($local.my_inst.value() == $local.instance.id());
                assert($local.tld.is_init());
                assert($local.page_empty_global@.wf_empty_page_global());
                assert($local.page_organization_valid());
                assert($local.wf_main());
                assert($local.wf());
                assert($local.inst() == old($local).inst());
                assert forall |heap: HeapPtr| heap.is_in(*old($local)) implies heap.is_in(*$local) by {
                    assert((*old($local)).heap_id == (*$local).heap_id);
                };
            }

        } }
    };
    ($ptr:expr, $local:ident, $page_inner:ident => {
        $popped:ident = $free_recv:ident . free . pop_block();
        $used_recv:ident . used = $used_recv2:ident . used + 1;
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = $ptr;
            let ghost page_id = page_ptr.page_id@;
            let ghost local_before_inner = *$local;
            let ghost page_state_before = $local.thread_token.value().pages[page_id];

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

            proof {
                reveal(PageInner::wf);
                assert(local_before_inner.wf());
                assert(page_state_before == local_before_inner.thread_token.value().pages[page_id]);
                assert(local_before_inner.page_inner(page_id).used == $page_inner.used);
                assert(local_before_inner.page_inner(page_id).free.len() == $page_inner.free.len());
                assert(local_before_inner.page_inner(page_id).local_free.len() == $page_inner.local_free.len());
                assert($page_inner.wf(page_id, page_state_before, $local.instance));
                assert($page_inner.free.wf());
                assert($page_inner.local_free.wf());
                assert($page_inner.free.first_addr() != 0);
                $page_inner.free.first_addr_nonzero_implies_len_positive();
            }
            let ghost used_before_alloc = $page_inner.used;
            let ghost free_len_before_alloc = $page_inner.free.len();
            let ghost local_free_len_before_alloc = $page_inner.local_free.len();

            $popped = $page_inner.free.pop_block();

            proof {
                reveal(PageInner::wf);
                assert(free_len_before_alloc > 0);
                assert($page_inner.free.len() == free_len_before_alloc - 1);
                assert(page_state_before.num_blocks <= u16::MAX) by(nonlinear_arith)
                    requires page_state_before.num_blocks == $page_inner.capacity as nat;
                assert($page_inner.used < u32::MAX) by(nonlinear_arith)
                    requires
                        $page_inner.used == used_before_alloc,
                        free_len_before_alloc > 0,
                        used_before_alloc + free_len_before_alloc + local_free_len_before_alloc
                            == page_state_before.num_blocks,
                        page_state_before.num_blocks <= u16::MAX;
            }
            $page_inner.used = $page_inner.used + 1;

            proof {
                reveal(PageInner::wf);
                assert($page_inner.used == used_before_alloc + 1);
                assert($page_inner.free.len() == free_len_before_alloc - 1);
                assert($page_inner.local_free.len() == local_free_len_before_alloc);
                assert($page_inner.used + $page_inner.free.len() + $page_inner.local_free.len()
                    == page_state_before.num_blocks) by(nonlinear_arith)
                    requires
                        $page_inner.used == used_before_alloc + 1,
                        $page_inner.free.len() == free_len_before_alloc - 1,
                        $page_inner.local_free.len() == local_free_len_before_alloc,
                        used_before_alloc + free_len_before_alloc + local_free_len_before_alloc
                            == page_state_before.num_blocks,
                        free_len_before_alloc > 0;
                assert($page_inner.wf(page_id, page_state_before, $local.instance));
            }

            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }

            proof {
                assert($local.wf_basic());
                assert($local.page_organization.popped == Popped::No);
                assert($local.thread_token.value().pages.dom().subset_of($local.pages.dom()));
                assert forall |pid: PageId| #[trigger] $local.pages.dom().contains(pid) implies
                    ($local.unused_pages.dom().contains(pid) <==>
                        !$local.thread_token.value().pages.dom().contains(pid)) by {
                    if pid == page_id {
                        assert($local.thread_token.value().pages.dom().contains(page_id));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] $local.pages.dom().contains(pid))
                    && $local.thread_token.value().pages.dom().contains(pid) implies
                        $local.pages.index(pid).wf(
                            pid,
                            $local.thread_token.value().pages.index(pid),
                            $local.instance,
                        ) by {
                    if pid == page_id {
                        assert($local.pages[pid].wf(pid, $local.thread_token.value().pages[pid], $local.instance));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] $local.pages.dom().contains(pid))
                    && $local.unused_pages.dom().contains(pid) implies
                        $local.pages.index(pid).wf_unused(pid, $local.unused_pages[pid], $local.page_organization.popped, $local.instance) by {
                    if pid == page_id {
                        assert($local.thread_token.value().pages.dom().contains(page_id));
                        assert(!$local.unused_pages.dom().contains(page_id));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |sid| #[trigger] $local.segments.dom().contains(sid) implies
                    $local.segments[sid].wf(
                        sid,
                        $local.thread_token.value().segments.index(sid),
                        $local.instance,
                    ) by {
                    assert($local.segments[sid] == local_before_inner.segments[sid]);
                };
                assert forall |sid| #[trigger] $local.segments.dom().contains(sid) implies
                    $local.mem_chunk_good(sid) by {
                    assert(local_before_inner.segments.dom().contains(sid));
                    assert(local_before_inner.mem_chunk_good(sid));
                    assert($local.segments == local_before_inner.segments);
                    assert($local.page_organization == local_before_inner.page_organization);
                    assert($local.pages.dom() == local_before_inner.pages.dom());
                    assert forall |pid: PageId| $local.page_organization.pages.dom().contains(pid) && pid != page_id implies
                        $local.pages[pid] == local_before_inner.pages[pid] by {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    };
                    assert($local.page_count(page_id) == local_before_inner.page_count(page_id));
                    assert($local.page_capacity(page_id) == local_before_inner.page_capacity(page_id));
                    assert($local.block_size(page_id) == local_before_inner.block_size(page_id));
                    $local.page_inner_update_preserves_mem_chunk_good(local_before_inner, sid, page_id);
                };
                assert($local.thread_id == $local.is_thread@);
                assert($local.checked_token.instance_id() == $local.instance.id());
                assert($local.checked_token.key() == $local.thread_id);
                assert($local.my_inst.instance_id() == $local.instance.id());
                assert($local.my_inst.value() == $local.instance.id());
                assert($local.tld.is_init());
                assert($local.page_empty_global@.wf_empty_page_global());
                assert($local.page_organization_valid());
                assert($local.wf_main());
                assert($local.wf());
                assert($local.inst() == old($local).inst());
                assert forall |heap: HeapPtr| heap.is_in(*old($local)) implies heap.is_in(*$local) by {
                    assert((*old($local)).heap_id == (*$local).heap_id);
                };
            }
        } }
    };
    ($ptr:expr, $local:ident, $page_inner:ident => {
        $zero_recv:ident . set_is_zero_init(false);
        $capacity_recv:ident . capacity = 0;
        $reserved_recv:ident . reserved = 0;
        let (Tracked($ll_state1:ident)) = $free_recv:ident . free . make_empty();
        $flags1_recv:ident . flags1 = 0;
        $flags2_recv:ident . flags2 = 0;
        $used_recv:ident . used = 0;
        $xblock_size_recv:ident . xblock_size = 0;
        let (Tracked($ll_state2:ident)) = $local_free_recv:ident . local_free . make_empty();

        let tracked ($block_pt:ident, $block_tokens:ident) = LL::reconvene_state(
            $inst:expr, &$thread_token_src:expr, $ll_state1_arg:ident, $ll_state2_arg:ident,
            $num_blocks:expr);
    }) => {
        $crate::types::page_get_mut_inner_internal!($ptr, $local, $page_inner => {
            $zero_recv.set_is_zero_init(false);
            $capacity_recv.capacity = 0;
            $reserved_recv.reserved = 0;
            let (Tracked($ll_state1)) = $free_recv.free.make_empty();
            $flags1_recv.flags1 = 0;
            $flags2_recv.flags2 = 0;
            $used_recv.used = 0;
            $xblock_size_recv.xblock_size = 0;
            let (Tracked($ll_state2)) = $local_free_recv.local_free.make_empty();

            let tracked ($block_pt, $block_tokens) = LL::reconvene_state(
                $inst, &$thread_token_src, $ll_state1_arg, $ll_state2_arg,
                $num_blocks);
        })
    };
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::page_get_mut_inner_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! page_get_mut_inner_internal {
    ($ptr:expr, $local:ident, $page_inner:ident => {
        $zero_recv:ident . set_is_zero_init(false);
        $capacity_recv:ident . capacity = 0;
        $reserved_recv:ident . reserved = 0;
        let (Tracked($ll_state1:ident)) = $free_recv:ident . free . make_empty();
        $flags1_recv:ident . flags1 = 0;
        $flags2_recv:ident . flags2 = 0;
        $used_recv:ident . used = 0;
        $xblock_size_recv:ident . xblock_size = 0;
        let (Tracked($ll_state2:ident)) = $local_free_recv:ident . local_free . make_empty();

        let tracked ($block_pt:ident, $block_tokens:ident) = LL::reconvene_state(
            $inst:expr, &$thread_token_src:expr, $ll_state1_arg:ident, $ll_state2_arg:ident,
            $num_blocks:expr);
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = $ptr;
            let ghost page_id = page_ptr.page_id@;

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

            proof {
                reveal(PageInner::wf);
                assert($page_inner.free.page_id() == page_id);
                assert($page_inner.local_free.page_id() == page_id);
                assert($page_inner.free.instance() == $local.instance);
                assert($page_inner.local_free.instance() == $local.instance);
            }
            $page_inner.set_is_zero_init(false);
            $page_inner.capacity = 0;
            $page_inner.reserved = 0;
            let (Tracked($ll_state1)) = $page_inner.free.make_empty();
            $page_inner.flags1 = 0;
            $page_inner.flags2 = 0;
            $page_inner.used = 0;
            $page_inner.xblock_size = 0;
            let (Tracked($ll_state2)) = $page_inner.local_free.make_empty();
            proof {
                assert($ll_state1.page_id == page_id);
                assert($ll_state2.page_id == page_id);
                assert($ll_state1.instance == $local.instance);
                assert($ll_state2.instance == $local.instance);
            }

            let tracked ($block_pt, $block_tokens) = LL::reconvene_state(
                $inst, &$thread_token_src, $ll_state1_arg, $ll_state2_arg,
                $num_blocks);
            proof {
                let ghost page_clear_block_size = $ll_state1.block_size as int;
                let ghost page_clear_block_range = set_int_range(
                    page_start(page_id) + start_offset(page_clear_block_size),
                    page_start(page_id) + start_offset(page_clear_block_size)
                        + $num_blocks * page_clear_block_size);
                assert($block_pt.dom() == page_clear_block_range);
                let tracked mut page_clear_segment = $local.segments.tracked_remove(page_id.segment_id);
                let tracked empty_os = Map::<int, $crate::os_mem::OsMem>::tracked_empty();
                let tracked block_mem = $crate::os_mem::MemChunk { os: empty_os, points_to: $block_pt };
                page_clear_segment.mem.join(block_mem);
                $local.segments.tracked_insert(page_id.segment_id, page_clear_segment);
                assert(page_clear_block_range <= $local.segments[page_id.segment_id].mem.points_to.dom());
            }
            proof {
                let tracked page_clear_thread_token = $local.take_thread_token();
                let tracked page_clear_block_tokens =
                    ::vstd::tokens::MapToken::<$crate::tokens::BlockId, $crate::tokens::BlockState, $crate::tokens::Mim::block>::from_map(
                        $local.instance.id(), $block_tokens);
                let ghost page_clear_block_states = page_clear_block_tokens.map();
                let tracked page_clear_thread_token0 = $local.instance.page_destroy_block_tokens(
                    $local.thread_id, page_id, page_clear_block_states, page_clear_thread_token, page_clear_block_tokens);
                $local.thread_token = page_clear_thread_token0;
                assert($local.thread_token.instance_id() == $local.instance.id());
                assert($local.thread_token.key() == $local.thread_id);
                assert($local.thread_token.value().pages.dom().contains(page_id));
                assert($local.thread_token.value().pages[page_id].is_enabled);
                assert($local.thread_token.value().pages[page_id].num_blocks == 0);
            }

            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }

        } }
    };
    ($ptr:expr, $local:ident, $page_inner:ident => {
        let tracked mim_block = $dealloc:ident . mim_block;
        $receiver:ident . free . insert_block($block_ptr:expr, Tracked($perm:ident), Tracked(mim_block));
        $used:ident = $receiver2:ident . used - 1;
        $receiver3:ident . used = $used_again:ident;
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = $ptr;
            let ghost page_id = page_ptr.page_id@;
            let ghost local_before_inner = *$local;
            let ghost page_state_before = $local.thread_token.value().pages[page_id];

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

                let tracked $crate::dealloc_token::MimDeallocInner { mim_instance: dealloc_mim_instance, mim_block: mut live_block, ptr: dealloc_ptr } = $dealloc;
                let ghost dealloc_block_id = live_block.key();
                proof {
                    reveal(PageInner::wf);
                    assert($crate::dealloc_token::valid_block_token(live_block, dealloc_mim_instance));

                    assert(local_before_inner.wf());
                    assert(page_state_before == local_before_inner.thread_token.value().pages[page_id]);
                    assert(local_before_inner.page_inner(page_id).used == $page_inner.used);
                    assert(local_before_inner.page_inner(page_id).free.len() == $page_inner.free.len());
                    assert(local_before_inner.page_inner(page_id).local_free.len() == $page_inner.local_free.len());
                    assert($page_inner.wf(page_id, page_state_before, $local.instance));
                    assert($page_inner.free.wf());
                    assert($page_inner.local_free.wf());

                    assert(dealloc_block_id.page_id == page_id);
                    assert(dealloc_block_id.idx < page_state_before.num_blocks);
                    assert(live_block.instance_id() == $local.instance.id());

                    if exists |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                        && !(block_id.idx < page_state_before.num_blocks) {
                        let bad_id = choose |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                            && !(block_id.idx < page_state_before.num_blocks);
                        $page_inner.free.block_ids_contains_witness(bad_id);
                        let i = choose |i: nat| i < $page_inner.free.len()
                            && $page_inner.free.perms@.dom().contains(i)
                            && $page_inner.free.perms@[i].2.key() == bad_id;
                        $page_inner.free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == bad_id);
                        assert(entry_block.instance_id() == $local.instance.id());
                        free_fast_block_token_idx_lt_num_blocks(
                            &$local.instance,
                            &$local.thread_token,
                            $local.thread_id,
                            &entry_block,
                            page_state_before.num_blocks,
                        );
                        $page_inner.free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.free.block_ids().contains(block_id) implies
                        block_id.idx < page_state_before.num_blocks by {
                        if !(block_id.idx < page_state_before.num_blocks) {
                            assert(exists |bad_id: BlockId| $page_inner.free.block_ids().contains(bad_id)
                                && !(bad_id.idx < page_state_before.num_blocks));
                            assert(false);
                        }
                    };
                    if exists |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                        && !(block_id.idx < page_state_before.num_blocks) {
                        let bad_id = choose |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                            && !(block_id.idx < page_state_before.num_blocks);
                        $page_inner.local_free.block_ids_contains_witness(bad_id);
                        let i = choose |i: nat| i < $page_inner.local_free.len()
                            && $page_inner.local_free.perms@.dom().contains(i)
                            && $page_inner.local_free.perms@[i].2.key() == bad_id;
                        $page_inner.local_free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.local_free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == bad_id);
                        assert(entry_block.instance_id() == $local.instance.id());
                        free_fast_block_token_idx_lt_num_blocks(
                            &$local.instance,
                            &$local.thread_token,
                            $local.thread_id,
                            &entry_block,
                            page_state_before.num_blocks,
                        );
                        $page_inner.local_free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.local_free.block_ids().contains(block_id) implies
                        block_id.idx < page_state_before.num_blocks by {
                        if !(block_id.idx < page_state_before.num_blocks) {
                            assert(exists |bad_id: BlockId| $page_inner.local_free.block_ids().contains(bad_id)
                                && !(bad_id.idx < page_state_before.num_blocks));
                            assert(false);
                        }
                    };

                    if exists |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                        && block_id.idx == dealloc_block_id.idx {
                        let collision_id = choose |block_id: BlockId| $page_inner.free.block_ids().contains(block_id)
                            && block_id.idx == dealloc_block_id.idx;
                        $page_inner.free.block_ids_contains_witness(collision_id);
                        let i = choose |i: nat| i < $page_inner.free.len()
                            && $page_inner.free.perms@.dom().contains(i)
                            && $page_inner.free.perms@[i].2.key() == collision_id;
                        $page_inner.free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == collision_id);
                        assert(entry_block.key().page_id == dealloc_block_id.page_id);
                        assert(entry_block.key().idx == dealloc_block_id.idx);
                        assert(entry_block.instance_id() == $local.instance.id());
                        let tracked (Tracked(entry_block), Tracked(returned_live_block)) =
                            LL::owned_block_tokens_same_page_idx_impossible_retain(&$local.instance, entry_block, live_block);
                        $page_inner.free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        live_block = returned_live_block;
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.free.block_ids().contains(block_id) implies
                        block_id.idx != dealloc_block_id.idx by {
                        if block_id.idx == dealloc_block_id.idx {
                            assert(exists |collision_id: BlockId| $page_inner.free.block_ids().contains(collision_id)
                                && collision_id.idx == dealloc_block_id.idx);
                            assert(false);
                        }
                    };
                    assert(!$page_inner.free.block_ids().contains(dealloc_block_id));

                    if exists |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                        && block_id.idx == dealloc_block_id.idx {
                        let collision_id = choose |block_id: BlockId| $page_inner.local_free.block_ids().contains(block_id)
                            && block_id.idx == dealloc_block_id.idx;
                        $page_inner.local_free.block_ids_contains_witness(collision_id);
                        let i = choose |i: nat| i < $page_inner.local_free.len()
                            && $page_inner.local_free.perms@.dom().contains(i)
                            && $page_inner.local_free.perms@[i].2.key() == collision_id;
                        $page_inner.local_free.entry_token_matches_metadata(i);
                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                            $page_inner.local_free.perms.borrow_mut().tracked_remove(i);
                        assert(entry_block.key() == collision_id);
                        assert(entry_block.key().page_id == dealloc_block_id.page_id);
                        assert(entry_block.key().idx == dealloc_block_id.idx);
                        assert(entry_block.instance_id() == $local.instance.id());
                        let tracked (Tracked(entry_block), Tracked(returned_live_block)) =
                            LL::owned_block_tokens_same_page_idx_impossible_retain(&$local.instance, entry_block, live_block);
                        $page_inner.local_free.perms.borrow_mut().tracked_insert(i, (
                            entry_node,
                            entry_raw,
                            entry_block,
                            entry_exposed,
                        ));
                        live_block = returned_live_block;
                        assert(false);
                    }
                    assert forall |block_id: BlockId| #[trigger] $page_inner.local_free.block_ids().contains(block_id) implies
                        block_id.idx != dealloc_block_id.idx by {
                        if block_id.idx == dealloc_block_id.idx {
                            assert(exists |collision_id: BlockId| $page_inner.local_free.block_ids().contains(collision_id)
                                && collision_id.idx == dealloc_block_id.idx);
                            assert(false);
                        }
                    };
                    assert(!$page_inner.local_free.block_ids().contains(dealloc_block_id));

                    if exists |free_id: BlockId, local_id: BlockId|
                        #[trigger] $page_inner.free.block_ids().contains(free_id)
                            && #[trigger] $page_inner.local_free.block_ids().contains(local_id)
                            && free_id.idx == local_id.idx {
                        let free_id = choose |free_id: BlockId| exists |local_id: BlockId|
                            #[trigger] $page_inner.free.block_ids().contains(free_id)
                                && #[trigger] $page_inner.local_free.block_ids().contains(local_id)
                                && free_id.idx == local_id.idx;
                        let local_id = choose |local_id: BlockId|
                            $page_inner.free.block_ids().contains(free_id)
                                && $page_inner.local_free.block_ids().contains(local_id)
                                && free_id.idx == local_id.idx;
                        $page_inner.free.block_ids_contains_witness(free_id);
                        let i = choose |i: nat| i < $page_inner.free.len()
                            && $page_inner.free.perms@.dom().contains(i)
                            && $page_inner.free.perms@[i].2.key() == free_id;
                        $page_inner.free.entry_token_matches_metadata(i);
                        $page_inner.local_free.block_ids_contains_witness(local_id);
                        let j = choose |j: nat| j < $page_inner.local_free.len()
                            && $page_inner.local_free.perms@.dom().contains(j)
                            && $page_inner.local_free.perms@[j].2.key() == local_id;
                        $page_inner.local_free.entry_token_matches_metadata(j);
                        let tracked (free_node, free_raw, free_block, free_exposed) =
                            $page_inner.free.perms.borrow_mut().tracked_remove(i);
                        let tracked (local_node, local_raw, local_block, local_exposed) =
                            $page_inner.local_free.perms.borrow_mut().tracked_remove(j);
                        assert(free_block.key() == free_id);
                        assert(local_block.key() == local_id);
                        assert(free_block.key().page_id == local_block.key().page_id);
                        assert(free_block.key().idx == local_block.key().idx);
                        assert(free_block.instance_id() == $local.instance.id());
                        assert(local_block.instance_id() == $local.instance.id());
                        let tracked (Tracked(free_block), Tracked(local_block)) =
                            LL::owned_block_tokens_same_page_idx_impossible_retain(&$local.instance, free_block, local_block);
                        $page_inner.free.perms.borrow_mut().tracked_insert(i, (
                            free_node,
                            free_raw,
                            free_block,
                            free_exposed,
                        ));
                        $page_inner.local_free.perms.borrow_mut().tracked_insert(j, (
                            local_node,
                            local_raw,
                            local_block,
                            local_exposed,
                        ));
                        assert(false);
                    }
                    assert forall |free_id: BlockId, local_id: BlockId|
                        #[trigger] $page_inner.free.block_ids().contains(free_id)
                            && #[trigger] $page_inner.local_free.block_ids().contains(local_id)
                            && free_id.idx == local_id.idx implies false by {
                        assert(exists |free_id0: BlockId, local_id0: BlockId|
                            $page_inner.free.block_ids().contains(free_id0)
                                && $page_inner.local_free.block_ids().contains(local_id0)
                                && free_id0.idx == local_id0.idx);
                        assert(false);
                    };
                    assert($page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids())) by {
                        if !$page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids()) {
                            let block_id = choose |block_id: BlockId|
                                $page_inner.free.block_ids().contains(block_id)
                                    && $page_inner.local_free.block_ids().contains(block_id);
                            assert(false);
                        }
                    };

                    LL::two_lists_with_live_cardinality_gap(
                        &$page_inner.free,
                        &$page_inner.local_free,
                        dealloc_block_id,
                        page_state_before.num_blocks,
                    );
                    assert(local_before_inner.page_inner(page_id).free.len()
                        + local_before_inner.page_inner(page_id).local_free.len()
                        < page_state_before.num_blocks);
                    free_fast_live_block_implies_page_used(&live_block, local_before_inner);
                    assert($page_inner.used >= 1);
                }
                let ghost used_before_free = $page_inner.used;
                let ghost free_len_before = $page_inner.free.len();
                let ghost local_free_len_before = $page_inner.local_free.len();
                let ghost local_free_block_ids_before = $page_inner.local_free.block_ids();
                let ghost freed_block_id = dealloc_block_id;
                let tracked mim_block = live_block;
                proof {
                    assert(mim_block.key() == dealloc_block_id);
                    assert(!$page_inner.free.block_ids().contains(mim_block.key()));
                    assert forall |block_id: BlockId| #[trigger] $page_inner.free.block_ids().contains(block_id) implies
                        block_id.idx != mim_block.key().idx by {
                        assert(block_id.idx != dealloc_block_id.idx);
                    };
                    assert($page_inner.used >= 1);
                }

                $page_inner.free.insert_block($block_ptr, Tracked($perm), Tracked(mim_block));
                proof {
                    assert($page_inner.used == used_before_free);
                    assert($page_inner.used >= 1);
                }

                $used = $page_inner.used - 1;
                $page_inner.used = $used;

                proof {
                    reveal(PageInner::wf);
                    assert($page_inner.used == used_before_free - 1);
                    assert($page_inner.free.len() == free_len_before + 1);
                    assert($page_inner.local_free.len() == local_free_len_before);
                    assert($page_inner.local_free.block_ids() == local_free_block_ids_before);
                    assert($page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids())) by {
                        if !$page_inner.free.block_ids().disjoint($page_inner.local_free.block_ids()) {
                            let block_id = choose |block_id: BlockId|
                                $page_inner.free.block_ids().contains(block_id)
                                    && $page_inner.local_free.block_ids().contains(block_id);
                            if block_id == freed_block_id {
                                assert(!$page_inner.local_free.block_ids().contains(freed_block_id));
                            } else {
                                assert(local_before_inner.page_inner(page_id).free.block_ids().contains(block_id));
                                assert(local_before_inner.page_inner(page_id).local_free.block_ids().contains(block_id));
                                assert(false);
                            }
                        }
                    };
                    assert($page_inner.used + $page_inner.free.len() + $page_inner.local_free.len()
                        == page_state_before.num_blocks) by(nonlinear_arith)
                        requires
                            $page_inner.used == used_before_free - 1,
                            $page_inner.free.len() == free_len_before + 1,
                            $page_inner.local_free.len() == local_free_len_before,
                            used_before_free + free_len_before + local_free_len_before
                                == page_state_before.num_blocks,
                            used_before_free >= 1;
                    assert($page_inner.wf(page_id, page_state_before, $local.instance));
                }

            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }

            proof {
                assert($local.wf_basic());
                assert($local.page_organization.popped == Popped::No);
                assert($local.thread_token.value().pages.dom().subset_of($local.pages.dom()));
                assert forall |pid: PageId| #[trigger] $local.pages.dom().contains(pid) implies
                    ($local.unused_pages.dom().contains(pid) <==>
                        !$local.thread_token.value().pages.dom().contains(pid)) by {
                    if pid == page_id {
                        assert($local.thread_token.value().pages.dom().contains(page_id));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] $local.pages.dom().contains(pid))
                    && $local.thread_token.value().pages.dom().contains(pid) implies
                        $local.pages.index(pid).wf(
                            pid,
                            $local.thread_token.value().pages.index(pid),
                            $local.instance,
                        ) by {
                    if pid == page_id {
                        assert($local.pages[pid].wf(pid, $local.thread_token.value().pages[pid], $local.instance));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |pid: PageId| (#[trigger] $local.pages.dom().contains(pid))
                    && $local.unused_pages.dom().contains(pid) implies
                        $local.pages.index(pid).wf_unused(pid, $local.unused_pages[pid], $local.page_organization.popped, $local.instance) by {
                    if pid == page_id {
                        assert($local.thread_token.value().pages.dom().contains(page_id));
                        assert(!$local.unused_pages.dom().contains(page_id));
                    } else {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    }
                };
                assert forall |sid| #[trigger] $local.segments.dom().contains(sid) implies
                    $local.segments[sid].wf(
                        sid,
                        $local.thread_token.value().segments.index(sid),
                        $local.instance,
                    ) by {
                    assert($local.segments[sid] == local_before_inner.segments[sid]);
                };
                assert forall |sid| #[trigger] $local.segments.dom().contains(sid) implies
                    $local.mem_chunk_good(sid) by {
                    assert(local_before_inner.segments.dom().contains(sid));
                    assert(local_before_inner.mem_chunk_good(sid));
                    assert($local.segments == local_before_inner.segments);
                    assert($local.page_organization == local_before_inner.page_organization);
                    assert($local.pages.dom() == local_before_inner.pages.dom());
                    assert forall |pid: PageId| $local.page_organization.pages.dom().contains(pid) && pid != page_id implies
                        $local.pages[pid] == local_before_inner.pages[pid] by {
                        assert($local.pages[pid] == local_before_inner.pages[pid]);
                    };
                    assert($local.page_count(page_id) == local_before_inner.page_count(page_id));
                    assert($local.page_capacity(page_id) == local_before_inner.page_capacity(page_id));
                    assert($local.block_size(page_id) == local_before_inner.block_size(page_id));
                    $local.page_inner_update_preserves_mem_chunk_good(local_before_inner, sid, page_id);
                };
                assert($local.thread_id == $local.is_thread@);
                assert($local.checked_token.instance_id() == $local.instance.id());
                assert($local.checked_token.key() == $local.thread_id);
                assert($local.my_inst.instance_id() == $local.instance.id());
                assert($local.my_inst.value() == $local.instance.id());
                assert($local.tld.is_init());
                assert($local.page_empty_global@.wf_empty_page_global());
                assert($local.page_organization_valid());
                assert($local.wf_main());
                assert($local.wf());
                assert($local.inst() == old($local).inst());
                assert forall |heap: HeapPtr| heap.is_in(*old($local)) implies heap.is_in(*$local) by {
                    assert((*old($local)).heap_id == (*$local).heap_id);
                };
            }

        } }
    };
    ($ptr:expr, $local:ident, $page_inner:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                    $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

            { $body }

            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }

        } }
    }
}

pub use page_get_mut_inner;
pub use page_get_mut_inner_internal;

#[macro_export]
macro_rules! unused_page_get_mut_prev {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_prev_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_prev_internal {
    ($ptr:expr, $local:ident, $page_prev:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: mut prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_prev = page.prev.read(Tracked(&mut prev_0));

            { $body }

            page.prev.write(Tracked(&mut prev_0), $page_prev);
            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }
        } }
    }
}

pub use unused_page_get_mut_prev;
pub use unused_page_get_mut_prev_internal;

#[macro_export]
macro_rules! unused_page_get_mut_inner {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_inner_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_inner_internal {
    ($ptr:expr, $local:ident, $page_inner:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: mut inner_0, prev: prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_inner = page.inner.borrow_mut(Tracked(&mut inner_0));

            { $body }

            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }

        } }
    }
}

pub use unused_page_get_mut_inner;
pub use unused_page_get_mut_inner_internal;


#[macro_export]
macro_rules! unused_page_get_mut_next {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_next_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_next_internal {
    ($ptr:expr, $local:ident, $page_next:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: mut next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_next = page.next.read(Tracked(&mut next_0));

            { $body }

            page.next.write(Tracked(&mut next_0), $page_next);
            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }
        } }
    }
}

pub use unused_page_get_mut_next;
pub use unused_page_get_mut_next_internal;

#[macro_export]
macro_rules! unused_page_get_mut_count {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_count_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_count_internal {
    ($ptr:expr, $local:ident, $page_count:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked perm = &$local.unused_pages.tracked_borrow(page_ptr.page_id@).points_to;
            let page = ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: mut count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_count = page.count.read(Tracked(&mut count_0));

            { $body }

            page.count.write(Tracked(&mut count_0), $page_count);
            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }
        } }
    }
}

pub use unused_page_get_mut_count;
pub use unused_page_get_mut_count_internal;


#[macro_export]
macro_rules! unused_page_get_mut {
    ($ptr:expr, $local:ident, $page:ident => {
        let Tracked($delay_token:ident) = $delay_recv:ident . xthread_free . disable();
        let Tracked($heap_of_page_token:ident) = $heap_recv:ident . xheap . disable();
    }) => {
        $crate::types::unused_page_get_mut_internal!($ptr, $local, $page => {
            let Tracked($delay_token) = $delay_recv.xthread_free.disable();
            let Tracked($heap_of_page_token) = $heap_recv.xheap.disable();
        })
    };
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::unused_page_get_mut_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! unused_page_get_mut_internal {
    ($ptr:expr, $local:ident, $page:ident => {
        let Tracked($delay_token:ident) = $delay_recv:ident . xthread_free . disable();
        let Tracked($heap_of_page_token:ident) = $heap_recv:ident . xheap . disable();
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            let ghost page_id = page_ptr.page_id@;
            let ghost n_slices = $local.page_organization.pages[page_id].count.unwrap();
            let ghost next_state = PageOrg::take_step::set_range_to_not_used($local.page_organization);

            proof {
                assert($local.page_organization.invariant());
                assert($local.page_organization.popped.is_Used());
                $local.page_organization.used_popped_range_facts();
                assert(n_slices > 0);
                assert($local.thread_token.value().pages.dom().contains(page_id));
                assert($local.thread_token.value().pages[page_id].is_enabled);
                assert($local.thread_token.value().pages[page_id].num_blocks == 0);
                assert($local.checked_token.value().pages.contains(page_id));
                assert(page_id.range_from(0, n_slices as int).subset_of($local.thread_token.value().pages.dom()));
                assert forall |pid: PageId|
                    #[trigger] page_id.range_from(0, n_slices as int).contains(pid)
                implies
                    $local.thread_token.value().pages.dom().contains(pid)
                    && $local.thread_token.value().pages[pid].is_enabled
                    && $local.thread_token.value().pages[pid].offset == pid.idx - page_id.idx
                by { }
                let tracked page_clear_thread_token = $local.take_thread_token();
                let tracked (Tracked(page_clear_thread_token0), Tracked(page_shared_access)) = $local.instance.page_disable(
                    $local.thread_id, page_id, n_slices, page_clear_thread_token, &$local.checked_token);
                $local.thread_token = page_clear_thread_token0;
                $local.unused_pages.tracked_union_prefer_right(page_shared_access);
                $local.page_organization = next_state;
            }

            let tracked psa = $local.unused_pages.tracked_remove(page_ptr.page_id@);
            let tracked PageSharedAccess { points_to: mut points_to, exposed } = psa;
            let mut $page = vstd::raw_ptr::ptr_mut_read(page_ptr.page_ptr, Tracked(&mut points_to));

            let Tracked($delay_token) = $page.xthread_free.disable();
            let Tracked($heap_of_page_token) = $page.xheap.disable();
            proof {
                assert($page.xthread_free.wf());
                assert($page.xthread_free.is_empty());
                assert($page.xthread_free.instance == $local.instance);
                assert($page.wf_unused($local.instance));
                assert(n_slices >= 1);
                assert(page_id.range_from(0, n_slices as int).subset_of($local.thread_token.value().pages.dom()));
                assert forall |pid: PageId|
                    #[trigger] page_id.range_from(0, n_slices as int).contains(pid)
                implies
                    !$local.thread_token.value().pages[pid].is_enabled
                by { }
                assert forall |pid: PageId|
                    #[trigger] page_id.range_from(0, n_slices as int).contains(pid)
                implies
                    page_id != pid ==> $local.thread_token.value().pages[pid].offset != 0
                by {
                    if page_id != pid {
                        assert(page_id.idx <= pid.idx < page_id.idx + n_slices);
                        assert(pid.idx != page_id.idx);
                        assert($local.thread_token.value().pages[pid].offset == pid.idx - page_id.idx);
                    }
                }
                let tracked page_clear_thread_token = $local.take_thread_token();
                let tracked page_clear_thread_token0 = $local.instance.page_destroy_tokens(
                    $local.thread_id, page_id, n_slices, page_clear_thread_token, $delay_token, $heap_of_page_token);
                $local.thread_token = page_clear_thread_token0;
            }

            vstd::raw_ptr::ptr_mut_write(page_ptr.page_ptr, Tracked(&mut points_to), $page);
            let tracked page_shared = PageSharedAccess { points_to, exposed };
            proof {
                $local.unused_pages.tracked_insert(page_ptr.page_id@, page_shared);
            }
        } }
    };
    ($ptr:expr, $local:ident, $page:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);

            let tracked psa = $local.unused_pages.tracked_remove(page_ptr.page_id@);
            let tracked PageSharedAccess { points_to: mut points_to, exposed } = psa;
            let mut $page = vstd::raw_ptr::ptr_mut_read(page_ptr.page_ptr, Tracked(&mut points_to));

            { $body }

            vstd::raw_ptr::ptr_mut_write(page_ptr.page_ptr, Tracked(&mut points_to), $page);
            let tracked page_shared = PageSharedAccess { points_to, exposed };
            proof {
                $local.unused_pages.tracked_insert(page_ptr.page_id@, page_shared);
            }
        } }
    }
}

pub use unused_page_get_mut;
pub use unused_page_get_mut_internal;


#[macro_export]
macro_rules! used_page_get_mut_prev {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::used_page_get_mut_prev_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! used_page_get_mut_prev_internal {
    ($ptr:expr, $local:ident, $page_prev:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: mut prev_0, next: next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_prev = page.prev.read(Tracked(&mut prev_0));

            { $body }

            page.prev.write(Tracked(&mut prev_0), $page_prev);
            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }
        } }
    }
}

pub use used_page_get_mut_prev;
pub use used_page_get_mut_prev_internal;

#[macro_export]
macro_rules! heap_get_pages {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::heap_get_pages_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! heap_get_pages_internal {
    ($ptr:expr, $local:ident, $pages:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let heap_ptr = ($ptr);

            let tracked perm = &$local.instance.thread_local_state_guards_heap(
                $local.thread_id, &$local.thread_token).points_to;
            let heap = vstd::raw_ptr::ptr_ref(heap_ptr.heap_ptr, Tracked(perm));
            let mut $pages = heap.pages.read(Tracked(&mut $local.heap.pages));

            { $body }

            heap.pages.write(Tracked(&mut $local.heap.pages), $pages);
        } }
    }
}

pub use heap_get_pages;
pub use heap_get_pages_internal;

#[macro_export]
macro_rules! heap_get_pages_free_direct {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::heap_get_pages_free_direct_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! heap_get_pages_free_direct_internal {
    ($ptr:expr, $local:ident, $pages_free_direct:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let heap_ptr = ($ptr);

            let tracked perm = &$local.instance.thread_local_state_guards_heap(
                $local.thread_id, &$local.thread_token).points_to;
            let heap = vstd::raw_ptr::ptr_ref(heap_ptr.heap_ptr, Tracked(perm));
            let mut $pages_free_direct = heap.pages_free_direct.read(Tracked(&mut $local.heap.pages_free_direct));

            { $body }

            let mut $pages_free_direct = heap.pages_free_direct.write(Tracked(&mut $local.heap.pages_free_direct), $pages_free_direct);
        } }
    }
}

pub use heap_get_pages_free_direct;
pub use heap_get_pages_free_direct_internal;



#[macro_export]
macro_rules! used_page_get_mut_next {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::used_page_get_mut_next_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! used_page_get_mut_next_internal {
    ($ptr:expr, $local:ident, $page_next:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let page_ptr = ($ptr);
            assert(page_ptr.wf());

            let tracked perm = &$local.instance.thread_local_state_guards_page(
                $local.thread_id, page_ptr.page_id@, &$local.thread_token).points_to;
            let page = vstd::raw_ptr::ptr_ref(page_ptr.page_ptr, Tracked(perm));

            let tracked PageLocalAccess { inner: inner_0, prev: prev_0, next: mut next_0, count: count_0 } =
                $local.pages.tracked_remove(page_ptr.page_id@);
            let mut $page_next = page.next.read(Tracked(&mut next_0));

            { $body }

            page.next.write(Tracked(&mut next_0), $page_next);
            let tracked page_local =
                PageLocalAccess { inner: inner_0, prev: prev_0, next: next_0, count: count_0 };
            proof {
                $local.pages.tracked_insert(page_ptr.page_id@, page_local);
            }
        } }
    }
}

pub use used_page_get_mut_next;
pub use used_page_get_mut_next_internal;

#[verus::trusted]
#[verifier::external_body]
pub fn print_hex(s: &'static str, u: usize)
{
    println!("{:} {:x}", s, u);
}

#[verus::trusted]
#[cfg(feature = "override_system_allocator")]
#[verifier::external_body]
pub fn todo()
    ensures false
{
    std::process::abort();
}

#[verus::trusted]
#[cfg(not(feature = "override_system_allocator"))]
#[verifier::external_body]
pub fn todo()
    ensures false
{
    panic!("todo");
}

#[macro_export]
macro_rules! segment_get_mut_main {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_main_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_main_internal {
    ($ptr:expr, $local:ident, $segment_main:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked SegmentLocalAccess { main: mut main_0, mem: mem_0, main2: main2_0 } =
                $local.segments.tracked_remove(segment_ptr.segment_id@);
            {
                let mut $segment_main = segment.main.borrow_mut(Tracked(&mut main_0));
                { $body }
            }
            let tracked segment_local =
                SegmentLocalAccess { main: main_0, mem: mem_0, main2: main2_0 };
            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, segment_local);
            }

        } }
    }
}

pub use segment_get_mut_main;
pub use segment_get_mut_main_internal;

#[macro_export]
macro_rules! segment_get_mut_main2 {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_main2_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_main2_internal {
    ($ptr:expr, $local:ident, $segment_main2:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked SegmentLocalAccess { main: main_0, mem: mem_0, main2: mut main2_0 } =
                $local.segments.tracked_remove(segment_ptr.segment_id@);
            {
                let mut $segment_main2 = segment.main2.borrow_mut(Tracked(&mut main2_0));
                { $body }
            }
            let tracked segment_local =
                SegmentLocalAccess { main: main_0, mem: mem_0, main2: main2_0 };
            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, segment_local);
            }

        } }
    }
}

pub use segment_get_mut_main2;
pub use segment_get_mut_main2_internal;

#[macro_export]
macro_rules! segment_get_mut_local {
    [$($tail:tt)*] => {
        ::vstd::prelude::verus_exec_macro_exprs!(
            $crate::types::segment_get_mut_local_internal!($($tail)*))
    };
}

#[macro_export]
macro_rules! segment_get_mut_local_internal {
    ($ptr:expr, $local:ident, $segment_local:ident => $body:expr) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let segment_ptr = $ptr;

            let tracked perm = &$local.instance.thread_local_state_guards_segment(
                    $local.thread_id, segment_ptr.segment_id@, &$local.thread_token).points_to;
            let segment = vstd::raw_ptr::ptr_ref(segment_ptr.segment_ptr, Tracked(perm));

            let tracked mut $segment_local =
                $local.segments.tracked_remove(segment_ptr.segment_id@);

            { $body }
            proof {
                $local.segments.tracked_insert(segment_ptr.segment_id@, $segment_local);
            }

        } }
    }
}

pub use segment_get_mut_local;
pub use segment_get_mut_local_internal;


}
