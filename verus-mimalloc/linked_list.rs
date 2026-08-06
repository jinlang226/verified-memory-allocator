#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::set_lib::*;
use vstd::layout::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, PageId, DelayState, HeapId};
use crate::layout::{is_block_ptr, block_size_ge_word, block_ptr_aligned_to_word, block_start_at, block_start, is_block_ptr1};
use crate::types::*;
use crate::config::INTPTR_SIZE;
use core::intrinsics::unlikely;

verus!{

// Originally I wanted to do a linked list here in the proper Rust-idiomatic
// way, something like:
//
//    struct LL { next: Option<Box<LL>> }
//
// However, there were a couple of problems:
//
//  1. We need to pad each node out to the block size, which isn't statically fixed.
//     This problem isn't too hard to work around though, we just need to make our
//     own Box-like type that manages the size of the allocation.
//
//  2. Because of the way the thread-safe atomic linked list works, we need to
//     split the 'ownership' from the 'physical pointer', so we can write the pointer 
//     into a node without the ownership.
//
// Problem (2) seems more annoying to work around. At any rate, I've decided to just
// give up on the recursive datatype and do a flat list of pointers and pointer permissions.

#[repr(C)]
#[derive(Copy)]
pub struct Node {
    pub ptr: *mut Node,
}

impl Clone for Node {
    #[verifier::external_body]
    fn clone(&self) -> Node
    {
        unimplemented!()
    }
}

global layout Node is size == 8, align == 8;

#[verifier::external_body]
pub proof fn size_of_node()
    ensures size_of::<Node>() == 8
        && align_of::<Node>() == 8
{
    unimplemented!()
}

pub ghost struct LLData {
    ghost fixed_page: bool,
    ghost block_size: nat,   // only used if fixed_page=true
    ghost page_id: PageId,   // only used if fixed_page=true
    ghost heap_id: Option<HeapId>, // if set, then all blocks must have this HeapId

    ghost instance: Mim::Instance,
    ghost len: nat,
}

pub struct LL {
    first: *mut Node,

    data: Ghost<LLData>,

    // first to be popped off goes at the end
    perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>,
}

pub tracked struct LLGhostStateToReconvene {
    pub ghost block_size: nat,
    pub ghost page_id: PageId,
    pub ghost instance: Mim::Instance,

    pub tracked map: Map<nat, (PointsToRaw, Mim::block)>,
}

impl LL {
    pub closed spec fn next_ptr(&self, i: nat) -> *mut Node {
        if i == 0 {
            core::ptr::null_mut()
        } else {
            self.perms@.index((i - 1) as nat).0.ptr()
        }
    }

    pub closed spec fn valid_node(&self, i: nat, next_ptr: *mut Node) -> bool {
        0 <= i < self.data@.len ==> (
            self.perms@.dom().contains(i) && {
                  let (perm, padding, block_token, is_exposed) = self.perms@.index(i);

                  // Each node points to the next node
                  perm.is_init()
                  && perm.value().ptr.addr() == next_ptr.addr()

                  // The PointsToRaw makes up the rest of the block size allocation
                  && block_token.key().block_size - size_of::<Node>() >= 0
                  && padding.is_range(perm.ptr().addr() + size_of::<Node>(),
                      block_token.key().block_size - size_of::<Node>())
                  && padding.provenance() == perm.ptr()@.provenance
                  && is_exposed.provenance() == padding.provenance()

                  // block_token is correct
                  && block_token.instance_id() == self.data@.instance.id()
                  && is_block_ptr(perm.ptr() as *mut u8, block_token.key())

                  && (self.data@.fixed_page ==> (
                      block_token.key().page_id == self.data@.page_id
                      && block_token.key().block_size == self.data@.block_size
                      //&& padding.provenance() == self.data@.page_id.segment_id.provenance
                  ))

                  && (match self.data@.heap_id {
                      Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                      None => true,
                  })
            }
        )
    }

    pub closed spec fn wf(&self) -> bool {
        &&& (forall |i: nat| self.perms@.dom().contains(i) ==> 0 <= i < self.data@.len)
        &&& self.first.addr() == self.next_ptr(self.data@.len).addr()
        &&& (forall |i: nat| self.valid_node(i, #[trigger] self.next_ptr(i)))
    }

    pub closed spec fn len(&self) -> nat {
        self.data@.len
    }

    pub closed spec fn page_id(&self) -> PageId {
        self.data@.page_id
    }

    pub closed spec fn block_size(&self) -> nat {
        self.data@.block_size
    }

    pub closed spec fn fixed_page(&self) -> bool {
        self.data@.fixed_page
    }

    pub closed spec fn instance(&self) -> Mim::Instance {
        self.data@.instance
    }

    pub closed spec fn heap_id(&self) -> Option<HeapId> {
        self.data@.heap_id
    }

    pub closed spec fn ptr(&self) -> *mut Node {
        self.first
    }

    /*spec fn is_valid_page_address(&self, ptr: int) -> bool {
        // We need this to save a ptr at this address
        // this is probably redundant since we also have is_block_ptr 
        ptr as int % size_of::<Node>() as int == 0
    }*/

    #[verifier::external_body]
    #[inline(always)]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
        requires old(self).wf(),
            points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
            //old(self).is_valid_page_address(points_to_raw.ptr()),
            block_token.instance_id() == old(self).instance().id(),
            is_block_ptr(ptr, block_token.key()),
            old(self).fixed_page() ==> (
                block_token.key().page_id == old(self).page_id()
                && block_token.key().block_size == old(self).block_size()
            ),
            old(self).heap_id().is_none(),
        ensures
            final(self).wf(),
            final(self).block_size() == old(self).block_size(),
            final(self).len() == old(self).len() + 1,
            final(self).instance() == old(self).instance(),
            final(self).page_id() == old(self).page_id(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).heap_id() == old(self).heap_id()
    {
        unimplemented!()
    }

    // This is like insert_block but it only does the operation "ghostily".
    // This is used by the ThreadLL
    //
    // It requires the pointer writer has already been done, so it's just arranging
    // ghost data in a ghost LL.

    #[verifier::external_body]
    pub proof fn ghost_insert_block(
        tracked self_: &mut Tracked<LL>,
        tracked ptr: *mut Node,
        tracked points_to_ptr: PointsTo<Node>,
        tracked points_to_raw: PointsToRaw,
        tracked block_token: Mim::block,
        tracked is_exposed: IsExposed,
     )
        requires old(self_).wf(),
            block_token.instance_id() == old(self_).instance().id(),
            is_block_ptr(ptr as *mut u8, block_token.key()),

            // Require that the pointer has already been written:
            points_to_ptr.ptr() == ptr,
            points_to_ptr.is_init(),
            points_to_ptr.value().ptr.addr() == old(self_).ptr().addr(),

            // Require the padding to be correct
            points_to_raw.is_range(
                ptr as int + size_of::<Node>(),
                block_token.key().block_size - size_of::<Node>()),
            points_to_raw.provenance() == is_exposed.provenance(),
            points_to_raw.provenance() == ptr@.provenance,
            block_token.key().block_size - size_of::<Node>() >= 0,

            old(self_).fixed_page() ==> (
                block_token.key().page_id == old(self_).page_id()
                && block_token.key().block_size == old(self_).block_size()
            ),
            (match old(self_).heap_id() {
                Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                None => true,
            }),
        ensures
            final(self_).wf(),
            final(self_).block_size() == old(self_).block_size(),
            final(self_).len() == old(self_).len() + 1,
            final(self_).instance() == old(self_).instance(),
            final(self_).page_id() == old(self_).page_id(),
            final(self_).fixed_page() == old(self_).fixed_page(),
            final(self_).heap_id() == old(self_).heap_id(),
            final(self_).ptr() == ptr
    {
        unimplemented!()
    }

    #[verifier::external_body]
    proof fn is_empty_iff_null(tracked &self)
        requires self.wf(),
        ensures self.len() == 0 <==> self.first.addr() == 0
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn is_empty(&self) -> (b: bool)
        requires self.wf(),
        ensures b <==> (self.len() == 0)
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
        requires old(self).wf(),
            old(self).len() != 0,
        ensures ({
            let (ptr, points_to, block_token) = x;
            {
                &&& final(self).wf()
                &&& final(self).block_size() == old(self).block_size()
                &&& final(self).len() + 1 == old(self).len()
                &&& final(self).instance() == old(self).instance()
                &&& final(self).page_id() == old(self).page_id()
                &&& final(self).fixed_page() == old(self).fixed_page()
                &&& final(self).heap_id() == old(self).heap_id()

                &&& points_to@.is_range(ptr as int, block_token@.key().block_size as int)
                &&& points_to@.provenance() == ptr@.provenance

                &&& block_token@.instance_id() == old(self).instance().id()
                &&& is_block_ptr(ptr, block_token@.key())

                &&& (final(self).fixed_page() ==> (
                    block_token@.key().page_id == final(self).page_id()
                    && block_token@.key().block_size == final(self).block_size()
                ))
                &&& (match final(self).heap_id() {
                    Some(heap_id) => block_token@.value().heap_id == Some(heap_id),
                    None => true,
                })
            }
        })
    {
        unimplemented!()
    }

    // helper for clients using ghost_insert_block

    #[verifier::external_body]
    #[inline(always)]
    pub fn block_write_ptr(ptr: *mut Node, Tracked(perm): Tracked<PointsToRaw>, next: *mut Node)
        -> (res: (Tracked<PointsTo<Node>>, Tracked<PointsToRaw>))
        requires
            perm.contains_range(ptr as int, size_of::<Node>() as int),
            perm.provenance() == ptr@.provenance,
            ptr as int % align_of::<crate::linked_list::Node>() as int == 0,
        ensures ({
            let points_to = res.0@;
            let points_to_raw = res.1@;

            points_to.ptr() == ptr
              && points_to.opt_value() == MemContents::Init(Node { ptr: next })

              && points_to_raw.dom() == perm.dom().difference(set_int_range(ptr as int, ptr as int + size_of::<Node>()))
              && points_to_raw.provenance() == ptr@.provenance
        })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn new(Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    ) -> (ll: LL)
        ensures ll.wf(),
            ll.page_id() == page_id,
            ll.fixed_page() == fixed_page,
            ll.instance() == instance,
            ll.block_size() == block_size,
            ll.heap_id() == heap_id,
            ll.len() == 0
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn empty() -> (ll: LL)
        ensures ll.wf(),
            ll.len() == 0
    {
        unimplemented!()
    }


    #[verifier::external_body]
    #[inline(always)]
    pub fn set_ghost_data(
        &mut self,
        Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    )
        requires old(self).wf(), old(self).len() == 0,
        ensures
            final(self).wf(),
            final(self).page_id() == page_id,
            final(self).fixed_page() == fixed_page,
            final(self).instance() == instance,
            final(self).block_size() == block_size,
            final(self).heap_id() == heap_id,
            final(self).len() == 0
    {
        unimplemented!()
    }


    // Traverse `other` to find the tail, append `self`,
    // and leave the resulting list in `self`.
    // Returns the # of entries in `other`

    #[verifier::external_body]
    #[inline(always)]
    pub fn append(&mut self, other: &mut LL) -> (other_len: u32)
        requires
            old(self).wf() && old(other).wf(),
            old(self).page_id() == old(other).page_id(),
            old(self).block_size() == old(other).block_size(),
            old(self).fixed_page() == old(other).fixed_page(),
            old(self).instance() == old(other).instance(),
            old(self).heap_id().is_none(),
            old(other).heap_id().is_none(),
            old(other).len() < u32::MAX,
        ensures 
            // Book-keeping junk:
            final(self).wf() && final(other).wf(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(other).page_id() == old(other).page_id(),
            final(other).block_size() == old(other).block_size(),
            final(other).fixed_page() == old(other).fixed_page(),
            final(other).instance() == old(other).instance(),
            final(other).heap_id() == old(other).heap_id(),

            // What you're here for:
            final(self).len() == old(self).len() + old(other).len(),
            final(other).len() == 0,

            other_len as int == old(other).len()
    {
        unimplemented!()
    }

    // don't need this?
    /*// Despite being 'exec', this function is a no-op
    #[inline(always)]
    pub fn mark_each_block_allocated(&mut self, tracked thread_token: &mut ThreadToken)
        requires
            self.wf(),
            self.fixed_page(),
            self.page_id() == old(self).page_id(),
        ensures 
            // Book-keeping junk:
            final(self).wf()
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).instance() == old(self).instance(),
    {
    } */

    #[verifier::external_body]
    #[inline(always)]
    pub fn prepend_contiguous_blocks(
        &mut self,
        start: *mut u8,
        last: *mut u8,
        bsize: usize,

        Ghost(cap): Ghost<nat>,     // current capacity
        Ghost(extend): Ghost<nat>,  // spec we're extending to

        Tracked(points_to_raw_r): Tracked<&mut PointsToRaw>,
        Tracked(tokens): Tracked<&mut Map<int, Mim::block>>,
    )
        requires
            old(self).wf(),
            old(self).fixed_page(),
            old(self).block_size() == bsize as nat,
            old(self).heap_id().is_none(),
            INTPTR_SIZE <= bsize,
            start as int % INTPTR_SIZE as int == 0,
            bsize as int % INTPTR_SIZE as int == 0,

            old(points_to_raw_r).is_range(start as int, extend as int * bsize as int),
            old(points_to_raw_r).provenance() == start@.provenance,
            start@.provenance == old(self).page_id().segment_id.provenance,
            start as int + extend * bsize <= usize::MAX,

            start as int ==
                block_start_at(old(self).page_id(), old(self).block_size() as int, cap as int),

            extend >= 1,
            last as int == start as int + ((extend as int - 1) * bsize as int),

            (forall |i: int| cap <= i < cap + extend ==> old(tokens).dom().contains(i)),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).instance_id() == old(self).instance().id()),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).key().page_id == old(self).page_id()),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).key().idx == i),
            (forall |i: int| cap <= i < cap + extend ==> old(tokens).index(i).key().block_size == bsize),
            (forall |i: int| cap <= i < cap + extend ==> is_block_ptr1(
                block_start(old(tokens).index(i).key()),
                old(tokens).index(i).key())
            )
        ensures
            final(self).wf(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),

            final(self).len() == old(self).len() + extend,

            //points_to_raw.ptr() == old(points_to_raw).ptr() + extend * (bsize as int),
            //points_to_raw@.size == old(points_to_raw)@.size - extend * (bsize as int),
            *final(tokens) == old(tokens).remove_keys(
                set_int_range(cap as int, cap as int + extend))
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub fn make_empty(&mut self) -> (llgstr: Tracked<LLGhostStateToReconvene>)
        requires old(self).wf(),
            old(self).fixed_page(),
        ensures
            llgstr_wf(llgstr@),
            llgstr@.block_size == old(self).block_size(),
            llgstr@.page_id == old(self).page_id(),
            llgstr@.instance == old(self).instance(),
            llgstr@.map.len() == old(self).len(),
            final(self).wf(),
            final(self).len() == 0
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn convene_pt_map(
        tracked m: Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>,
        len: nat,
        instance: Mim::Instance,
        page_id: PageId,
        block_size: nat,
    ) -> (tracked m2: Map<nat, (PointsToRaw, Mim::block)>)
        requires
            forall |i: nat| (#[trigger] m.dom().contains(i) <==> 0 <= i < len)
              && (m.dom().contains(i) ==> ({
                  let (perm, padding, block_token, exposed) = m[i];
                    perm.is_init()
                    && block_token.key().block_size - size_of::<Node>() >= 0
                    && padding.is_range(perm.ptr() as int + size_of::<Node>(),
                        block_token.key().block_size - size_of::<Node>())
                    && padding.provenance() == page_id.segment_id.provenance
                    && padding.provenance() == exposed.provenance()
                    && block_token.instance_id() == instance.id()
                    && is_block_ptr(perm.ptr() as *mut u8, block_token.key())
                    && block_token.key().page_id == page_id
                    && block_token.key().block_size == block_size
              }))
        ensures
            m2.len() == len,
            forall |i: nat| (#[trigger] m2.dom().contains(i) <==> 0 <= i < len)
              && (m2.dom().contains(i) ==> ({
                  let (padding, block_token) = m2[i];
                    && block_token.key().block_size - size_of::<Node>() >= 0
                    && padding.is_range(
                        block_start(block_token.key()),
                        block_token.key().block_size as int)
                    && padding.provenance() == page_id.segment_id.provenance
                    && block_token.instance_id() == instance.id()
                    && block_token.key().page_id == page_id
                    && block_token.key().block_size == block_size
              }))
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn reconvene_state(
        tracked inst: Mim::Instance,
        tracked ts: &Mim::thread_local_state,
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
        n_blocks: int,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        requires
            llgstr_wf(llgstr1),
            llgstr_wf(llgstr2),
            llgstr1.block_size == llgstr2.block_size,
            llgstr1.page_id == llgstr2.page_id,
            llgstr1.instance == inst,
            llgstr2.instance == inst,
            ts.instance_id() == inst.id(),
            n_blocks >= 0,
            llgstr1.map.len() + llgstr2.map.len() == n_blocks,
            ts.value().pages.dom().contains(llgstr1.page_id),
            ts.value().pages[llgstr1.page_id].num_blocks == n_blocks,
        ensures ({ let (points_to, map) = res; {
            &&& map.len() == n_blocks
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    block_id.page_id == llgstr1.page_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].key() == block_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].instance_id() == inst.id())

            &&& points_to.is_range(block_start_at(llgstr1.page_id, llgstr1.block_size as int, 0), n_blocks * llgstr1.block_size)
            &&& points_to.provenance() == llgstr1.page_id.segment_id.provenance
        }})
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn llgstr_merge(
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
    ) -> (tracked llgstr: LLGhostStateToReconvene)
        requires
            llgstr_wf(llgstr1),
            llgstr_wf(llgstr2),
            llgstr1.block_size == llgstr2.block_size,
            llgstr1.page_id == llgstr2.page_id,
            llgstr1.instance == llgstr2.instance,
        ensures
            llgstr_wf(llgstr),
            llgstr.block_size == llgstr2.block_size,
            llgstr.page_id == llgstr2.page_id,
            llgstr.instance == llgstr2.instance,
            llgstr.map.len() == llgstr1.map.len() + llgstr2.map.len()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    pub proof fn reconvene_rec(
        tracked m: Map<nat, (PointsToRaw, Mim::block)>,
        len: nat,
        instance: Mim::Instance,
        page_id: PageId,
        block_size: nat,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        requires
            forall |j: nat| 0 <= j < len ==> #[trigger] has_idx(m, j),
            forall |i: nat|
                  (m.dom().contains(i) ==> ({
                      let (padding, block_token) = m[i];
                        && block_token.key().block_size - size_of::<Node>() >= 0
                        && padding.is_range(
                            block_start(block_token.key()),
                            block_token.key().block_size as int)
                        && padding.provenance() == page_id.segment_id.provenance
                        && block_token.instance_id() == instance.id()
                        && block_token.key().page_id == page_id
                        && block_token.key().block_size == block_size
                  })),
        ensures ({ let (points_to, map) = res; {
            &&& map.len() == len
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    block_id.page_id == page_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].key() == block_id)
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    map[block_id].instance_id() == instance.id())
            &&& (forall |block_id| map.dom().contains(block_id) ==>
                    0 <= block_id.idx < len)
            &&& points_to.is_range(block_start_at(page_id, block_size as int, 0), (len * block_size) as int)
            &&& points_to.provenance() == page_id.segment_id.provenance
        }})
    {
        unimplemented!()
    }
}

pub closed spec fn has_idx(map: Map<nat, (PointsToRaw, Mim::block)>, i: nat) -> bool {
    exists |p: nat| map.dom().contains(p) && map[p].1.key().idx == i
}

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::range(lo, hi)
}

#[verifier::external_body]
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).len() == hi - lo
{
    unimplemented!()
}

pub closed spec fn llgstr_wf(llgstr: LLGhostStateToReconvene) -> bool {
    let len = llgstr.map.len();
    let map = llgstr.map;
    let block_size = llgstr.block_size;
    let page_id = llgstr.page_id;
    let instance = llgstr.instance;

    forall |i: nat| (#[trigger] map.dom().contains(i) <==> 0 <= i < len)
        && (map.dom().contains(i) ==> ({
            let (padding, block_token) = map[i];
              && block_token.key().block_size - size_of::<Node>() >= 0
              && padding.is_range(
                  block_start(block_token.key()),
                  block_token.key().block_size as int)
              && padding.provenance() == page_id.segment_id.provenance
              && block_token.instance_id() == instance.id()
              && block_token.key().page_id == page_id
              && block_token.key().block_size == block_size
        }))
}

#[verifier::external_body]
pub proof fn bound_on_2_lists(
    tracked instance: Mim::Instance,
    tracked thread_token: &Mim::thread_local_state,
    tracked ll1: &mut LL,
    tracked ll2: &mut LL,
)
    requires thread_token.instance_id() == instance.id(),
        old(ll1).wf(), old(ll2).wf(),
        old(ll1).fixed_page(),
        old(ll2).fixed_page(),
        old(ll1).instance() == instance,
        old(ll2).instance() == instance,
        old(ll1).page_id() == old(ll2).page_id(),
        // shouldn't really be necessary, but I'm reusing llgstr_merge
        // which requires it
        old(ll1).block_size() == old(ll2).block_size(),
        thread_token.value().pages.dom().contains(old(ll1).page_id()),
    ensures *final(ll1) == *old(ll1), *final(ll2) == *old(ll2),
        final(ll1).len() + final(ll2).len() <= thread_token.value().pages[final(ll1).page_id()].num_blocks
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn bound_on_1_lists(
    tracked instance: Mim::Instance,
    tracked thread_token: &Mim::thread_local_state,
    tracked ll1: &mut LL,
)
    requires thread_token.instance_id() == instance.id(),
        old(ll1).wf(),
        old(ll1).fixed_page(),
        old(ll1).instance() == instance,
        thread_token.value().pages.dom().contains(old(ll1).page_id()),
    ensures *final(ll1) == *old(ll1),
        final(ll1).len() <= thread_token.value().pages[final(ll1).page_id()].num_blocks
{
    unimplemented!()
}


struct_with_invariants!{
    pub struct ThreadLLSimple {
        pub instance: Ghost<Mim::Instance>,
        pub heap_id: Ghost<HeapId>,

        pub atomic: AtomicPtr<Node, _, Tracked<LL>, _>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant
            on atomic
            with (instance, heap_id)
            is (v: *mut Node, ll: Tracked<LL>)
        {
            // Valid linked list

            ll.wf()
            && ll.instance() == instance
            && !ll.fixed_page()
            && ll.heap_id() == Some(heap_id@)

            // The usize value stores the pointer and the delay state

            && v == ll.ptr()
        }
    }
}

impl ThreadLLSimple {
    #[verifier::external_body]
    #[inline(always)]
    pub fn empty(Ghost(instance): Ghost<Mim::Instance>, Ghost(heap_id): Ghost<HeapId>) -> (s: Self)
        ensures s.wf(),
            s.instance@ == instance,
            s.heap_id@ == heap_id
    {
        unimplemented!()
    }

    // Oughta have a similar spec as LL:insert_block except that
    //  (i) self argument is a & reference so we don't need to talk about how it updates
    //  (ii) is we don't expose the length

    #[verifier::external_body]
    #[inline(always)]
    pub fn atomic_insert_block(&self, ptr: *mut Node,
        Tracked(points_to_raw): Tracked<PointsToRaw>,
        Tracked(block_token): Tracked<Mim::block>,
    )
        requires self.wf(),
            points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
            block_token.instance_id() == self.instance@.id(),
            block_token.value().heap_id == Some(self.heap_id@),
            is_block_ptr(ptr as *mut u8, block_token.key())
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires self.wf()
        ensures
            ll.wf(),
            ll.instance() == self.instance,
            ll.heap_id() == Some(self.heap_id@)
    {
        unimplemented!()
    }
}

pub struct BlockSizePageId {
    pub block_size: nat,
    pub page_id: PageId,
}

tokenized_state_machine!{ StuffAgree {
    fields {
        #[sharding(variable)] pub x: Option<BlockSizePageId>,
        #[sharding(variable)] pub y: Option<BlockSizePageId>,
    }
    init!{
        initialize(b: Option<BlockSizePageId>) {
            init x = b;
            init y = b;
        }
    }
    transition!{
        set(b: Option<BlockSizePageId>) {
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

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, b: Option<BlockSizePageId>) {
        assume(false);
    }
   
    #[inductive(set)]
    fn set_inductive(pre: Self, post: Self, b: Option<BlockSizePageId>) {
        assume(false);
    }
}}


struct_with_invariants!{
    pub struct ThreadLLWithDelayBits {
        pub instance: Tracked<Mim::Instance>,

        // In order to make an 'atomic' LL, we store a ghost LL with the atomic usize.
        // Note that the only physical field in an LL is the pointer, so we can obtain
        // a real LL by combining the 'ghost LL' with the pointer value.

        // The pointer value is stored in the usize of the atomic.
        // We also use the lower 2 bits of the usize to store the delay state.

        pub atomic: AtomicPtr<Node, _, (StuffAgree::y, Option<(Mim::delay, LL)>), _>,

        pub emp: Tracked<StuffAgree::x>,
        pub emp_inst: Tracked<StuffAgree::Instance>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
            self.emp@.instance_id() == self.emp_inst@.id()
        }
        invariant
            on atomic
            with (instance, emp_inst)
            is (v: *mut Node, all_g: (StuffAgree::y, Option<(Mim::delay, LL)>))
        {
            let (is_emp, g_opt) = all_g;
            is_emp.instance_id() == emp_inst@.id()
            && (match (g_opt, is_emp.value()) {
                (None, None) => {
                    v == core::ptr::null_mut::<Node>()
                }
                (Some(g), Some(stuff)) => {
                    let (delay_token, ll) = g;
                    let page_id = stuff.page_id;
                    let block_size = stuff.block_size;

                    // Valid linked list

                    ll.wf()
                    && ll.block_size() == block_size
                    && ll.instance() == instance@
                    && ll.page_id() == page_id
                    && ll.fixed_page()
                    && ll.heap_id().is_none()

                    // Valid delay_token

                    && delay_token.instance_id() == instance@.id()
                    && delay_token.key() == page_id

                    // The usize value stores the pointer and the delay state

                    && v as int == ll.ptr() as int + delay_token.value().to_int()

                    // Verus should be smart enough to figure out the
                    // encoding is injective from this:
                    && ll.ptr() as int % 4 == 0

                    //&& (v as int != 0 ==> ({
                    //  &&& ll.ptr()@.provenance == page_id.segment_id.provenance
                    //}))
                    //&& (v as int == 0 ==> ({
                    //  &&& ll.ptr() == core::ptr::null_mut::<Node>()
                    //}))
                }
                _ => false,
            })
        }
    }
}

impl ThreadLLWithDelayBits {
    pub open spec fn is_empty(&self) -> bool {
        self.emp@.value().is_none()
    }

    pub open spec fn block_size(&self) -> nat {
        self.emp@.value().unwrap().block_size
    }

    pub open spec fn page_id(&self) -> PageId {
        self.emp@.value().unwrap().page_id
    }

    #[verifier::external_body]
    pub fn empty(Tracked(instance): Tracked<Mim::Instance>) -> (ll: ThreadLLWithDelayBits)
        ensures ll.is_empty(),
            ll.wf(),
            ll.instance == instance
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn enable(&mut self,
        Ghost(block_size): Ghost<nat>,
        Ghost(page_id): Ghost<PageId>,
        Tracked(instance): Tracked<Mim::Instance>,
        Tracked(delay_token): Tracked<Mim::delay>,
    )
        requires old(self).is_empty(),
            old(self).wf(),
            old(self).instance == instance,
            delay_token.instance_id() == instance.id(),
            delay_token.key() == page_id,
            delay_token.value() == DelayState::UseDelayedFree,
        ensures
            final(self).wf(),
            !final(self).is_empty(),
            final(self).block_size() == block_size,
            final(self).page_id() == page_id,
            final(self).instance == instance
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn disable(&mut self) -> (delay: Tracked<Mim::delay>)
        requires !old(self).is_empty(),
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).is_empty(),
            final(self).instance == old(self).instance,
            delay@.instance_id() == old(self).instance@.id(),
            delay@.key() == old(self).page_id()
    {
        unimplemented!()
    }

    /*#[inline(always)]
    pub fn exit_delaying_state(
        &self,
        Tracked(delay_actor_token): Tracked<Mim::delay_actor>,
    )
        requires self.wf(),
            !self.is_empty(),
            delay_actor_token@.key == self.page_id,
            delay_actor_token@.instance == self.instance,
    {
        // DelayState::Freeing -> DelayState::NoDelayedFree

        // Note: the original implementation in _mi_free_block_mt
        // uses a compare-and-swap loop. But we can just use fetch_xor so I thought
        // I'd simplify it

        atomic_with_ghost!(
            &self.atomic => fetch_xor(3);
            update v_old -> v_new;
            ghost g => {
                let tracked (mut delay_token, ll) = g;
                delay_token = self.instance.borrow().delay_leave_freeing(self.page_id@,
                    delay_token, delay_actor_token);

                // TODO right now this only works for fixed-width architecture
                //verus_proof_expr!{ { // TODO fix atomic_with_ghost
                //    assert(v_old % 4 == 1usize ==> (v_old ^ 3) == add(v_old, 1)) by (bit_vector);
                //} }

                g = (delay_token, ll);
            }
        );
    }*/

    #[verifier::external_body]
    #[inline(always)]
    pub fn check_is_good(
        &self,
        Tracked(thread_tok): Tracked<&Mim::thread_local_state>,
        Tracked(tok): Tracked<Mim::thread_checked_state>,
    ) -> (new_tok: Tracked<Mim::thread_checked_state>)
        requires self.wf(), !self.is_empty(),
            thread_tok.instance_id() == self.instance@.id(),
            thread_tok.value().pages.dom().contains(self.page_id()),
            thread_tok.value().pages[self.page_id()].num_blocks == 0,
            tok.instance_id() == self.instance@.id(),
            tok.key() == thread_tok.key(),
        ensures
            new_tok@.instance_id() == tok.instance_id(),
            new_tok@.key() == tok.key(),
            new_tok@.value() == (crate::tokens::ThreadCheckedState {
                pages: tok.value().pages.insert(self.page_id()),
            })
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn try_use_delayed_free(
        &self,
        delay: usize,
        override_never: bool,
    ) -> (b: bool)
        requires self.wf(), !self.is_empty(),
            !override_never && delay == 0, // UseDelayedFree
    {
        unimplemented!()
    }

    #[verifier::external_body]
    // Clears the list (but leaves the 'delay' bit intact)
    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires self.wf(), !self.is_empty(),
        ensures
            ll.wf(),
            ll.page_id() == self.page_id(),
            ll.block_size() == self.block_size(),
            ll.instance() == self.instance,
            ll.heap_id().is_none(),
            ll.fixed_page()
    {
        unimplemented!()
    }
}

#[verifier::external_body]
#[inline(always)]
pub fn masked_ptr_delay_get_is_use_delayed(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (b: bool)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures b <==> (expected_delay == DelayState::UseDelayedFree)
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
pub fn masked_ptr_delay_get_delay(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (d: usize)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures d == expected_delay.to_int()
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
pub fn masked_ptr_delay_get_ptr(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (ptr: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0
  ensures ptr.addr() == expected_ptr.addr()
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
pub fn masked_ptr_delay_set_ptr(v: *mut Node, new_ptr: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
      new_ptr as int % 4 == 0,
  ensures v2 as int == new_ptr as int + expected_delay.to_int(), v2@.provenance == new_ptr@.provenance
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
pub fn masked_ptr_delay_set_freeing(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0,
  ensures v2 as int == expected_ptr as int + DelayState::Freeing.to_int(), v2@.provenance == v@.provenance
{
    unimplemented!()
}

#[verifier::external_body]
#[inline(always)]
pub fn masked_ptr_delay_set_delay(v: *mut Node, new_delay: usize,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
  requires v as int == expected_ptr as int + expected_delay.to_int(),
      expected_ptr as int % 4 == 0, new_delay <= 3,
  ensures v2 as int == expected_ptr as int + new_delay,
      v2@.provenance == v@.provenance
{
    unimplemented!()
}

/*
#[inline(always)]
fn free_delayed_block(ll: &mut LL, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    requires old(local).wf(), old(ll).wf(), old(ll).len() != 0,
        old(ll).instance() == old(local).instance,
    ensures
        local.wf(),
        common_preserves(*old(local), *local),
        ll.instance() == old(ll).instance(),
{
    let ghost i = (ll.data@.len - 1) as nat;
    assert(ll.valid_node(i, ll.next_ptr(i)));
    let tracked (points_to_node, points_to_raw, block) = self.perms.borrow_mut().tracked_remove(i);
    let node = *ptr.borrow(Tracked(&points_to_node));

    let ghost block_id = block@.key;

    assert(crate::dealloc_token::valid_block_token(block, local.instance));

    let ptr = PPtr::<u8>::from_usize(ll.first.to_usize());
    let segment = crate::layout::calculate_segment_ptr_from_block(ptr, Ghost(block_id));

    let slice_page_ptr = crate::layout::calculate_slice_page_ptr_from_block(ptr, segment, Ghost(block_id));
    let tracked page_slice_shared_access: &PageSharedAccess =
        local.instance.alloc_guards_page_slice_shared_access(
            block_id,
            &block,
        );
    let slice_page: &Page = slice_page_ptr.borrow(
        Tracked(&page_slice_shared_access.points_to));
    let offset = slice_page.offset;
    let page_ptr = crate::layout::calculate_page_ptr_subtract_offset(
        slice_page_ptr,
        offset,
        Ghost(block_id.page_id_for_slice()),
        Ghost(block_id.page_id),
    );
    assert(crate::layout::is_page_ptr(page_ptr.id(), block_id.page_id));

    let page = PageId { page_ptr: page_ptr, page_id: Ghost(block_id.page_id) };
    if !crate::page::page_try_use_delayed_free(page, 0, false) {
        proof {
            self.perms.borrow_mut().tracked_insert((points_to_node, points_to_raw, block));
        }
        return false;
    }

    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

    proof { points_to_node.leak_contents(); }
    let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
    let tracked dealloc = MimDeallocInner {
        mim_instance: local.instance,
        mim_block: block,
        ptr: ptr.id(),
    };

    crate::free::free_block(page, true, ptr,
        Tracked(points_to_raw), Tracked(dealloc), Tracked(&mut *local));

    return true;
}
*/

#[verifier::external_body]
#[inline(always)]
fn atomic_yield()
{
    unimplemented!()
}

}
