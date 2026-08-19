#![allow(unused_imports)]

use verus_state_machines_macros::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::modes::*;
use vstd::*;
use vstd::set_lib::*;
use vstd::layout::*;
use vstd::atomic_ghost::*;

use crate::tokens::{Mim, BlockId, PageId, DelayState, HeapId, ThreadId};
use crate::layout::{is_block_ptr, block_size_ge_word, block_ptr_aligned_to_word, block_start_at, block_start, is_block_ptr1, lemma_is_block_ptr_aligned_to_node, page_start, start_offset, segment_start, lemma_segment_start_basics};
use crate::types::*;
use crate::config::{INTPTR_SIZE, SEGMENT_SIZE};
use crate::pigeonhole::block_id_set_len_bound;
use core::intrinsics::unlikely;

macro_rules! atomic_with_ghost {
    (&$receiver:ident . atomic => fetch_and(3); update $old_v:ident -> $new_v:ident; ghost $g:ident => {
        $receiver_agree1:ident . emp_inst . borrow() . agree($receiver_agree2:ident . emp . borrow(), &$g_agree:ident . 0);
        let tracked ($emp_token:ident, $pair_opt:ident) = $g_in:ident;
        let tracked $pair:ident = $pair_opt_use:ident . tracked_unwrap();
        let tracked ($delay:ident, $_ll:ident) = $pair_use:ident;
        $ll_out:ident = $_ll_use:ident;
        let mut $data:ident = $ll_data:ident . data@;
        $data_len:ident . len = 0;
        let tracked $new_ll:ident = LL {
            first: $p:ident,
            data: Ghost($data_ghost:ident),
            perms: Tracked(Map::tracked_empty()),
        };
        $g_out:ident = ($emp_token_use:ident, Some(($delay_use:ident, $new_ll_use:ident)));
        $($post:tt)*
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            let ghost mut __argus_ret_ptr: *mut Node = core::ptr::null_mut();
            let ghost mut __argus_ret_delay = DelayState::UseDelayedFree;
            let __argus_res = ::vstd::atomic_ghost::atomic_with_ghost!(
                &$receiver.atomic => fetch_and(3);
                update $old_v -> $new_v;
                ghost $g => {
                    $receiver.emp_inst.borrow().agree($receiver.emp.borrow(), &$g.0);
                    let tracked ($emp_token, $pair_opt) = $g;
                    let tracked $pair = $pair_opt.tracked_unwrap();
                    let tracked ($delay, $_ll) = $pair;
                    $ll_out = $_ll;
                    __argus_ret_ptr = $ll_out.ptr();
                    __argus_ret_delay = $delay.value();
                    masked_ptr_delay_from_int($old_v, __argus_ret_delay, __argus_ret_ptr);
                    let mut $data = $ll_out.data@;
                    $data.len = 0;
                    $data.block_ids = Set::empty();
                    let tracked $new_ll = LL {
                        first: $p,
                        data: Ghost($data),
                        perms: Tracked(Map::tracked_empty()),
                    };
                    $new_ll.empty_fields_wf();
                    assert($new_v.addr() == ($old_v.addr() & 3usize));
                    masked_ptr_delay_clear_ptr($old_v, $new_v, __argus_ret_delay, __argus_ret_ptr, $new_ll.ptr());
                    assert($new_v as int == $new_ll.ptr() as int + $delay.value().to_int());
                    $g = ($emp_token, Some(($delay, $new_ll)));
                    $($post)*
                }
            );
            proof! {
                masked_ptr_delay_from_int(__argus_res, __argus_ret_delay, __argus_ret_ptr);
                masked_ptr_delay_wf_facts(__argus_res, __argus_ret_delay, __argus_ret_ptr);
                assert((__argus_res.addr() & !3usize) == $ll_out.ptr().addr());
            }
            __argus_res
        } }
    };
    (&$receiver:ident . atomic => no_op(); update $old_v:ident -> $new_v:ident; ghost $g:ident => {
        let tracked (mut $y:ident, $g_opt:ident) = $g_in:ident;
        let $bspi:ident = BlockSizePageId { $block_size:ident, $page_id:ident };
        $receiver_set:ident . emp_inst . borrow() . set(Some($bspi_set:ident), $receiver_emp:ident . emp . borrow_mut(), &mut $y_set:ident);
        $g_out:ident = ($y_out:ident, Some(($delay_token:ident, $new_ll:ident)));
        $($post:tt)*
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            ::vstd::atomic_ghost::atomic_with_ghost!(
                &$receiver.atomic => no_op();
                update $old_v -> $new_v;
                ghost $g => {
                    let tracked (mut $y, $g_opt) = $g;
                    $receiver.emp_inst.borrow().agree($receiver.emp.borrow(), &$y);
                    assert($y.value().is_none());
                    assert($g_opt.is_none());
                    assert($old_v == core::ptr::null_mut::<Node>());
                    let $bspi = BlockSizePageId { $block_size, $page_id };
                    $receiver.emp_inst.borrow().set(Some($bspi), $receiver.emp.borrow_mut(), &mut $y);
                    assert($y.value() == Some($bspi));
                    assert($new_ll.wf());
                    assert($new_ll.block_size() == $block_size);
                    assert($new_ll.instance() == $receiver.instance@);
                    assert($new_ll.page_id() == $page_id);
                    assert($new_ll.fixed_page());
                    assert($new_ll.heap_id().is_none());
                    assert($new_ll.ptr() == core::ptr::null_mut::<Node>());
                    assert($new_ll.ptr() as int == 0);
                    assert($delay_token.instance_id() == $receiver.instance@.id());
                    assert($delay_token.key() == $page_id);
                    delay_state_to_int_facts($delay_token.value());
                    assert($delay_token.value().to_int() == 0);
                    assert($new_v == $old_v);
                    assert($new_v as int == $new_ll.ptr() as int + $delay_token.value().to_int());
                    assert($new_ll.ptr() as int % 4 == 0);
                    $g = ($y, Some(($delay_token, $new_ll)));
                    $($post)*
                }
            )
        } }
    };

    (&$receiver:ident . atomic => swap(core::ptr::null_mut()); ghost $g:ident => {
        $ll:ident = $g_get:ident . get();
        let mut $data:ident = $ll_data:ident . data@;
        $data_len:ident . len = 0;
        let tracked $new_ll:ident = LL {
            first: $p:ident,
            data: Ghost($data_ghost:ident),
            perms: Tracked(Map::tracked_empty()),
        };
        $g_out:ident = Tracked($new_ll_use:ident);
    }) => {
        ::vstd::prelude::verus_exec_expr!{ {
            ::vstd::atomic_ghost::atomic_with_ghost!(
                &$receiver.atomic => swap(core::ptr::null_mut());
                ghost $g => {
                    $ll = $g.get();
                    let mut $data = $ll.data@;
                    $data.len = 0;
                    $data.block_ids = Set::empty();
                    $data.idx_bound = 0;
                    let tracked $new_ll = LL {
                        first: $p,
                        data: Ghost($data),
                        perms: Tracked(Map::tracked_empty()),
                    };
                    $new_ll.empty_fields_wf();
                    $g = Tracked($new_ll);
                }
            )
        } }
    };

    ($($tokens:tt)*) => {
        ::vstd::atomic_ghost::atomic_with_ghost!($($tokens)*)
    };
}
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
        Node { ptr: self.ptr }
    }
}

global layout Node is size == 8, align == 8;

pub proof fn node_layout_facts()
    ensures
        size_of::<Node>() == 8,
        align_of::<Node>() == 8,
{
}

pub ghost struct LLData {
    ghost fixed_page: bool,
    ghost block_size: nat,   // only used if fixed_page=true
    ghost page_id: PageId,   // only used if fixed_page=true
    ghost heap_id: Option<HeapId>, // if set, then all blocks must have this HeapId

    ghost instance: Mim::Instance,
    ghost len: nat,
    ghost block_ids: Set<BlockId>,
    ghost idx_bound: nat,
}

pub struct LL {
    pub(crate) first: *mut Node,

    pub(crate) data: Ghost<LLData>,

    // first to be popped off goes at the end
    pub(crate) perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>,
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
        &&& self.data@.block_ids.len() == self.data@.len
        &&& self.no_duplicate_keys()
        &&& (forall |i: nat| 0 <= i < self.data@.len ==>
            self.data@.block_ids.contains(#[trigger] self.perms@[i].2.key()))
        &&& (forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) ==>
            exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == block_id)
        &&& (forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) ==>
            block_id.page_id == self.data@.page_id
                && block_id.block_size == self.data@.block_size)
        &&& (forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] self.data@.block_ids.contains(block_id1)
                && #[trigger] self.data@.block_ids.contains(block_id2)
                && block_id1.page_id == block_id2.page_id
                && block_id1.idx == block_id2.idx ==> block_id1 == block_id2)
    }

    pub closed spec fn len(&self) -> nat {
        self.data@.len
    }

    pub closed spec fn block_ids(&self) -> Set<BlockId> {
        self.data@.block_ids
    }

    pub closed spec fn idx_bound(&self) -> nat {
        self.data@.idx_bound
    }

    pub closed spec fn block_id_at(&self, i: nat) -> BlockId {
        self.perms@[i].2.key()
    }

    pub closed spec fn no_duplicate_keys(&self) -> bool {
        forall |i: nat, j: nat|
            0 <= i < self.data@.len && 0 <= j < self.data@.len && i != j
                ==> self.perms@[i].2.key() != self.perms@[j].2.key()
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

    pub closed spec fn first_addr(&self) -> usize {
        self.first.addr()
    }

    pub proof fn len_zero_implies_first_addr_zero(&self)
        requires
            self.wf(),
            self.len() == 0,
        ensures
            self.first_addr() == 0,
    {
        reveal(LL::wf);
        reveal(LL::len);
        reveal(LL::next_ptr);
        reveal(LL::first_addr);
    }

    pub proof fn first_addr_nonzero_implies_len_positive(&self)
        requires
            self.wf(),
            self.first_addr() != 0,
        ensures
            self.len() > 0,
    {
        reveal(LL::wf);
        reveal(LL::len);
        reveal(LL::next_ptr);
        reveal(LL::first_addr);
        if self.len() == 0 {
            assert(self.first_addr() == 0);
            assert(false);
        }
    }

    /*spec fn is_valid_page_address(&self, ptr: int) -> bool {
        // We need this to save a ptr at this address
        // this is probably redundant since we also have is_block_ptr
        ptr as int % size_of::<Node>() as int == 0
    }*/

}
}

#[cfg(not(verus_keep_ghost))]
impl LL {
    #[inline(always)]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
    {
        let Tracked(mut mem1) = Tracked::<PointsTo<Node>>::assume_new();
        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$

        let ptr = ptr as *mut Node;
        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
        self.first = ptr;
        let Tracked(is_exposed) = expose_provenance(ptr);

    }
}

#[cfg(verus_keep_ghost)]
verus!{
impl LL {
    #[inline(always)]
    #[verus_verify]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
        requires
            old(self).wf(),
            old(self).fixed_page(),
            block_token.instance_id() == old(self).instance().id(),
            block_token.key().page_id == old(self).page_id(),
            block_token.key().block_size == old(self).block_size(),
            !old(self).block_ids().contains(block_token.key()),
            (forall |block_id: BlockId| #[trigger] old(self).block_ids().contains(block_id) ==>
                block_id.idx != block_token.key().idx),
            match old(self).heap_id() {
                Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                None => true,
            },
            is_block_ptr(ptr, block_token.key()),
            points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
        ensures
            final(self).wf(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(self).block_ids() == old(self).block_ids().insert(block_token.key()),
            final(self).len() == old(self).len() + 1,
    {
        let ghost old_len = self.data@.len;
        let ghost old_first = self.first;
        let ghost old_data = self.data@;

        proof! {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::block_ids);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(is_block_ptr1);
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            lemma_is_block_ptr_aligned_to_node(ptr, block_token.key());
            assert(block_token.key().block_size >= size_of::<Node>());
        }

        proof_decl! {
            let tracked (points_to_node_raw, points_to_padding) =
                points_to_raw.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));
        }

        proof! {
            assert(points_to_padding.provenance() == ptr@.provenance);
            assert(points_to_padding.is_range(
                ptr as int + size_of::<Node>(),
                block_token.key().block_size as int - size_of::<Node>() as int));
        }

        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$

        let ptr = ptr as *mut Node;
        proof! {
            vstd::set_lib::lemma_int_range(ptr as int, ptr as int + size_of::<Node>());
            assert(points_to_node_raw.is_range(ptr as int, size_of::<Node>() as int));
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            assert(ptr.addr() as int == ptr as int);
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, block_token.key());
            assert(ptr.addr() as int % align_of::<Node>() as int == 0);
        }
        proof_decl! {
            let tracked mut mem1 = points_to_node_raw.into_typed::<Node>(ptr.addr());
        }
        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
        self.first = ptr;
        let Tracked(is_exposed) = expose_provenance(ptr);

        proof! {
            self.perms.borrow_mut().tracked_insert(old_len, (
                mem1,
                points_to_padding,
                block_token,
                is_exposed,
            ));
            self.data = Ghost(LLData {
                fixed_page: old_data.fixed_page,
                block_size: old_data.block_size,
                page_id: old_data.page_id,
                heap_id: old_data.heap_id,
                instance: old_data.instance,
                len: old_len + 1,
                block_ids: old_data.block_ids.insert(block_token.key()),
                idx_bound: old_data.idx_bound,
            });

            assert(self.data@.len == old_len + 1);
            assert(self.perms@.dom() =~= old(self).perms@.dom().insert(old_len));
            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len by {
                if i == old_len {
                } else {
                    assert(old(self).perms@.dom().contains(i));
                    assert(0 <= i < old_len);
                }
            }
            assert(self.next_ptr(self.data@.len).addr() == self.first.addr());
            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
                if 0 <= i < self.data@.len {
                    if i == old_len {
                        assert(self.perms@.dom().contains(i));
                        assert(self.perms@[i].0.ptr() == self.first);
                        assert(self.perms@[i].0.is_init());
                        assert(self.perms@[i].0.value().ptr.addr() == old_first.addr());
                        assert(self.next_ptr(i).addr() == old_first.addr());
                        assert(self.perms@[i].0.value().ptr.addr() == self.next_ptr(i).addr());
                        assert(self.perms@[i].2.key().block_size - size_of::<Node>() >= 0);
                        assert(self.perms@[i].1.is_range(
                            self.perms@[i].0.ptr().addr() + size_of::<Node>(),
                            self.perms@[i].2.key().block_size - size_of::<Node>()));
                        assert(self.perms@[i].1.provenance() == self.perms@[i].0.ptr()@.provenance);
                        assert(self.perms@[i].3.provenance() == self.perms@[i].1.provenance());
                        assert(self.perms@[i].2.instance_id() == self.data@.instance.id());
                        assert(is_block_ptr(self.perms@[i].0.ptr() as *mut u8, self.perms@[i].2.key()));
                        assert(self.perms@[i].2.key().page_id == self.data@.page_id);
                        assert(self.perms@[i].2.key().block_size == self.data@.block_size);
                        assert(self.data@.heap_id.is_None() || self.perms@[i].2.value().heap_id == self.data@.heap_id);
                        assert(self.valid_node(i, self.next_ptr(i)));
                    } else {
                        assert(old(self).valid_node(i, old(self).next_ptr(i)));
                        assert(self.perms@[i] == old(self).perms@[i]);
                        assert(self.next_ptr(i) == old(self).next_ptr(i));
                        assert(self.data@.fixed_page == old(self).data@.fixed_page);
                        assert(self.data@.block_size == old(self).data@.block_size);
                        assert(self.data@.page_id == old(self).data@.page_id);
                        assert(self.data@.heap_id == old(self).data@.heap_id);
                        assert(self.data@.instance == old(self).data@.instance);
                        assert(self.data@.block_ids == old(self).data@.block_ids.insert(block_token.key()));
                        assert(self.valid_node(i, self.next_ptr(i)));
                    }
                }
            }

            assert(old(self).block_ids() == old_data.block_ids);
            assert(!old_data.block_ids.contains(block_token.key())) by {
                if old_data.block_ids.contains(block_token.key()) {
                    assert(old(self).block_ids().contains(block_token.key()));
                    assert(false);
                }
            };
            assert(self.data@.block_ids.len() == self.data@.len) by {
                vstd::set::lemma_set_insert_len(old_data.block_ids, block_token.key());
            }
            assert forall |i: nat| 0 <= i < self.data@.len implies
                self.data@.block_ids.contains(#[trigger] self.perms@[i].2.key())
            by {
                if i == old_len {
                    assert(self.perms@[i].2.key() == block_token.key());
                } else {
                    assert(0 <= i < old_len);
                    assert(old(self).data@.block_ids.contains(old(self).perms@[i].2.key()));
                    assert(self.perms@[i] == old(self).perms@[i]);
                }
            };
            assert forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) implies
                exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == block_id
            by {
                if block_id == block_token.key() {
                    assert(0 <= old_len < self.data@.len);
                    assert(self.perms@[old_len].2.key() == block_id);
                } else {
                    assert(old_data.block_ids.contains(block_id));
                    let i = choose |i: nat| 0 <= i < old_len && old(self).perms@[i].2.key() == block_id;
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(0 <= i < self.data@.len);
                }
            };
            assert forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) implies
                block_id.page_id == self.data@.page_id
                    && block_id.block_size == self.data@.block_size
            by {
                if block_id == block_token.key() {
                } else {
                    assert(old_data.block_ids.contains(block_id));
                }
            };
            assert forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] self.data@.block_ids.contains(block_id1)
                    && #[trigger] self.data@.block_ids.contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx implies block_id1 == block_id2
            by {
                if block_id1 == block_token.key() {
                    if block_id2 == block_token.key() {
                    } else {
                        assert(old_data.block_ids.contains(block_id2));
                        assert(old(self).block_ids().contains(block_id2));
                        assert(block_id2.page_id == block_token.key().page_id);
                        assert(block_id2.idx == block_token.key().idx);
                        assert(false);
                    }
                } else if block_id2 == block_token.key() {
                    assert(old_data.block_ids.contains(block_id1));
                    assert(old(self).block_ids().contains(block_id1));
                    assert(block_id1.page_id == block_token.key().page_id);
                    assert(block_id1.idx == block_token.key().idx);
                    assert(false);
                } else {
                    assert(old_data.block_ids.contains(block_id1));
                    assert(old_data.block_ids.contains(block_id2));
                }
            };
            assert(self.wf());
        }
    }
}
}


verus!{
impl LL {

    pub proof fn block_token_fresh_for_ll(
        tracked inst: &Mim::Instance,
        tracked ll: LL,
        tracked block_token: Mim::block,
    ) -> (tracked out: (LL, Mim::block))
        requires
            ll.wf(),
            ll.fixed_page(),
            ll.instance().id() == inst.id(),
            block_token.instance_id() == inst.id(),
            block_token.key().page_id == ll.page_id(),
        ensures
            out.0.wf(),
            out.0.fixed_page() == ll.fixed_page(),
            out.0.page_id() == ll.page_id(),
            out.0.block_size() == ll.block_size(),
            out.0.instance() == ll.instance(),
            out.0.heap_id() == ll.heap_id(),
            out.0.block_ids() == ll.block_ids(),
            out.0.len() == ll.len(),
            out.0.ptr() == ll.ptr(),
            out.1.instance_id() == block_token.instance_id(),
            out.1.key() == block_token.key(),
            out.1.value().heap_id == block_token.value().heap_id,
            !out.0.block_ids().contains(out.1.key()),
            (forall |block_id: BlockId| #[trigger] out.0.block_ids().contains(block_id) ==>
                block_id.idx != out.1.key().idx),
    {
        let ghost old_ll = ll;
        let tracked mut ll = ll;
        let tracked mut block_token = block_token;
        reveal(LL::wf);
        reveal(LL::block_ids);
        reveal(LL::fixed_page);
        reveal(LL::page_id);
        reveal(LL::block_size);
        reveal(LL::instance);
        reveal(LL::heap_id);
        reveal(LL::len);
        reveal(LL::ptr);
        reveal(LL::valid_node);
        reveal(LL::next_ptr);

        if exists |block_id: BlockId| old_ll.block_ids().contains(block_id)
            && block_id.idx == block_token.key().idx {
            let block_id = choose |block_id: BlockId| old_ll.block_ids().contains(block_id)
                && block_id.idx == block_token.key().idx;
            old_ll.block_ids_contains_witness(block_id);
            let i = choose |i: nat| i < old_ll.len()
                && old_ll.perms@.dom().contains(i)
                && old_ll.perms@[i].2.key() == block_id;
            assert(old_ll.valid_node(i, old_ll.next_ptr(i)));
            assert(old_ll.perms@[i].2.instance_id() == old_ll.instance().id());
            assert(block_id.page_id == old_ll.page_id());
            assert(block_token.key().page_id == old_ll.page_id());
            let tracked entry = ll.perms.borrow_mut().tracked_remove(i);
            let tracked (points_to, raw_mem, old_block, exposed) = entry;
            let tracked (Tracked(block_token0), Tracked(old_block0)) =
                LL::owned_block_tokens_same_page_idx_impossible_retain(
                    inst, block_token, old_block);
            block_token = block_token0;
            ll.perms.borrow_mut().tracked_insert(i, (points_to, raw_mem, old_block0, exposed));
            assert(false);
        }
        assert(!exists |block_id: BlockId| old_ll.block_ids().contains(block_id)
            && block_id.idx == block_token.key().idx);
        assert forall |block_id: BlockId| #[trigger] old_ll.block_ids().contains(block_id) implies
            block_id.idx != block_token.key().idx by {
            if block_id.idx == block_token.key().idx {
                assert(exists |block_id: BlockId| old_ll.block_ids().contains(block_id)
                    && block_id.idx == block_token.key().idx);
                assert(false);
            }
        };
        assert(!old_ll.block_ids().contains(block_token.key())) by {
            if old_ll.block_ids().contains(block_token.key()) {
                assert(exists |block_id: BlockId| old_ll.block_ids().contains(block_id)
                    && block_id.idx == block_token.key().idx);
                assert(false);
            }
        };
        (ll, block_token)
    }

    pub proof fn ghost_insert_block(
        tracked self_: LL,
        tracked ptr: *mut Node,
        tracked points_to_ptr: PointsTo<Node>,
        tracked points_to_raw: PointsToRaw,
        tracked block_token: Mim::block,
        tracked is_exposed: IsExposed,
     ) -> (tracked out: LL)
        requires
            self_.wf(),
            self_.fixed_page(),
            block_token.instance_id() == self_.instance().id(),
            block_token.key().page_id == self_.page_id(),
            block_token.key().block_size == self_.block_size(),
            !self_.block_ids().contains(block_token.key()),
            (forall |block_id: BlockId| #[trigger] self_.block_ids().contains(block_id) ==>
                block_id.idx != block_token.key().idx),
            match self_.heap_id() {
                Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                None => true,
            },
            is_block_ptr(ptr as *mut u8, block_token.key()),
            points_to_ptr.ptr() == ptr,
            points_to_ptr.is_init(),
            points_to_ptr.value().ptr.addr() == self_.ptr().addr(),
            points_to_raw.is_range(ptr as int + size_of::<Node>() as int,
                block_token.key().block_size as int - size_of::<Node>() as int),
            points_to_raw.provenance() == ptr@.provenance,
            is_exposed.provenance() == ptr@.provenance,
        ensures
            out.wf(),
            out.fixed_page() == self_.fixed_page(),
            out.page_id() == self_.page_id(),
            out.block_size() == self_.block_size(),
            out.instance() == self_.instance(),
            out.heap_id() == self_.heap_id(),
            out.block_ids() == self_.block_ids().insert(block_token.key()),
            out.len() == self_.len() + 1,
            out.ptr() == ptr,
    {
        let ghost old_self = self_;
        let ghost old_len = self_.data@.len;
        let ghost old_first = self_.first;
        let ghost old_data = self_.data@;
        let tracked mut perms = self_.perms.get();

        reveal(LL::wf);
        reveal(LL::next_ptr);
        reveal(LL::valid_node);
        reveal(LL::len);
        reveal(LL::block_ids);
        reveal(LL::fixed_page);
        reveal(LL::page_id);
        reveal(LL::block_size);
        reveal(LL::instance);
        reveal(LL::heap_id);
        reveal(LL::ptr);
        reveal(is_block_ptr1);
        assert(size_of::<Node>() == 8);
        assert(align_of::<Node>() == 8);
        lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, block_token.key());
        assert(block_token.key().block_size >= size_of::<Node>());

        perms.tracked_insert(old_len, (
            points_to_ptr,
            points_to_raw,
            block_token,
            is_exposed,
        ));
        let tracked out = LL {
            first: ptr,
            data: Ghost(LLData {
                fixed_page: old_data.fixed_page,
                block_size: old_data.block_size,
                page_id: old_data.page_id,
                heap_id: old_data.heap_id,
                instance: old_data.instance,
                len: old_len + 1,
                block_ids: old_data.block_ids.insert(block_token.key()),
                idx_bound: old_data.idx_bound,
            }),
            perms: Tracked(perms),
        };

        assert(out.data@.len == old_len + 1);
        assert(out.perms@.dom() =~= old_self.perms@.dom().insert(old_len));
        assert forall |i: nat| out.perms@.dom().contains(i) implies 0 <= i < out.data@.len by {
            if i == old_len {
            } else {
                assert(old_self.perms@.dom().contains(i));
                assert(0 <= i < old_len);
            }
        }
        assert(out.next_ptr(out.data@.len).addr() == out.first.addr());
        assert forall |i: nat| #[trigger] out.valid_node(i, out.next_ptr(i)) by {
            if 0 <= i < out.data@.len {
                if i == old_len {
                    assert(out.perms@.dom().contains(i));
                    assert(out.perms@[i].0.ptr() == out.first);
                    assert(out.perms@[i].0.is_init());
                    assert(out.perms@[i].0.value().ptr.addr() == old_first.addr());
                    assert(out.next_ptr(i).addr() == old_first.addr());
                    assert(out.perms@[i].0.value().ptr.addr() == out.next_ptr(i).addr());
                    assert(out.perms@[i].2.key().block_size - size_of::<Node>() >= 0);
                    assert(out.perms@[i].1.is_range(
                        out.perms@[i].0.ptr().addr() + size_of::<Node>(),
                        out.perms@[i].2.key().block_size - size_of::<Node>()));
                    assert(out.perms@[i].1.provenance() == out.perms@[i].0.ptr()@.provenance);
                    assert(out.perms@[i].3.provenance() == out.perms@[i].1.provenance());
                    assert(out.perms@[i].2.instance_id() == out.data@.instance.id());
                    assert(is_block_ptr(out.perms@[i].0.ptr() as *mut u8, out.perms@[i].2.key()));
                    assert(out.perms@[i].2.key().page_id == out.data@.page_id);
                    assert(out.perms@[i].2.key().block_size == out.data@.block_size);
                    assert(out.data@.heap_id.is_None() || out.perms@[i].2.value().heap_id == out.data@.heap_id);
                    assert(out.valid_node(i, out.next_ptr(i)));
                } else {
                    assert(old_self.valid_node(i, old_self.next_ptr(i)));
                    assert(out.perms@[i] == old_self.perms@[i]);
                    assert(out.next_ptr(i) == old_self.next_ptr(i));
                    assert(out.data@.fixed_page == old_self.data@.fixed_page);
                    assert(out.data@.block_size == old_self.data@.block_size);
                    assert(out.data@.page_id == old_self.data@.page_id);
                    assert(out.data@.heap_id == old_self.data@.heap_id);
                    assert(out.data@.instance == old_self.data@.instance);
                    assert(out.data@.block_ids == old_self.data@.block_ids.insert(block_token.key()));
                    assert(out.valid_node(i, out.next_ptr(i)));
                }
            }
        }

        assert(old_self.block_ids() == old_data.block_ids);
        assert(!old_data.block_ids.contains(block_token.key())) by {
            if old_data.block_ids.contains(block_token.key()) {
                assert(old_self.block_ids().contains(block_token.key()));
                assert(false);
            }
        };
        assert(out.data@.block_ids.len() == out.data@.len) by {
            vstd::set::lemma_set_insert_len(old_data.block_ids, block_token.key());
        }
        assert forall |i: nat| 0 <= i < out.data@.len implies
            out.data@.block_ids.contains(#[trigger] out.perms@[i].2.key())
        by {
            if i == old_len {
                assert(out.perms@[i].2.key() == block_token.key());
            } else {
                assert(0 <= i < old_len);
                assert(old_self.data@.block_ids.contains(old_self.perms@[i].2.key()));
                assert(out.perms@[i] == old_self.perms@[i]);
            }
        };
        assert forall |block_id: BlockId| #[trigger] out.data@.block_ids.contains(block_id) implies
            exists |i: nat| 0 <= i < out.data@.len && out.perms@[i].2.key() == block_id
        by {
            if block_id == block_token.key() {
                assert(0 <= old_len < out.data@.len);
                assert(out.perms@[old_len].2.key() == block_id);
            } else {
                assert(old_data.block_ids.contains(block_id));
                let i = choose |i: nat| 0 <= i < old_len && old_self.perms@[i].2.key() == block_id;
                assert(out.perms@[i] == old_self.perms@[i]);
                assert(0 <= i < out.data@.len);
            }
        };
        assert forall |block_id: BlockId| #[trigger] out.data@.block_ids.contains(block_id) implies
            block_id.page_id == out.data@.page_id
                && block_id.block_size == out.data@.block_size
        by {
            if block_id == block_token.key() {
            } else {
                assert(old_data.block_ids.contains(block_id));
            }
        };
        assert forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] out.data@.block_ids.contains(block_id1)
                && #[trigger] out.data@.block_ids.contains(block_id2)
                && block_id1.page_id == block_id2.page_id
                && block_id1.idx == block_id2.idx implies block_id1 == block_id2
        by {
            if block_id1 == block_token.key() {
                if block_id2 == block_token.key() {
                } else {
                    assert(old_data.block_ids.contains(block_id2));
                    assert(old_self.block_ids().contains(block_id2));
                    assert(block_id2.page_id == block_token.key().page_id);
                    assert(block_id2.idx == block_token.key().idx);
                    assert(false);
                }
            } else if block_id2 == block_token.key() {
                assert(old_data.block_ids.contains(block_id1));
                assert(old_self.block_ids().contains(block_id1));
                assert(block_id1.page_id == block_token.key().page_id);
                assert(block_id1.idx == block_token.key().idx);
                assert(false);
            } else {
                assert(old_data.block_ids.contains(block_id1));
                assert(old_data.block_ids.contains(block_id2));
            }
        };
        assert(out.wf());
        assert(out.ptr() == ptr);
        out
    }



    pub proof fn owned_block_tokens_same_page_idx_impossible_retain(
        tracked inst: &Mim::Instance,
        tracked block1: Mim::block,
        tracked block2: Mim::block,
    ) -> (tracked out: (Tracked<Mim::block>, Tracked<Mim::block>))
        requires
            block1.instance_id() == inst.id(),
            block2.instance_id() == inst.id(),
            block1.key().page_id == block2.key().page_id,
            block1.key().idx == block2.key().idx,
        ensures
            false,
    {
        inst.block_tokens_distinct_retain(block1.key(), block2.key(), block1, block2)
    }


    pub(crate) proof fn block_ids_contains_witness(&self, block_id: BlockId)
        requires
            self.wf(),
            self.block_ids().contains(block_id),
        ensures
            exists |i: nat| i < self.len()
                && self.perms@.dom().contains(i)
                && self.perms@[i].2.key() == block_id,
    {
        reveal(LL::wf);
        reveal(LL::len);
        reveal(LL::block_ids);
        assert(exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == block_id);
        let i = choose |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == block_id;
        assert(self.valid_node(i, self.next_ptr(i)));
        assert(self.perms@.dom().contains(i));
    }


    pub(crate) proof fn entry_token_matches_metadata(&self, i: nat)
        requires
            self.wf(),
            i < self.len(),
            self.perms@.dom().contains(i),
        ensures
            self.perms@[i].2.instance_id() == self.instance().id(),
            self.perms@[i].2.key().page_id == self.page_id(),
            self.perms@[i].2.key().block_size == self.block_size(),
    {
        reveal(LL::wf);
        reveal(LL::valid_node);
        reveal(LL::next_ptr);
        reveal(LL::len);
        reveal(LL::instance);
        reveal(LL::page_id);
        reveal(LL::block_size);
        assert(self.valid_node(i, self.next_ptr(i)));
    }

    proof fn empty_fields_wf(&self)
        requires
            self.first.addr() == 0,
            self.data@.len == 0,
            self.data@.block_ids == Set::empty(),
            self.perms@.dom() =~= Set::empty(),
        ensures
            self.wf(),
            self.no_duplicate_keys(),
            self.len() == 0,
            self.first_addr() == 0,
    {
        reveal(LL::wf);
        reveal(LL::next_ptr);
        reveal(LL::valid_node);
        reveal(LL::len);
        reveal(LL::first_addr);
        reveal(LL::no_duplicate_keys);
        assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len by {
            assert(false);
        };
        assert(self.next_ptr(self.data@.len).addr() == self.first.addr());
        assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
            if 0 <= i < self.data@.len {
                assert(false);
            }
        };
        assert(self.data@.block_ids.len() == self.data@.len);
        assert forall |i: nat| 0 <= i < self.data@.len implies
            self.data@.block_ids.contains(#[trigger] self.perms@[i].2.key()) by {
            assert(false);
        };
        assert forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) implies
            exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == block_id by {
            assert(false);
        };
        assert forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) implies
            block_id.page_id == self.data@.page_id
                && block_id.block_size == self.data@.block_size by {
            assert(false);
        };
        assert forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] self.data@.block_ids.contains(block_id1)
                && #[trigger] self.data@.block_ids.contains(block_id2)
                && block_id1.page_id == block_id2.page_id
                && block_id1.idx == block_id2.idx implies block_id1 == block_id2 by {
            assert(false);
        };
    }

    proof fn wf_from_same_repr_addr(&self, old_ll: &LL)
        requires
            old_ll.wf(),
            self.data@ == old_ll.data@,
            self.perms@ == old_ll.perms@,
            self.first.addr() == old_ll.first.addr(),
        ensures
            self.wf(),
            self.len() == old_ll.len(),
            self.block_ids() == old_ll.block_ids(),
            self.fixed_page() == old_ll.fixed_page(),
            self.page_id() == old_ll.page_id(),
            self.block_size() == old_ll.block_size(),
            self.instance() == old_ll.instance(),
            self.heap_id() == old_ll.heap_id(),
    {
        reveal(LL::wf);
        reveal(LL::next_ptr);
        reveal(LL::valid_node);
        reveal(LL::len);
        reveal(LL::block_ids);
        reveal(LL::fixed_page);
        reveal(LL::page_id);
        reveal(LL::block_size);
        reveal(LL::instance);
        reveal(LL::heap_id);
        assert(self.next_ptr(self.data@.len) == old_ll.next_ptr(old_ll.data@.len));
        assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
            if 0 <= i < self.data@.len {
                assert(old_ll.valid_node(i, old_ll.next_ptr(i)));
                assert(self.next_ptr(i) == old_ll.next_ptr(i));
                assert(self.valid_node(i, self.next_ptr(i)));
            }
        };
    }

    proof fn wf_first_zero_implies_empty(&self)
        requires
            self.wf(),
            self.first.addr() == 0,
        ensures
            self.len() == 0,
            self.block_ids() == Set::empty(),
    {
        reveal(LL::wf);
        reveal(LL::next_ptr);
        reveal(LL::valid_node);
        reveal(LL::len);
        reveal(LL::block_ids);
        if self.data@.len != 0 {
            let i = (self.data@.len - 1) as nat;
            assert(0 <= i < self.data@.len);
            assert(self.valid_node(i, self.next_ptr(i)));
            assert(self.perms@.dom().contains(i));
            assert(self.next_ptr(self.data@.len) == self.perms@[i].0.ptr());
            assert(self.first.addr() == self.perms@[i].0.ptr().addr());
            assert(is_block_ptr(self.perms@[i].0.ptr() as *mut u8, self.perms@[i].2.key()));
            reveal(is_block_ptr1);
            lemma_segment_start_basics(self.perms@[i].2.key().page_id.segment_id);
            assert(segment_start(self.perms@[i].2.key().page_id.segment_id) >= 0);
            assert(self.perms@[i].0.ptr() as int > 0);
            assert(self.perms@[i].0.ptr().addr() as int == self.perms@[i].0.ptr() as int);
            assert(self.perms@[i].0.ptr().addr() != 0);
            assert(false);
        }
        assert(self.data@.block_ids.len() == 0);
        vstd::set_lib::lemma_set_empty_equivalency_len(self.data@.block_ids);
    }

    pub proof fn wf_first_addr_zero_implies_empty(&self)
        requires
            self.wf(),
            self.first_addr() == 0,
        ensures
            self.len() == 0,
            self.block_ids() == Set::empty(),
    {
        reveal(LL::first_addr);
        self.wf_first_zero_implies_empty();
    }

    proof fn entry_ptr_nonzero(&self, i: nat)
        requires
            self.wf(),
            i < self.len(),
            self.perms@.dom().contains(i),
        ensures
            self.perms@[i].0.ptr().addr() != 0,
    {
        reveal(LL::wf);
        reveal(LL::valid_node);
        reveal(LL::next_ptr);
        reveal(LL::len);
        assert(self.valid_node(i, self.next_ptr(i)));
        assert(is_block_ptr(self.perms@[i].0.ptr() as *mut u8, self.perms@[i].2.key()));
        reveal(is_block_ptr1);
        lemma_segment_start_basics(self.perms@[i].2.key().page_id.segment_id);
        assert(segment_start(self.perms@[i].2.key().page_id.segment_id) >= 0);
        assert(self.perms@[i].0.ptr() as int > 0);
        assert(self.perms@[i].0.ptr().addr() as int == self.perms@[i].0.ptr() as int);
    }

    pub proof fn two_lists_with_live_cardinality_gap(
        free: &LL,
        local_free: &LL,
        live_block_id: BlockId,
        num_blocks: nat,
    )
        requires
            free.wf(),
            local_free.wf(),
            free.fixed_page(),
            local_free.fixed_page(),
            free.page_id() == live_block_id.page_id,
            local_free.page_id() == live_block_id.page_id,
            free.block_size() == live_block_id.block_size,
            local_free.block_size() == live_block_id.block_size,
            live_block_id.idx < num_blocks,
            (forall |block_id: BlockId| #[trigger] free.block_ids().contains(block_id) ==> block_id.idx < num_blocks),
            (forall |block_id: BlockId| #[trigger] local_free.block_ids().contains(block_id) ==> block_id.idx < num_blocks),
            (forall |block_id: BlockId| #[trigger] free.block_ids().contains(block_id) ==> block_id.idx != live_block_id.idx),
            (forall |block_id: BlockId| #[trigger] local_free.block_ids().contains(block_id) ==> block_id.idx != live_block_id.idx),
            (forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] free.block_ids().contains(block_id1) && #[trigger] local_free.block_ids().contains(block_id2)
                && block_id1.idx == block_id2.idx ==> false),
            free.block_ids().disjoint(local_free.block_ids()),
            !free.block_ids().contains(live_block_id),
            !local_free.block_ids().contains(live_block_id),
        ensures
            free.len() + local_free.len() < num_blocks,
    {
        broadcast use vstd::set::group_set_lemmas;
        reveal(LL::wf);
        reveal(LL::len);
        reveal(LL::fixed_page);
        reveal(LL::page_id);
        reveal(LL::block_size);
        reveal(LL::block_ids);
        let list_set = free.block_ids() + local_free.block_ids();
        vstd::set_lib::lemma_set_disjoint_lens(free.block_ids(), local_free.block_ids());
        assert(list_set.len() == free.len() + local_free.len());
        assert(!list_set.contains(live_block_id));
        let all_set = list_set.insert(live_block_id);
        assert(all_set.len() == list_set.len() + 1) by {
            vstd::set::lemma_set_insert_len(list_set, live_block_id);
        }
        assert(all_set.len() == free.len() + local_free.len() + 1);

        assert forall |block_id: BlockId| #[trigger] all_set.contains(block_id) implies
            block_id.page_id == live_block_id.page_id && block_id.idx < num_blocks
        by {
            if block_id == live_block_id {
            } else if free.block_ids().contains(block_id) {
            } else {
                assert(local_free.block_ids().contains(block_id));
            }
        };

        assert forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] all_set.contains(block_id1) && #[trigger] all_set.contains(block_id2)
            && block_id1.page_id == block_id2.page_id
            && block_id1.idx == block_id2.idx implies block_id1 == block_id2
        by {
            if block_id1 == live_block_id {
                if block_id2 == live_block_id {
                } else {
                    if free.block_ids().contains(block_id2) {
                        assert(block_id2.idx != live_block_id.idx);
                        assert(false);
                    } else {
                        assert(local_free.block_ids().contains(block_id2));
                        assert(block_id2.idx != live_block_id.idx);
                        assert(false);
                    }
                }
            } else if block_id2 == live_block_id {
                if free.block_ids().contains(block_id1) {
                    assert(block_id1.idx != live_block_id.idx);
                    assert(false);
                } else {
                    assert(local_free.block_ids().contains(block_id1));
                    assert(block_id1.idx != live_block_id.idx);
                    assert(false);
                }
            } else if free.block_ids().contains(block_id1) && free.block_ids().contains(block_id2) {
            } else if local_free.block_ids().contains(block_id1) && local_free.block_ids().contains(block_id2) {
            } else {
                assert(free.block_ids().contains(block_id1) && local_free.block_ids().contains(block_id2)
                    || local_free.block_ids().contains(block_id1) && free.block_ids().contains(block_id2));
                if free.block_ids().contains(block_id1) {
                    assert(local_free.block_ids().contains(block_id2));
                    assert(false);
                } else {
                    assert(local_free.block_ids().contains(block_id1));
                    assert(free.block_ids().contains(block_id2));
                    assert(false);
                }
            }
        };

        block_id_set_len_bound(all_set, live_block_id.page_id, num_blocks);
        assert(free.len() + local_free.len() < num_blocks) by(nonlinear_arith)
            requires
                all_set.len() == free.len() + local_free.len() + 1,
                all_set.len() <= num_blocks;
    }

    pub proof fn block_ids_idx_lt_num_blocks(
        tracked &mut self,
        tracked inst: &Mim::Instance,
        tracked thread_token: &Mim::thread_local_state,
        thread_id: ThreadId,
        num_blocks: nat,
    )
        requires
            old(self).wf(),
            old(self).instance().id() == inst.id(),
            inst.id() == thread_token.instance_id(),
            thread_token.key() == thread_id,
            thread_token.value().pages.dom().contains(old(self).page_id()),
            thread_token.value().pages[old(self).page_id()].num_blocks == num_blocks,
        ensures
            *final(self) == *old(self),
            forall |block_id: BlockId| #[trigger] final(self).block_ids().contains(block_id) ==>
                block_id.idx < num_blocks,
    {
        reveal(LL::wf);
        reveal(LL::block_ids);
        reveal(LL::len);
        if exists |block_id: BlockId| self.block_ids().contains(block_id) && !(block_id.idx < num_blocks) {
            let block_id = choose |block_id: BlockId| self.block_ids().contains(block_id) && !(block_id.idx < num_blocks);
            self.block_ids_contains_witness(block_id);
            let i = choose |i: nat| i < self.len()
                && self.perms@.dom().contains(i)
                && self.perms@[i].2.key() == block_id;
            self.entry_token_matches_metadata(i);
            let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
                self.perms.borrow_mut().tracked_remove(i);
            assert(entry_block.key() == block_id);
            assert(entry_block.instance_id() == inst.id());
            assert(thread_token.value().pages.dom().contains(entry_block.key().page_id));
            assert(thread_token.value().pages[entry_block.key().page_id].num_blocks == num_blocks);
            free_fast_block_token_idx_lt_num_blocks(inst, thread_token, thread_id, &entry_block, num_blocks);
            self.perms.borrow_mut().tracked_insert(i, (
                entry_node,
                entry_raw,
                entry_block,
                entry_exposed,
            ));
            assert(false);
        }
        assert forall |block_id: BlockId| #[trigger] self.block_ids().contains(block_id) implies
            block_id.idx < num_blocks by {
            if !(block_id.idx < num_blocks) {
                assert(exists |bad_id: BlockId| self.block_ids().contains(bad_id) && !(bad_id.idx < num_blocks));
                assert(false);
            }
        };
    }

    pub proof fn block_ids_idx_disjoint_from(tracked &mut self, tracked other: &mut LL, tracked inst: &Mim::Instance)
        requires
            old(self).wf(),
            old(other).wf(),
            old(self).instance().id() == inst.id(),
            old(other).instance().id() == inst.id(),
        ensures
            *final(self) == *old(self),
            *final(other) == *old(other),
            forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] final(self).block_ids().contains(block_id1)
                    && #[trigger] final(other).block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx ==> false,
    {
        reveal(LL::wf);
        reveal(LL::block_ids);
        reveal(LL::len);
        if exists |block_id1: BlockId, block_id2: BlockId|
            self.block_ids().contains(block_id1)
                && other.block_ids().contains(block_id2)
                && block_id1.page_id == block_id2.page_id
                && block_id1.idx == block_id2.idx {
            let block_id1 = choose |block_id1: BlockId| exists |block_id2: BlockId|
                #[trigger] self.block_ids().contains(block_id1)
                    && #[trigger] other.block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx;
            let block_id2 = choose |block_id2: BlockId|
                #[trigger] self.block_ids().contains(block_id1)
                    && #[trigger] other.block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx;
            self.block_ids_contains_witness(block_id1);
            other.block_ids_contains_witness(block_id2);
            let i = choose |i: nat| i < self.len()
                && self.perms@.dom().contains(i)
                && self.perms@[i].2.key() == block_id1;
            let j = choose |j: nat| j < other.len()
                && other.perms@.dom().contains(j)
                && other.perms@[j].2.key() == block_id2;
            self.entry_token_matches_metadata(i);
            other.entry_token_matches_metadata(j);
            let tracked (node1, raw1, block1, exposed1) =
                self.perms.borrow_mut().tracked_remove(i);
            let tracked (node2, raw2, block2, exposed2) =
                other.perms.borrow_mut().tracked_remove(j);
            assert(block1.key() == block_id1);
            assert(block2.key() == block_id2);
            assert(block1.key().page_id == block2.key().page_id);
            assert(block1.key().idx == block2.key().idx);
            assert(block1.instance_id() == inst.id());
            assert(block2.instance_id() == inst.id());
            let tracked (Tracked(block1), Tracked(block2)) =
                LL::owned_block_tokens_same_page_idx_impossible_retain(inst, block1, block2);
            self.perms.borrow_mut().tracked_insert(i, (node1, raw1, block1, exposed1));
            other.perms.borrow_mut().tracked_insert(j, (node2, raw2, block2, exposed2));
            assert(false);
        }
        assert forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] self.block_ids().contains(block_id1)
                && #[trigger] other.block_ids().contains(block_id2)
                && block_id1.page_id == block_id2.page_id
                && block_id1.idx == block_id2.idx implies false by {
            assert(exists |a: BlockId, b: BlockId|
                self.block_ids().contains(a)
                    && other.block_ids().contains(b)
                    && a.page_id == b.page_id
                    && a.idx == b.idx);
            assert(false);
        };
    }

    pub proof fn three_lists_len_bound(
        free: &LL,
        local_free: &LL,
        thread_free: &LL,
        page_id: PageId,
        num_blocks: nat,
    )
        requires
            free.wf(),
            local_free.wf(),
            thread_free.wf(),
            free.page_id() == page_id,
            local_free.page_id() == page_id,
            thread_free.page_id() == page_id,
            forall |block_id: BlockId| #[trigger] free.block_ids().contains(block_id) ==>
                block_id.idx < num_blocks,
            forall |block_id: BlockId| #[trigger] local_free.block_ids().contains(block_id) ==>
                block_id.idx < num_blocks,
            forall |block_id: BlockId| #[trigger] thread_free.block_ids().contains(block_id) ==>
                block_id.idx < num_blocks,
            forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] free.block_ids().contains(block_id1)
                    && #[trigger] local_free.block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx ==> false,
            forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] free.block_ids().contains(block_id1)
                    && #[trigger] thread_free.block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx ==> false,
            forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] local_free.block_ids().contains(block_id1)
                    && #[trigger] thread_free.block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx ==> false,
        ensures
            free.len() + local_free.len() + thread_free.len() <= num_blocks,
    {
        broadcast use vstd::set::group_set_lemmas;
        reveal(LL::wf);
        reveal(LL::len);
        reveal(LL::block_ids);
        reveal(LL::page_id);
        let free_set = free.block_ids();
        let local_set = local_free.block_ids();
        let thread_set = thread_free.block_ids();
        assert(free_set.disjoint(local_set)) by {
            if !free_set.disjoint(local_set) {
                let block_id = choose |block_id: BlockId| free_set.contains(block_id) && local_set.contains(block_id);
                assert(false);
            }
        };
        vstd::set_lib::lemma_set_disjoint_lens(free_set, local_set);
        let first_two = free_set + local_set;
        assert(first_two.len() == free.len() + local_free.len());
        assert(first_two.disjoint(thread_set)) by {
            if !first_two.disjoint(thread_set) {
                let block_id = choose |block_id: BlockId| first_two.contains(block_id) && thread_set.contains(block_id);
                if free_set.contains(block_id) {
                    assert(false);
                } else {
                    assert(local_set.contains(block_id));
                    assert(false);
                }
            }
        };
        vstd::set_lib::lemma_set_disjoint_lens(first_two, thread_set);
        let all_set = first_two + thread_set;
        assert(all_set.len() == free.len() + local_free.len() + thread_free.len());
        assert forall |block_id: BlockId| #[trigger] all_set.contains(block_id) implies
            block_id.page_id == page_id && block_id.idx < num_blocks by {
            if free_set.contains(block_id) {
            } else if local_set.contains(block_id) {
            } else {
                assert(thread_set.contains(block_id));
            }
        };
        assert forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] all_set.contains(block_id1) && #[trigger] all_set.contains(block_id2)
            && block_id1.page_id == block_id2.page_id
            && block_id1.idx == block_id2.idx implies block_id1 == block_id2 by {
            if free_set.contains(block_id1) && free_set.contains(block_id2) {
            } else if local_set.contains(block_id1) && local_set.contains(block_id2) {
            } else if thread_set.contains(block_id1) && thread_set.contains(block_id2) {
            } else if free_set.contains(block_id1) && local_set.contains(block_id2) {
                assert(false);
            } else if local_set.contains(block_id1) && free_set.contains(block_id2) {
                assert(false);
            } else if free_set.contains(block_id1) && thread_set.contains(block_id2) {
                assert(false);
            } else if thread_set.contains(block_id1) && free_set.contains(block_id2) {
                assert(false);
            } else if local_set.contains(block_id1) && thread_set.contains(block_id2) {
                assert(false);
            } else {
                assert(thread_set.contains(block_id1));
                assert(local_set.contains(block_id2));
                assert(false);
            }
        };
        block_id_set_len_bound(all_set, page_id, num_blocks);
    }

    #[inline(always)]
    #[verus_verify]
    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self.first_addr() == 0),
            self.ptr().addr() == self.first_addr() ==> b == (self.ptr().addr() == 0),
    {
        proof! { reveal(LL::first_addr); }
        self.first.addr() == 0
    }

    #[inline(always)]
    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
        requires
            old(self).wf(),
            old(self).first_addr() != 0,
        ensures
            final(self).wf(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(self).len() == old(self).len() - 1,
            x.1@.is_range(x.0 as int, x.2@.key().block_size as int),
            x.1@.provenance() == x.0@.provenance,
            x.2@.instance_id() == old(self).instance().id(),
            old(self).fixed_page() ==> x.2@.key().page_id == old(self).page_id(),
            old(self).fixed_page() ==> x.2@.key().block_size == old(self).block_size(),
            match old(self).heap_id() {
                Some(heap_id) => x.2@.value().heap_id == Some(heap_id),
                None => true,
            },
            is_block_ptr(x.0, x.2@.key()),
    {
        let ghost old_data = self.data@;
        let ghost old_len = self.data@.len;
        let ghost pop_idx = (old_len - 1) as nat;
        proof {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::block_ids);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(LL::first_addr);
            reveal(LL::no_duplicate_keys);
            if old_len == 0 {
                assert(self.next_ptr(self.data@.len) == core::ptr::null_mut::<Node>());
                assert(self.first.addr() == 0);
                assert(false);
            }
            assert(0 <= pop_idx < old_len);
            assert(self.valid_node(pop_idx, self.next_ptr(pop_idx)));
            assert(self.perms@.dom().contains(pop_idx));
            assert(self.perms@[pop_idx].0.ptr().addr() == self.first.addr());
            assert(self.perms@[pop_idx].0.is_init());
            assert(self.data@.block_ids.contains(self.perms@[pop_idx].2.key()));
        }
        let tracked (mut points_to_node, points_to_raw, block, is_exposed) = self.perms.borrow_mut().tracked_remove((self.data@.len - 1) as nat);

        let ptr: *mut Node = with_exposed_provenance(self.first.addr(), Tracked(is_exposed));
        proof {
            assert(block.key() == old(self).perms@[pop_idx].2.key());
            assert(points_to_node.ptr().addr() == old(self).first.addr());
            assert(points_to_node.is_init());
            assert(points_to_raw.is_range(
                points_to_node.ptr().addr() + size_of::<Node>(),
                block.key().block_size - size_of::<Node>()));
            assert(points_to_raw.provenance() == points_to_node.ptr()@.provenance);
            assert(is_exposed.provenance() == points_to_raw.provenance());
            assert(ptr.addr() == points_to_node.ptr().addr());
            assert(ptr@.provenance == points_to_node.ptr()@.provenance);
            assert(ptr == points_to_node.ptr());
        }
        let node = ptr_mut_read(ptr, Tracked(&mut points_to_node));
        proof {
            assert(node.ptr.addr() == old(self).next_ptr(pop_idx).addr());
        }
        self.first = node.ptr;

        proof {
            assert(points_to_node.ptr() == ptr);
        }
        let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
        let ptru = ptr as *mut u8;

        proof {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::block_ids);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(LL::first_addr);
            reveal(LL::no_duplicate_keys);
            let ghost block_id = block.key();
            self.data = Ghost(LLData {
                fixed_page: old_data.fixed_page,
                block_size: old_data.block_size,
                page_id: old_data.page_id,
                heap_id: old_data.heap_id,
                instance: old_data.instance,
                len: pop_idx,
                block_ids: old_data.block_ids.remove(block_id),
                idx_bound: old_data.idx_bound,
            });
            assert(self.perms@.dom() =~= old(self).perms@.dom().remove(pop_idx));
            assert(self.next_ptr(self.data@.len).addr() == self.first.addr());
            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len by {
                assert(old(self).perms@.dom().contains(i));
                assert(i != pop_idx);
                assert(0 <= i < old_len);
                assert(i < pop_idx);
            }
            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
                if 0 <= i < self.data@.len {
                    assert(old(self).valid_node(i, old(self).next_ptr(i)));
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(self.next_ptr(i) == old(self).next_ptr(i));
                    assert(self.valid_node(i, self.next_ptr(i)));
                }
            }
            assert(old_data.block_ids.contains(block_id));
            assert(self.data@.block_ids.len() == self.data@.len) by {
                vstd::set::lemma_set_remove_len(old_data.block_ids, block_id);
            }
            assert forall |i: nat| 0 <= i < self.data@.len implies
                self.data@.block_ids.contains(#[trigger] self.perms@[i].2.key()) by {
                assert(old(self).data@.block_ids.contains(old(self).perms@[i].2.key()));
                assert(self.perms@[i] == old(self).perms@[i]);
                assert(self.perms@[i].2.key() != block_id) by {
                    if self.perms@[i].2.key() == block_id {
                        assert(old(self).perms@[i].2.key() == old(self).perms@[pop_idx].2.key());
                        assert(i != pop_idx);
                        assert(old(self).no_duplicate_keys());
                        assert(false);
                    }
                }
            }
            assert forall |bid: BlockId| #[trigger] self.data@.block_ids.contains(bid) implies
                exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == bid by {
                assert(old_data.block_ids.contains(bid));
                assert(bid != block_id);
                let i = choose |i: nat| 0 <= i < old_len && old(self).perms@[i].2.key() == bid;
                assert(i != pop_idx) by {
                    if i == pop_idx {
                        assert(bid == block_id);
                        assert(false);
                    }
                }
                assert(i < pop_idx);
                assert(self.perms@[i] == old(self).perms@[i]);
            }
            assert forall |bid: BlockId| #[trigger] self.data@.block_ids.contains(bid) implies
                bid.page_id == self.data@.page_id && bid.block_size == self.data@.block_size by {
                assert(old_data.block_ids.contains(bid));
            }
            assert forall |bid1: BlockId, bid2: BlockId|
                #[trigger] self.data@.block_ids.contains(bid1)
                    && #[trigger] self.data@.block_ids.contains(bid2)
                    && bid1.page_id == bid2.page_id
                    && bid1.idx == bid2.idx implies bid1 == bid2 by {
                assert(old_data.block_ids.contains(bid1));
                assert(old_data.block_ids.contains(bid2));
            }
            assert forall |i: nat, j: nat|
                0 <= i < self.data@.len && 0 <= j < self.data@.len && i != j implies
                    self.perms@[i].2.key() != self.perms@[j].2.key() by {
                assert(old(self).no_duplicate_keys());
                assert(self.perms@[i] == old(self).perms@[i]);
                assert(self.perms@[j] == old(self).perms@[j]);
            }
            assert(self.no_duplicate_keys());
            assert(self.wf());
            assert(self.len() == old(self).len() - 1);
            assert(points_to_raw.is_range(ptru as int, block.key().block_size as int));
            assert(points_to_raw.provenance() == ptru@.provenance);
            assert(block.instance_id() == old(self).instance().id());
            assert(old(self).fixed_page() ==> block.key().page_id == old(self).page_id());
            assert(old(self).fixed_page() ==> block.key().block_size == old(self).block_size());
            match old(self).heap_id() {
                Some(heap_id) => assert(block.value().heap_id == Some(heap_id)),
                None => { },
            }
            assert(is_block_ptr(ptru, block.key()));
        }

        return (ptru, Tracked(points_to_raw), Tracked(block))
    }

    // helper for clients using ghost_insert_block


    #[inline(always)]
    #[verus_verify]
    pub fn block_write_ptr(ptr: *mut Node, Tracked(perm): Tracked<PointsToRaw>, next: *mut Node)
        -> (res: (Tracked<PointsTo<Node>>, Tracked<PointsToRaw>))
        requires
            exists |block_id: BlockId|
                is_block_ptr(ptr as *mut u8, block_id)
                && perm.is_range(ptr as int, block_id.block_size as int)
                && perm.provenance() == ptr@.provenance,
        ensures
            res.0@.ptr() == ptr,
            res.0@.is_init(),
            res.0@.value().ptr == next,
            res.1@.provenance() == ptr@.provenance,
            forall |block_id: BlockId|
                is_block_ptr(ptr as *mut u8, block_id)
                && perm.is_range(ptr as int, block_id.block_size as int)
                && perm.provenance() == ptr@.provenance
                ==> res.1@.is_range(
                    ptr as int + size_of::<Node>() as int,
                    block_id.block_size as int - size_of::<Node>() as int),
    {
        let ghost block_id = choose |block_id: BlockId|
            is_block_ptr(ptr as *mut u8, block_id)
            && perm.is_range(ptr as int, block_id.block_size as int)
            && perm.provenance() == ptr@.provenance;
        proof! {
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, block_id);
            vstd::set_lib::lemma_int_range(ptr as int, ptr as int + size_of::<Node>() as int);
            vstd::set_lib::lemma_int_range(ptr as int, ptr as int + block_id.block_size as int);
            assert(set_int_range(ptr as int, ptr as int + size_of::<Node>() as int)
                .subset_of(perm.dom())) by {
                assert forall |addr: int| #[trigger] set_int_range(
                    ptr as int, ptr as int + size_of::<Node>() as int).contains(addr)
                implies perm.dom().contains(addr) by {
                    assert(ptr as int <= addr < ptr as int + size_of::<Node>() as int);
                    assert(size_of::<Node>() as int <= block_id.block_size as int);
                    assert(ptr as int <= addr < ptr as int + block_id.block_size as int);
                    assert(Set::<int>::range(
                        ptr as int,
                        ptr as int + block_id.block_size as int).contains(addr));
                }
            }
        }
        let tracked (points_to, rest) = perm.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));

        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
        proof! {
            assert(ptr.addr() as int == ptr as int);
            assert(points_to.is_range(ptr.addr() as int, size_of::<Node>() as int));
        }
        let tracked mut points_to_node = points_to.into_typed::<Node>(ptr.addr());
        proof! {
            assert(points_to_node.ptr() == ptr);
        }
        ptr_mut_write(ptr, Tracked(&mut points_to_node), Node { ptr: next });
        proof! {
            assert forall |bid: BlockId|
                is_block_ptr(ptr as *mut u8, bid)
                && perm.is_range(ptr as int, bid.block_size as int)
                && perm.provenance() == ptr@.provenance
                implies #[trigger] rest.is_range(
                    ptr as int + size_of::<Node>() as int,
                    bid.block_size as int - size_of::<Node>() as int)
            by {
                assert(size_of::<Node>() == 8);
                assert(align_of::<Node>() == 8);
                lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, bid);
                vstd::set_lib::lemma_int_range(
                    ptr as int + size_of::<Node>() as int,
                    ptr as int + bid.block_size as int);
                assert(rest.dom() =~= set_int_range(
                    ptr as int + size_of::<Node>() as int,
                    ptr as int + bid.block_size as int)) by {
                    assert forall |addr: int| rest.dom().contains(addr) implies
                        set_int_range(
                            ptr as int + size_of::<Node>() as int,
                            ptr as int + bid.block_size as int).contains(addr) by {
                        assert(rest.dom().contains(addr));
                        assert(perm.dom().contains(addr));
                        assert(!set_int_range(ptr as int, ptr as int + size_of::<Node>() as int).contains(addr));
                        assert(ptr as int <= addr < ptr as int + bid.block_size as int);
                        assert(!(ptr as int <= addr < ptr as int + size_of::<Node>() as int));
                        assert(ptr as int + size_of::<Node>() as int <= addr);
                    }
                    assert forall |addr: int| set_int_range(
                        ptr as int + size_of::<Node>() as int,
                        ptr as int + bid.block_size as int).contains(addr) implies
                        rest.dom().contains(addr) by {
                        assert(ptr as int + size_of::<Node>() as int <= addr < ptr as int + bid.block_size as int);
                        assert(perm.dom().contains(addr));
                        assert(!set_int_range(ptr as int, ptr as int + size_of::<Node>() as int).contains(addr));
                    }
                }
            }
        }
        (Tracked(points_to_node), Tracked(rest))
    }


    pub proof fn block_write_ptr_rejoin(tracked ptr_raw: PointsToRaw, tracked raw_mem: PointsToRaw,
        ptr: *mut Node, block_id: BlockId) -> (tracked joined: PointsToRaw)
        requires
            is_block_ptr(ptr as *mut u8, block_id),
            ptr_raw.is_range(ptr as int, size_of::<Node>() as int),
            raw_mem.is_range(
                ptr as int + size_of::<Node>() as int,
                block_id.block_size as int - size_of::<Node>() as int),
            ptr_raw.provenance() == raw_mem.provenance(),
        ensures
            joined.is_range(ptr as int, block_id.block_size as int),
            joined.provenance() == ptr_raw.provenance(),
    {
        assert(size_of::<Node>() == 8);
        assert(align_of::<Node>() == 8);
        lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, block_id);
        vstd::set_lib::lemma_int_range(ptr as int, ptr as int + size_of::<Node>() as int);
        vstd::set_lib::lemma_int_range(
            ptr as int + size_of::<Node>() as int,
            ptr as int + block_id.block_size as int);
        vstd::set_lib::lemma_int_range(ptr as int, ptr as int + block_id.block_size as int);
        let tracked joined = ptr_raw.join(raw_mem);
        assert(joined.dom() =~= set_int_range(ptr as int, ptr as int + block_id.block_size as int)) by {
            assert forall |addr: int| joined.dom().contains(addr) implies
                set_int_range(ptr as int, ptr as int + block_id.block_size as int).contains(addr) by {
                if ptr_raw.dom().contains(addr) {
                    assert(ptr as int <= addr < ptr as int + size_of::<Node>() as int);
                    assert(size_of::<Node>() as int <= block_id.block_size as int);
                    assert(ptr as int <= addr < ptr as int + block_id.block_size as int);
                } else {
                    assert(raw_mem.dom().contains(addr));
                    assert(ptr as int + size_of::<Node>() as int <= addr < ptr as int + block_id.block_size as int);
                    assert(ptr as int <= addr < ptr as int + block_id.block_size as int);
                }
            }
            assert forall |addr: int| set_int_range(ptr as int, ptr as int + block_id.block_size as int).contains(addr) implies
                joined.dom().contains(addr) by {
                assert(ptr as int <= addr < ptr as int + block_id.block_size as int);
                if addr < ptr as int + size_of::<Node>() as int {
                    assert(ptr_raw.dom().contains(addr));
                } else {
                    assert(ptr as int + size_of::<Node>() as int <= addr);
                    assert(raw_mem.dom().contains(addr));
                }
            }
        }
        joined
    }

}
}

verus!{
#[cfg(not(verus_keep_ghost))]
impl LL {
    #[inline(always)]
#[verifier::external_body]
    pub fn new(Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    ) -> (ll: LL)
    {
        LL {
            first: core::ptr::null_mut(),
            data: Ghost(LLData {
                fixed_page, block_size, page_id, instance, len: 0, heap_id,
            }),
            perms: Tracked(Map::tracked_empty()),
        }
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn empty() -> (ll: LL)
    {
        LL::new(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }
}
}

verus!{
#[cfg(verus_keep_ghost)]
impl LL {
    #[inline(always)]
    pub fn new(Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    ) -> (ll: LL)
        ensures
            ll.wf(),
            ll.len() == 0,
            ll.first_addr() == 0,
            ll.ptr().addr() == 0,
            ll.page_id() == page_id,
            ll.fixed_page() == fixed_page,
            ll.instance() == instance,
            ll.block_size() == block_size,
            ll.heap_id() == heap_id,
    {
        proof! {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::first_addr);
            reveal(LL::ptr);
            reveal(LL::page_id);
            reveal(LL::fixed_page);
            reveal(LL::instance);
            reveal(LL::block_size);
            reveal(LL::heap_id);
        }
        LL {
            first: core::ptr::null_mut(),
            data: Ghost(LLData {
                fixed_page, block_size, page_id, instance, len: 0, heap_id, block_ids: Set::empty(), idx_bound: 0,
            }),
            perms: Tracked(Map::tracked_empty()),
        }
    }

    #[inline(always)]
    pub fn empty() -> (ll: LL) ensures ll.wf(),
            ll.len() == 0,
            ll.first_addr() == 0,
            ll.ptr().addr() == 0,
    {
        LL::new(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }
}
}

verus!{
impl LL {

    #[inline(always)]
    pub fn set_ghost_data(
        &mut self,
        Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    )
        requires
            old(self).wf(),
            old(self).len() == 0,
        ensures
            final(self).wf(),
            final(self).len() == 0,
            final(self).first_addr() == 0,
            final(self).ptr().addr() == 0,
            final(self).page_id() == page_id,
            final(self).fixed_page() == fixed_page,
            final(self).instance() == instance,
            final(self).block_size() == block_size,
            final(self).heap_id() == heap_id,
    {
        proof! {
            reveal(LL::wf);
            reveal(LL::len);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::first_addr);
            reveal(LL::ptr);
            reveal(LL::page_id);
            reveal(LL::fixed_page);
            reveal(LL::instance);
            reveal(LL::block_size);
            reveal(LL::heap_id);
            self.data = Ghost(LLData {
                fixed_page,
                block_size,
                page_id,
                heap_id,
                instance,
                len: 0,
                block_ids: Set::empty(),
                idx_bound: 0,
            });
        }
    }

    // Traverse `other` to find the tail, append `self`,
    // and leave the resulting list in `self`.
    // Returns the # of entries in `other`

    #[inline(always)]
    #[verifier::rlimit(200)]
    pub fn append(&mut self, other: &mut LL) -> (other_len: u32)
        requires
            old(self).wf(),
            old(other).wf(),
            old(self).fixed_page() == old(other).fixed_page(),
            old(self).page_id() == old(other).page_id(),
            old(self).block_size() == old(other).block_size(),
            old(self).instance() == old(other).instance(),
            old(self).heap_id() == old(other).heap_id(),
            old(other).len() < u32::MAX,
            old(self).len() + old(other).len() <= u32::MAX,
            forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] old(self).block_ids().contains(block_id1)
                    && #[trigger] old(other).block_ids().contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx ==> false,
        ensures
            final(self).wf(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(self).len() == old(self).len() + old(other).len(),
            final(self).block_ids() == old(self).block_ids() + old(other).block_ids(),
            final(other).wf(),
            final(other).fixed_page() == old(other).fixed_page(),
            final(other).page_id() == old(other).page_id(),
            final(other).block_size() == old(other).block_size(),
            final(other).instance() == old(other).instance(),
            final(other).heap_id() == old(other).heap_id(),
            final(other).len() == 0,
            final(other).block_ids() == Set::empty(),
            other_len as nat == old(other).len(),
    {
        if other.first.addr() == 0 {
            proof! {
                other.wf_first_zero_implies_empty();
                assert(other.len() == 0);
                assert(other.block_ids() == Set::empty());
                assert(self.len() == old(self).len() + old(other).len());
                assert(self.block_ids() == old(self).block_ids() + old(other).block_ids());
            }
            return 0;
        }

        let mut count = 1;
        let mut p = other.first;
        proof! {
            reveal(LL::wf);
            reveal(LL::valid_node);
            reveal(LL::next_ptr);
            reveal(LL::len);
            if other.len() == 0 {
                assert(other.next_ptr(other.len()).addr() == 0);
                assert(other.first.addr() == 0);
                assert(false);
            }
            let idx = (other.len() - count) as nat;
            assert(idx == other.len() - 1);
            assert(other.valid_node(idx, other.next_ptr(idx)));
            assert(other.perms@.dom().contains(idx));
        }
        loop
            invariant
                1 <= count <= other.len(),
                other.len() < u32::MAX,
                other.wf(),
                p.addr() == other.perms@[(other.len() - count) as nat].0.ptr().addr(),
            ensures
                count == other.len(),
                p == other.perms@[0].0.ptr(),
        {

            proof! {
                reveal(LL::wf);
                reveal(LL::valid_node);
                reveal(LL::next_ptr);
                reveal(LL::len);
                let idx = (other.len() - count) as nat;
                assert(other.valid_node(idx, other.next_ptr(idx)));
                assert(other.perms@.dom().contains(idx));
                assert(other.perms@[idx].3.provenance() == other.perms@[idx].0.ptr()@.provenance);
            }
            p = with_exposed_provenance(p.addr(),
                Tracked(other.perms.borrow().tracked_borrow((other.len() - count) as nat).3));
            proof! {
                let idx = (other.len() - count) as nat;
                assert(p == other.perms@[idx].0.ptr());
            }

            let next = *ptr_ref(p, Tracked(&other.perms.borrow().tracked_borrow((other.len() - count) as nat).0));
            if next.ptr.addr() != 0 {
                proof! {
                    reveal(LL::wf);
                    reveal(LL::valid_node);
                    reveal(LL::next_ptr);
                    reveal(LL::len);
                    let idx = (other.len() - count) as nat;
                    assert(other.valid_node(idx, other.next_ptr(idx)));
                    if idx == 0 {
                        assert(other.next_ptr(idx).addr() == 0);
                        assert(next.ptr.addr() == 0);
                        assert(false);
                    }
                    let next_idx = (idx - 1) as nat;
                    assert(next_idx < other.len());
                    assert(other.valid_node(next_idx, other.next_ptr(next_idx)));
                    assert(other.perms@.dom().contains(next_idx));
                }
                count += 1;
                p = next.ptr;
                proof! {
                    let idx = (other.len() - count) as nat;
                    assert(other.perms@.dom().contains(idx));
                    assert(p.addr() == other.perms@[idx].0.ptr().addr());
                }
            } else {
                proof! {
                    reveal(LL::wf);
                    reveal(LL::valid_node);
                    reveal(LL::next_ptr);
                    reveal(LL::len);
                    let idx = (other.len() - count) as nat;
                    assert(other.valid_node(idx, other.next_ptr(idx)));
                    if idx != 0 {
                        let prev_idx = (idx - 1) as nat;
                        assert(prev_idx < other.len());
                        assert(other.valid_node(prev_idx, other.next_ptr(prev_idx)));
                        assert(other.perms@.dom().contains(prev_idx));
                        other.entry_ptr_nonzero(prev_idx);
                        assert(other.next_ptr(idx) == other.perms@[prev_idx].0.ptr());
                        assert(next.ptr.addr() == other.next_ptr(idx).addr());
                        assert(false);
                    }
                    assert(idx == 0);
                    assert(count == other.len());
                    assert(p == other.perms@[0].0.ptr());
                }
                break;
            }
        }

        let ghost old_other = *other;
        let ghost old_self = *self;

        proof! {
            reveal(LL::wf);
            reveal(LL::valid_node);
            reveal(LL::next_ptr);
            reveal(LL::len);
            assert(other.len() > 0);
            assert(other.valid_node(0, other.next_ptr(0)));
            assert(other.perms@.dom().contains(0));
        }
        let tracked mut perm = other.perms.borrow_mut().tracked_remove(0);
        let tracked (mut a, b, c, exposed) = perm;
        proof! {
            reveal(LL::wf);
            reveal(LL::valid_node);
            reveal(LL::next_ptr);
            assert(old_other.valid_node(0, old_other.next_ptr(0)));
            assert(old_other.perms@.dom().contains(0));
            assert(old_other.perms@[0].0.is_init());
            assert(a == old_other.perms@[0].0);
            assert(a.ptr() == old_other.perms@[0].0.ptr());
            assert(p == old_other.perms@[0].0.ptr());
            assert(a.ptr() == p);
            assert(a.is_init());
        }
        let _ = ptr_mut_read(p, Tracked(&mut a));
        ptr_mut_write(p, Tracked(&mut a), Node { ptr: self.first });
        proof! {
            assert(a.ptr() == old_other.perms@[0].0.ptr());
            assert(a.is_init());
            assert(a.value().ptr == old_self.first);
        }

        self.first = other.first;
        other.first = core::ptr::null_mut();

        proof! {
            let ghost self_len = old_self.len();
            let ghost other_len = old_other.len();
            let ghost old_self_block_ids = old_self.block_ids();
            let ghost old_other_block_ids = old_other.block_ids();
            assert(count as nat == other_len);
            assert(other_len > 0);
            assert(self_len + other_len <= u32::MAX);
            assert(other.perms@.dom() == old_other.perms@.dom().remove(0));
            let ghost rest_dom = other.perms@.dom();
            let tracked rest = other.perms.borrow_mut().tracked_remove_keys(rest_dom);
            let ghost shifted_dom = rest_dom.map_by(
                |i: nat| (self_len + i) as nat,
                |j: nat| (j - self_len) as nat,
            );
            let ghost key_map = Map::new(shifted_dom, |j: nat| (j - self_len) as nat);
            assert forall |j: nat| #[trigger] key_map.contains_key(j) implies rest.contains_key(key_map[j]) by {
                assert(shifted_dom.contains(j));
                let i0 = (j - self_len) as nat;
                assert(rest_dom.contains(i0));
                assert(j == self_len + i0);
                assert(self_len < j < self_len + other_len);
                assert(1 <= j - self_len < other_len);
                assert(key_map[j] == (j - self_len) as nat);
                assert(old_other.perms@.dom().contains(key_map[j]));
                assert(key_map[j] != 0);
                assert(rest_dom.contains(key_map[j]));
            };
            assert forall |j1: nat, j2: nat|
                j1 != j2 && key_map.contains_key(j1) && key_map.contains_key(j2) implies key_map[j1] != key_map[j2] by {
                assert(key_map[j1] == (j1 - self_len) as nat);
                assert(key_map[j2] == (j2 - self_len) as nat);
            };
            let tracked shifted_rest = Map::tracked_map_keys(rest, key_map);
            self.perms.borrow_mut().tracked_insert(self_len, (a, b, c, exposed));
            self.perms.borrow_mut().tracked_union_prefer_right(shifted_rest);
            self.data = Ghost(LLData {
                fixed_page: old_self.data@.fixed_page,
                block_size: old_self.data@.block_size,
                page_id: old_self.data@.page_id,
                heap_id: old_self.data@.heap_id,
                instance: old_self.data@.instance,
                len: self_len + other_len,
                block_ids: old_self_block_ids + old_other_block_ids,
                idx_bound: old_self.data@.idx_bound,
            });
            other.data = Ghost(LLData {
                fixed_page: old_other.data@.fixed_page,
                block_size: old_other.data@.block_size,
                page_id: old_other.data@.page_id,
                heap_id: old_other.data@.heap_id,
                instance: old_other.data@.instance,
                len: 0,
                block_ids: Set::empty(),
                idx_bound: old_other.data@.idx_bound,
            });
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::block_ids);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(LL::no_duplicate_keys);
            other.empty_fields_wf();
            assert(self.perms@.dom() =~= old_self.perms@.dom().insert(self_len) + shifted_dom);
            assert forall |j: nat| #[trigger] old_self.perms@.dom().contains(j) implies
                self.perms@.dom().contains(j) && self.perms@[j] == old_self.perms@[j] by {
                assert(!shifted_dom.contains(j)) by {
                    if shifted_dom.contains(j) {
                        let i0 = choose |i: nat| rest_dom.contains(i) && j == self_len + i;
                        assert(old_other.perms@.dom().contains(i0));
                        assert(0 <= i0 < other_len);
                        assert(j >= self_len);
                        assert(j < self_len);
                        assert(false);
                    }
                };
            };
            assert(self.perms@.dom().contains(self_len));
            assert(self.perms@[self_len].0 == a);
            assert(self.perms@[self_len].1 == b);
            assert(self.perms@[self_len].2 == c);
            assert(self.perms@[self_len].3 == exposed);
            assert(self.perms@[self_len].2.key() == old_other.perms@[0].2.key());
            assert forall |j: nat| #[trigger] shifted_dom.contains(j) implies
                self.perms@.dom().contains(j)
                    && self.perms@[j] == old_other.perms@[(j - self_len) as nat] by {
                assert(key_map.contains_key(j));
                assert(shifted_rest.contains_key(j));
                assert(self.perms@[j] == shifted_rest[j]);
                assert(shifted_rest[j] == rest[key_map[j]]);
                assert(key_map[j] == (j - self_len) as nat);
                assert(rest[key_map[j]] == old_other.perms@[key_map[j]]);
            };
            assert(self.len() == self_len + other_len);
            assert(self.block_ids() == old_self_block_ids + old_other_block_ids);
            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len by {
                if old_self.perms@.dom().contains(i) {
                    assert(0 <= i < self_len);
                } else if i == self_len {
                    assert(other_len > 0);
                } else {
                    assert(shifted_dom.contains(i));
                    let k = (i - self_len) as nat;
                    assert(rest_dom.contains(k));
                    assert(old_other.perms@.dom().contains(k));
                    assert(0 <= k < other_len);
                    assert(i == self_len + k);
                }
            };
            assert(self.next_ptr(self.data@.len).addr() == self.first.addr()) by {
                assert(old_other.next_ptr(other_len).addr() == old_other.first.addr());
                if other_len == 1 {
                    assert(self.data@.len - 1 == self_len);
                    assert(self.next_ptr(self.data@.len) == self.perms@[self_len].0.ptr());
                    assert(self.perms@[self_len].0.ptr().addr() == old_other.perms@[0].0.ptr().addr());
                    assert(old_other.next_ptr(other_len) == old_other.perms@[0].0.ptr());
                } else {
                    let j = (self_len + other_len - 1) as nat;
                    let k = (other_len - 1) as nat;
                    assert(k != 0);
                    assert(rest_dom.contains(k));
                    assert(shifted_dom.contains(j));
                    assert(self.perms@[j] == old_other.perms@[k]);
                    assert(self.next_ptr(self.data@.len) == self.perms@[j].0.ptr());
                    assert(old_other.next_ptr(other_len) == old_other.perms@[k].0.ptr());
                }
            };
            assert(old_self_block_ids.disjoint(old_other_block_ids)) by {
                if !old_self_block_ids.disjoint(old_other_block_ids) {
                    let block_id = choose |block_id: BlockId|
                        old_self_block_ids.contains(block_id) && old_other_block_ids.contains(block_id);
                    assert(false);
                }
            };
            vstd::set_lib::lemma_set_disjoint_lens(old_self_block_ids, old_other_block_ids);
            assert(self.data@.block_ids.len() == self.data@.len);
            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
                if 0 <= i < self.data@.len {
                    if i < self_len {
                        assert(old_self.valid_node(i, old_self.next_ptr(i)));
                        assert(old_self.perms@.dom().contains(i));
                        assert(self.perms@[i] == old_self.perms@[i]);
                        if i == 0 {
                            assert(self.next_ptr(i).addr() == 0);
                            assert(old_self.next_ptr(i).addr() == 0);
                        } else {
                            assert(i - 1 < self_len);
                            assert(old_self.valid_node((i - 1) as nat, old_self.next_ptr((i - 1) as nat)));
                            assert(old_self.perms@.dom().contains((i - 1) as nat));
                            assert(self.perms@[(i - 1) as nat] == old_self.perms@[(i - 1) as nat]);
                            assert(self.next_ptr(i) == old_self.next_ptr(i));
                        }
                        assert(self.data@.fixed_page == old_self.data@.fixed_page);
                        assert(self.data@.block_size == old_self.data@.block_size);
                        assert(self.data@.page_id == old_self.data@.page_id);
                        assert(self.data@.heap_id == old_self.data@.heap_id);
                        assert(self.data@.instance == old_self.data@.instance);
                        assert(self.valid_node(i, self.next_ptr(i)));
                    } else if i == self_len {
                        assert(old_other.valid_node(0, old_other.next_ptr(0)));
                        assert(old_other.perms@.dom().contains(0));
                        assert(self.perms@[i].0 == a);
                        assert(self.perms@[i].1 == b);
                        assert(self.perms@[i].2 == c);
                        assert(self.perms@[i].3 == exposed);
                        assert(a.ptr() == old_other.perms@[0].0.ptr());
                        assert(a.is_init());
                        assert(b == old_other.perms@[0].1);
                        assert(c == old_other.perms@[0].2);
                        assert(exposed == old_other.perms@[0].3);
                        if self_len == 0 {
                            assert(old_self.next_ptr(0).addr() == old_self.first.addr());
                            assert(old_self.first.addr() == 0);
                            assert(self.next_ptr(i).addr() == 0);
                        } else {
                            let prev = (self_len - 1) as nat;
                            assert(old_self.valid_node(prev, old_self.next_ptr(prev)));
                            assert(old_self.perms@.dom().contains(prev));
                            assert(self.perms@[prev] == old_self.perms@[prev]);
                            assert(old_self.next_ptr(self_len).addr() == old_self.first.addr());
                            assert(self.next_ptr(i).addr() == old_self.first.addr());
                        }
                        assert(a.value().ptr.addr() == self.next_ptr(i).addr());
                        assert(self.data@.fixed_page == old_other.data@.fixed_page);
                        assert(self.data@.block_size == old_other.data@.block_size);
                        assert(self.data@.page_id == old_other.data@.page_id);
                        assert(self.data@.heap_id == old_other.data@.heap_id);
                        assert(self.data@.instance == old_other.data@.instance);
                        assert(self.valid_node(i, self.next_ptr(i)));
                    } else {
                        let k = (i - self_len) as nat;
                        assert(0 < k < other_len);
                        assert(old_other.valid_node(k, old_other.next_ptr(k)));
                        assert(old_other.perms@.dom().contains(k));
                        assert(shifted_dom.contains(i));
                        assert(self.perms@[i] == old_other.perms@[k]);
                        if k == 1 {
                            assert(i == self_len + 1);
                            assert(self.next_ptr(i) == self.perms@[self_len].0.ptr());
                            assert(self.perms@[self_len].0.ptr() == old_other.perms@[0].0.ptr());
                            assert(old_other.next_ptr(k) == old_other.perms@[0].0.ptr());
                        } else {
                            let prev_i = (i - 1) as nat;
                            let prev_k = (k - 1) as nat;
                            assert(prev_k != 0);
                            assert(old_other.valid_node(prev_k, old_other.next_ptr(prev_k)));
                            assert(old_other.perms@.dom().contains(prev_k));
                            assert(rest_dom.contains(prev_k));
                            assert(shifted_dom.contains(prev_i));
                            assert(prev_i == self_len + prev_k);
                            assert(self.perms@[prev_i] == old_other.perms@[prev_k]);
                            assert(self.next_ptr(i) == old_other.next_ptr(k));
                        }
                        assert(self.data@.fixed_page == old_other.data@.fixed_page);
                        assert(self.data@.block_size == old_other.data@.block_size);
                        assert(self.data@.page_id == old_other.data@.page_id);
                        assert(self.data@.heap_id == old_other.data@.heap_id);
                        assert(self.data@.instance == old_other.data@.instance);
                        assert(self.valid_node(i, self.next_ptr(i)));
                    }
                }
            };
            assert forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) implies
                exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == block_id by {
                if old_self_block_ids.contains(block_id) {
                    let i = choose |i: nat| 0 <= i < self_len && old_self.perms@[i].2.key() == block_id;
                    assert(old_self.valid_node(i, old_self.next_ptr(i)));
                    assert(old_self.perms@.dom().contains(i));
                    assert(self.perms@[i] == old_self.perms@[i]);
                } else {
                    assert(old_other_block_ids.contains(block_id));
                    let k = choose |i: nat| 0 <= i < other_len && old_other.perms@[i].2.key() == block_id;
                    assert(old_other.valid_node(k, old_other.next_ptr(k)));
                    assert(old_other.perms@.dom().contains(k));
                    if k == 0 {
                        assert(self.perms@[self_len].2.key() == block_id);
                    } else {
                        let i = (self_len + k) as nat;
                        assert(rest_dom.contains(k));
                        assert(shifted_dom.contains(i));
                        assert(self.perms@[i] == old_other.perms@[k]);
                        assert(0 <= i < self.data@.len);
                    }
                }
            };
            assert forall |i: nat| 0 <= i < self.data@.len implies
                self.data@.block_ids.contains(#[trigger] self.perms@[i].2.key()) by {
                if i < self_len {
                    assert(old_self.valid_node(i, old_self.next_ptr(i)));
                    assert(old_self.perms@.dom().contains(i));
                    assert(self.perms@[i] == old_self.perms@[i]);
                    assert(old_self_block_ids.contains(old_self.perms@[i].2.key()));
                } else if i == self_len {
                    assert(self.perms@[i].2.key() == old_other.perms@[0].2.key());
                    assert(old_other_block_ids.contains(old_other.perms@[0].2.key()));
                } else {
                    let k = (i - self_len) as nat;
                    assert(0 < k < other_len);
                    assert(old_other.valid_node(k, old_other.next_ptr(k)));
                    assert(old_other.perms@.dom().contains(k));
                    assert(rest_dom.contains(k));
                    assert(shifted_dom.contains(i));
                    assert(self.perms@[i] == old_other.perms@[k]);
                    assert(old_other_block_ids.contains(old_other.perms@[k].2.key()));
                }
            };
            assert forall |block_id: BlockId| #[trigger] self.data@.block_ids.contains(block_id) implies
                block_id.page_id == self.data@.page_id
                    && block_id.block_size == self.data@.block_size by {
                if old_self_block_ids.contains(block_id) {
                } else {
                    assert(old_other_block_ids.contains(block_id));
                }
            };
            assert forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] self.data@.block_ids.contains(block_id1)
                    && #[trigger] self.data@.block_ids.contains(block_id2)
                    && block_id1.page_id == block_id2.page_id
                    && block_id1.idx == block_id2.idx implies block_id1 == block_id2 by {
                if old_self_block_ids.contains(block_id1) && old_self_block_ids.contains(block_id2) {
                } else if old_other_block_ids.contains(block_id1) && old_other_block_ids.contains(block_id2) {
                } else if old_self_block_ids.contains(block_id1) && old_other_block_ids.contains(block_id2) {
                    assert(false);
                } else {
                    assert(old_other_block_ids.contains(block_id1));
                    assert(old_self_block_ids.contains(block_id2));
                    assert(false);
                }
            };
            assert forall |i: nat, j: nat|
                0 <= i < self.data@.len && 0 <= j < self.data@.len && i != j implies
                    self.perms@[i].2.key() != self.perms@[j].2.key() by {
                if i < self_len {
                    assert(old_self.valid_node(i, old_self.next_ptr(i)));
                    assert(old_self.perms@.dom().contains(i));
                    assert(self.perms@[i] == old_self.perms@[i]);
                    if j < self_len {
                        assert(old_self.valid_node(j, old_self.next_ptr(j)));
                        assert(old_self.perms@.dom().contains(j));
                        assert(self.perms@[j] == old_self.perms@[j]);
                        assert(old_self.no_duplicate_keys());
                    } else {
                        assert(old_self_block_ids.contains(self.perms@[i].2.key()));
                        if j == self_len {
                            assert(self.perms@[j].2.key() == old_other.perms@[0].2.key());
                            assert(old_other_block_ids.contains(self.perms@[j].2.key()));
                        } else {
                            let k = (j - self_len) as nat;
                            assert(0 < k < other_len);
                            assert(old_other.valid_node(k, old_other.next_ptr(k)));
                            assert(old_other.perms@.dom().contains(k));
                            assert(k != 0);
                            assert(rest_dom.contains(k));
                            assert(shifted_dom.contains(j));
                            assert(self.perms@[j] == old_other.perms@[k]);
                            assert(old_other_block_ids.contains(self.perms@[j].2.key()));
                        }
                        if self.perms@[i].2.key() == self.perms@[j].2.key() {
                            assert(!old_self_block_ids.disjoint(old_other_block_ids));
                            assert(false);
                        }
                    }
                } else {
                    if i == self_len {
                        assert(self.perms@[i].2.key() == old_other.perms@[0].2.key());
                    } else {
                        let k = (i - self_len) as nat;
                        assert(0 < k < other_len);
                        assert(old_other.valid_node(k, old_other.next_ptr(k)));
                        assert(old_other.perms@.dom().contains(k));
                        assert(k != 0);
                        assert(rest_dom.contains(k));
                        assert(shifted_dom.contains(i));
                        assert(self.perms@[i] == old_other.perms@[k]);
                    }
                    assert(old_other_block_ids.contains(self.perms@[i].2.key()));
                    if j < self_len {
                        assert(old_self.valid_node(j, old_self.next_ptr(j)));
                        assert(old_self.perms@.dom().contains(j));
                        assert(self.perms@[j] == old_self.perms@[j]);
                        assert(old_self_block_ids.contains(self.perms@[j].2.key()));
                        if self.perms@[i].2.key() == self.perms@[j].2.key() {
                            assert(!old_self_block_ids.disjoint(old_other_block_ids));
                            assert(false);
                        }
                    } else {
                        if j == self_len {
                            assert(self.perms@[j].2.key() == old_other.perms@[0].2.key());
                        } else {
                            let k2 = (j - self_len) as nat;
                            assert(0 < k2 < other_len);
                            assert(old_other.valid_node(k2, old_other.next_ptr(k2)));
                            assert(old_other.perms@.dom().contains(k2));
                            assert(k2 != 0);
                            assert(rest_dom.contains(k2));
                            assert(shifted_dom.contains(j));
                            assert(self.perms@[j] == old_other.perms@[k2]);
                        }
                        assert(old_other_block_ids.contains(self.perms@[j].2.key()));
                        if i == self_len {
                            if j == self_len {
                            } else {
                                assert(old_other.no_duplicate_keys());
                            }
                        } else if j == self_len {
                            assert(old_other.no_duplicate_keys());
                        } else {
                            assert(old_other.no_duplicate_keys());
                        }
                    }
                }
            };
            assert(self.no_duplicate_keys());
            assert(self.wf());
        }

        return count;
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

    #[inline(always)]
#[verifier::external_body]
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
        ensures
            final(self).wf(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(self).len() == old(self).len() + extend,
    {
        // based on mi_page_free_list_extend

        let tracked mut points_to_raw = PointsToRaw::empty(start@.provenance);
        let tracked mut new_map: Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)> = Map::tracked_empty();

        let mut block = start.addr();
        let Tracked(exposed) = expose_provenance(start);
        let ghost mut i: int = 0;
        let ghost tokens_snap = *tokens;
        while block < last.addr()
            invariant 0 <= i < extend,
              start as int + extend * bsize <= usize::MAX,
              block == start as int + i * bsize,
              last as int == start.addr() + (extend - 1) * bsize,
              points_to_raw.is_range(block as int, (extend - i) * bsize),
              points_to_raw.provenance() == start@.provenance,
              start@.provenance == self.data@.page_id.segment_id.provenance,
              start@.provenance == exposed.provenance(),
              INTPTR_SIZE as int <= bsize,
              block as int % INTPTR_SIZE as int == 0,
              bsize as int % INTPTR_SIZE as int == 0,
              *tokens =~= tokens_snap.remove_keys(
                  set_int_range(cap as int, cap as int + i)),

              forall |j| #![trigger tokens.dom().contains(j)]
                  #![trigger tokens.index(j)]
                cap + i <= j < cap + extend ==>
                  tokens.dom().contains(j) && tokens[j] == tokens_snap[j],
              forall |j| (self.data@.len + extend - i <= j < self.data@.len + extend)
                    <==> #[trigger] new_map.dom().contains(j),
              *old(self) == *self,
              forall |j|
                  #![trigger new_map.dom().contains(j)]
                  #![trigger new_map.index(j)]
                ((self.data@.len + extend - i <= j < self.data@.len + extend)
                    ==> { let k = self.data@.len + extend - 1 - j; {
                      &&& new_map[j].2 == tokens_snap[cap + k]
                      &&& new_map[j].0.ptr() as int == start as int + k * bsize
                      &&& new_map[j].0.ptr()@.provenance == start@.provenance
                      &&& new_map[j].0.is_init()
                      &&& new_map[j].0.value().ptr as int == start.addr() + (k+1) * bsize
                      &&& new_map[j].0.value().ptr@.provenance == start@.provenance
                      &&& new_map[j].1.is_range(
                         start.addr() + k * bsize + size_of::<Node>(),
                         bsize - size_of::<Node>())
                      &&& new_map[j].1.provenance() == start@.provenance
                      &&& new_map[j].3.provenance() == start@.provenance
                }})
        {

            let next: *mut Node = start.with_addr(block + bsize) as *mut Node;

            let tracked (points_to, rest) = points_to_raw.split(set_int_range(block as int, block as int + bsize as int));
            let tracked (points_to1, points_to2) = points_to.split(set_int_range(block as int, block as int + size_of::<Node>() as int));
            vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
            let tracked mut points_to_node = points_to1.into_typed::<Node>(block);

            let block_ptr = next.with_addr(block);
            ptr_mut_write(block_ptr, Tracked(&mut points_to_node), Node { ptr: next });

            block = next.addr();

        }

        

        

        

        let tracked (points_to, rest) = points_to_raw.split(set_int_range(block as int, block as int + bsize as int));
        let tracked (points_to1, points_to2) = points_to.split(set_int_range(block as int, block as int + size_of::<Node>() as int));
        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
        let tracked mut points_to_node = points_to1.into_typed::<Node>(block);

        let block_ptr = start.with_addr(block) as *mut Node;
        ptr_mut_write(block_ptr, Tracked(&mut points_to_node), Node { ptr: self.first });

        self.first = start as *mut Node;

    }

#[verifier::external_body]
    pub fn make_empty(&mut self) -> (llgstr: Tracked<LLGhostStateToReconvene>)
        ensures
            final(self).wf(),
            final(self).len() == 0,
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).heap_id() == old(self).heap_id(),
            llgstr@.page_id == old(self).page_id(),
            llgstr@.block_size == old(self).block_size(),
            llgstr@.instance == old(self).instance(),
    {

        self.first = core::ptr::null_mut();

        let ghost block_size = self.block_size();
        let ghost page_id = self.page_id();
        let ghost instance = self.instance();
        let tracked map;
        Tracked(LLGhostStateToReconvene {
            map: map,
            block_size,
            page_id,
            instance,
        })
    }

    #[verifier::external_body]
    pub proof fn reconvene_state(
        tracked inst: Mim::Instance,
        tracked ts: &Mim::thread_local_state,
        tracked llgstr1: LLGhostStateToReconvene,
        tracked llgstr2: LLGhostStateToReconvene,
        n_blocks: int,
    ) -> (tracked res: (PointsToRaw, Map<BlockId, Mim::block>))
        ensures
            res.0.provenance() == llgstr1.page_id.segment_id.provenance,
            res.0.dom() == set_int_range(
                page_start(llgstr1.page_id) + start_offset(llgstr1.block_size as int),
                page_start(llgstr1.page_id) + start_offset(llgstr1.block_size as int)
                    + n_blocks * llgstr1.block_size as int),
            res.1.len() == n_blocks,
            forall |block_id: BlockId| #[trigger] res.1.dom().contains(block_id) ==>
                res.1[block_id].instance_id() == inst.id(),
            forall |block_id: BlockId| #[trigger] res.1.dom().contains(block_id) ==>
                res.1[block_id].key() == block_id,
            forall |block_id: BlockId| #[trigger] res.1.dom().contains(block_id) ==>
                block_id.page_id == llgstr1.page_id,
    {
        unimplemented!();
    }

}

pub open spec fn has_idx(map: Map<nat, (PointsToRaw, Mim::block)>, i: nat) -> bool {
    exists |p: nat| map.dom().contains(p) && map[p].1.key().idx == i
}

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::range(lo, hi)
}

pub open spec fn llgstr_wf(llgstr: LLGhostStateToReconvene) -> bool {
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
}
}

verus!{
#[cfg(not(verus_keep_ghost))]
impl ThreadLLSimple {
    #[inline(always)]
#[verifier::external_body]
    pub fn empty(Ghost(instance): Ghost<Mim::Instance>, Ghost(heap_id): Ghost<HeapId>) -> (s: Self)
    {
        let p: *mut Node = core::ptr::null_mut();
        Self {
            instance: Ghost(instance),
            heap_id: Ghost(heap_id),
            atomic: AtomicPtr::new(Ghost((Ghost(instance), Ghost(heap_id))), core::ptr::null_mut(), Tracked(Tracked(LL { first: p, data: Ghost(LLData { fixed_page: false, block_size: arbitrary(), page_id: arbitrary(), instance, len: 0, heap_id: Some(heap_id), }), perms: Tracked(Map::tracked_empty()), })),),
        }
    }
}
}

#[cfg(verus_keep_ghost)]
verus!{
impl ThreadLLSimple {
    #[inline(always)]
#[verifier::external_body]
    pub fn empty(Ghost(instance): Ghost<Mim::Instance>, Ghost(heap_id): Ghost<HeapId>) -> (s: Self)
        ensures
            s.wf(),
            s.instance@ == instance,
            s.heap_id@ == heap_id,
    {
        let p: *mut Node = core::ptr::null_mut();
        Self {
            instance: Ghost(instance),
            heap_id: Ghost(heap_id),
            atomic: AtomicPtr::new(Ghost((Ghost(instance), Ghost(heap_id))), core::ptr::null_mut(), Tracked(Tracked(LL { first: p, data: Ghost(LLData { fixed_page: false, block_size: arbitrary(), page_id: arbitrary(), instance, len: 0, heap_id: Some(heap_id), block_ids: Set::empty(), idx_bound: 0, }), perms: Tracked(Map::tracked_empty()), })),),
        }
    }
}
}

verus!{
impl ThreadLLSimple {

    // Oughta have a similar spec as LL:insert_block except that
    //  (i) self argument is a & reference so we don't need to talk about how it updates
    //  (ii) is we don't expose the length

}
}

verus!{
impl ThreadLLSimple {
    #[inline(always)]
    #[cfg(any())]
#[verifier::external_body]
    pub fn atomic_insert_block(&self, ptr: *mut Node,
        Tracked(points_to_raw): Tracked<PointsToRaw>,
        Tracked(block_token): Tracked<Mim::block>,
    )
    {
        let tracked mut points_to_raw = points_to_raw;
        let tracked mut block_token_opt = Some(block_token);

        let Tracked(exposed) = expose_provenance(ptr);

        loop
            invariant_except_break
                block_token_opt == Some(block_token),

                self.wf(),
                points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
                points_to_raw.provenance() == ptr@.provenance,
                exposed.provenance() == ptr@.provenance,

                block_token.instance_id() == self.instance@.id(),
                block_token.value().heap_id == Some(self.heap_id@),
                is_block_ptr(ptr as *mut u8, block_token.key()),
        {
            let next_ptr = atomic_with_ghost!(
                &self.atomic => load(); ghost g => { });

            let (Tracked(ptr_mem0), Tracked(raw_mem0)) = LL::block_write_ptr(ptr, Tracked(points_to_raw), next_ptr);

            let cas_result = atomic_with_ghost!(
                &self.atomic => compare_exchange_weak(next_ptr, ptr);
                returning cas_result;
                ghost ghost_ll =>
            {
                let tracked mut ptr_mem = ptr_mem0;
                let tracked raw_mem = raw_mem0;

                let ghost ok = cas_result.is_ok();

                if ok {
                    let tracked block_token = block_token_opt.tracked_unwrap();
                    LL::ghost_insert_block(&mut ghost_ll, ptr, ptr_mem, raw_mem, block_token, exposed);
                    block_token_opt = None;

                    points_to_raw = PointsToRaw::empty(ptr@.provenance);
                } else {
                    ptr_mem.leak_contents();
                    points_to_raw = ptr_mem.into_raw().join(raw_mem);
                }
            });

            match cas_result {
                Result::Ok(_) => { break; }
                _ => { }
            }
        }
    }

}
}

#[cfg(not(any()))]
verus!{
impl ThreadLLSimple {
    #[inline(always)]
#[verifier::external_body]
    pub fn atomic_insert_block(&self, ptr: *mut Node,
        Tracked(points_to_raw): Tracked<PointsToRaw>,
        Tracked(block_token): Tracked<Mim::block>,
    )
    {
        let tracked mut points_to_raw = points_to_raw;
        let tracked mut block_token_opt = Some(block_token);

        let Tracked(exposed) = expose_provenance(ptr);

        loop
            invariant_except_break
                block_token_opt == Some(block_token),

                self.wf(),
                points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
                points_to_raw.provenance() == ptr@.provenance,
                exposed.provenance() == ptr@.provenance,

                block_token.instance_id() == self.instance@.id(),
                block_token.value().heap_id == Some(self.heap_id@),
                is_block_ptr(ptr as *mut u8, block_token.key()),
        {
            let next_ptr = atomic_with_ghost!(
                &self.atomic => load(); ghost g => { });

            let (Tracked(ptr_mem0), Tracked(raw_mem0)) = LL::block_write_ptr(
                ptr, Tracked(points_to_raw), next_ptr);

            let cas_result = atomic_with_ghost!(
                &self.atomic => compare_exchange_weak(next_ptr, ptr);
                returning cas_result;
                ghost ghost_ll =>
            {
                let tracked mut ptr_mem = ptr_mem0;
                let tracked raw_mem = raw_mem0;

                let ghost ok = cas_result.is_ok();

                if ok {
                    let tracked block_token = block_token_opt.tracked_unwrap();
                    let tracked ll = ghost_ll.get();
                    let tracked ll = LL::ghost_insert_block(ll, ptr, ptr_mem, raw_mem, block_token, exposed);
                    ghost_ll = Tracked(ll);
                    block_token_opt = None;

                    points_to_raw = PointsToRaw::empty(ptr@.provenance);
                } else {
                    ptr_mem.leak_contents();
                    let tracked ptr_raw = ptr_mem.into_raw();
                    points_to_raw = LL::block_write_ptr_rejoin(ptr_raw, raw_mem, ptr, block_token.key());
                }
            });

            match cas_result {
                Result::Ok(_) => { break; }
                _ => { }
            }
        }
    }

}
}

verus!{
impl ThreadLLSimple {
    #[inline(always)]
    pub fn take(&self) -> (ll: LL)
        requires
            self.wf(),
        ensures
            ll.wf(),
            ll.instance() == self.instance@,
            ll.heap_id() == Some(self.heap_id@),
    {
        let res = self.atomic.load();
        if res.addr() == 0 {
            return LL::new(Ghost(arbitrary()), Ghost(arbitrary()),
                Ghost(self.instance@), Ghost(arbitrary()), Ghost(Some(self.heap_id@)));
        }

        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => swap(core::ptr::null_mut());
            ghost g => {
                ll = g.get();
                let mut data = ll.data@;
                data.len = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                g = Tracked(new_ll);
            }
        );
        let new_ll = LL {
            first: res,
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };
        proof {
            reveal(LL::no_duplicate_keys);
            assert(new_ll.no_duplicate_keys());
        }

        new_ll
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
#[verifier::external_body]
    fn initialize_inductive(post: Self, b: Option<BlockSizePageId>) { }

    #[inductive(set)]
#[verifier::external_body]
    fn set_inductive(pre: Self, post: Self, b: Option<BlockSizePageId>) { }
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
    pub proof fn wf_emp_instance_ids(&self)
        requires self.wf(),
        ensures self.emp@.instance_id() == self.emp_inst@.id(),
    {
    }

    pub open spec fn is_empty(&self) -> bool {
        self.emp@.value().is_none()
    }

    pub open spec fn block_size(&self) -> nat {
        self.emp@.value().unwrap().block_size
    }

    pub open spec fn page_id(&self) -> PageId {
        self.emp@.value().unwrap().page_id
    }

    pub fn empty(Tracked(instance): Tracked<Mim::Instance>) -> (ll: ThreadLLWithDelayBits)
        ensures
            ll.wf(),
            ll.is_empty(),
            ll.instance == instance,
    {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = StuffAgree::Instance::initialize(None);
        let emp = Tracked(emp_x);
        let emp_inst = Tracked(emp_inst);
        ThreadLLWithDelayBits {
            instance: Tracked(instance),
            atomic: AtomicPtr::new(Ghost((Tracked(instance), emp_inst)), core::ptr::null_mut(), Tracked((emp_y, None))),
            emp,
            emp_inst,
        }
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    pub fn enable(&mut self,
        Ghost(block_size): Ghost<nat>,
        Ghost(page_id): Ghost<PageId>,
        Tracked(instance): Tracked<Mim::Instance>,
        Tracked(delay_token): Tracked<Mim::delay>,
    )
        requires
            old(self).wf(),
            old(self).is_empty(),
            old(self).instance == instance,
            delay_token.instance_id() == instance.id(),
            delay_token.key() == page_id,
            delay_token.value() == DelayState::UseDelayedFree,
        ensures
            final(self).wf(),
            !final(self).is_empty(),
            final(self).instance == instance,
            final(self).block_size() == block_size,
            final(self).page_id() == page_id,
    {
        let p = core::ptr::null_mut::<Node>();
        let ghost data = LLData {
            fixed_page: true, block_size, page_id, instance: self.instance@, len: 0, heap_id: None, block_ids: Set::empty(), idx_bound: 0,
        };
        let tracked new_ll = LL {
            first: p,
            data: Ghost(data),
            perms: Tracked(Map::tracked_empty()),
        };
        atomic_with_ghost!(
            &self.atomic => no_op();
            update old_v -> v;
            ghost g => {
                let tracked (mut y, g_opt) = g;
                let bspi = BlockSizePageId { block_size, page_id };
                self.emp_inst.borrow().set(Some(bspi), self.emp.borrow_mut(), &mut y);
                g = (y, Some((delay_token, new_ll)));

                    /*let instance = self.instance;
                    let emp = self.emp;
                    let emp_inst = self.emp_inst;
                    assert(g.1.is_some());
                    assert(y@.value.is_some());
                    assert(g.0@.instance == self.emp_inst@);
                    assert(g.0@.instance == emp_inst@);
                    let (delay_token, ll) = g.1.unwrap();
                    let stuff = y@.value.unwrap();
                    let page_id = stuff.page_id;
                    let block_size = stuff.block_size;

                    // Valid linked list

                    assert(ll.wf());
                    assert(ll.block_size() == block_size);
                    assert(ll.instance() == instance@);
                    assert(ll.page_id() == page_id);
                    assert(ll.fixed_page());

                    // Valid delay_token

                    assert(delay_token@.instance == instance);
                    assert(delay_token@.key == page_id);

                    // The usize value stores the pointer and the delay state

                    assert(v as int == ll.ptr() as int + delay_token@.value.to_int());
                    assert(ll.ptr().id() % 4 == 0);*/

            }
        );
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn disable(&mut self) -> (delay: Tracked<Mim::delay>)
        ensures
            final(self).wf(),
            final(self).is_empty(),
            final(self).instance == old(self).instance,
            delay@.instance_id() == old(self).instance@.id(),
            delay@.key() == old(self).page_id(),
    {
        let mut tmp = Self::empty(Tracked(self.instance.borrow().clone()));
        core::mem::swap(&mut *self, &mut tmp);

        let ThreadLLWithDelayBits { instance: Tracked(instance),
            atomic: ato,
            emp: Tracked(emp), emp_inst: Tracked(emp_inst) } = tmp;
        let (v, Tracked(g)) = ato.into_inner();
        let tracked (y, g_opt) = g;
        Tracked(g_opt.tracked_unwrap().0)
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

    #[inline(always)]
#[verifier::external_body]
    pub fn check_is_good(
        &self,
        Tracked(thread_tok): Tracked<&Mim::thread_local_state>,
        Tracked(tok): Tracked<Mim::thread_checked_state>,
    ) -> (new_tok: Tracked<Mim::thread_checked_state>)
        ensures
            new_tok@.instance_id() == tok.instance_id(),
            new_tok@.key() == tok.key(),
            new_tok@.value().pages == tok.value().pages.insert(self.page_id()),
    {
        let tracked mut tok0 = tok;
        loop
            invariant self.wf(), !self.is_empty(),
                thread_tok.instance_id() == self.instance@.id(),
                thread_tok.value().pages.dom().contains(self.page_id()),
                thread_tok.value().pages[self.page_id()].num_blocks == 0,
                tok.instance_id() == self.instance@.id(),
                tok.key() == thread_tok.key(),
                tok0 == tok,
        {
            let ghost mut the_ptr;
            let ghost mut the_delay;
            let tfree = atomic_with_ghost!(&self.atomic => load(); ghost g => {
                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                the_ptr = g.1.unwrap().1.ptr();
                the_delay = g.1.unwrap().0.value();

                if the_delay != DelayState::Freeing {
                    let tracked new_tok = self.instance.borrow().page_check_delay_state(
                        tok0.key(),
                        self.page_id(),
                        thread_tok,
                        &g.1.tracked_borrow().0,
                        tok0);
                    tok0 = new_tok;
                }
            });

            let old_delay = masked_ptr_delay_get_delay(tfree, Ghost(the_delay), Ghost(the_ptr));
            if unlikely(old_delay == 1) { // Freeing
                atomic_yield();
            } else {
                return Tracked(tok0);
            }
        }
    }

    #[inline(always)]
    #[verifier::rlimit(200)]
    pub fn try_use_delayed_free(
        &self,
        delay: usize,
        override_never: bool,
    ) -> (b: bool)
        requires
            self.wf(),
            !self.is_empty(),
            !override_never,
            delay == 0,
        ensures
            self.wf(),
            !self.is_empty(),
    {
        let mut yield_count = 0;
        loop
            invariant self.wf(), !self.is_empty(), !override_never, delay == 0,
        {
            let ghost mut the_ptr;
            let ghost mut the_delay;
            let tfree = atomic_with_ghost!(&self.atomic => load(); ghost g => {
                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                the_ptr = g.1.unwrap().1.ptr();
                the_delay = g.1.unwrap().0.value();
            });

            let tfreex = masked_ptr_delay_set_delay(tfree, delay, Ghost(the_delay), Ghost(the_ptr));
            let old_delay = masked_ptr_delay_get_delay(tfree, Ghost(the_delay), Ghost(the_ptr));
            if unlikely(old_delay == 1) { // Freeing
                if yield_count >= 4 {
                    return false;
                }
                yield_count += 1;
                atomic_yield();
            } else if delay == old_delay {
                return true;
            } else if !override_never && old_delay == 3 {
                return true;
            }

            if old_delay != 1 {
                let res = atomic_with_ghost!(
                    &self.atomic => compare_exchange_weak(tfree, tfreex);
                    returning cas_result;
                    ghost g => {
                        self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                        if cas_result.is_ok() {
                            let tracked (emp_token, pair_opt) = g;
                            let tracked pair = pair_opt.tracked_unwrap();
                            let tracked (delay_token, ghost_ll) = pair;
                            let tracked dt = self.instance.borrow().set_use_delayed_free(self.page_id(), delay_token);
                            g = (emp_token, Some((dt, ghost_ll)));
                        }
                    }
                );

                if res.is_ok() {
                    return true;
                }
            }
        }
    }

    // Clears the list (but leaves the 'delay' bit intact)
    #[inline(always)]
    #[verifier::rlimit(200)]
    pub fn take(&self) -> (ll: LL)
        requires
            self.wf(),
            !self.is_empty(),
        ensures
            self.wf(),
            !self.is_empty(),
            ll.wf(),
            ll.fixed_page(),
            ll.page_id() == self.page_id(),
            ll.block_size() == self.block_size(),
            ll.instance() == self.instance@,
            ll.heap_id().is_none(),
    {
        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => fetch_and(3);
            update old_v -> new_v;
            ghost g => {

                

                self.emp_inst.borrow().agree(self.emp.borrow(), &g.0);
                let tracked (emp_token, pair_opt) = g;
                let tracked pair = pair_opt.tracked_unwrap();
                let tracked (delay, _ll) = pair;
                ll = _ll;
                let mut data = ll.data@;
                data.len = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                g = (emp_token, Some((delay, new_ll)));

                let x = ll.first as usize;
                let y = delay.value().to_int() as usize;

                

                //assert(new_v@.provenance == ll.ptr()@.provenance);
                //assert((new_ll.ptr() as int != 0 ==> new_v@.provenance == new_ll.ptr()@.provenance));
                //assert(new_v as int == new_ll.ptr() as int + delay@.value.to_int());
            }
        );
        let ret_ll = LL {
            first: res.with_addr(res.addr() & !3),
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };
        proof! {
            assert(ret_ll.first.addr() == ll.ptr().addr());
            ret_ll.wf_from_same_repr_addr(&ll);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
        }
        ret_ll
    }
}

pub open spec fn masked_ptr_delay_wf(v: *mut Node, expected_delay: DelayState, expected_ptr: *mut Node) -> bool {
    expected_ptr.addr() % 4 == 0
        && v.addr() as int == expected_ptr.addr() as int + expected_delay.to_int()
}

proof fn masked_ptr_delay_from_int(v: *mut Node, expected_delay: DelayState, expected_ptr: *mut Node)
    requires
        expected_ptr.addr() % 4 == 0,
        v as int == expected_ptr as int + expected_delay.to_int(),
    ensures
        masked_ptr_delay_wf(v, expected_delay, expected_ptr),
{
    assert(v.addr() as int == v as int);
    assert(expected_ptr.addr() as int == expected_ptr as int);
}

#[verifier::rlimit(20)]
proof fn masked_ptr_delay_clear_ptr(old_v: *mut Node, new_v: *mut Node, delay: DelayState, old_ptr: *mut Node, new_ptr: *mut Node)
    requires
        masked_ptr_delay_wf(old_v, delay, old_ptr),
        new_v.addr() == (old_v.addr() & 3usize),
        new_ptr.addr() == 0,
    ensures
        masked_ptr_delay_wf(new_v, delay, new_ptr),
        new_v as int == new_ptr as int + delay.to_int(),
{
    masked_ptr_delay_wf_facts(old_v, delay, old_ptr);
    delay_state_to_int_facts(delay);
    assert(new_v.addr() == delay.to_int() as usize);
    assert(new_v.addr() as int == delay.to_int());
    assert(new_ptr.addr() as int == 0);
    assert(new_ptr as int == 0);
    assert(new_v.addr() as int == new_v as int);
}

proof fn delay_state_to_int_facts(d: DelayState)
    ensures
        0 <= d.to_int() < 4,
        (d.to_int() == 0) == (d == DelayState::UseDelayedFree),
        (d.to_int() == 1) == (d == DelayState::Freeing),
        (d.to_int() == 2) == (d == DelayState::NoDelayedFree),
        (d.to_int() == 3) == (d == DelayState::NeverDelayedFree),
{
    match d {
        DelayState::UseDelayedFree => { }
        DelayState::Freeing => { }
        DelayState::NoDelayedFree => { }
        DelayState::NeverDelayedFree => { }
    }
}

#[verifier::rlimit(20)]
proof fn masked_ptr_delay_aligned_room(base: usize, delay: usize)
    requires
        base % 4 == 0,
        delay < 4,
    ensures
        base as int + delay as int <= usize::MAX,
{
    assert(base <= usize::MAX - 3) by (bit_vector)
        requires
            base % 4 == 0;
    assert(delay <= 3);
}

#[verifier::rlimit(20)]
proof fn masked_ptr_delay_low_bits(base: usize, delay: usize)
    requires
        base % 4 == 0,
        delay < 4,
    ensures
        base as int + delay as int <= usize::MAX,
        add(base, delay) as int == base as int + delay as int,
        add(base, delay) % 4 == delay,
        (add(base, delay) & 3usize) == delay,
        (add(base, delay) & !3usize) == base,
        (base | delay) == add(base, delay),
        (delay | base) == add(base, delay),
{
    masked_ptr_delay_aligned_room(base, delay);
    assert(add(base, delay) as int == base as int + delay as int);
    assert(add(base, delay) % 4 == delay) by (bit_vector)
        requires
            base % 4 == 0,
            delay < 4;
    assert((add(base, delay) & 3usize) == delay) by (bit_vector)
        requires
            base % 4 == 0,
            delay < 4;
    assert((add(base, delay) & !3usize) == base) by (bit_vector)
        requires
            base % 4 == 0,
            delay < 4;
    assert((base | delay) == add(base, delay)) by (bit_vector)
        requires
            base % 4 == 0,
            delay < 4;
    assert((delay | base) == add(base, delay)) by (bit_vector)
        requires
            base % 4 == 0,
            delay < 4;
}

pub proof fn masked_ptr_delay_xor3_freeing_to_no_delayed(
    v_old: *mut Node,
    v_new: *mut Node,
    ptr: *mut Node,
)
    requires
        masked_ptr_delay_wf(v_old, DelayState::Freeing, ptr),
        v_new.addr() == (v_old.addr() ^ 3usize),
    ensures
        masked_ptr_delay_wf(v_new, DelayState::NoDelayedFree, ptr),
{
    masked_ptr_delay_wf_facts(v_old, DelayState::Freeing, ptr);
    delay_state_to_int_facts(DelayState::Freeing);
    delay_state_to_int_facts(DelayState::NoDelayedFree);
    let base = ptr.addr();
    assert(base % 4 == 0);
    assert(v_old.addr() == add(base, 1usize));
    assert((add(base, 1usize) ^ 3usize) == add(base, 2usize)) by (bit_vector)
        requires
            base % 4 == 0;
    masked_ptr_delay_low_bits(base, 2usize);
    assert(v_new.addr() == add(base, 2usize));
    assert(v_new.addr() as int == base as int + DelayState::NoDelayedFree.to_int());
}

pub proof fn masked_ptr_delay_wf_unique(
    v: *mut Node,
    delay1: DelayState,
    ptr1: *mut Node,
    delay2: DelayState,
    ptr2: *mut Node,
)
    requires
        masked_ptr_delay_wf(v, delay1, ptr1),
        masked_ptr_delay_wf(v, delay2, ptr2),
    ensures
        delay1 == delay2,
        ptr1.addr() == ptr2.addr(),
{
    masked_ptr_delay_wf_facts(v, delay1, ptr1);
    masked_ptr_delay_wf_facts(v, delay2, ptr2);
    delay_state_to_int_facts(delay1);
    delay_state_to_int_facts(delay2);
    assert(delay1.to_int() == delay2.to_int()) by {
        assert((v.addr() & 3usize) == delay1.to_int() as usize);
        assert((v.addr() & 3usize) == delay2.to_int() as usize);
    }
    assert(delay1 == delay2);
    assert(ptr1.addr() == (v.addr() & !3usize));
    assert(ptr2.addr() == (v.addr() & !3usize));
}

proof fn masked_ptr_delay_wf_facts(v: *mut Node, expected_delay: DelayState, expected_ptr: *mut Node)
    requires
        masked_ptr_delay_wf(v, expected_delay, expected_ptr),
    ensures
        v.addr() % 4 == expected_delay.to_int() as usize,
        (v.addr() & 3usize) == expected_delay.to_int() as usize,
        (v.addr() & !3usize) == expected_ptr.addr(),
{
    delay_state_to_int_facts(expected_delay);
    let ghost delay = expected_delay.to_int() as usize;
    assert(delay as int == expected_delay.to_int());
    assert(expected_ptr.addr() as int + delay as int <= usize::MAX);
    assert(v.addr() == add(expected_ptr.addr(), delay));
    masked_ptr_delay_low_bits(expected_ptr.addr(), delay);
}

#[inline(always)]
#[verus_verify]
pub fn masked_ptr_delay_get_is_use_delayed(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (b: bool)
    ensures
        b == (v.addr() % 4 == 0),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> b == (expected_delay == DelayState::UseDelayedFree),
{
    proof! {
        if masked_ptr_delay_wf(v, expected_delay, expected_ptr) {
            masked_ptr_delay_wf_facts(v, expected_delay, expected_ptr);
            delay_state_to_int_facts(expected_delay);
        }
    }
    v.addr() % 4 == 0
}

#[inline(always)]
#[verus_verify]
pub fn masked_ptr_delay_get_delay(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (d: usize)
    ensures
        d == v.addr() % 4,
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> d as int == expected_delay.to_int(),
{
    proof! {
        if masked_ptr_delay_wf(v, expected_delay, expected_ptr) {
            masked_ptr_delay_wf_facts(v, expected_delay, expected_ptr);
            delay_state_to_int_facts(expected_delay);
        }
    }
    v.addr() % 4
}

#[inline(always)]
#[verus_verify]
pub fn masked_ptr_delay_get_ptr(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (ptr: *mut Node)
    ensures
        ptr == v.with_addr(v.addr() & !3usize),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> ptr.addr() == expected_ptr.addr(),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> ptr@.provenance == v@.provenance,
{
    proof! {
        if masked_ptr_delay_wf(v, expected_delay, expected_ptr) {
            masked_ptr_delay_wf_facts(v, expected_delay, expected_ptr);
        }
    }
    v.with_addr(v.addr() & !3)
}

#[inline(always)]
#[verus_verify]
pub fn masked_ptr_delay_set_ptr(v: *mut Node, new_ptr: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
    ensures
        v2 == new_ptr.with_addr((v.addr() & 3usize) | new_ptr.addr()),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_ptr.addr() % 4 == 0
            ==> masked_ptr_delay_wf(v2, expected_delay, new_ptr),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> v2@.provenance == new_ptr@.provenance,
{
    proof! {
        if masked_ptr_delay_wf(v, expected_delay, expected_ptr) {
            masked_ptr_delay_wf_facts(v, expected_delay, expected_ptr);
            delay_state_to_int_facts(expected_delay);
            if new_ptr.addr() % 4 == 0 {
                let ghost delay = expected_delay.to_int() as usize;
                masked_ptr_delay_low_bits(new_ptr.addr(), delay);
            }
        }
    }
    new_ptr.with_addr((v.addr() & 3) | new_ptr.addr())
}

#[inline(always)]
#[verus_verify]
pub fn masked_ptr_delay_set_freeing(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
    ensures
        v2 == v.with_addr((v.addr() & !3usize) | 1usize),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr)
            ==> masked_ptr_delay_wf(v2, DelayState::Freeing, expected_ptr),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> v2@.provenance == v@.provenance,
{
    proof! {
        if masked_ptr_delay_wf(v, expected_delay, expected_ptr) {
            masked_ptr_delay_wf_facts(v, expected_delay, expected_ptr);
            delay_state_to_int_facts(DelayState::Freeing);
            masked_ptr_delay_low_bits(expected_ptr.addr(), 1usize);
        }
    }
    v.with_addr((v.addr() & !3) | 1)
}

#[inline(always)]
#[verus_verify]
pub fn masked_ptr_delay_set_delay(v: *mut Node, new_delay: usize,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
    ensures
        v2 == v.with_addr((v.addr() & !3usize) | new_delay),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_delay < 4
            ==> expected_ptr.addr() % 4 == 0,
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_delay < 4
            ==> v2.addr() as int == expected_ptr.addr() as int + new_delay as int,
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_delay == 0
            ==> masked_ptr_delay_wf(v2, DelayState::UseDelayedFree, expected_ptr),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_delay == 1
            ==> masked_ptr_delay_wf(v2, DelayState::Freeing, expected_ptr),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_delay == 2
            ==> masked_ptr_delay_wf(v2, DelayState::NoDelayedFree, expected_ptr),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) && new_delay == 3
            ==> masked_ptr_delay_wf(v2, DelayState::NeverDelayedFree, expected_ptr),
        masked_ptr_delay_wf(v, expected_delay, expected_ptr) ==> v2@.provenance == v@.provenance,
{
    proof! {
        if masked_ptr_delay_wf(v, expected_delay, expected_ptr) {
            masked_ptr_delay_wf_facts(v, expected_delay, expected_ptr);
            if new_delay < 4 {
                masked_ptr_delay_low_bits(expected_ptr.addr(), new_delay);
                delay_state_to_int_facts(DelayState::UseDelayedFree);
                delay_state_to_int_facts(DelayState::Freeing);
                delay_state_to_int_facts(DelayState::NoDelayedFree);
                delay_state_to_int_facts(DelayState::NeverDelayedFree);
            }
        }
    }
    v.with_addr((v.addr() & !3) | new_delay)
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
        proof! {
            self.perms.borrow_mut().tracked_insert((points_to_node, points_to_raw, block));
        }
        return false;
    }

    crate::alloc_generic::page_free_collect(page, false, Tracked(&mut *local));

    proof! { points_to_node.leak_contents(); }
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

#[inline(always)]
#[verifier::external_body]
fn atomic_yield()
{
    std::thread::yield_now();
}

}
