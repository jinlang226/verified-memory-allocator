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
        Node { ptr: self.ptr }
    }
}

global layout Node is size == 8, align == 8;

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
    pub closed spec fn next_ptr(&self, i: nat) -> *mut Node
    { arbitrary() }

    pub closed spec fn valid_node(&self, i: nat, next_ptr: *mut Node) -> bool
    { true }

    pub closed spec fn wf(&self) -> bool
    { true }

    pub closed spec fn len(&self) -> nat
    { arbitrary() }

    pub closed spec fn page_id(&self) -> PageId
    { arbitrary() }

    pub closed spec fn block_size(&self) -> nat
    { arbitrary() }

    pub closed spec fn fixed_page(&self) -> bool
    { true }

    pub closed spec fn instance(&self) -> Mim::Instance
    { arbitrary() }

    pub closed spec fn heap_id(&self) -> Option<HeapId>
    { arbitrary() }

    pub closed spec fn ptr(&self) -> *mut Node
    { arbitrary() }

    /*spec fn is_valid_page_address(&self, ptr: int) -> bool {
        // We need this to save a ptr at this address
        // this is probably redundant since we also have is_block_ptr
        ptr as int % size_of::<Node>() as int == 0
    }*/

    #[inline(always)]
#[verifier::external_body]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
    {
        let Tracked(mut mem1) = Tracked::<PointsTo<Node>>::assume_new();
        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$

        let ptr = ptr as *mut Node;
        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
        self.first = ptr;
        let Tracked(is_exposed) = expose_provenance(ptr);

    }

    // This is like insert_block but it only does the operation "ghostily".
    // This is used by the ThreadLL
    //
    // It requires the pointer writer has already been done, so it's just arranging
    // ghost data in a ghost LL.

    pub proof fn ghost_insert_block(
        tracked self_: &mut Tracked<LL>,
        tracked ptr: *mut Node,
        tracked points_to_ptr: PointsTo<Node>,
        tracked points_to_raw: PointsToRaw,
        tracked block_token: Mim::block,
        tracked is_exposed: IsExposed,
     )
    { }

    #[inline(always)]
#[verifier::external_body]
    pub fn is_empty(&self) -> (b: bool)
    {
        self.first.addr() == 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
    {
        let tracked (mut points_to_node, points_to_raw, block, is_exposed) = self.perms.borrow_mut().tracked_remove((self.data@.len - 1) as nat);

        let ptr: *mut Node = with_exposed_provenance(self.first.addr(), Tracked(is_exposed));
        //assert(ptr.addr() == points_to_node.ptr().addr());
        //assert(ptr@.provenance == points_to_node.ptr()@.provenance);
        let node = ptr_mut_read(ptr, Tracked(&mut points_to_node));
        self.first = node.ptr;

        let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
        let ptru = ptr as *mut u8;

        return (ptru, Tracked(points_to_raw), Tracked(block))
    }

    // helper for clients using ghost_insert_block

    #[inline(always)]
#[verifier::external_body]
    pub fn block_write_ptr(ptr: *mut Node, Tracked(perm): Tracked<PointsToRaw>, next: *mut Node)
        -> (res: (Tracked<PointsTo<Node>>, Tracked<PointsToRaw>))
    {
        let tracked (points_to, rest) = perm.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));

        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
        let tracked mut points_to_node = points_to.into_typed::<Node>(ptr.addr());
        ptr_mut_write(ptr, Tracked(&mut points_to_node), Node { ptr: next });
        (Tracked(points_to_node), Tracked(rest))
    }

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

    #[inline(always)]
#[verifier::external_body]
    pub fn set_ghost_data(
        &mut self,
        Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    )
    {
    }

    // Traverse `other` to find the tail, append `self`,
    // and leave the resulting list in `self`.
    // Returns the # of entries in `other`

    #[inline(always)]
#[verifier::external_body]
    pub fn append(&mut self, other: &mut LL) -> (other_len: u32)
    {
        if other.first.addr() == 0 {
            return 0;
        }

        let mut count = 1;
        let mut p = other.first;
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

            p = with_exposed_provenance(p.addr(),
                Tracked(other.perms.borrow().tracked_borrow((other.len() - count) as nat).3));

            let next = *ptr_ref(p, Tracked(&other.perms.borrow().tracked_borrow((other.len() - count) as nat).0));
            if next.ptr.addr() != 0 {
                count += 1;
                p = next.ptr;
            } else {
                break;
            }
        }

        let ghost old_other = *other;
        let ghost old_self = *self;

        let tracked mut perm = other.perms.borrow_mut().tracked_remove(0);
        let tracked (mut a, b, c, exposed) = perm;
        let _ = ptr_mut_read(p, Tracked(&mut a));
        ptr_mut_write(p, Tracked(&mut a), Node { ptr: self.first });

        self.first = other.first;
        other.first = core::ptr::null_mut();

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
    {
        unimplemented!();
    }

}

pub closed spec fn has_idx(map: Map<nat, (PointsToRaw, Mim::block)>, i: nat) -> bool
{ true }

pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::range(lo, hi)
}

pub closed spec fn llgstr_wf(llgstr: LLGhostStateToReconvene) -> bool
{ true }

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

    // Oughta have a similar spec as LL:insert_block except that
    //  (i) self argument is a & reference so we don't need to talk about how it updates
    //  (ii) is we don't expose the length

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

    #[inline(always)]
#[verifier::external_body]
    pub fn take(&self) -> (ll: LL)
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
#[verifier::external_body]
    pub fn enable(&mut self,
        Ghost(block_size): Ghost<nat>,
        Ghost(page_id): Ghost<PageId>,
        Tracked(instance): Tracked<Mim::Instance>,
        Tracked(delay_token): Tracked<Mim::delay>,
    )
    {
        let p = core::ptr::null_mut::<Node>();
        let ghost data = LLData {
            fixed_page: true, block_size, page_id, instance, len: 0, heap_id: None,
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
#[verifier::external_body]
    pub fn try_use_delayed_free(
        &self,
        delay: usize,
        override_never: bool,
    ) -> (b: bool)
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
#[verifier::external_body]
    pub fn take(&self) -> (ll: LL)
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
        ret_ll
    }
}

#[inline(always)]
#[verifier::external_body]
pub fn masked_ptr_delay_get_is_use_delayed(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (b: bool)
{
    v.addr() % 4 == 0
}

#[inline(always)]
#[verifier::external_body]
pub fn masked_ptr_delay_get_delay(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (d: usize)
{
    v.addr() % 4
}

#[inline(always)]
#[verifier::external_body]
pub fn masked_ptr_delay_get_ptr(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (ptr: *mut Node)
{
    v.with_addr(v.addr() & !3)
}

#[inline(always)]
#[verifier::external_body]
pub fn masked_ptr_delay_set_ptr(v: *mut Node, new_ptr: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
{
    new_ptr.with_addr((v.addr() & 3) | new_ptr.addr())
}

#[inline(always)]
#[verifier::external_body]
pub fn masked_ptr_delay_set_freeing(v: *mut Node,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
{
    v.with_addr((v.addr() & !3) | 1)
}

#[inline(always)]
#[verifier::external_body]
pub fn masked_ptr_delay_set_delay(v: *mut Node, new_delay: usize,
    Ghost(expected_delay): Ghost<DelayState>,
    Ghost(expected_ptr): Ghost<*mut Node>) -> (v2: *mut Node)
{
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

#[inline(always)]
#[verifier::external_body]
fn atomic_yield()
{
    std::thread::yield_now();
}

}
