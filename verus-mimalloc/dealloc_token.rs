#![allow(unused_imports)]
use vstd::raw_ptr::*;
use crate::tokens::{Mim, BlockId, DelayState};
use crate::types::*;
use crate::layout::*;
use vstd::prelude::*;
use vstd::set_lib::*;

verus!{

pub tracked struct MimDealloc {
    pub(crate) tracked padding: PointsToRaw,

    // Size of the allocation from the user perspective, <= the block size
    pub(crate) ghost _size: int,

    // Memory to make up the difference between user size and block size
    pub(crate) tracked inner: MimDeallocInner,
}

pub tracked struct MimDeallocInner {
    pub tracked mim_instance: Mim::Instance,
    pub tracked mim_block: Mim::block,

    pub ghost ptr: *mut u8,
}

pub open spec fn valid_block_token(block: Mim::block, instance: Mim::Instance) -> bool {
    &&& block.key().wf()
    &&& block.instance_id() == instance.id()

    // TODO factor this stuff into wf predicates

    // Valid segment

    &&& is_segment_ptr(
        block.value().segment_shared_access.points_to.ptr(),
        block.key().page_id.segment_id)
    &&& block.value().segment_shared_access.points_to.is_init()
    &&& block.value().segment_shared_access.points_to.value()
        .wf(instance, block.key().page_id.segment_id)

    // Valid slice page

    &&& is_page_ptr(
        block.value().page_slice_shared_access.points_to.ptr(),
        block.key().page_id_for_slice())
    &&& block.value().page_slice_shared_access.points_to.is_init()
    &&& block.value().page_slice_shared_access.points_to.value().offset as int
          == (block.key().slice_idx - block.key().page_id.idx) * crate::config::SIZEOF_PAGE_HEADER

    // Valid main page

    &&& block.value().page_shared_access.wf(
        block.key().page_id,
        block.key().block_size,
        instance)
}

impl MimDeallocInner {
    #[verifier(inline)]
    pub open spec fn block_id(&self) -> BlockId {
        self.mim_block.key()
    }

    pub open spec fn wf(&self) -> bool {
        &&& valid_block_token(self.mim_block, self.mim_instance)
        &&& is_block_ptr(self.ptr, self.block_id())
    }

}

#[verifier::rlimit(200)]
proof fn lemma_join_user_padding_range(start: int, user_size: int, block_size: int)
    requires
        0 <= user_size,
        user_size <= block_size,
    ensures
        set_int_range(start, start + user_size) + set_int_range(start + user_size, start + block_size)
            =~= set_int_range(start, start + block_size),
{
    vstd::set_lib::lemma_int_range(start, start + user_size);
    vstd::set_lib::lemma_int_range(start + user_size, start + block_size);
    vstd::set_lib::lemma_int_range(start, start + block_size);

    assert forall |addr: int|
        #[trigger] (set_int_range(start, start + user_size)
            + set_int_range(start + user_size, start + block_size)).contains(addr)
    implies
        set_int_range(start, start + block_size).contains(addr)
    by {
        if set_int_range(start, start + user_size).contains(addr) {
            assert(start <= addr < start + user_size);
            assert(addr < start + block_size) by(nonlinear_arith)
                requires
                    addr < start + user_size,
                    user_size <= block_size;
        } else {
            assert(set_int_range(start + user_size, start + block_size).contains(addr));
            assert(start + user_size <= addr < start + block_size);
            assert(start <= addr) by(nonlinear_arith)
                requires
                    0 <= user_size,
                    start + user_size <= addr;
        }
    };

    assert forall |addr: int|
        #[trigger] set_int_range(start, start + block_size).contains(addr)
    implies
        (set_int_range(start, start + user_size)
            + set_int_range(start + user_size, start + block_size)).contains(addr)
    by {
        assert(start <= addr < start + block_size);
        if addr < start + user_size {
            assert(set_int_range(start, start + user_size).contains(addr));
        } else {
            assert(start + user_size <= addr) by(nonlinear_arith)
                requires
                    !(addr < start + user_size);
            assert(set_int_range(start + user_size, start + block_size).contains(addr));
        }
    };
}

impl MimDealloc {
    pub closed spec fn block_id(&self) -> BlockId {
        self.inner.block_id()
    }

    pub closed spec fn ptr(&self) -> *mut u8 {
        self.inner.ptr
    }

    pub closed spec fn inst(&self) -> Mim::Instance {
        self.inner.mim_instance
    }

    pub closed spec fn size(&self) -> int {
        self._size
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.inner.wf()
          // PAPER CUT: is_range should probably have this condition in it
          && self.block_id().block_size - self._size >= 0
          && self._size >= 0
          && self.padding.is_range(self.inner.ptr as int + self._size,
              self.block_id().block_size - self._size)
          && self.padding.provenance() == self.inner.ptr@.provenance
    }



    pub(crate) proof fn new(
        tracked padding: PointsToRaw,
        size: int,
        tracked inner: MimDeallocInner,
    ) -> (tracked dealloc: MimDealloc)
        requires
            inner.wf(),
            0 <= size,
            size <= inner.block_id().block_size,
            padding.is_range(inner.ptr as int + size, inner.block_id().block_size as int - size),
            padding.provenance() == inner.ptr@.provenance,
        ensures
            dealloc.ptr() == inner.ptr,
            dealloc.inst() == inner.mim_instance,
            dealloc.size() == size,
    {
        reveal(MimDealloc::wf);
        reveal(MimDealloc::ptr);
        reveal(MimDealloc::inst);
        reveal(MimDealloc::size);
        reveal(MimDealloc::block_id);
        let tracked dealloc = MimDealloc {
            padding,
            _size: size,
            inner,
        };
        assert(dealloc.wf());
        assert(dealloc.ptr() == inner.ptr);
        assert(dealloc.inst() == inner.mim_instance);
        assert(dealloc.size() == size);
        dealloc
    }



    pub(crate) proof fn into_internal(tracked self, tracked points_to_raw: PointsToRaw)
        -> (tracked res: (MimDeallocInner, PointsToRaw))
        requires
            points_to_raw.is_range(self.ptr() as int, self.size()),
            points_to_raw.provenance() == self.ptr()@.provenance,
        ensures
            res.0 == self.inner,
            res.0.wf(),
            res.0.ptr == self.ptr(),
            res.0.mim_instance == self.inst(),
            res.1.is_range(res.0.ptr as int, res.0.block_id().block_size as int),
            res.1.provenance() == res.0.ptr@.provenance,
    {
        use_type_invariant(&self);
        reveal(MimDealloc::wf);
        reveal(MimDealloc::ptr);
        reveal(MimDealloc::size);
        reveal(MimDealloc::block_id);
        reveal(MimDealloc::inst);

        assert(self.wf());
        assert(self.inner.wf());
        assert(0 <= self._size);
        assert(self._size <= self.block_id().block_size);
        assert(self.padding.provenance() == self.inner.ptr@.provenance);

        let tracked MimDealloc { padding, _size, inner } = self;
        let ghost start = inner.ptr as int;
        let ghost block_size = inner.block_id().block_size as int;

        assert(0 <= _size);
        assert(_size <= block_size);
        assert(points_to_raw.provenance() == padding.provenance());
        assert(points_to_raw.dom() =~= set_int_range(start, start + _size));
        assert(padding.dom() =~= set_int_range(start + _size, start + block_size));

        lemma_join_user_padding_range(start, _size, block_size);
        let tracked raw = points_to_raw.join(padding);
        assert(raw.dom() =~= set_int_range(start, start + block_size));

        (inner, raw)
    }
}

}
