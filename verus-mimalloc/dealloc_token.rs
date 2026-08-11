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

impl MimDealloc {
    pub closed spec fn block_id(&self) -> BlockId
    { arbitrary() }

    pub closed spec fn ptr(&self) -> *mut u8
    { arbitrary() }

    pub closed spec fn inst(&self) -> Mim::Instance
    { arbitrary() }

    pub closed spec fn size(&self) -> int
    { arbitrary() }

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

    #[verifier::external_body]
    pub(crate) proof fn into_internal(tracked self, tracked points_to_raw: PointsToRaw)
        -> (tracked res: (MimDeallocInner, PointsToRaw))
    {
        unimplemented!();
    }
}

}
