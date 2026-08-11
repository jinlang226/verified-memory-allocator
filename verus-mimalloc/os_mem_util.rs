use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::raw_ptr::*;
use vstd::modes::*;

use crate::os_mem::*;
use crate::layout::*;
use crate::tokens::*;
use crate::config::*;
use crate::page_organization::*;
use crate::types::*;

verus!{

impl MemChunk {
    #[verifier::external_body]
    pub proof fn empty() -> (tracked mc: MemChunk)
    {
        unimplemented!();
    }

    #[verifier::inline]
    pub open spec fn pointsto_has_range(&self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.range_points_to()
    }

    pub open spec fn os_rw_bytes(&self) -> Set<int> {
        self.range_os_rw()
    }

    pub open spec fn committed_pointsto_has_range(&self, start: int, len: int) -> bool {
        self.pointsto_has_range(start, len) && self.os_has_range_read_write(start, len)
    }

    #[verifier::external_body]
    pub proof fn split(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked t: Self)
    {
        unimplemented!();
    }

    pub proof fn join(
        tracked &mut self,
        tracked t: Self,
    )
    { }

    #[verifier::external_body]
    pub proof fn take_points_to_set(
        tracked &mut self,
        s: Set<int>,
    ) -> (tracked points_to: PointsToRaw)
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn take_points_to_range(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked points_to: PointsToRaw)
    {
        unimplemented!();
    }

}

pub open spec fn segment_info_range(segment_id: SegmentId) -> Set<int> {
    set_int_range(segment_start(segment_id),
        segment_start(segment_id) + SIZEOF_SEGMENT_HEADER + SIZEOF_PAGE_HEADER * (SLICES_PER_SEGMENT + 1)
    )
}

pub open spec fn mem_chunk_good1(
    mem: MemChunk,
    segment_id: SegmentId,
    commit_bytes: Set<int>,
    decommit_bytes: Set<int>,
    pages_range_total: Set<int>,
    pages_used_total: Set<int>,
) -> bool {
    &&& mem.wf()
    &&& mem.os_exact_range(segment_start(segment_id), SEGMENT_SIZE as int)
    &&& mem.points_to.provenance() == segment_id.provenance

    &&& commit_bytes.subset_of(mem.os_rw_bytes())

    &&& decommit_bytes <= commit_bytes
    &&& segment_info_range(segment_id) <= commit_bytes - decommit_bytes
    &&& pages_used_total <= commit_bytes - decommit_bytes

    &&& mem.os_rw_bytes() <=
          mem.points_to.dom()
            + segment_info_range(segment_id)
            + pages_range_total
}

impl Local {
    spec fn segment_page_range(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id) + start_offset(self.block_size(page_id)),
                page_start(page_id) + start_offset(self.block_size(page_id))
                    + self.page_capacity(page_id) * self.block_size(page_id)
            )
        } else {
            Set::empty()
        }
    }

    pub uninterp spec fn segment_pages_range_total(&self, segment_id: SegmentId) -> Set<int>;

    spec fn segment_page_used(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id),
                page_start(page_id) + self.page_count(page_id) * SLICE_SIZE
            )
        } else {
            Set::empty()
        }
    }

    pub uninterp spec fn segment_pages_used_total(&self, segment_id: SegmentId) -> Set<int>;

    /*spec fn segment_page_range_reserved(&self, segment_id: SegmentId, page_id: PageId) -> Set<int> {
        if page_id.segment_id == segment_id && self.is_used_primary(page_id) {
            set_int_range(
                page_start(page_id) + start_offset(self.block_size(page_id)),
                page_start(page_id) + start_offset(self.block_size(page_id))
                    + self.page_reserved(page_id) * self.block_size(page_id)
            )
        } else {
            Set::empty()
        }
    }

    spec fn segment_pages_range_reserved_total(&self, segment_id: SegmentId) -> Set<int> {
        Set::<int>::new(|addr| exists |page_id|
            self.segment_page_range_reserved(segment_id, page_id).contains(addr)
        )
    }*/

    pub open spec fn mem_chunk_good(&self, segment_id: SegmentId) -> bool {
        self.segments.dom().contains(segment_id)
        && mem_chunk_good1(
            self.segments[segment_id].mem,
            segment_id,
            self.commit_mask(segment_id).bytes(segment_id),
            self.decommit_mask(segment_id).bytes(segment_id),
            self.segment_pages_range_total(segment_id),
            self.segment_pages_used_total(segment_id),
        )
    }
}

///////

pub open spec fn page_init_is_committed(page_id: PageId, local: Local) -> bool {
    let count = local.page_organization.pages[page_id].count.unwrap() as int;
    let start = page_start(page_id);
    let len = count * SLICE_SIZE;
    let cm = local.segments[page_id.segment_id].main.value().commit_mask@;

    set_int_range(start, start + len) <=
        local.commit_mask(page_id.segment_id).bytes(page_id.segment_id)
        - local.decommit_mask(page_id.segment_id).bytes(page_id.segment_id)
    && count == local.page_count(page_id)
}

}
