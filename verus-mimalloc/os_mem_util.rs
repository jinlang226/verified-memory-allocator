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
        ensures
            t.points_to.dom() == old(self).points_to.dom().intersect(set_int_range(start, start + len)),
            t.os == old(self).os.restrict(set_int_range(start, start + len)),
            final(self).points_to.dom() == old(self).points_to.dom().difference(set_int_range(start, start + len)),
            final(self).os == old(self).os.remove_keys(set_int_range(start, start + len)),
            final(self).points_to.provenance() == old(self).points_to.provenance(),
            final(self).points_to.provenance() == t.points_to.provenance(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn join(
        tracked &mut self,
        tracked t: Self,
    )
        requires
            old(self).points_to.provenance() == t.points_to.provenance(),
        ensures
            final(self).points_to.dom() == old(self).points_to.dom().union(t.points_to.dom()),
            final(self).os == old(self).os.union_prefer_right(t.os),
            final(self).points_to.provenance() == old(self).points_to.provenance(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn os_restrict(
        tracked &mut self,
        start: int,
        len: int
    )
        requires old(self).os_has_range(start, len),
        ensures final(self).points_to == old(self).points_to,
            final(self).os == old(self).os.restrict(set_int_range(start, start + len))
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn take_points_to_set(
        tracked &mut self,
        s: Set<int>,
    ) -> (tracked points_to: PointsToRaw)
        requires
            s <= old(self).points_to.dom()
        ensures
            final(self).os == old(self).os,
            final(self).points_to.dom() == old(self).points_to.dom().difference(s),
            points_to.dom() == s,
            final(self).points_to.provenance() == old(self).points_to.provenance(),
            points_to.provenance() == old(self).points_to.provenance(),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn take_points_to_range(
        tracked &mut self,
        start: int,
        len: int
    ) -> (tracked points_to: PointsToRaw)
        requires
            len >= 0,
            old(self).pointsto_has_range(start, len),
        ensures
            final(self).os == old(self).os,
            final(self).points_to.dom() == old(self).points_to.dom().difference(set_int_range(start, start+len)),
            final(self).points_to.provenance() == old(self).points_to.provenance(),
            points_to.is_range(start, len),
            points_to.provenance() == old(self).points_to.provenance(),

    {
        unimplemented!();
    }

    #[verifier::external_body]
    pub proof fn give_points_to_range(
        tracked &mut self,
        tracked points_to: PointsToRaw,
    )
        requires
            old(self).wf(),
            old(self).points_to.provenance() == points_to.provenance()
        ensures
            final(self).wf(),
            final(self).os == old(self).os,
            final(self).points_to.dom() == old(self).points_to.dom() + points_to.dom(),
            final(self).points_to.provenance() == points_to.provenance(),
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

    pub closed spec fn segment_pages_range_total(&self, segment_id: SegmentId) -> Set<int> {
        self.page_organization.pages.dom().map(
            |page_id| self.segment_page_range(segment_id, page_id)
        ).flatten()
        /* The following old way of building the set isn't evidently finite:
        Set::<int>::new(|addr| exists |page_id|
            self.segment_page_range(segment_id, page_id).contains(addr)
        )
        */
    }

    #[verifier::external_body]
    proof fn get_page_id_of_addr_in_segment_pages_range_total(
        self,
        segment_id: SegmentId,
        addr: int
    ) -> (page_id: PageId)
        requires
            self.segment_pages_range_total(segment_id).contains(addr),
        ensures
            self.page_organization.pages.dom().contains(page_id),
            self.segment_page_range(segment_id, page_id).contains(addr),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    proof fn lemma_establish_segment_pages_range_total_contains(
        self,
        segment_id: SegmentId,
        page_id: PageId,
        addr: int
    )
        requires
            self.segment_page_range(segment_id, page_id).contains(addr),
            self.page_organization.pages.dom().contains(page_id),
        ensures
            self.segment_pages_range_total(segment_id).contains(addr),
    {
        unimplemented!();
    }

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

    pub closed spec fn segment_pages_used_total(&self, segment_id: SegmentId) -> Set<int> {
        self.page_organization.pages.dom().map(
            |page_id| self.segment_page_used(segment_id, page_id)
        ).flatten()
        /* The following old way of building the set isn't evidently finite:
        Set::<int>::new(|addr| exists |page_id|
            self.segment_page_used(segment_id, page_id).contains(addr)
        )
        */
    }

    #[verifier::external_body]
    proof fn get_page_id_of_addr_in_segment_pages_used_total(
        self,
        segment_id: SegmentId,
        addr: int
    ) -> (page_id: PageId)
        requires
            self.segment_pages_used_total(segment_id).contains(addr),
        ensures
            self.page_organization.pages.dom().contains(page_id),
            self.segment_page_used(segment_id, page_id).contains(addr),
    {
        unimplemented!();
    }

    #[verifier::external_body]
    proof fn lemma_establish_segment_pages_used_total_contains(
        self,
        segment_id: SegmentId,
        page_id: PageId,
        addr: int
    )
        requires
            self.segment_page_used(segment_id, page_id).contains(addr),
            self.page_organization.pages.dom().contains(page_id),
        ensures
            self.segment_pages_used_total(segment_id).contains(addr),
    {
        unimplemented!();
    }

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

#[verifier::external_body]
pub proof fn range_total_le_used_total(local: Local, sid: SegmentId)
    requires
        local.wf_main(),
        local.segments.dom().contains(sid),
    ensures
        local.segment_pages_range_total(sid)
            <= local.segment_pages_used_total(sid)
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn decommit_subset_of_pointsto(local: Local, sid: SegmentId)
    requires
        local.wf_main(),
        local.segments.dom().contains(sid),
        local.mem_chunk_good(sid),
    ensures
        local.decommit_mask(sid).bytes(sid) <=
            local.segments[sid].mem.points_to.dom()
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn very_unready_range_okay_to_decommit(local: Local)
    requires
        local.wf_main(),
        local.page_organization.popped.is_VeryUnready(),
    ensures
        (match local.page_organization.popped {
            Popped::VeryUnready(segment_id, idx, count, _) => {
                set_int_range(
                    segment_start(segment_id) + idx * SLICE_SIZE,
                    segment_start(segment_id) + idx * SLICE_SIZE + count * SLICE_SIZE,
                ).disjoint(
                    segment_info_range(segment_id)
                        + local.segment_pages_used_total(segment_id)
                )
            }
            _ => false,
        }),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good(local1: Local, local2: Local)
    requires
        //local2.page_organization == local1.page_organization,
        //local2.pages == local1.pages,
        //local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        //local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local1.segments.dom() == local2.segments.dom(),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.segments[sid].mem == local1.segments[sid].mem,
        forall |page_id| local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),
        forall |page_id: PageId| #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

    ensures forall |sid| #[trigger] local1.segments.dom().contains(sid) ==>
        local1.mem_chunk_good(sid) ==> local2.mem_chunk_good(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_except(local1: Local, local2: Local, esegment_id: SegmentId)
    requires
        //local2.page_organization == local1.page_organization,
        //local2.pages == local1.pages,
        //local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        //local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local1.segments.dom().subset_of(local2.segments.dom()),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==> local2.segments[sid].mem == local1.segments[sid].mem,
        forall |page_id: PageId| page_id.segment_id != esegment_id && #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.page_reserved(page_id) <= local2.page_reserved(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),

        forall |page_id: PageId| page_id.segment_id != esegment_id && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

    ensures forall |sid| sid != esegment_id ==> #[trigger] local1.segments.dom().contains(sid) ==>
        local1.mem_chunk_good(sid) ==> local2.mem_chunk_good(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn empty_segment_pages_used_total(local1: Local, sid: SegmentId)
    requires
        forall |pid: PageId| pid.segment_id == sid ==> !local1.is_used_primary(pid),
    ensures
        local1.segment_pages_used_total(sid) =~= Set::empty(),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_segment_pages_used_total(local1: Local, local2: Local, sid: SegmentId)
    requires
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id),
    ensures local2.segment_pages_used_total(sid) <=
        local1.segment_pages_used_total(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserve_totals(local1: Local, local2: Local, sid: SegmentId)
    requires
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id)
              && local1.page_capacity(page_id) == local2.page_capacity(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id),
        forall |page_id: PageId| page_id.segment_id == sid && #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
    ensures
        local2.segment_pages_used_total(sid) =~= local1.segment_pages_used_total(sid),
        local2.segment_pages_range_total(sid) =~= local1.segment_pages_range_total(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_commit(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local2.segments[sid].mem.points_to.provenance() == local1.segments[sid].mem.points_to.provenance(),
    ensures local2.mem_chunk_good(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_decommit(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.points_to.provenance() == local1.segments[sid].mem.points_to.provenance(),

        local2.decommit_mask(sid).bytes(sid) <= local1.decommit_mask(sid).bytes(sid),
        local2.commit_mask(sid).bytes(sid) =~=
            local1.commit_mask(sid).bytes(sid) -
              (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

        local2.segments[sid].mem.os_rw_bytes() <= local1.segments[sid].mem.os_rw_bytes(),
        local2.segments[sid].mem.points_to.dom() =~=
            local1.segments[sid].mem.points_to.dom() -
              (local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes()),

        (local1.segments[sid].mem.os_rw_bytes() - local2.segments[sid].mem.os_rw_bytes())
          <= (local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

              //(local1.decommit_mask(sid).bytes(sid) - local2.decommit_mask(sid).bytes(sid)),

        local2.segments[sid].mem.os.dom() =~= local1.segments[sid].mem.os.dom(),
    ensures local2.mem_chunk_good(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_commit_with_mask_set(local1: Local, local2: Local, sid: SegmentId)
    requires
        local1.segments.dom().contains(sid),
        local2.segments.dom().contains(sid),
        local1.mem_chunk_good(sid),
        local2.page_organization == local1.page_organization,
        local2.pages == local1.pages,
        local2.segments[sid].mem.wf(),
        local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local2.segments[sid].mem.points_to.provenance() == sid.provenance,

        local2.decommit_mask(sid).bytes(sid).subset_of( local1.decommit_mask(sid).bytes(sid) ),
        local1.commit_mask(sid).bytes(sid).subset_of( local2.commit_mask(sid).bytes(sid) ),

        local2.decommit_mask(sid).bytes(sid).disjoint(
            local2.commit_mask(sid).bytes(sid) - local1.commit_mask(sid).bytes(sid)),

        (local1.segments[sid].mem.os_rw_bytes() + (
            local2.commit_mask(sid).bytes(sid) - local1.commit_mask(sid).bytes(sid)))
          .subset_of(local2.segments[sid].mem.os_rw_bytes())
    ensures local2.mem_chunk_good(sid),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_transfer_to_capacity(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.segments.dom().contains(page_id.segment_id),
        local2.segments.dom().contains(page_id.segment_id),
        local1.mem_chunk_good(page_id.segment_id),
        local2.page_organization == local1.page_organization,
        local1.pages.dom().contains(page_id),
        local2.pages.dom().contains(page_id),
        local2.commit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.commit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.decommit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.segments[page_id.segment_id].mem.wf(),
        local2.segments[page_id.segment_id].mem.points_to.provenance() == page_id.segment_id.provenance,

        local1.is_used_primary(page_id),
        forall |page_id| #[trigger] local1.is_used_primary(page_id) ==>
              local2.is_used_primary(page_id)
              && local1.page_capacity(page_id) <= local2.page_capacity(page_id)
              && local1.block_size(page_id) == local2.block_size(page_id)
              && local1.page_count(page_id) == local2.page_count(page_id),

        forall |page_id| local2.is_used_primary(page_id) ==>
              local1.is_used_primary(page_id),

        local2.segments[page_id.segment_id].mem.os
          == local1.segments[page_id.segment_id].mem.os,
        ({ let sr = set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local2.page_capacity(page_id) * local1.block_size(page_id),
            );
          local2.segments[page_id.segment_id].mem.points_to.dom() =~=
              local1.segments[page_id.segment_id].mem.points_to.dom() - sr
          //&& local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id).disjoint(sr)
        }),
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_good_on_transfer_back(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.segments.dom().contains(page_id.segment_id),
        local2.segments.dom().contains(page_id.segment_id),
        local1.mem_chunk_good(page_id.segment_id),

        local1.pages.dom().contains(page_id),
        local2.pages.dom().contains(page_id),
        local2.commit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.commit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.decommit_mask(page_id.segment_id).bytes(page_id.segment_id) == local1.decommit_mask(page_id.segment_id).bytes(page_id.segment_id),
        local2.segments[page_id.segment_id].mem.wf(),
        local2.segments[page_id.segment_id].mem.points_to.provenance() == page_id.segment_id.provenance,

        local1.is_used_primary(page_id),
        forall |pid| #[trigger] local1.is_used_primary(pid) && pid != page_id ==>
              local2.is_used_primary(pid)
              && local1.page_capacity(pid) <= local2.page_capacity(pid)
              && local1.block_size(pid) == local2.block_size(pid)
              && local1.page_count(pid) == local2.page_count(pid),

        forall |pid| #[trigger] local2.is_used_primary(pid) ==>
              local1.is_used_primary(pid),
        !local2.is_used_primary(page_id),

        local2.segments[page_id.segment_id].mem.os
          == local1.segments[page_id.segment_id].mem.os,
        local2.segments[page_id.segment_id].mem.points_to.dom() =~=
            local1.segments[page_id.segment_id].mem.points_to.dom() +
            set_int_range(
                page_start(page_id)
                    + start_offset(local1.block_size(page_id)),
                page_start(page_id)
                    + start_offset(local1.block_size(page_id))
                    + local1.page_capacity(page_id) * local1.block_size(page_id),
            )
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn preserves_mem_chunk_on_set_used(local1: Local, local2: Local, page_id: PageId)
    requires
        local1.mem_chunk_good(page_id.segment_id),
        //local2.page_organization == local1.page_organization,
        //local2.pages == local1.pages,
        //local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        //local2.segments[sid].mem.has_new_pointsto(&local1.segments[sid].mem),
        local1.segments.dom() == local2.segments.dom(),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.commit_mask(sid).bytes(sid) == local1.commit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.decommit_mask(sid).bytes(sid) == local1.decommit_mask(sid).bytes(sid),
        forall |sid| local1.segments.dom().contains(sid) ==>
            local2.segments[sid].mem == local1.segments[sid].mem,
        forall |pid| local1.is_used_primary(pid) ==>
              local2.is_used_primary(pid)
              && local1.page_capacity(pid) <= local2.page_capacity(pid)
              && local1.page_reserved(pid) <= local2.page_reserved(pid)
              && local1.page_count(pid) == local2.page_count(pid)
              && local1.block_size(pid) == local2.block_size(pid),
        forall |pid: PageId| #[trigger] local2.is_used_primary(pid) && page_id != pid ==>
              local1.is_used_primary(pid),
        page_init_is_committed(page_id, local2),
    ensures local2.mem_chunk_good(page_id.segment_id),
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn segment_mem_has_reserved_range(local: Local, page_id: PageId, new_cap: int)
    requires
        local.wf_main(),
        local.is_used_primary(page_id),
        local.page_capacity(page_id) <= new_cap <= local.page_reserved(page_id),
    ensures ({ let blocksize = local.block_size(page_id);
        local.segments[page_id.segment_id].mem.pointsto_has_range(
            block_start_at(page_id, blocksize, local.page_capacity(page_id)),
            (new_cap - local.page_capacity(page_id)) * blocksize)
    })
{
    unimplemented!();
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
