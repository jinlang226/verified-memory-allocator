#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::*;
use verus_state_machines_macros::*;

use crate::tokens::{PageId, SegmentId, TldId};
use crate::config::*;
use crate::bin_sizes::{valid_sbin_idx, smallest_sbin_fitting_size, smallest_bin_fitting_size, valid_bin_idx, size_of_bin};
use crate::layout::segment_start;

verus!{

pub ghost struct DlistHeader {
    pub first: Option<PageId>,
    pub last: Option<PageId>,
}

pub ghost struct DlistEntry {
    pub prev: Option<PageId>,
    pub next: Option<PageId>,
}

#[is_variant]
pub ghost enum PageHeaderKind {
    Normal(int, int),
}

pub ghost struct PageData {
    // Option means unspecified (i.e., does not constrain the physical value)
    pub dlist_entry: Option<DlistEntry>,
    pub count: Option<nat>,
    pub offset: Option<nat>,

    pub is_used: bool,
    pub full: Option<bool>,
    pub page_header_kind: Option<PageHeaderKind>,
}

pub ghost struct SegmentData {
    pub used: int,
}

#[is_variant]
pub ghost enum Popped {
    No,
    Ready(PageId, bool),            // set up the offsets   (all pages have offsets set)
    Used(PageId, bool),             // everything is set to 'used'

    SegmentCreating(SegmentId),     // just created
    VeryUnready(SegmentId, int, int, bool),      // no pages are set, not even first or last

    SegmentFreeing(SegmentId, int),

    ExtraCount(SegmentId),
}

// {page_id | page_id.segment_id == segment_id && lo <= page_id.idx < hi}
pub open spec fn page_id_range(segment_id: SegmentId, lo: nat, hi: nat) -> Set<PageId> {
    vstd::contrib::set_build!{ PageId { segment_id, idx }: PageId | idx: nat in lo..hi }
}

state_machine!{ PageOrg {
    fields {
        // Roughly corresponds to physical state
        pub unused_dlist_headers: Seq<DlistHeader>,     // indices are sbin
        pub used_dlist_headers: Seq<DlistHeader>,       // indices are bin
        pub pages: Map<PageId, PageData>,
        pub segments: Map<SegmentId, SegmentData>,

        // Actor state
        pub popped: Popped,

        // Internals
        pub unused_lists: Seq<Seq<PageId>>,
        pub used_lists: Seq<Seq<PageId>>,
    }

    #[invariant]
    pub closed spec fn ll_basics(&self) -> bool {
        &&& self.unused_dlist_headers.len() == SEGMENT_BIN_MAX + 1
        &&& self.unused_lists.len() == SEGMENT_BIN_MAX + 1
        &&& self.used_dlist_headers.len() == BIN_FULL + 1
        &&& self.used_lists.len() == BIN_FULL + 1
    }

    #[invariant]
    pub closed spec fn page_id_domain(&self) -> bool {
        forall |page_id: PageId|
            #![trigger self.pages.dom().contains(page_id)]
            self.pages.dom().contains(page_id) <==>
                self.segments.dom().contains(page_id.segment_id)
                    && page_id.idx <= SLICES_PER_SEGMENT
    }

    #[invariant]
    pub open spec fn segments_nonzero(&self) -> bool {
        forall |segment_id: SegmentId|
            #![trigger self.segments.dom().contains(segment_id)]
            self.segments.dom().contains(segment_id) ==> segment_start(segment_id) != 0
    }

    #[invariant]
    pub closed spec fn count_off0(&self) -> bool {
        forall |page_id: PageId|
            #![trigger self.pages.index(page_id)]
            self.pages.dom().contains(page_id)
            && self.pages[page_id].count.is_some()
            ==> {
                let count = self.pages[page_id].count.unwrap();
                &&& 1 <= count
                &&& page_id.idx + count <= SLICES_PER_SEGMENT
            }
    }

    #[invariant]
    pub closed spec fn end_is_unused(&self) -> bool {
        forall |segment_id: SegmentId|
            #![trigger self.segments.dom().contains(segment_id)]
            self.segments.dom().contains(segment_id)
            && !(match self.popped {
                Popped::SegmentCreating(sid) => sid == segment_id,
                Popped::SegmentFreeing(sid, _) => sid == segment_id,
                _ => false,
            })
            && self.segments[segment_id].used == self.popped_ec(segment_id)
            ==> {
                let page_id = PageId { segment_id, idx: 0 };
                &&& self.pages.dom().contains(page_id)
                &&& self.pages[page_id].offset == Some(0nat)
                &&& !self.pages[page_id].is_used
                &&& self.pages[page_id].count.is_some()
            }
    }

    #[invariant]
    pub closed spec fn count_is_right(&self) -> bool {
        forall |segment_id: SegmentId|
            #![trigger self.segments.dom().contains(segment_id)]
            self.segments.dom().contains(segment_id) ==>
                self.segments[segment_id].used == self.ucount(segment_id) as int + self.popped_ec(segment_id)
    }

    #[invariant]
    pub closed spec fn popped_basics(&self) -> bool {
        match self.popped {
            Popped::No => true,
            Popped::Ready(page_id, _) | Popped::Used(page_id, _) => {
                &&& self.segments.dom().contains(page_id.segment_id)
                &&& self.pages.dom().contains(page_id)
                &&& page_id.idx != 0
                &&& self.pages[page_id].offset == Some(0nat)
                &&& self.pages[page_id].count.is_some()
                &&& {
                    let count = self.pages[page_id].count.unwrap();
                    &&& 1 <= count
                    &&& page_id.idx + count <= SLICES_PER_SEGMENT
                }
            },
            Popped::SegmentCreating(segment_id) => self.segments.dom().contains(segment_id),
            Popped::VeryUnready(segment_id, start, count, _) => {
                &&& self.segments.dom().contains(segment_id)
                &&& 0 < start
                &&& 0 < count
                &&& start + count <= SLICES_PER_SEGMENT
            },
            Popped::SegmentFreeing(segment_id, idx) => {
                &&& self.segments.dom().contains(segment_id)
                &&& 0 <= idx <= SLICES_PER_SEGMENT
            },
            Popped::ExtraCount(segment_id) => self.segments.dom().contains(segment_id),
        }
    }

    #[invariant]
    pub closed spec fn data_for_used_header(&self) -> bool {
        forall |page_id: PageId|
            #![trigger self.pages.dom().contains(page_id)]
            #![trigger self.pages.index(page_id)]
            self.pages.dom().contains(page_id)
            && (self.popped.is_No()
                || self.popped.is_ExtraCount()
                || self.popped.is_SegmentFreeing()
                || ((self.popped.is_Ready() || self.popped.is_VeryUnready())
                    && !self.in_popped_range(page_id))
                || (self.popped.is_Used() && page_id != self.popped_page_id()))
            && self.pages[page_id].is_used
            && self.pages[page_id].offset == Some(0nat)
            ==>
            self.pages[page_id].dlist_entry.is_some()
            && self.pages[page_id].full.is_some()
            && (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
    }

    #[invariant]
    pub closed spec fn inv_segment_creating(&self) -> bool {
        match self.popped {
            Popped::SegmentCreating(segment_id) => {
                &&& self.segments.dom().contains(segment_id)
                &&& self.segments[segment_id].used == 0
                &&& (forall |pid: PageId|
                    #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                    pid.segment_id == segment_id
                    && pid.idx <= SLICES_PER_SEGMENT ==>
                        self.pages.dom().contains(pid)
                        && self.pages[pid].dlist_entry.is_none()
                        && self.pages[pid].count.is_none()
                        && self.pages[pid].offset.is_none()
                        && self.pages[pid].is_used == false
                        && self.pages[pid].full.is_none()
                        && self.pages[pid].page_header_kind.is_none())
                &&& (forall |pid: PageId|
                    #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                    self.pages.dom().contains(pid)
                    && pid.segment_id != segment_id
                    && self.pages[pid].is_used
                    && self.pages[pid].offset == Some(0nat) ==>
                        self.pages[pid].dlist_entry.is_some()
                        && self.pages[pid].full.is_some()
                        && (match self.pages[pid].page_header_kind {
                            Some(PageHeaderKind::Normal(bin, size)) =>
                                valid_bin_idx(bin)
                                && size == size_of_bin(bin)
                                && bin == smallest_bin_fitting_size(size)
                                && size <= MEDIUM_OBJ_SIZE_MAX,
                            None => false,
                        }))
                &&& (forall |pid: PageId|
                    #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                    self.pages.dom().contains(pid)
                    && pid.segment_id != segment_id
                    && self.pages[pid].is_used
                    && self.pages[pid].offset == Some(0nat)
                    && self.pages[pid].full != Some(false) ==>
                        is_in_list_at(pid, self.used_lists, BIN_FULL as int))
                &&& (forall |pid: PageId|
                    #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                    self.pages.dom().contains(pid)
                    && pid.segment_id != segment_id
                    && self.pages[pid].is_used
                    && self.pages[pid].offset == Some(0nat)
                    && self.pages[pid].full != Some(true) ==>
                        (match self.pages[pid].page_header_kind {
                            Some(PageHeaderKind::Normal(bin, _)) => is_in_list_at(pid, self.used_lists, bin),
                            None => false,
                        }))
                &&& (forall |pid: PageId|
                    #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                    self.pages.dom().contains(pid)
                    && pid.segment_id != segment_id
                    && self.pages[pid].offset == Some(0nat)
                    && !self.pages[pid].is_used
                    && pid.idx != 0 ==>
                        self.pages[pid].count.is_some()
                        && is_in_lls(pid, self.unused_lists))
            },
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_very_unready(&self) -> bool {
        match self.popped {
            Popped::VeryUnready(segment_id, start, count, _) => {
                let page_id = PageId { segment_id, idx: start as nat };
                &&& 0 < start
                &&& 0 < count
                &&& start + count <= SLICES_PER_SEGMENT
                &&& self.good_range_very_unready(page_id)
            },
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_segment_freeing(&self) -> bool {
        match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => {
                &&& self.segments.dom().contains(segment_id)
                &&& self.segments[segment_id].used == 0
                &&& 0 < idx <= SLICES_PER_SEGMENT
                &&& self.seg_free_prefix(segment_id, idx)
                &&& idx < SLICES_PER_SEGMENT ==> self.attached_rec(segment_id, idx, false)
            },
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_ready(&self) -> bool {
        match self.popped {
            Popped::Ready(page_id, _) => {
                &&& self.good_range_ready(page_id)
                &&& self.pages[page_id].dlist_entry.is_none()
                &&& self.pages[page_id].full.is_none()
                &&& self.pages[page_id].page_header_kind.is_none()
            },
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn inv_used(&self) -> bool {
        match self.popped {
            Popped::Used(page_id, _) => {
                &&& self.good_range_used(page_id)
                &&& self.pages[page_id].dlist_entry.is_none()
                &&& self.pages[page_id].full.is_none()
            },
            _ => true,
        }
    }

    #[invariant]
    pub closed spec fn data_for_unused_header(&self) -> bool {
        self.ll_inv_valid_unused()
    }

    #[invariant]
    pub closed spec fn ready_popped_not_in_unused_lists(&self) -> bool {
        forall |i: int, j: int|
            #![trigger self.unused_lists.index(i).index(j)]
            0 <= i < self.unused_lists.len()
            && 0 <= j < self.unused_lists[i].len()
            && self.popped.is_Ready()
            ==>
            self.unused_lists[i][j] != self.popped_page_id()
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_unused(&self) -> bool {
        &&& (forall |i: int|
            #![trigger self.unused_dlist_headers.index(i)]
            0 <= i < self.unused_lists.len() ==>
                valid_ll(self.pages, self.unused_dlist_headers[i], self.unused_lists[i]))
        &&& (forall |i: int, j: int|
            #![trigger self.unused_lists.index(i).index(j)]
            0 <= i < self.unused_lists.len()
            && 0 <= j < self.unused_lists[i].len() ==>
            ({
                let page_id = self.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& self.pages.dom().contains(page_id)
                &&& page_id.idx != 0
                &&& self.pages[page_id].is_used == false
                &&& (match self.pages[page_id].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& self.pages[page_id].offset == Some(0nat)
                &&& self.pages[page_id].dlist_entry.is_some()
                &&& 0 <= j < self.unused_lists[i].len()
                &&& self.unused_lists[i][j] == page_id
                &&& self.valid_unused_page(page_id, i, j)
                &&& i == smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int)
            }))
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_used(&self) -> bool {
        &&& (forall |i: int|
            #![trigger self.used_dlist_headers.index(i)]
            0 <= i < self.used_lists.len() ==>
                valid_ll(self.pages, self.used_dlist_headers[i], self.used_lists[i]))
        &&& (forall |i: int, j: int|
            #![trigger self.used_lists.index(i).index(j)]
            0 <= i < self.used_lists.len()
            && 0 <= j < self.used_lists[i].len() ==>
            ({
                let page_id = self.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& self.valid_used_page(page_id, i, j)
                &&& self.pages[page_id].count.is_some()
                &&& self.pages[page_id].full == Some(i == BIN_FULL)
                &&& (self.popped.is_Ready() ==> page_id != self.popped_page_id())
            }))
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_unused2(&self) -> bool {
        self.ll_inv_exists_in_some_list()
    }

    #[invariant]
    pub closed spec fn ll_inv_valid_used2(&self) -> bool {
        &&& (forall |page_id: PageId|
            #![trigger self.pages.dom().contains(page_id)]
            #![trigger self.pages.index(page_id)]
            self.pages.dom().contains(page_id)
            && (self.popped.is_No()
                || self.popped.is_ExtraCount()
                || self.popped.is_SegmentFreeing()
                || ((self.popped.is_Ready() || self.popped.is_VeryUnready())
                    && !self.in_popped_range(page_id))
                || (self.popped.is_Used() && page_id != self.popped_page_id()))
            && self.pages[page_id].is_used
            && self.pages[page_id].offset == Some(0nat)
            && self.pages[page_id].full != Some(false)
            ==>
                is_in_list_at(page_id, self.used_lists, BIN_FULL as int))
        &&& (forall |page_id: PageId|
            #![trigger self.pages.dom().contains(page_id)]
            #![trigger self.pages.index(page_id)]
            self.pages.dom().contains(page_id)
            && (self.popped.is_No()
                || self.popped.is_ExtraCount()
                || self.popped.is_SegmentFreeing()
                || ((self.popped.is_Ready() || self.popped.is_VeryUnready())
                    && !self.in_popped_range(page_id))
                || (self.popped.is_Used() && page_id != self.popped_page_id()))
            && self.pages[page_id].is_used
            && self.pages[page_id].offset == Some(0nat)
            && self.pages[page_id].full != Some(true)
            ==>
                (match self.pages[page_id].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, _)) =>
                        is_in_list_at(page_id, self.used_lists, bin),
                    None => false,
                }))
    }

    #[invariant]
    #[verifier::opaque]
    pub closed spec fn ll_inv_exists_in_some_list(&self) -> bool {
        &&& (forall |page_id: PageId|
            #![trigger self.pages.dom().contains(page_id)]
            #![trigger self.pages.index(page_id)]
            self.pages.dom().contains(page_id)
            && (self.popped.is_No() || self.popped.is_ExtraCount()
                || self.popped.is_Ready() || self.popped.is_Used()
                || self.popped.is_VeryUnready() || self.popped.is_SegmentFreeing())
            && !self.in_popped_range(page_id)
            && self.pages[page_id].offset == Some(0nat)
            && !self.pages[page_id].is_used
            && page_id.idx != 0
            ==>
            self.pages[page_id].count.is_some()
            && is_in_lls(page_id, self.unused_lists))
        &&& (forall |i: int, j: int|
            #![trigger self.unused_lists.index(i).index(j)]
            0 <= i < self.unused_lists.len()
            && 0 <= j < self.unused_lists[i].len()
            ==>
                i == smallest_sbin_fitting_size(
                    self.pages[self.unused_lists[i][j]].count.unwrap() as int))
    }

    ///////

    #[invariant]
    pub closed spec fn attached_ranges(&self) -> bool {
        forall |segment_id: SegmentId|
            #![trigger self.segments.dom().contains(segment_id)]
            self.segments.dom().contains(segment_id) ==> self.attached_ranges_segment(segment_id)
    }

    #[invariant]
    pub open spec fn public_invariant(&self) -> bool {
        &&& self.ll_basics()
        &&& self.page_id_domain()
        &&& self.count_off0()
        &&& self.popped_basics()
    }

    pub closed spec fn attached_ranges_segment(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::SegmentCreating(sid) if sid == segment_id => true,
            Popped::SegmentFreeing(sid, idx) if sid == segment_id && idx > 0 => self.attached_rec(segment_id, idx, false),
            _ => self.attached_rec0(segment_id, self.popped_for_seg(segment_id))
        }
    }

    pub closed spec fn seg_free_prefix(&self, segment_id: SegmentId, idx: int) -> bool {
        forall |pid: PageId|
            #![trigger self.pages.dom().contains(pid)]
            #![trigger self.pages.index(pid)]
            pid.segment_id == segment_id && 0 <= pid.idx < idx ==>
            self.pages.dom().contains(pid)
            && self.pages[pid].dlist_entry.is_none()
            && self.pages[pid].count.is_none()
            && self.pages[pid].offset.is_none()
            && self.pages[pid].is_used == false
            && self.pages[pid].full.is_none()
            && self.pages[pid].page_header_kind.is_none()
    }

    pub closed spec fn attached_rec0(&self, segment_id: SegmentId, sp: bool) -> bool {
        self.good_range0(segment_id)
          && self.attached_rec(segment_id, self.pages[PageId { segment_id, idx: 0 }].count.unwrap() as int, sp)
    }

    #[verifier::opaque]
    pub closed spec fn attached_rec(&self, segment_id: SegmentId, idx: int, sp: bool) -> bool
        decreases SLICES_PER_SEGMENT - idx
    {
        if idx == SLICES_PER_SEGMENT {
          !sp
        } else if idx > SLICES_PER_SEGMENT {
          false
        } else if Self::is_the_popped(segment_id, idx, self.popped) {
          sp
            && self.popped_len() > 0
            && idx + self.popped_len() <= SLICES_PER_SEGMENT
            && self.attached_rec(segment_id, idx + self.popped_len(), false)
        } else {
          let page_id = PageId { segment_id, idx: idx as nat };
               (self.pages[page_id].is_used ==> self.good_range_used(page_id))
            && (!self.pages[page_id].is_used ==> self.good_range_unused(page_id))
            && self.pages[page_id].count.unwrap() > 0
            && idx + self.pages[page_id].count.unwrap() <= SLICES_PER_SEGMENT
            && self.attached_rec(segment_id, idx + self.pages[page_id].count.unwrap(), sp)
        }
    }

    pub closed spec fn popped_ranges_match(pre: Self, post: Self) -> bool {
        Self::is_any_the_popped(pre.popped) == Self::is_any_the_popped(post.popped)
          && (Self::is_any_the_popped(pre.popped) ==>
              pre.popped_len() == post.popped_len()
                && Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped)
          )
    }

    pub closed spec fn popped_ranges_match_for_sid(pre: Self, post: Self, sid: SegmentId) -> bool {
        pre.popped_for_seg(sid) == post.popped_for_seg(sid)
          && (pre.popped_for_seg(sid) ==>
              pre.popped_len() == post.popped_len()
                && Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped)
          )
    }


    pub closed spec fn popped_for_seg(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, _, _, _) => sid == segment_id,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn is_any_the_popped(popped: Popped) -> bool {
        match popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => true,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, i, _, _) => true,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn is_the_popped(segment_id: SegmentId, idx: int, popped: Popped) -> bool {
        match popped {
            Popped::No => false,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id && page_id.idx == idx,
            Popped::SegmentCreating(_) => false,
            Popped::SegmentFreeing(_, _) => false,
            Popped::VeryUnready(sid, i, _, _) => sid == segment_id && i == idx,
            Popped::ExtraCount(_) => false,
        }
    }

    pub closed spec fn popped_len(&self) -> int {
        match self.popped {
            Popped::No => arbitrary(),
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => self.pages[page_id].count.unwrap() as int,
            Popped::SegmentCreating(_) => arbitrary(),
            Popped::SegmentFreeing(_, _) => arbitrary(),
            Popped::VeryUnready(sid, i, count, _) => count,
            Popped::ExtraCount(_) => arbitrary(),
        }
    }

    ///////

    pub open spec fn valid_unused_page(&self, page_id: PageId, sbin_idx: int, list_idx: int) -> bool {
        self.pages.dom().contains(page_id)
          && page_id.idx != 0
          && self.pages[page_id].is_used == false
          && (match self.pages[page_id].count {
              Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
              None => false,
          })
          && self.pages[page_id].dlist_entry.is_some()
          && 0 <= sbin_idx <= SEGMENT_BIN_MAX
          && 0 <= list_idx < self.unused_lists[sbin_idx].len()
          && self.unused_lists[sbin_idx][list_idx] == page_id
    }

    pub proof fn first_is_in(&self, sbin_idx: int)
        requires self.invariant(), self.popped.is_No(),
            0 <= sbin_idx <= SEGMENT_BIN_MAX,
        ensures
            match self.unused_dlist_headers[sbin_idx].first {
                Some(page_id) => self.valid_unused_page(page_id, sbin_idx, 0),
                None => true,
            }
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        match self.unused_dlist_headers[sbin_idx].first {
            Some(page_id) => {
                assert(0 <= sbin_idx < self.unused_lists.len());
                assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], self.unused_lists[sbin_idx]));
                assert(self.unused_lists[sbin_idx].len() != 0);
                assert(self.unused_lists[sbin_idx][0] == page_id);
                assert(self.valid_unused_page(page_id, sbin_idx, 0));
            }
            None => { }
        }
    }

    pub proof fn next_is_in(&self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires self.invariant(), self.popped.is_No(),
            self.valid_unused_page(page_id, sbin_idx, list_idx)
        ensures
            match self.pages[page_id].dlist_entry.unwrap().next {
                Some(page_id) => self.valid_unused_page(page_id, sbin_idx, list_idx + 1),
                None => true,
            }
    {
        reveal(State::ll_inv_valid_unused);
        assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], self.unused_lists[sbin_idx]));
        assert(valid_ll_i(self.pages, self.unused_lists[sbin_idx], list_idx));
        assert(self.unused_lists[sbin_idx][list_idx] == page_id);
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        match dlist_entry.next {
            Some(next_page_id) => {
                assert(dlist_entry.next == get_next(self.unused_lists[sbin_idx], list_idx));
                assert(get_next(self.unused_lists[sbin_idx], list_idx) == Some(next_page_id));
                assert(list_idx != self.unused_lists[sbin_idx].len() - 1);
                assert(list_idx + 1 < self.unused_lists[sbin_idx].len());
                assert(self.unused_lists[sbin_idx][list_idx + 1] == next_page_id);
                assert(self.valid_unused_page(next_page_id, sbin_idx, list_idx + 1));
            }
            None => { }
        }
    }

    pub proof fn segment_freeing_current_unused_header(&self)
        requires self.invariant(),
            self.popped.is_SegmentFreeing(),
            self.popped.get_SegmentFreeing_1() < SLICES_PER_SEGMENT,
        ensures (match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => {
                let page_id = PageId { segment_id, idx: idx as nat };
                &&& idx > 0
                &&& self.pages.dom().contains(page_id)
                &&& self.pages[page_id].offset == Some(0nat)
                &&& !self.pages[page_id].is_used
                &&& self.pages[page_id].count.is_some()
                &&& self.pages[page_id].dlist_entry.is_some()
            },
            _ => false,
        })
    {
        reveal(State::popped_basics);
        reveal(State::inv_segment_freeing);
        reveal(State::count_is_right);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::good_range_used);
        reveal(State::good_range_unused);
        reveal(State::does_count);

        match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => {
                assert(0 < idx < SLICES_PER_SEGMENT);
                let page_id = PageId { segment_id, idx: idx as nat };
                assert(self.segments.dom().contains(segment_id));
                assert(self.segments[segment_id].used == 0);
                assert(self.popped_ec(segment_id) == 0);
                assert(self.ucount(segment_id) == 0);
                assert(self.attached_rec(segment_id, idx, false));
                assert(!Self::is_the_popped(segment_id, idx, self.popped));
                if self.pages[page_id].is_used {
                    assert(self.good_range_used(page_id));
                    assert(self.pages.dom().contains(page_id));
                    assert(self.pages[page_id].offset == Some(0nat));
                    self.ucount_eq0_inverse(page_id);
                    assert(self.does_count(page_id));
                    assert(false);
                }
                assert(!self.pages[page_id].is_used);
                assert(self.good_range_unused(page_id));
                assert(self.pages.dom().contains(page_id));
                assert(self.pages[page_id].offset == Some(0nat));
                assert(self.pages[page_id].count.is_some());
                assert(self.pages[page_id].dlist_entry.is_some());
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn segment_freeing_is_in(&self) -> (list_idx: int)
        requires self.invariant(),
            self.popped.is_SegmentFreeing(),
            self.popped.get_SegmentFreeing_1() < SLICES_PER_SEGMENT,
        ensures (match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => { idx >= 0 && {
                let page_id = PageId { segment_id, idx: idx as nat };
                let count = self.pages[page_id].count.unwrap();
                let sbin_idx = smallest_sbin_fitting_size(count as int);
                self.valid_unused_page(page_id, sbin_idx, list_idx)
            }}
            _ => false,
        }),
    {
        self.segment_freeing_current_unused_header();
        match self.popped {
            Popped::SegmentFreeing(segment_id, idx) => {
                let page_id = PageId { segment_id, idx: idx as nat };
                self.unused_is_in_sbin(page_id);
                let pair = Self::get_list_idx(self.unused_lists, page_id);
                let list_idx = pair.1;
                let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
                assert(self.valid_unused_page(page_id, sbin_idx, list_idx));
                list_idx
            }
            _ => {
                assert(false);
                arbitrary()
            }
        }
    }

    pub proof fn used_page_dlist_facts(&self, page_id: PageId, bin_idx: int, list_idx: int)
        requires
            self.invariant(),
            self.valid_used_page(page_id, bin_idx, list_idx),
        ensures ({
            let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
            &&& 0 <= bin_idx < self.used_lists.len()
            &&& 0 <= list_idx < self.used_lists[bin_idx].len()
            &&& self.used_lists[bin_idx][list_idx] == page_id
            &&& (dlist_entry.prev.is_none() ==>
                list_idx == 0 && self.used_dlist_headers[bin_idx].first == Some(page_id))
            &&& (match dlist_entry.next {
                Some(next_page_id) =>
                    next_page_id != page_id
                    && self.pages.dom().contains(next_page_id)
                    && self.pages[next_page_id].dlist_entry.is_some()
                    && self.pages[next_page_id].is_used,
                None => true,
            })
        })
    {
        reveal(State::valid_used_page);
        reveal(State::ll_inv_valid_used);

        let old_ll = self.used_lists[bin_idx];
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        assert(0 <= bin_idx < self.used_lists.len());
        assert(0 <= list_idx < old_ll.len());
        assert(old_ll[list_idx] == page_id);
        assert(valid_ll(self.pages, self.used_dlist_headers[bin_idx], old_ll));
        assert(valid_ll_i(self.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));

        match dlist_entry.prev {
            Some(prev_page_id) => {
                assert(list_idx != 0);
                assert(prev_page_id == old_ll[list_idx - 1]);
                assert(0 <= list_idx - 1 < old_ll.len());
                self.ll_used_distinct(bin_idx, list_idx - 1, bin_idx, list_idx);
                assert(prev_page_id != page_id);
            }
            None => {
                assert(list_idx == 0);
                assert(self.used_dlist_headers[bin_idx].first == Some(old_ll[0]));
                assert(self.used_dlist_headers[bin_idx].first == Some(page_id));
            }
        }

        match dlist_entry.next {
            Some(next_page_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_page_id == old_ll[list_idx + 1]);
                assert(0 <= list_idx + 1 < old_ll.len());
                assert(self.used_lists[bin_idx][list_idx + 1] == next_page_id);
                assert(self.pages.dom().contains(next_page_id));
                assert(self.pages[next_page_id].dlist_entry.is_some());
                assert(self.pages[next_page_id].is_used);
                self.ll_used_distinct(bin_idx, list_idx + 1, bin_idx, list_idx);
                assert(next_page_id != page_id);
            }
            None => { }
        }
    }

    pub proof fn marked_full_is_in(&self, page_id: PageId) -> (list_idx: int)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_No(),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].full != Some(false),
            self.pages[page_id].is_used,
        ensures
            self.valid_used_page(page_id, BIN_FULL as int, list_idx),
            (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                  size == size_of_bin(bin)
                  && bin == smallest_bin_fitting_size(size)
                  && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            }),

    {
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_used);
        reveal(State::ll_inv_valid_used2);
        assert(is_in_list_at(page_id, self.used_lists, BIN_FULL as int));
        let list_idx = choose |j: int|
            0 <= (BIN_FULL as int) < self.used_lists.len()
            && 0 <= j < self.used_lists[BIN_FULL as int].len()
            && self.used_lists[BIN_FULL as int][j] == page_id;
        assert(0 <= (BIN_FULL as int) < self.used_lists.len());
        assert(0 <= list_idx < self.used_lists[BIN_FULL as int].len());
        assert(self.used_lists[BIN_FULL as int][list_idx] == page_id);
        assert(self.valid_used_page(page_id, BIN_FULL as int, list_idx));
        match self.pages[page_id].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) => {
                assert(size == size_of_bin(bin));
                assert(bin == smallest_bin_fitting_size(size));
                assert(size <= MEDIUM_OBJ_SIZE_MAX);
            }
            None => {
                assert(false);
            }
        }
        list_idx
    }

    pub proof fn marked_unfull_is_in(&self, page_id: PageId) -> (list_idx: int)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_No(),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].full != Some(true),
            self.pages[page_id].is_used,
        ensures
            (match self.pages[page_id].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                  size == size_of_bin(bin)
                  && self.valid_used_page(page_id, bin, list_idx)
                  && bin == smallest_bin_fitting_size(size)
                  && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            }),
    {
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_used);
        reveal(State::ll_inv_valid_used2);
        match self.pages[page_id].page_header_kind {
            Some(PageHeaderKind::Normal(bin, size)) => {
                assert(is_in_list_at(page_id, self.used_lists, bin));
                let list_idx = choose |j: int|
                    0 <= bin < self.used_lists.len()
                    && 0 <= j < self.used_lists[bin].len()
                    && self.used_lists[bin][j] == page_id;
                assert(0 <= bin < self.used_lists.len());
                assert(0 <= list_idx < self.used_lists[bin].len());
                assert(self.used_lists[bin][list_idx] == page_id);
                assert(self.valid_used_page(page_id, bin, list_idx));
                assert(size == size_of_bin(bin));
                assert(bin == smallest_bin_fitting_size(size));
                assert(size <= MEDIUM_OBJ_SIZE_MAX);
                list_idx
            }
            None => {
                assert(false);
                arbitrary()
            }
        }
    }

    #[verifier::opaque]
    pub closed spec fn get_list_idx(lists: Seq<Seq<PageId>>, pid: PageId) -> (int, int) {
        let (i, j): (int, int) = choose |i: int, j: int|
            0 <= i < lists.len()
            && 0 <= j < lists[i].len()
            && lists[i][j] == pid;
        (i, j)
    }

    proof fn unused_is_in_sbin(&self, page_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.popped.is_VeryUnready() || self.popped.is_SegmentFreeing(),
            self.pages[page_id].offset == Some(0nat),
            !self.pages[page_id].is_used,
            page_id.idx != 0,
        ensures ({
            let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
            let list_idx = Self::get_list_idx(self.unused_lists, page_id).1;
            self.valid_unused_page(page_id, sbin_idx, list_idx)
        })
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::get_list_idx);
        let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
        let pair = Self::get_list_idx(self.unused_lists, page_id);
        let list_idx = pair.1;
        assert(0 <= pair.0 < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[pair.0].len());
        assert(self.unused_lists[pair.0][list_idx] == page_id);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[sbin_idx].len());
        assert(self.unused_lists[sbin_idx][list_idx] == page_id);
        assert(self.valid_unused_page(page_id, sbin_idx, list_idx));
    }

    pub proof fn get_count_bound_very_unready(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures
            0 < self.popped.get_VeryUnready_1(),
            self.popped.get_VeryUnready_1() + 
                self.popped.get_VeryUnready_2() <= SLICES_PER_SEGMENT,
    {
        reveal(State::inv_very_unready);
    }

    pub proof fn lemma_range_disjoint_very_unready(&self, page_id: PageId)
        requires self.invariant(), self.popped.is_VeryUnready(),
            self.pages.dom().contains(page_id),
            self.pages[page_id].offset == Some(0nat),
            self.pages[page_id].is_used,
            page_id.segment_id == self.popped.get_VeryUnready_0(),
        ensures
            match self.popped {
                Popped::VeryUnready(_, idx, p_count, _) => {
                    match self.pages[page_id].count {
                        Some(count) => page_id.idx + count <= idx || idx + p_count <= page_id.idx,
                        None => false,
                    }
                }
                _ => false,
            }
    {
        assert(is_used_header(self.pages[page_id]));
        self.used_header_has_good_range(page_id);
        self.good_range_disjoint_very_unready(page_id);
    }

    pub proof fn lemma_range_disjoint_used2(&self, page_id1: PageId, page_id2: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id1),
            self.pages[page_id1].offset == Some(0nat),
            self.pages[page_id1].is_used,
            self.pages.dom().contains(page_id2),
            self.pages[page_id2].offset == Some(0nat),
            self.pages[page_id2].is_used,
            page_id1 != page_id2,
            page_id1.segment_id == page_id2.segment_id,
        ensures
            match (self.pages[page_id1].count, self.pages[page_id2].count) {
                (Some(count1), Some(count2)) => {
                    page_id1.idx + count1 <= page_id2.idx
                      || page_id2.idx + count2 <= page_id1.idx
                }
                _ => false,
            }
    {
        assert(is_used_header(self.pages[page_id1]));
        assert(is_used_header(self.pages[page_id2]));
        self.used_header_has_good_range(page_id1);
        self.used_header_has_good_range(page_id2);
        reveal(State::good_range_used);
        let count1 = self.pages[page_id1].count.unwrap();
        let count2 = self.pages[page_id2].count.unwrap();
        if !(page_id1.idx + count1 <= page_id2.idx || page_id2.idx + count2 <= page_id1.idx) {
            if page_id1.idx < page_id2.idx {
                assert(page_id1.idx <= page_id2.idx < page_id1.idx + count1);
                assert(self.pages[page_id2].offset == Some((page_id2.idx - page_id1.idx) as nat));
                assert(page_id2.idx - page_id1.idx > 0);
                assert(self.pages[page_id2].offset == Some(0nat));
                assert(false);
            } else {
                assert(page_id1.idx != page_id2.idx);
                assert(page_id2.idx < page_id1.idx);
                assert(page_id2.idx <= page_id1.idx < page_id2.idx + count2);
                assert(self.pages[page_id1].offset == Some((page_id1.idx - page_id2.idx) as nat));
                assert(page_id1.idx - page_id2.idx > 0);
                assert(self.pages[page_id1].offset == Some(0nat));
                assert(false);
            }
        }
    }

    pub proof fn used_offset0_has_count(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            self.pages[page_id].is_used,
            self.pages[page_id].offset == Some(0nat),
            page_id.idx != 0,
        ensures
            self.pages[page_id].count.is_some()
    {
        assert(is_used_header(self.pages[page_id]));
        self.used_header_has_good_range(page_id);
    }

    pub proof fn get_offset_for_something_in_used_range(&self, page_id: PageId, slice_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            self.pages[page_id].is_used,
            self.pages[page_id].offset == Some(0nat),
            slice_id.segment_id == page_id.segment_id,
            page_id.idx <= slice_id.idx < page_id.idx + self.pages[page_id].count.unwrap(),
        ensures
            self.pages.dom().contains(slice_id),
            self.pages[slice_id].is_used,
            self.pages[slice_id].offset == Some((slice_id.idx - page_id.idx) as nat)
    {
        assert(is_used_header(self.pages[page_id]));
        self.used_header_has_good_range(page_id);
        reveal(State::good_range_used);
    }

    pub proof fn ready_popped_range_facts(&self)
        requires self.invariant(), self.popped.is_Ready(),
        ensures
            match self.popped {
                Popped::Ready(page_id, _) => {
                    let count = self.pages[page_id].count.unwrap();
                    &&& self.pages.dom().contains(page_id)
                    &&& self.pages[page_id].count.is_some()
                    &&& count > 0
                    &&& self.pages[page_id].offset == Some(0nat)
                    &&& page_id.idx != 0
                    &&& page_id.idx + count <= SLICES_PER_SEGMENT
                    &&& self.pages[page_id].dlist_entry.is_none()
                    &&& self.pages[page_id].full.is_none()
                    &&& self.pages[page_id].page_header_kind.is_none()
                    &&& (forall |pid: PageId|
                        #![trigger self.pages.dom().contains(pid)]
                        #![trigger self.pages.index(pid)]
                        pid.segment_id == page_id.segment_id
                        && page_id.idx <= pid.idx < page_id.idx + count ==>
                            self.pages.dom().contains(pid)
                            && !self.pages[pid].is_used
                            && self.pages[pid].offset.is_some()
                            && self.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                            && self.pages[pid].full.is_none()
                            && self.pages[pid].page_header_kind.is_none()
                            && (self.pages[pid].count.is_some() <==> pid == page_id)
                            && self.pages[pid].dlist_entry.is_none())
                },
                _ => false,
            },
    {
        reveal(State::popped_basics);
        reveal(State::inv_ready);
        reveal(State::good_range_ready);
    }

    pub proof fn very_unready_popped_range_facts(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures
            match self.popped {
                Popped::VeryUnready(segment_id, idx, count, _) => {
                    let page_id = PageId { segment_id, idx: idx as nat };
                    &&& 0 < idx
                    &&& 0 < count
                    &&& idx + count <= SLICES_PER_SEGMENT
                    &&& page_id.idx == idx
                    &&& self.pages.dom().contains(page_id)
                    &&& self.pages[page_id].offset.is_none()
                    &&& self.pages[page_id].count.is_none()
                    &&& (forall |pid: PageId|
                        #![trigger self.pages.dom().contains(pid)]
                        #![trigger self.pages.index(pid)]
                        pid.segment_id == segment_id
                        && page_id.idx <= pid.idx < page_id.idx + count ==>
                            self.pages.dom().contains(pid)
                            && !self.pages[pid].is_used
                            && self.pages[pid].full.is_none()
                            && self.pages[pid].page_header_kind.is_none()
                            && self.pages[pid].count.is_none()
                            && self.pages[pid].dlist_entry.is_none()
                            && self.pages[pid].offset.is_none())
                },
                _ => false,
            },
    {
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        reveal(State::good_range_very_unready);
    }

    pub proof fn used_popped_range_facts(&self)
        requires self.invariant(), self.popped.is_Used(),
        ensures
            match self.popped {
                Popped::Used(page_id, _) => {
                    let count = self.pages[page_id].count.unwrap();
                    &&& self.pages.dom().contains(page_id)
                    &&& self.pages[page_id].count.is_some()
                    &&& count > 0
                    &&& self.pages[page_id].offset == Some(0nat)
                    &&& page_id.idx != 0
                    &&& page_id.idx + count <= SLICES_PER_SEGMENT
                    &&& self.pages[page_id].full.is_none()
                    &&& (forall |pid: PageId|
                        #![trigger self.pages.dom().contains(pid)]
                        #![trigger self.pages.index(pid)]
                        pid.segment_id == page_id.segment_id
                        && page_id.idx <= pid.idx < page_id.idx + count ==>
                            self.pages.dom().contains(pid)
                            && self.pages[pid].is_used
                            && self.pages[pid].offset.is_some()
                            && self.pages[pid].offset.unwrap() == pid.idx - page_id.idx)
                },
                _ => false,
            },
    {
        reveal(State::popped_basics);
        reveal(State::inv_used);
        reveal(State::good_range_used);
    }

    pub proof fn used_header_has_good_range(&self, page_id: PageId)
        requires self.invariant(),
            self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
    {
        match self.popped {
            Popped::Used(popped_page_id, _) => {
                if popped_page_id == page_id {
                    reveal(State::inv_used);
                    assert(self.good_range_used(page_id));
                    reveal(State::good_range_used);
                } else {
                    self.lemma_range_used(page_id);
                }
            }
            _ => {
                self.lemma_range_used(page_id);
            }
        }
    }

    #[verifier::rlimit(200)]
    pub proof fn used_header_range_page_facts(&self, page_id: PageId, pid: PageId)
        requires
            self.invariant(),
            self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            self.pages[page_id].count.is_some(),
            pid.segment_id == page_id.segment_id,
            page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap(),
        ensures
            self.pages.dom().contains(pid),
            self.pages[pid].is_used,
            self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat),
    {
        self.used_header_has_good_range(page_id);
        reveal(State::good_range_used);
        assert(self.good_range_used(page_id));
        assert(self.pages.dom().contains(pid));
        assert(self.pages[pid].is_used);
        assert(self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat));
    }

    pub proof fn get_count_bound(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
        ensures
            (match self.pages[page_id].count {
                None => true,
                Some(count) => page_id.idx + count <= SLICES_PER_SEGMENT
            }),
    {
        reveal(State::count_off0);
    }

    pub open spec fn valid_used_page(&self, page_id: PageId, bin_idx: int, list_idx: int) -> bool {
        self.pages.dom().contains(page_id)
          && page_id.idx != 0
          && self.pages[page_id].is_used == true
          //&& (match self.pages[page_id].count {
          //    Some(count) => 0 <= count <= SLICES_PER_SEGMENT,
          //    None => false,
          //})
          && self.pages[page_id].dlist_entry.is_some()
          && self.pages[page_id].offset == Some(0nat)
          && (crate::bin_sizes::valid_bin_idx(bin_idx) || bin_idx == BIN_FULL)
          && 0 <= list_idx < self.used_lists[bin_idx].len()
          && self.used_lists[bin_idx][list_idx] == page_id
          && (match self.pages[page_id].page_header_kind {
              None => false,
              Some(PageHeaderKind::Normal(bin, bsize)) =>
                  valid_bin_idx(bin)
                  && size_of_bin(bin) == bsize
                  && (bin_idx != BIN_FULL ==> bin_idx == bin)
          })
    }

    pub proof fn used_first_is_in(&self, bin_idx: int)
        requires self.invariant(), !self.popped.is_Ready(),
            0 <= bin_idx <= BIN_HUGE,
        ensures
            match self.used_dlist_headers[bin_idx].first {
                Some(page_id) => self.valid_used_page(page_id, bin_idx, 0),
                None => true,
            }
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_used);
        match self.used_dlist_headers[bin_idx].first {
            Some(page_id) => {
                assert(0 <= bin_idx < self.used_lists.len());
                assert(valid_ll(self.pages, self.used_dlist_headers[bin_idx], self.used_lists[bin_idx]));
                assert(self.used_lists[bin_idx].len() != 0);
                assert(self.used_lists[bin_idx][0] == page_id);
                assert(self.valid_used_page(page_id, bin_idx, 0));
            }
            None => { }
        }
    }

    pub proof fn used_next_is_in(&self, page_id: PageId, bin_idx: int, list_idx: int)
        requires self.invariant(),
            self.valid_used_page(page_id, bin_idx, list_idx)
        ensures
            match self.pages[page_id].dlist_entry.unwrap().next {
                Some(page_id) => self.valid_used_page(page_id, bin_idx, list_idx + 1),
                None => true,
            }
    {
        reveal(State::ll_inv_valid_used);
        assert(valid_ll(self.pages, self.used_dlist_headers[bin_idx], self.used_lists[bin_idx]));
        assert(valid_ll_i(self.pages, self.used_lists[bin_idx], list_idx));
        assert(self.used_lists[bin_idx][list_idx] == page_id);
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        match dlist_entry.next {
            Some(next_page_id) => {
                assert(dlist_entry.next == get_next(self.used_lists[bin_idx], list_idx));
                assert(get_next(self.used_lists[bin_idx], list_idx) == Some(next_page_id));
                assert(list_idx != self.used_lists[bin_idx].len() - 1);
                assert(list_idx + 1 < self.used_lists[bin_idx].len());
                assert(self.used_lists[bin_idx][list_idx + 1] == next_page_id);
                assert(self.valid_used_page(next_page_id, bin_idx, list_idx + 1));
            }
            None => { }
        }
    }

    pub proof fn rec_valid_page_after(&self, idx: int, sp: bool)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start + len < SLICES_PER_SEGMENT
                }
                _ => false,
            },
            self.attached_rec(self.popped.get_VeryUnready_0(), idx, sp),
            !sp ==>
                idx >= Self::page_id_of_popped(self.popped).idx + self.popped_len(),
            idx >= 0,
        ensures
            sp || idx == Self::page_id_of_popped(self.popped).idx + self.popped_len() ==> match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let page_id = PageId { segment_id: sid, idx: (start + len) as nat };
                    self.pages.dom().contains(page_id)
                      && self.pages[page_id].offset == Some(0nat)
                }
                _ => false,
            },
            sp ==>
                idx <= Self::page_id_of_popped(self.popped).idx,
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::popped_basics);
        match self.popped {
            Popped::VeryUnready(sid, start, len, _) => {
                assert(0 < len);
                assert(start + len < SLICES_PER_SEGMENT);
                let after_idx = start + len;
                let after_id = PageId { segment_id: sid, idx: after_idx as nat };
                assert(after_idx >= 0);
                if idx == SLICES_PER_SEGMENT {
                    assert(!sp);
                    assert(idx != after_idx);
                } else if idx > SLICES_PER_SEGMENT {
                    assert(!self.attached_rec(sid, idx, sp));
                    assert(false);
                } else if Self::is_the_popped(sid, idx, self.popped) {
                    assert(idx == start);
                    assert(sp);
                    assert(idx + self.popped_len() == after_idx);
                    assert(self.attached_rec(sid, after_idx, false));
                    self.rec_valid_page_after(after_idx, false);
                } else {
                    let page_id = PageId { segment_id: sid, idx: idx as nat };
                    let count = self.pages[page_id].count.unwrap();
                    assert(count > 0);
                    if idx == after_idx {
                        assert(page_id == after_id);
                        if self.pages[page_id].is_used {
                            assert(self.good_range_used(page_id));
                            reveal(State::good_range_used);
                        } else {
                            assert(self.good_range_unused(page_id));
                            reveal(State::good_range_unused);
                        }
                        assert(self.pages.dom().contains(after_id));
                        assert(self.pages[after_id].offset == Some(0nat));
                    }
                    if sp {
                        assert(self.attached_rec(sid, idx + count, sp));
                        self.rec_valid_page_after(idx + count, sp);
                        assert(idx + count <= start);
                        assert(idx <= start);
                    }
                }
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn valid_page_after(&self)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start + len < SLICES_PER_SEGMENT
                }
                _ => false,
            }
        ensures
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let page_id = PageId { segment_id: sid, idx: (start + len) as nat };
                    self.pages.dom().contains(page_id)
                      && self.pages[page_id].offset == Some(0nat)
                }
                _ => false,
            }
    {
        reveal(State::attached_ranges);
        reveal(State::popped_basics);
        match self.popped {
            Popped::VeryUnready(segment_id, start, len, _) => {
                assert(self.attached_ranges());
                self.attached_ranges_very_unready_start();
                assert(self.attached_rec(segment_id, start, true));
                assert(start >= 0);
                self.rec_valid_page_after(start, true);
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn rec_valid_page_before(&self, idx: int, sp: bool)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start > 0
                }
                _ => false,
            },
            self.attached_rec(self.popped.get_VeryUnready_0(), idx, sp),
            !sp ==>
                idx >= Self::page_id_of_popped(self.popped).idx + self.popped_len(),
            idx >= 0,
        ensures
            idx < Self::page_id_of_popped(self.popped).idx ==> (
                match self.popped {
                    Popped::VeryUnready(sid, start, len, _) => {
                        let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                        let offset = self.pages[last_id].offset.unwrap();
                        let page_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                        self.pages.dom().contains(last_id)
                        && last_id.idx - offset >= 0
                        && self.pages[last_id].offset.is_some()
                        && self.pages.dom().contains(page_id)
                        && self.pages[page_id].offset == Some(0nat)
                        && self.pages[page_id].count == Some(offset + 1)
                    }
                    _ => false,
                }),
            sp ==>
                idx <= Self::page_id_of_popped(self.popped).idx,
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::popped_basics);
        match self.popped {
            Popped::VeryUnready(sid, start, len, _) => {
                assert(0 < start);
                assert(0 < len);
                assert(start + len <= SLICES_PER_SEGMENT);
                if idx == SLICES_PER_SEGMENT {
                    assert(!sp);
                    if idx < start {
                        assert(false);
                    }
                } else if idx > SLICES_PER_SEGMENT {
                    assert(!self.attached_rec(sid, idx, sp));
                    assert(false);
                } else if Self::is_the_popped(sid, idx, self.popped) {
                    assert(idx == start);
                    assert(sp);
                    if idx < start {
                        assert(false);
                    }
                } else {
                    let page_id = PageId { segment_id: sid, idx: idx as nat };
                    let count = self.pages[page_id].count.unwrap();
                    assert(count > 0);

                    if sp {
                        assert(self.attached_rec(sid, idx + count, sp));
                        self.rec_valid_page_before(idx + count, sp);
                        assert(idx + count <= start);
                        assert(idx <= start);
                    }

                    if idx < start {
                        if !sp {
                            assert(idx >= start + len);
                            assert(false);
                        }
                        assert(sp);
                        assert(idx + count <= start);
                        if idx + count == start {
                            if self.pages[page_id].is_used {
                                assert(self.good_range_used(page_id));
                                reveal(State::good_range_used);
                            } else {
                                assert(self.good_range_unused(page_id));
                                reveal(State::good_range_unused);
                            }
                            assert(self.pages.dom().contains(page_id));
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(self.pages[page_id].count == Some(count));
                            let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                            assert(last_id.segment_id == page_id.segment_id);
                            assert(last_id.idx == start - 1);
                            assert(page_id.idx == idx);
                            assert(page_id.idx <= last_id.idx);
                            assert(last_id.idx < page_id.idx + count);
                            assert(self.pages.dom().contains(last_id));
                            assert(self.pages[last_id].offset == Some((last_id.idx - page_id.idx) as nat));
                            let offset = self.pages[last_id].offset.unwrap();
                            assert(offset == (last_id.idx - page_id.idx) as nat);
                            assert(offset + 1 == count);
                            assert(last_id.idx - offset == page_id.idx);
                            let before_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                            assert(before_id == page_id);
                            assert(self.pages.dom().contains(before_id));
                            assert(self.pages[before_id].offset == Some(0nat));
                            assert(self.pages[before_id].count == Some(offset + 1));
                        } else {
                            assert(idx + count < start);
                        }
                    }
                }
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn valid_page_before(&self)
        requires self.invariant(),
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    start > 0
                }
                _ => false,
            }
        ensures
            match self.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    let last_id = PageId { segment_id: sid, idx: (start - 1) as nat };
                    let offset = self.pages[last_id].offset.unwrap();
                    let page_id = PageId { segment_id: sid, idx: (last_id.idx - offset) as nat };
                    self.pages.dom().contains(last_id)
                    && last_id.idx - offset >= 0
                    && self.pages[last_id].offset.is_some()
                    && self.pages.dom().contains(page_id)
                    && self.pages[page_id].offset == Some(0nat)
                    && self.pages[page_id].count == Some(offset + 1)
                }
                _ => false,
            }
    {
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        match self.popped {
            Popped::VeryUnready(segment_id, start, len, _) => {
                assert(0 < start);
                assert(0 < len);
                assert(start + len <= SLICES_PER_SEGMENT);
                reveal(State::popped_ranges_match);
                reveal(State::is_any_the_popped);
                reveal(State::page_id_of_popped);
                reveal(State::popped_len);
                reveal(State::in_popped_range);

                let s = *self;
                assert(Self::popped_ranges_match(s, s));
                assert(s.segments.dom() =~= s.segments.dom());
                assert forall |pid: PageId|
                    #![trigger s.pages.dom().contains(pid)]
                    #![trigger s.pages[pid]]
                    (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                    && (s.pages.dom().contains(pid) && !s.in_popped_range(pid) ==> {
                        &&& s.pages.dom().contains(pid)
                        &&& s.pages[pid].count == s.pages[pid].count
                        &&& s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some()
                        &&& s.pages[pid].offset == s.pages[pid].offset
                        &&& s.pages[pid].is_used == s.pages[pid].is_used
                        &&& s.pages[pid].full == s.pages[pid].full
                        &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                    })
                by { };
                Self::attached_ranges_all(s, s);
                assert(s.segments.dom().contains(segment_id));
                assert(s.attached_ranges_segment(segment_id));
                reveal(State::attached_ranges_segment);
                assert(s.attached_rec0(segment_id, true));
                reveal(State::attached_rec0);
                assert(s.good_range0(segment_id));

                let first_id = PageId { segment_id, idx: 0 };
                let first_count = s.pages[first_id].count.unwrap();
                assert(s.pages.dom().contains(first_id));
                assert(s.pages[first_id].offset == Some(0nat));
                assert(s.pages[first_id].count == Some(first_count));
                reveal(State::count_off0);
                assert(1 <= first_count);
                assert(s.attached_rec(segment_id, first_count as int, true));
                s.rec_valid_page_before(first_count as int, true);
                assert(first_count <= start);

                if first_count == start {
                    reveal(State::good_range0);
                    let last_id = PageId { segment_id, idx: (start - 1) as nat };
                    assert(last_id.segment_id == first_id.segment_id);
                    assert(last_id.idx == start - 1);
                    assert(first_id.idx <= last_id.idx);
                    assert(last_id.idx < first_id.idx + first_count);
                    assert(s.pages.dom().contains(last_id));
                    assert(s.pages[last_id].offset == Some((last_id.idx - first_id.idx) as nat));
                    let offset = s.pages[last_id].offset.unwrap();
                    assert(offset == (last_id.idx - first_id.idx) as nat);
                    assert(offset + 1 == first_count);
                    assert(last_id.idx - offset == first_id.idx);
                    let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
                    assert(page_id == first_id);
                    assert(s.pages.dom().contains(page_id));
                    assert(s.pages[page_id].offset == Some(0nat));
                    assert(s.pages[page_id].count == Some(offset + 1));
                } else {
                    assert(first_count < start);
                }
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn rec_attached_to_very_unready_start(s: Self, idx: int, sp: bool)
        requires
            match s.popped {
                Popped::VeryUnready(sid, start, len, _) => {
                    &&& 0 < start
                    &&& 0 < len
                    &&& start + len <= SLICES_PER_SEGMENT
                },
                _ => false,
            },
            s.attached_rec(s.popped.get_VeryUnready_0(), idx, sp),
            !sp ==> idx >= s.popped.get_VeryUnready_1() + s.popped.get_VeryUnready_2(),
            idx >= 0,
        ensures
            sp ==> idx <= s.popped.get_VeryUnready_1(),
            sp ==> s.attached_rec(s.popped.get_VeryUnready_0(), s.popped.get_VeryUnready_1(), true),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        match s.popped {
            Popped::VeryUnready(sid, start, len, _) => {
                if idx == SLICES_PER_SEGMENT {
                    assert(!sp);
                } else if idx > SLICES_PER_SEGMENT {
                    assert(!s.attached_rec(sid, idx, sp));
                    assert(false);
                } else if Self::is_the_popped(sid, idx, s.popped) {
                    assert(idx == start);
                    assert(sp);
                    assert(s.attached_rec(sid, start, true));
                } else {
                    let page_id = PageId { segment_id: sid, idx: idx as nat };
                    let count = s.pages[page_id].count.unwrap();
                    assert(count > 0);
                    if sp {
                        assert(s.attached_rec(sid, idx + count, sp));
                        Self::rec_attached_to_very_unready_start(s, idx + count, sp);
                        assert(idx + count <= start);
                        assert(s.attached_rec(sid, start, true));
                    } else {
                        assert(idx >= start + len);
                    }
                }
            }
            _ => {
                assert(false);
            }
        }
    }


    pub proof fn attached_ranges_from_segments(s: Self)
        requires
            forall |sid: SegmentId| #[trigger] s.segments.dom().contains(sid) ==> s.attached_ranges_segment(sid),
        ensures s.attached_ranges(),
    {
        reveal(State::attached_ranges);
    }

    pub proof fn attached_ranges_very_unready_start(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures match self.popped {
            Popped::VeryUnready(segment_id, start, _, _) => self.attached_rec(segment_id, start, true),
            _ => false,
        }
    {
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        match self.popped {
            Popped::VeryUnready(segment_id, start, len, b) => {
                assert(self.segments.dom().contains(segment_id));
                assert(self.attached_ranges_segment(segment_id));
                assert(self.attached_rec0(segment_id, true));
                let first_id = PageId { segment_id, idx: 0 };
                let first_count = self.pages[first_id].count.unwrap();
                assert(self.attached_rec(segment_id, first_count as int, true));
                Self::rec_attached_to_very_unready_start(*self, first_count as int, true);
                assert(self.attached_rec(segment_id, start, true));
            }
            _ => { assert(false); }
        }
    }


    pub proof fn good_range0_same(pre: Self, post: Self, segment_id: SegmentId)
        requires
            pre.good_range0(segment_id),
            ({
                let first_id = PageId { segment_id, idx: 0 };
                let first_count = pre.pages[first_id].count.unwrap();
                &&& post.pages[first_id].count == pre.pages[first_id].count
                &&& 0 < first_count
            }),
            forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                ({
                    let first_id = PageId { segment_id, idx: 0 };
                    let first_count = pre.pages[first_id].count.unwrap();
                    pid.segment_id == segment_id
                    && first_id.idx <= pid.idx < first_id.idx + first_count
                }) ==> (post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]),
        ensures post.good_range0(segment_id),
    {
        reveal(State::good_range0);
        let first_id = PageId { segment_id, idx: 0 };
        let first_count = pre.pages[first_id].count.unwrap();
        assert(first_id.idx < first_id.idx + first_count);
        assert(post.pages[first_id] == pre.pages[first_id]);
        assert(post.pages.dom().contains(first_id));
        assert(post.pages[first_id].offset == Some(0nat));
        assert(post.pages[first_id].count.is_some());
        assert(first_id.idx + first_count <= SLICES_PER_SEGMENT);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == segment_id
            && first_id.idx <= pid.idx < first_id.idx + first_count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == first_id)
            && post.pages[pid].dlist_entry.is_none()
            && post.pages[pid].offset == Some((pid.idx - first_id.idx) as nat)
        by {
            assert(post.pages[pid] == pre.pages[pid]);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == false);
            assert(pre.pages[pid].full.is_none());
            assert(pre.pages[pid].page_header_kind.is_none());
            assert(pre.pages[pid].count.is_some() <==> pid == first_id);
            assert(pre.pages[pid].dlist_entry.is_none());
            assert(pre.pages[pid].offset == Some((pid.idx - first_id.idx) as nat));
        };
    }

    init!{
        initialize() {
            init unused_dlist_headers = Seq::new((SEGMENT_BIN_MAX + 1) as nat,
                |i| DlistHeader { first: None, last: None });
            init used_dlist_headers = Seq::new((BIN_FULL + 1) as nat,
                |i| DlistHeader { first: None, last: None });
            init pages = Map::empty();
            init segments = Map::empty();
            init popped = Popped::No;

            // TODO internals
            init unused_lists = Seq::new((SEGMENT_BIN_MAX + 1) as nat, |i| Seq::empty());
            init used_lists = Seq::new((BIN_FULL + 1) as nat, |i| Seq::empty());
        }
    }

    transition!{
        take_page_from_unused_queue(page_id: PageId, sbin_idx: int, list_idx: int) {
            require pre.valid_unused_page(page_id, sbin_idx, list_idx);
            require pre.popped == Popped::No
                || pre.popped == Popped::SegmentFreeing(page_id.segment_id, page_id.idx as int);

            assert pre.pages[page_id].dlist_entry.is_some() by {
                pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
            };
            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;
            assert pre.pages[page_id].is_used == false by {
                pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
            };

            update pages[page_id] = PageData {
                dlist_entry: None,
                count: None,
                offset: None,
                .. pre.pages[page_id]
            };

            // Update prev to point to next
            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                      && pre.pages.dom().contains(prev_page_id)
                      && pre.pages[prev_page_id].dlist_entry.is_some()
                      && pre.pages[prev_page_id].is_used == false

                      by {
                          pre.take_page_from_unused_queue_dlist_facts(page_id, sbin_idx, list_idx);
                      };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            // Update next to point to prev
            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                      && pre.pages.dom().contains(next_page_id)
                      && pre.pages[next_page_id].dlist_entry.is_some()
                      && pre.pages[next_page_id].is_used == false

                      by {
                          pre.take_page_from_unused_queue_dlist_facts(page_id, sbin_idx, list_idx);
                      };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            // Workaround for not begin able to do `update unused_dlist_headers[sbin_idx].first = ...`
            if dlist_entry.prev.is_none() && dlist_entry.next.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    first: dlist_entry.next,
                    last: dlist_entry.prev,
                };
            } else if dlist_entry.prev.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    first: dlist_entry.next,
                    .. pre.unused_dlist_headers[sbin_idx]
                };
            } else if dlist_entry.next.is_none() {
                update unused_dlist_headers[sbin_idx] = DlistHeader {
                    last: dlist_entry.prev,
                    .. pre.unused_dlist_headers[sbin_idx]
                };
            }

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by {
                    pre.take_page_from_unused_queue_dlist_facts(page_id, sbin_idx, list_idx);
                };

            assert pre.pages[page_id].count.is_some() by {
                pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
            };
            assert let Some(count) = pre.pages[page_id].count;

            assert count >= 1 by {
                pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
            };
            let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
            if last_id != page_id {
                update pages[last_id] = PageData {
                    offset: None,
                    .. pre.pages[last_id]
                };
                assert(pre.pages.dom().contains(last_id))
                    by {
                        pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
                    };

                assert(pre.pages[last_id].is_used == false
                      && pre.pages[last_id].page_header_kind.is_none())

                    by {
                        pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
                    };
            }
            assert dlist_entry.prev != Some(last_id)
                && dlist_entry.next != Some(last_id)
              by {
                  pre.take_page_from_unused_queue_last_id_not_removed_neighbors(
                      page_id, sbin_idx, list_idx);
              };

            match pre.popped {
                Popped::No => {
                    update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, false);
                }
                Popped::SegmentFreeing(sid, i) => {
                    update popped = Popped::SegmentFreeing(sid, i + count);
                }
                _ => { }
            }

            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    transition!{
        split_page(page_id: PageId, current_count: int, target_count: int, sbin_idx: int) {
            // Require that `page_id` is currently popped
            // and that it has has count equal to `current_count`
            require pre.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, current_count, false);
            assert pre.pages.dom().contains(page_id) by {
                pre.very_unready_popped_range_facts();
            };
            assert pre.pages[page_id].count.is_none() by {
                pre.very_unready_popped_range_facts();
            };
            require !pre.pages[page_id].is_used;

            require 1 <= target_count < current_count;
            require 0 <= sbin_idx <= SEGMENT_BIN_MAX;
            require sbin_idx == smallest_sbin_fitting_size(current_count - target_count);

            //  |------------current_count---------------|
            //  
            //  |--------------|-------------------------|
            //    target_count
            //
            //                   ^                      ^
            //                   |                      |
            //    ^           next_page_id          last_page_id
            //    |
            //  page_id

            let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, .. page_id };
            let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, .. page_id };
            assert pre.pages.dom().contains(next_page_id)
                && pre.pages.dom().contains(last_page_id)
                && pre.pages[next_page_id].is_used == false
                && pre.pages[last_page_id].is_used == false by {
                    pre.very_unready_popped_range_facts();
                    assert(next_page_id.segment_id == page_id.segment_id);
                    assert(last_page_id.segment_id == page_id.segment_id);
                    assert(page_id.idx <= next_page_id.idx);
                    assert(next_page_id.idx < page_id.idx + current_count);
                    assert(page_id.idx <= last_page_id.idx);
                    assert(last_page_id.idx < page_id.idx + current_count);
                };

            update pages[next_page_id] = PageData {
                count: Some((current_count - target_count) as nat),
                offset: Some(0),
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.unused_dlist_headers[sbin_idx].first,
                }),
                .. pre.pages[next_page_id]
            };

            // If the 'last page' is distinct from the 'next page'
            // we have to update it too
            if current_count - target_count > 1 {
                update pages[last_page_id] = PageData {
                    count: None, //Some((current_count - target_count) as nat),
                    offset: Some((current_count - target_count - 1) as nat),
                    .. pre.pages[last_page_id]
                };
            }

            // Insert into the queue
            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: Some(next_page_id),
                last:
                    if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                        pre.unused_dlist_headers[sbin_idx].last
                    } else {
                        Some(next_page_id)
                    },
            };
            if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                assert pre.pages.dom().contains(first_id)
                    && !pre.pages[first_id].is_used
                    && pre.pages[first_id].dlist_entry.is_some()
                    && first_id != page_id
                    && first_id != next_page_id
                    && first_id != last_page_id
                by {
                    pre.very_unready_popped_range_facts();
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_unused);
                    reveal(State::valid_unused_page);
                    assert(0 <= sbin_idx < pre.unused_lists.len());
                    assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], pre.unused_lists[sbin_idx]));
                    assert(pre.unused_lists[sbin_idx].len() != 0);
                    assert(pre.unused_lists[sbin_idx][0] == first_id);
                    assert(valid_ll_i(pre.pages, pre.unused_lists[sbin_idx], 0));
                    assert(pre.valid_unused_page(first_id, sbin_idx, 0));
                    if first_id == page_id {
                        assert(pre.pages[first_id].count.is_some());
                        assert(pre.pages[page_id].count.is_none());
                        assert(false);
                    }
                    if first_id == next_page_id {
                        assert(next_page_id.segment_id == page_id.segment_id);
                        assert(page_id.idx <= next_page_id.idx);
                        assert(next_page_id.idx < page_id.idx + current_count);
                        assert(pre.pages[first_id].count.is_some());
                        assert(pre.pages[next_page_id].count.is_none());
                        assert(false);
                    }
                    if first_id == last_page_id {
                        assert(last_page_id.segment_id == page_id.segment_id);
                        assert(page_id.idx <= last_page_id.idx);
                        assert(last_page_id.idx < page_id.idx + current_count);
                        assert(pre.pages[first_id].count.is_some());
                        assert(pre.pages[last_page_id].count.is_none());
                        assert(false);
                    }
                };
                update pages[first_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(next_page_id),
                        .. pre.pages[first_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[first_id]
                };
            }

            update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, target_count, false);
            update unused_lists = Self::insert_front(pre.unused_lists, sbin_idx, next_page_id);
        }
    }

    transition!{
        create_segment(segment_id: SegmentId) {
            require pre.popped == Popped::No;
            require !pre.segments.dom().contains(segment_id);
            require segment_start(segment_id) != 0;

            let new_pages = Map::new(
                page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1),
                |page_id: PageId| PageData {
                    dlist_entry: None,
                    count: None,
                    offset: None,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                });

            update segments = pre.segments.insert(segment_id, SegmentData { used: 0 });
            update pages = pre.pages.union_prefer_right(new_pages);
            update popped = Popped::SegmentCreating(segment_id);
        }
    }

    transition!{
        allocate_popped() {
            require let Popped::VeryUnready(segment_id, idx, count, fals) = pre.popped;
            require fals == false;
            assert idx >= 0 by {
                pre.very_unready_popped_range_facts();
            };
            let page_id = PageId { segment_id, idx: idx as nat };
            assert page_id.idx == idx by {
                pre.very_unready_popped_range_facts();
            };
            assert pre.pages.dom().contains(page_id) by {
                pre.very_unready_popped_range_facts();
            };
            assert count > 0 by {
                pre.very_unready_popped_range_facts();
            };
            assert count + page_id.idx <= SLICES_PER_SEGMENT by {
                pre.very_unready_popped_range_facts();
            };

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                ) by {
                    pre.very_unready_popped_range_facts();
                };
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> !pre.pages[pid].is_used
                ) by {
                    pre.very_unready_popped_range_facts();
                };

            let changed_pages = Map::new(
                page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count as nat),
                |pid: PageId| PageData {
                    count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                    offset: Some((pid.idx - page_id.idx) as nat), // set offset
                    dlist_entry: pre.pages[pid].dlist_entry,
                    // keep is_used=false for now
                    // instead, we mark that this operation is done by setting popped=Ready
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom() by {
                vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
                assert forall |pid: PageId|
                    changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
                by {
                    assert(pid.segment_id == page_id.segment_id);
                    assert(page_id.idx <= pid.idx < page_id.idx + count);
                };
                assert(changed_pages.dom().subset_of(pre.pages.dom()));
                assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
                assert(pre.pages.dom() =~= new_pages.dom());
            };

            assert pre.segments[page_id.segment_id].used <= SLICES_PER_SEGMENT + 1
                by {
                    pre.lemma_used_bound(page_id.segment_id);
                };
            update segments[page_id.segment_id] = SegmentData {
                used: pre.segments[page_id.segment_id].used + 1,
            };

            update pages = new_pages;
            update popped = Popped::Ready(page_id, true);
        }
    }

    transition!{
        forget_about_first_page(count: int) {
            require 1 <= count < SLICES_PER_SEGMENT;
            require let Popped::SegmentCreating(segment_id) = pre.popped;
            assert pre.segments.dom().contains(segment_id) by {
                pre.segment_creating_facts(segment_id);
            };

            assert forall |pid: PageId| pid.segment_id == segment_id &&
                    0 <= pid.idx < count
                    ==> pre.pages.dom().contains(pid)
                by {
                    pre.segment_creating_facts(segment_id);
                };
            assert forall |pid: PageId| pid.segment_id == segment_id &&
                    0 <= pid.idx < count
                    ==> !pre.pages[pid].is_used
                by {
                    pre.segment_creating_facts(segment_id);
                };

            let page_id = PageId { segment_id, idx: 0 };
            assert pre.pages.dom().contains(page_id) by {
                pre.segment_creating_facts(segment_id);
            };
            assert count + page_id.idx <= SLICES_PER_SEGMENT by { };
            let changed_pages = Map::new(
                page_id_range(segment_id, 0, count as nat),
                |pid: PageId| PageData {
                    count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                    offset: Some((pid.idx - page_id.idx) as nat), // set offset
                    dlist_entry: pre.pages[pid].dlist_entry,
                    is_used: false,
                    page_header_kind: None,
                    full: None,
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom() by {
                vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
                assert forall |pid: PageId|
                    changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
                by {
                    assert(pid.segment_id == segment_id);
                    assert(0 <= pid.idx < count);
                    pre.segment_creating_facts(segment_id);
                    assert(pid.idx <= SLICES_PER_SEGMENT);
                };
                assert(changed_pages.dom().subset_of(pre.pages.dom()));
                assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
                assert(pre.pages.dom() =~= new_pages.dom());
            };
            update pages = new_pages;

            assert pre.segments[page_id.segment_id].used <= SLICES_PER_SEGMENT + 1
                by {
                    pre.segment_creating_facts(segment_id);
                };
            update segments[page_id.segment_id] = SegmentData {
                used: pre.segments[page_id.segment_id].used + 1,
            };

            update popped = Popped::VeryUnready(segment_id, count, SLICES_PER_SEGMENT - count, true);
        }
    }

    transition!{
        forget_about_first_page2() {
            require let Popped::VeryUnready(segment_id, start, count, tru) = pre.popped;
            require tru == true;

            assert pre.segments[segment_id].used >= 1 by {
                reveal(State::popped_basics);
                reveal(State::count_is_right);
                reveal(State::popped_ec);
                reveal(State::ec_of_popped);
                assert(pre.popped == Popped::VeryUnready(segment_id, start, count, true));
                assert(pre.segments.dom().contains(segment_id));
                assert(pre.popped_ec(segment_id) == 1);
                assert(pre.segments[segment_id].used == pre.ucount(segment_id) as int + 1);
            };
            update segments[segment_id] = SegmentData {
                used: pre.segments[segment_id].used - 1,
            };

            update popped = Popped::VeryUnready(segment_id, start, count, false);
        }
    }

    transition!{
        clear_ec() {
            require let Popped::ExtraCount(segment_id) = pre.popped;

            assert pre.segments[segment_id].used >= 1 by {
                reveal(State::popped_basics);
                reveal(State::count_is_right);
                reveal(State::popped_ec);
                reveal(State::ec_of_popped);
                assert(pre.popped == Popped::ExtraCount(segment_id));
                assert(pre.segments.dom().contains(segment_id));
                assert(pre.popped_ec(segment_id) == 1);
                assert(pre.segments[segment_id].used == pre.ucount(segment_id) as int + 1);
            };
            update segments[segment_id] = SegmentData {
                used: pre.segments[segment_id].used - 1,
            };

            update popped = Popped::No;
        }
    }


    transition!{
        free_to_unused_queue(sbin_idx: int) {
            require valid_sbin_idx(sbin_idx);
            require let Popped::VeryUnready(segment_id, start, count, ec) = pre.popped;
            assert pre.segments.dom().contains(segment_id) by {
                pre.very_unready_popped_range_facts();
            };
            assert 1 <= start < start + count <= SLICES_PER_SEGMENT by {
                pre.very_unready_popped_range_facts();
            };

            require sbin_idx == smallest_sbin_fitting_size(count);

            let first_page = PageId { segment_id, idx: start as nat };
            let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };

            assert pre.pages.dom().contains(first_page) by {
                pre.very_unready_popped_range_facts();
            };
            assert !pre.pages[first_page].is_used by {
                pre.very_unready_popped_range_facts();
            };
            assert pre.pages.dom().contains(last_page) by {
                pre.very_unready_popped_range_facts();
                assert(first_page.idx <= last_page.idx);
                assert(last_page.idx < first_page.idx + count);
            };
            assert !pre.pages[last_page].is_used by {
                pre.very_unready_popped_range_facts();
                assert(first_page.idx <= last_page.idx);
                assert(last_page.idx < first_page.idx + count);
            };

            assert pre.pages[first_page].count.is_none() by {
                pre.very_unready_popped_range_facts();
            };
            assert pre.pages[first_page].offset.is_none() by {
                pre.very_unready_popped_range_facts();
            };
            assert pre.pages[last_page].offset.is_none() by {
                pre.very_unready_popped_range_facts();
                assert(first_page.idx <= last_page.idx);
                assert(last_page.idx < first_page.idx + count);
            };

            update pages[first_page] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.unused_dlist_headers[sbin_idx].first,
                }),
                count: Some(count as nat),
                offset: Some(0),
                is_used: false,
                page_header_kind: None,
                full: None,
            };

            if count > 1 {
                assert last_page != first_page by { };
                update pages[last_page] = PageData {
                    offset: Some((count - 1) as nat),
                    .. pre.pages[last_page]
                };
            }

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: Some(first_page),
                last: if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    pre.unused_dlist_headers[sbin_idx].last
                } else {
                    Some(first_page)
                },
            };

            if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                assert queue_first_page_id != first_page
                    && queue_first_page_id != last_page
                    && pre.pages.dom().contains(queue_first_page_id)
                    && !pre.pages[queue_first_page_id].is_used
                    && pre.pages[queue_first_page_id].dlist_entry.is_some()
                by {
                    pre.very_unready_popped_range_facts();
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_unused);
                    reveal(State::valid_unused_page);
                    assert(0 <= sbin_idx < pre.unused_lists.len());
                    assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], pre.unused_lists[sbin_idx]));
                    assert(pre.unused_lists[sbin_idx].len() != 0);
                    assert(pre.unused_lists[sbin_idx][0] == queue_first_page_id);
                    assert(valid_ll_i(pre.pages, pre.unused_lists[sbin_idx], 0));
                    assert(pre.valid_unused_page(queue_first_page_id, sbin_idx, 0));
                    if queue_first_page_id == first_page {
                        assert(pre.pages[queue_first_page_id].count.is_some());
                        assert(pre.pages[first_page].count.is_none());
                        assert(false);
                    }
                    if queue_first_page_id == last_page {
                        assert(first_page.idx <= last_page.idx);
                        assert(last_page.idx < first_page.idx + count);
                        assert(pre.pages[queue_first_page_id].count.is_some());
                        assert(pre.pages[last_page].count.is_none());
                        assert(false);
                    }
                };

                update pages[queue_first_page_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(first_page),
                        .. pre.pages[queue_first_page_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[queue_first_page_id]
                };
            }

            update popped = if ec { Popped::ExtraCount(segment_id) } else { Popped::No };
            update unused_lists = Self::insert_front(pre.unused_lists, sbin_idx, first_page);
        }
    }

    /*transition!{
        original_free_in_segment_creation() {
            require let Popped::SegmentCreatingSkipped(segment_id, skip_count) = pre.popped;
        }
    }*/

    transition!{
        set_range_to_used(page_header_kind: PageHeaderKind) {
            require let Popped::Ready(page_id, b) = pre.popped;
            assert pre.pages.dom().contains(page_id) by {
                pre.ready_popped_range_facts();
            };
            assert pre.pages[page_id].count.is_some() by {
                pre.ready_popped_range_facts();
            };
            let count = pre.pages[page_id].count.unwrap();
            assert count > 0 by {
                pre.ready_popped_range_facts();
            };
            assert pre.pages[page_id].offset == Some(0nat) by {
                pre.ready_popped_range_facts();
            };
            assert page_id.idx != 0 by {
                pre.ready_popped_range_facts();
            };

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                ) by {
                    pre.ready_popped_range_facts();
                };
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> !pre.pages[pid].is_used
                ) by {
                    pre.ready_popped_range_facts();
                };
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].offset.is_some()
                        && pre.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                ) by {
                    pre.ready_popped_range_facts();
                };

            let changed_pages = Map::new(
                page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count),
                |pid: PageId| PageData {
                    is_used: true,
                    page_header_kind: if pid == page_id { Some(page_header_kind) } else { None },
                    .. pre.pages[pid]
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom() by {
                vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
                assert forall |pid: PageId|
                    changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
                by {
                    assert(pid.segment_id == page_id.segment_id);
                    assert(page_id.idx <= pid.idx < page_id.idx + count);
                };
                assert(changed_pages.dom().subset_of(pre.pages.dom()));
                assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
                assert(pre.pages.dom() =~= new_pages.dom());
            };

            update pages = new_pages;
            update popped = Popped::Used(page_id, b);
        }
    }

    transition!{
        set_range_to_not_used() {
            require let Popped::Used(page_id, b) = pre.popped;
            assert pre.pages.dom().contains(page_id) by {
                pre.used_popped_range_facts();
            };
            assert pre.pages[page_id].count.is_some() by {
                pre.used_popped_range_facts();
            };
            let count = pre.pages[page_id].count.unwrap();
            assert count > 0 by {
                pre.used_popped_range_facts();
            };
            assert pre.pages[page_id].offset == Some(0nat) by {
                pre.used_popped_range_facts();
            };
            assert pre.pages[page_id].full.is_none() by {
                pre.used_popped_range_facts();
            };

            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages.dom().contains(pid)
                ) by {
                    pre.used_popped_range_facts();
                };
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].is_used
                ) by {
                    pre.used_popped_range_facts();
                };
            assert (forall |pid: PageId| pid.segment_id == page_id.segment_id &&
                    page_id.idx <= pid.idx < page_id.idx + count
                    ==> pre.pages[pid].offset.is_some()
                        && pre.pages[pid].offset.unwrap() == pid.idx - page_id.idx
                ) by {
                    pre.used_popped_range_facts();
                };

            let changed_pages = Map::new(
                page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count),
                |pid: PageId| PageData {
                    is_used: false,
                    page_header_kind: None,
                    offset: None,
                    count: None,
                    .. pre.pages[pid]
                }
            );

            let new_pages = pre.pages.union_prefer_right(changed_pages);
            assert pre.pages.dom() =~= new_pages.dom() by {
                vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
                assert forall |pid: PageId|
                    changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
                by {
                    assert(pid.segment_id == page_id.segment_id);
                    assert(page_id.idx <= pid.idx < page_id.idx + count);
                };
                assert(changed_pages.dom().subset_of(pre.pages.dom()));
                assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
                assert(pre.pages.dom() =~= new_pages.dom());
            };

            update pages = new_pages;
            update popped = Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, b);
        }
    }

    transition!{
        into_used_list(bin_idx: int) {
            require valid_bin_idx(bin_idx) || bin_idx == BIN_FULL;
            require let Popped::Used(page_id, tru) = pre.popped;
            require tru == true;

            assert pre.pages.dom().contains(page_id) by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].page_header_kind.is_some() by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            match pre.pages[page_id].page_header_kind.unwrap() {
                PageHeaderKind::Normal(i, bsize) => {
                    require((bin_idx != BIN_FULL ==> bin_idx == i)
                        && valid_bin_idx(i)
                        && bsize == crate::bin_sizes::size_of_bin(i)
                        && i == smallest_bin_fitting_size(bsize)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX);
                }
            }

            update used_dlist_headers[bin_idx] = DlistHeader {
                first: Some(page_id),
                last:
                    if pre.used_dlist_headers[bin_idx].first.is_some() {
                        pre.used_dlist_headers[bin_idx].last
                    } else {
                        Some(page_id)
                    },
            };
            if pre.used_dlist_headers[bin_idx].first.is_some() {
                let first_id = pre.used_dlist_headers[bin_idx].first.unwrap();
                assert pre.pages.dom().contains(first_id) by {
                    reveal(State::ll_basics);
                    pre.first_last_ll_stuff_used(bin_idx);
                };
                assert pre.pages[first_id].is_used by {
                    reveal(State::ll_basics);
                    pre.first_last_ll_stuff_used(bin_idx);
                };
                assert pre.pages[first_id].dlist_entry.is_some()
                    by {
                        reveal(State::ll_basics);
                        pre.first_last_ll_stuff_used(bin_idx);
                    };
                assert first_id != page_id by {
                    reveal(State::inv_used);
                    pre.first_last_ll_stuff_used(bin_idx);
                };
                update pages[first_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        prev: Some(page_id),
                        .. pre.pages[first_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[first_id]
                };
            }

            assert pre.pages.dom().contains(page_id) by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].is_used by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].offset == Some(0nat) by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].dlist_entry.is_none() by {
                reveal(State::inv_used);
            };

            update pages[page_id] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: None,
                    next: pre.used_dlist_headers[bin_idx].first,
                }),
                full: Some(bin_idx == BIN_FULL),
                .. pre.pages[page_id]
            };

            update popped = Popped::No;
            update used_lists = Self::insert_front(pre.used_lists, bin_idx, page_id);
        }
    }

    transition!{
        into_used_list_back(bin_idx: int) {
            require valid_bin_idx(bin_idx) || bin_idx == BIN_FULL;
            require let Popped::Used(page_id, tru) = pre.popped;
            require tru == true;

            assert pre.pages.dom().contains(page_id) by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].page_header_kind.is_some() by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            match pre.pages[page_id].page_header_kind.unwrap() {
                PageHeaderKind::Normal(i, bsize) => {
                    require((bin_idx != BIN_FULL ==> bin_idx == i)
                        && valid_bin_idx(i)
                        && bsize == crate::bin_sizes::size_of_bin(i)
                        && i == smallest_bin_fitting_size(bsize)
                        && bsize <= MEDIUM_OBJ_SIZE_MAX);
                }
            }

            assert pre.used_dlist_headers[bin_idx].last.is_some()
                <==> pre.used_dlist_headers[bin_idx].first.is_some()

                by {
                    reveal(State::ll_basics);
                    pre.first_last_ll_stuff_used(bin_idx);
                };

            update used_dlist_headers[bin_idx] = DlistHeader {
                first:
                    if pre.used_dlist_headers[bin_idx].last.is_some() {
                        pre.used_dlist_headers[bin_idx].first
                    } else {
                        Some(page_id)
                    },
                last: Some(page_id),
            };
            if pre.used_dlist_headers[bin_idx].last.is_some() {
                let last_id = pre.used_dlist_headers[bin_idx].last.unwrap();
                assert pre.pages.dom().contains(last_id)
                    && pre.pages[last_id].is_used
                    && pre.pages[last_id].dlist_entry.is_some()
                    && last_id != page_id

                    by {
                        reveal(State::ll_basics);
                        reveal(State::inv_used);
                        pre.first_last_ll_stuff_used(bin_idx);
                    };

                update pages[last_id] = PageData {
                    dlist_entry: Some(DlistEntry {
                        next: Some(page_id),
                        .. pre.pages[last_id].dlist_entry.unwrap()
                    }),
                    .. pre.pages[last_id]
                };
            }

            assert pre.pages.dom().contains(page_id) by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].is_used by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].offset == Some(0nat) by {
                reveal(State::inv_used);
                reveal(State::good_range_used);
            };
            assert pre.pages[page_id].dlist_entry.is_none() by {
                reveal(State::inv_used);
            };

            update pages[page_id] = PageData {
                dlist_entry: Some(DlistEntry {
                    prev: pre.used_dlist_headers[bin_idx].last,
                    next: None,
                }),
                full: Some(bin_idx == BIN_FULL),
                .. pre.pages[page_id]
            };

            update popped = Popped::No;
            update used_lists = Self::insert_back(pre.used_lists, bin_idx, page_id);
        }
    }

    transition!{
        out_of_used_list(page_id: PageId, bin_idx: int, list_idx: int) {
            require pre.popped == Popped::No;
            require pre.valid_used_page(page_id, bin_idx, list_idx);

            assert pre.pages[page_id].dlist_entry.is_some() by {
                reveal(State::valid_used_page);
            };
            let prev_page_id_opt = pre.pages[page_id].dlist_entry.unwrap().prev;
            let next_page_id_opt = pre.pages[page_id].dlist_entry.unwrap().next;

            assert prev_page_id_opt != Some(page_id)
                && next_page_id_opt != Some(page_id)
                && prev_page_id_opt.is_some() ==> prev_page_id_opt != next_page_id_opt

                by {
                    reveal(State::valid_used_page);
                    reveal(State::ll_basics);
                    pre.used_ll_stuff(bin_idx, list_idx);
                };

            match prev_page_id_opt {
                Option::Some(prev_page_id) => {
                    assert pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used

                      by {
                          reveal(State::valid_used_page);
                          reveal(State::ll_basics);
                          pre.used_ll_stuff(bin_idx, list_idx);
                      };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: next_page_id_opt,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match next_page_id_opt {
                Option::Some(next_page_id) => {
                    assert pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used

                      by {
                          reveal(State::valid_used_page);
                          reveal(State::ll_basics);
                          pre.used_ll_stuff(bin_idx, list_idx);
                      };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: prev_page_id_opt,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            update used_dlist_headers[bin_idx] = DlistHeader {
                first: if prev_page_id_opt.is_some() {
                    pre.used_dlist_headers[bin_idx].first // no change
                } else {
                    next_page_id_opt
                },
                last: if next_page_id_opt.is_some() {
                    pre.used_dlist_headers[bin_idx].last // no change
                } else {
                    prev_page_id_opt
                }
            };

            update pages[page_id] = PageData {
                full: None,
                dlist_entry: None,
                .. pre.pages[page_id]
            };

            update popped = Popped::Used(page_id, true);
            update used_lists[bin_idx] = pre.used_lists[bin_idx].remove(list_idx);
        }
    }

    transition!{
        segment_freeing_start(segment_id: SegmentId) {
            require let Popped::No = pre.popped;
            require pre.segments.dom().contains(segment_id);
            require pre.segments[segment_id].used == 0;

            let page_id = PageId { segment_id, idx: 0 };
            assert pre.pages.dom().contains(page_id) by {
                reveal(State::page_id_domain);
            };
            assert pre.pages[page_id].count.is_some() by {
                reveal(State::end_is_unused);
                reveal(State::popped_ec);
                reveal(State::ec_of_popped);
                assert(pre.popped == Popped::No);
                assert(pre.popped_ec(segment_id) == 0);
                assert(pre.segments[segment_id].used == pre.popped_ec(segment_id));
            };
            let count = pre.pages[page_id].count.unwrap();
            assert 1 <= count <= SLICES_PER_SEGMENT by {
                reveal(State::count_off0);
            };

            let last_id = PageId { segment_id, idx: (count - 1) as nat };

            let new_page_map = Map::<PageId, PageData>::new(
                page_id_range(segment_id, 0, count),
                |page_id: PageId| PageData {
                    dlist_entry: None,
                    count: None,
                    offset: None,
                    is_used: false,
                    full: None,
                    page_header_kind: None,
                }
            );

            update pages = pre.pages.union_prefer_right(new_page_map);

            update popped = Popped::SegmentFreeing(segment_id, count as int);
        }
    }

    transition!{
        segment_freeing_finish() {
            require let Popped::SegmentFreeing(segment_id, idx) = pre.popped;
            require idx == SLICES_PER_SEGMENT;
            assert pre.segments.dom().contains(segment_id) by {
                reveal(State::popped_basics);
            };
            update segments = pre.segments.remove(segment_id);
            update popped = Popped::No;

            let keys = page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1);
            update pages = pre.pages.remove_keys(keys);
        }
    }


    transition!{
        merge_with_after() {
            require let Popped::VeryUnready(segment_id, cur_start, cur_count, b) = pre.popped;

            require cur_start + cur_count < SLICES_PER_SEGMENT;
            let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
            assert pre.pages.dom().contains(page_id) by {
                pre.merge_with_after_page_dom();
            };
            require !pre.pages[page_id].is_used;
            assert pre.pages[page_id].count.is_some()
                by {
                    pre.merge_with_after_page_facts();
                };
            let n_count = pre.pages[page_id].count.unwrap();
            assert cur_count + n_count <= SLICES_PER_SEGMENT
                by {
                    pre.merge_with_after_page_facts();
                };


            assert pre.pages[page_id].dlist_entry.is_some()
                by {
                    pre.merge_with_after_page_facts();
                };

            assert pre.pages[page_id].dlist_entry.is_some() by {
                pre.merge_with_after_page_facts();
            };
            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;

            update pages[page_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[page_id]
            };
            let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
            assert pre.pages.dom().contains(final_id) by {
                pre.merge_with_after_page_facts();
            };
            update pages[final_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[final_id]
            };
            assert !pre.pages[final_id].is_used

                    by {
                        pre.merge_with_after_page_facts();
                    };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                        && pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used == false

                    by {
                        pre.merge_with_after_dlist_facts();
                    };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                        && pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used == false

                    by {
                        pre.merge_with_after_dlist_facts();
                    };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            let sbin_idx = smallest_sbin_fitting_size(n_count as int);
            assert 0 <= sbin_idx <= SEGMENT_BIN_MAX
                by {
                    pre.merge_with_after_page_facts();
                };

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: if dlist_entry.prev.is_none() {
                    dlist_entry.next
                } else {
                    pre.unused_dlist_headers[sbin_idx].first
                },
                last: if dlist_entry.next.is_none() {
                    dlist_entry.prev
                } else {
                    pre.unused_dlist_headers[sbin_idx].last
                }
            };

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by {
                    pre.merge_with_after_dlist_facts();
                };

            update popped = Popped::VeryUnready(segment_id, cur_start, (cur_count + n_count) as int, b);

            let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    transition!{
        merge_with_before() {
            require let Popped::VeryUnready(segment_id, cur_start, cur_count, b) = pre.popped;

            require cur_start > 1;
            let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
            assert pre.pages[last_id].offset.is_some() by {
                pre.merge_with_before_page_dom();
            };
            let offset = pre.pages[last_id].offset.unwrap();
            require last_id.idx - offset > 0; // exclude very first page
            let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
            require !pre.pages[page_id].is_used;
            assert !pre.pages[last_id].is_used by {
                pre.merge_with_before_page_facts();
            };

            assert pre.pages[page_id].count.is_some() by {
                pre.merge_with_before_page_facts();
            };
            let p_count = pre.pages[page_id].count.unwrap();
            assert cur_count + p_count <= SLICES_PER_SEGMENT
                by {
                    pre.merge_with_before_page_facts();
                };

            assert pre.pages[page_id].dlist_entry.is_some()
                by {
                    pre.merge_with_before_page_facts();
                };

            assert pre.pages[page_id].dlist_entry.is_some() by {
                pre.merge_with_before_page_facts();
            };
            assert let Some(dlist_entry) = pre.pages[page_id].dlist_entry;

            update pages[page_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[page_id]
            };
            assert pre.pages.dom().contains(last_id) by {
                pre.merge_with_before_page_facts();
            };
            update pages[last_id] = PageData {
              offset: None,
              count: None,
              dlist_entry: None,
              .. pre.pages[last_id]
            };

            match dlist_entry.prev {
                Some(prev_page_id) => {
                    assert prev_page_id != page_id
                        && pre.pages.dom().contains(prev_page_id)
                        && pre.pages[prev_page_id].dlist_entry.is_some()
                        && pre.pages[prev_page_id].is_used == false
                        && prev_page_id != last_id
                        by {
                            pre.merge_with_before_dlist_facts();
                        };

                    update pages[prev_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            next: dlist_entry.next,
                            .. pre.pages[prev_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[prev_page_id]
                    };
                }
                Option::None => { }
            }

            match dlist_entry.next {
                Some(next_page_id) => {
                    assert next_page_id != page_id
                        && pre.pages.dom().contains(next_page_id)
                        && pre.pages[next_page_id].dlist_entry.is_some()
                        && pre.pages[next_page_id].is_used == false
                        && next_page_id != last_id
                        by {
                            pre.merge_with_before_dlist_facts();
                        };

                    update pages[next_page_id] = PageData {
                        dlist_entry: Some(DlistEntry {
                            prev: dlist_entry.prev,
                            .. pre.pages[next_page_id].dlist_entry.unwrap()
                        }),
                        .. pre.pages[next_page_id]
                    };
                }
                Option::None => { }
            }

            let sbin_idx = smallest_sbin_fitting_size(p_count as int);

            assert 0 <= sbin_idx <= SEGMENT_BIN_MAX
                by {
                    pre.merge_with_before_page_facts();
                };

            update unused_dlist_headers[sbin_idx] = DlistHeader {
                first: if dlist_entry.prev.is_none() {
                    dlist_entry.next
                } else {
                    pre.unused_dlist_headers[sbin_idx].first
                },
                last: if dlist_entry.next.is_none() {
                    dlist_entry.prev
                } else {
                    pre.unused_dlist_headers[sbin_idx].last
                }
            };

            assert dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap()

                by {
                    pre.merge_with_before_dlist_facts();
                };

            update popped = Popped::VeryUnready(segment_id,
                  page_id.idx as int, (cur_count + p_count) as int, b);

            let list_idx = Self::get_list_idx(pre.unused_lists, page_id).1;
            update unused_lists[sbin_idx] = pre.unused_lists[sbin_idx].remove(list_idx);
        }
    }

    pub proof fn take_page_from_unused_queue_page_facts(&self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires
            self.invariant(),
            self.valid_unused_page(page_id, sbin_idx, list_idx),
            match self.popped {
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            },
        ensures ({
            let count = self.pages[page_id].count.unwrap();
            let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
            &&& self.pages.dom().contains(page_id)
            &&& page_id.idx != 0
            &&& self.pages[page_id].is_used == false
            &&& self.pages[page_id].offset == Some(0nat)
            &&& self.pages[page_id].count.is_some()
            &&& 1 <= count <= SLICES_PER_SEGMENT
            &&& self.pages[page_id].dlist_entry.is_some()
            &&& self.good_range_unused(page_id)
            &&& last_id.segment_id == page_id.segment_id
            &&& last_id.idx == page_id.idx + count - 1
            &&& self.pages.dom().contains(last_id)
            &&& self.pages[last_id].is_used == false
            &&& self.pages[last_id].page_header_kind.is_none()
            &&& (last_id != page_id ==> self.pages[last_id].dlist_entry.is_none())
        })
    {
        reveal(State::valid_unused_page);
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);

        assert(0 <= sbin_idx < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[sbin_idx].len());
        assert(self.unused_lists[sbin_idx][list_idx] == page_id);
        assert(self.pages[page_id].offset == Some(0nat));
        assert(is_unused_header(self.pages[page_id]));
        self.lemma_range_not_used(page_id);
        assert(self.good_range_unused(page_id));

        reveal(State::good_range_unused);
        let count = self.pages[page_id].count.unwrap();
        assert(1 <= count <= SLICES_PER_SEGMENT);
        assert(page_id.idx + count <= SLICES_PER_SEGMENT);
        let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
        assert(last_id.segment_id == page_id.segment_id);
        assert(last_id.idx == page_id.idx + count - 1);
        assert(page_id.idx <= last_id.idx);
        assert(last_id.idx < page_id.idx + count);
        assert(self.pages.dom().contains(last_id));
        assert(self.pages[last_id].is_used == false);
        assert(self.pages[last_id].page_header_kind.is_none());
        if last_id != page_id {
            assert(self.pages[last_id].dlist_entry.is_none());
        }
    }

    pub proof fn take_page_from_unused_queue_dlist_facts(&self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires
            self.invariant(),
            self.valid_unused_page(page_id, sbin_idx, list_idx),
            match self.popped {
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            },
        ensures ({
            let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
            &&& (match dlist_entry.prev {
                Some(prev_page_id) =>
                    prev_page_id != page_id
                    && self.pages.dom().contains(prev_page_id)
                    && self.pages[prev_page_id].dlist_entry.is_some()
                    && self.pages[prev_page_id].is_used == false,
                None => true,
            })
            &&& (match dlist_entry.next {
                Some(next_page_id) =>
                    next_page_id != page_id
                    && self.pages.dom().contains(next_page_id)
                    && self.pages[next_page_id].dlist_entry.is_some()
                    && self.pages[next_page_id].is_used == false,
                None => true,
            })
            &&& (dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap())
        })
    {
        self.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
        reveal(State::ll_inv_valid_unused);
        let old_ll = self.unused_lists[sbin_idx];
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(self.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));

        match dlist_entry.prev {
            Some(prev_page_id) => {
                assert(list_idx != 0);
                assert(prev_page_id == old_ll[list_idx - 1]);
                assert(0 <= list_idx - 1 < old_ll.len());
                assert(self.unused_lists[sbin_idx][list_idx - 1] == prev_page_id);
                assert(self.pages.dom().contains(prev_page_id));
                assert(self.pages[prev_page_id].dlist_entry.is_some());
                assert(self.pages[prev_page_id].is_used == false);
                self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx);
                assert(prev_page_id != page_id);
            }
            None => { }
        }

        match dlist_entry.next {
            Some(next_page_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_page_id == old_ll[list_idx + 1]);
                assert(0 <= list_idx + 1 < old_ll.len());
                assert(self.unused_lists[sbin_idx][list_idx + 1] == next_page_id);
                assert(self.pages.dom().contains(next_page_id));
                assert(self.pages[next_page_id].dlist_entry.is_some());
                assert(self.pages[next_page_id].is_used == false);
                self.ll_unused_distinct(sbin_idx, list_idx + 1, sbin_idx, list_idx);
                assert(next_page_id != page_id);
            }
            None => { }
        }

        if dlist_entry.prev.is_some() && dlist_entry.next.is_some() {
            let prev_page_id = dlist_entry.prev.unwrap();
            let next_page_id = dlist_entry.next.unwrap();
            assert(list_idx != 0);
            assert(list_idx != old_ll.len() - 1);
            assert(prev_page_id == old_ll[list_idx - 1]);
            assert(next_page_id == old_ll[list_idx + 1]);
            assert(0 <= list_idx - 1 < old_ll.len());
            assert(0 <= list_idx + 1 < old_ll.len());
            assert(list_idx - 1 != list_idx + 1);
            self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx + 1);
            assert(prev_page_id != next_page_id);
        }
    }

    pub proof fn take_page_from_unused_queue_last_id_not_removed_neighbors(
        &self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires
            self.invariant(),
            self.valid_unused_page(page_id, sbin_idx, list_idx),
            match self.popped {
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            },
        ensures ({
            let count = self.pages[page_id].count.unwrap();
            let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
            let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
            dlist_entry.prev != Some(last_id) && dlist_entry.next != Some(last_id)
        })
    {
        self.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
        self.take_page_from_unused_queue_dlist_facts(page_id, sbin_idx, list_idx);
        reveal(State::ll_inv_valid_unused);
        reveal(State::good_range_unused);

        let count = self.pages[page_id].count.unwrap();
        let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
        let old_ll = self.unused_lists[sbin_idx];
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(self.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));
        assert(last_id.segment_id == page_id.segment_id);
        assert(last_id.idx == page_id.idx + count - 1);

        match dlist_entry.prev {
            Some(prev_id) => {
                assert(list_idx != 0);
                assert(prev_id == old_ll[list_idx - 1]);
                if prev_id == last_id {
                    if count == 1 {
                        assert(last_id == page_id);
                        self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx);
                    } else {
                        assert(count > 1);
                        assert(page_id.idx < last_id.idx);
                        assert(last_id != page_id);
                        assert(self.pages[last_id].dlist_entry.is_none());
                        assert(self.pages[prev_id].dlist_entry.is_some());
                    }
                    assert(false);
                }
            }
            None => { }
        }

        match dlist_entry.next {
            Some(next_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_id == old_ll[list_idx + 1]);
                if next_id == last_id {
                    if count == 1 {
                        assert(last_id == page_id);
                        self.ll_unused_distinct(sbin_idx, list_idx + 1, sbin_idx, list_idx);
                    } else {
                        assert(count > 1);
                        assert(page_id.idx < last_id.idx);
                        assert(last_id != page_id);
                        assert(self.pages[last_id].dlist_entry.is_none());
                        assert(self.pages[next_id].dlist_entry.is_some());
                    }
                    assert(false);
                }
            }
            None => { }
        }
    }

    #[inductive(take_page_from_unused_queue)]
    #[verifier::spinoff_prover]
    fn take_page_from_unused_queue_inductive(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int) {
        reveal(State::inv_very_unready);
        reveal(State::valid_unused_page);
        if pre.popped.is_No() {
            assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
            assert(page_id.idx != 0);
            assert(0 < page_id.idx);
            let count = pre.pages[page_id].count.unwrap();
            assert(0 < count);
            pre.lemma_range_not_used(page_id);
            assert(pre.good_range_unused(page_id));
            assert(page_id.idx + count <= SLICES_PER_SEGMENT) by {
                reveal(State::good_range_unused);
                assert(pre.good_range_unused(page_id));
            }
            assert(post.inv_very_unready());
        } else {
            assert(post.inv_very_unready());
        }
        Self::take_page_from_unused_queue_ll_inv_valid_unused(pre, post, page_id, sbin_idx, list_idx);
        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            assert(pid != page_id);
        }
        Self::unchanged_used_ll(pre, post);
        Self::take_page_from_unused_queue_inductive_attached_ranges(pre, post, page_id, sbin_idx, list_idx);
        Self::ll_inv_exists_take_page_from_unused_queue(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_inductive_unusedinv2(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_count_is_right(pre, post, page_id, sbin_idx, list_idx);
        Self::take_page_from_unused_queue_inv_segment_freeing(pre, post, page_id, sbin_idx, list_idx);
    }

    pub proof fn take_page_from_unused_queue_count_is_right(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires
            pre.invariant(),
            State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures
            post.count_is_right(),
    {
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_dlist_facts(page_id, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_last_id_not_removed_neighbors(page_id, sbin_idx, list_idx);
        let count = pre.pages[page_id].count.unwrap();
        let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            if pid == page_id {
                assert(pre.pages[page_id].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else if pid == last_id {
                assert(pre.pages[last_id].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else {
                match dlist_entry.prev {
                    Some(prev_id) => {
                        if pid == prev_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                match dlist_entry.next {
                    Some(next_id) => {
                        if pid == next_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        }

        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            assert(post.segments == pre.segments);
            match pre.popped {
                Popped::No => {
                    assert(post.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, false));
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == 0);
                }
                Popped::SegmentFreeing(seg_id, idx) => {
                    assert(post.popped == Popped::SegmentFreeing(seg_id, idx + count));
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == 0);
                }
                _ => {
                    assert(false);
                }
            }
        }

        Self::count_is_right_preserve_all(pre, post);
    }

    pub proof fn take_page_from_unused_queue_ll_inv_valid_unused(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
        requires pre.invariant(),
            State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures
            post.ll_inv_valid_unused()
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);
        let old_ll = pre.unused_lists[sbin_idx];
        let new_ll = old_ll.remove(list_idx);
        old_ll.remove_ensures(list_idx);
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        assert(old_ll[list_idx] == page_id);
        assert(pre.pages[page_id].dlist_entry.is_some());
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(pre.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));
        assert(pre.pages[page_id].offset == Some(0nat)) by {
            reveal(State::valid_unused_page);
            assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        }
        assert(!pre.pages[page_id].is_used) by {
            reveal(State::valid_unused_page);
            assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        }
        assert(is_unused_header(pre.pages[page_id]));
        pre.lemma_range_not_used(page_id);
        assert(pre.good_range_unused(page_id));
        let count = pre.pages[page_id].count.unwrap();
        assert(page_id.idx + count <= SLICES_PER_SEGMENT) by {
            reveal(State::good_range_unused);
            assert(pre.good_range_unused(page_id));
        }
        let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
        assert(post.unused_lists =~= pre.unused_lists.update(sbin_idx, new_ll));

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            if i == sbin_idx {
                assert(post.unused_lists[i] == new_ll);
                if new_ll.len() == 0 {
                    assert(old_ll.len() == 1);
                    assert(list_idx == 0);
                    assert(dlist_entry.prev.is_none());
                    assert(dlist_entry.next.is_none());
                    assert(post.unused_dlist_headers[i].first.is_none());
                    assert(post.unused_dlist_headers[i].last.is_none());
                } else {
                    if list_idx == 0 {
                        assert(dlist_entry.prev.is_none());
                        assert(dlist_entry.next == Some(old_ll[1]));
                        assert(new_ll[0] == old_ll[1]);
                        assert(post.unused_dlist_headers[i].first == Some(new_ll[0]));
                    } else {
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[0] == old_ll[0]);
                        assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                        assert(post.unused_dlist_headers[i].first == Some(new_ll[0]));
                    }
                    if list_idx == old_ll.len() - 1 {
                        assert(dlist_entry.next.is_none());
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[list_idx - 1]);
                        assert(post.unused_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    } else {
                        assert(dlist_entry.next == Some(old_ll[list_idx + 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                        assert(pre.unused_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                        assert(post.unused_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    }
                }
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let old_j = if j < list_idx { j } else { j + 1 };
                    assert(0 <= old_j < old_ll.len());
                    assert(old_j != list_idx);
                    assert(post.unused_lists[i][j] == old_ll[old_j]);
                    let pid = post.unused_lists[i][j];
                    pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                    assert(pid != page_id);
                    assert(valid_ll_i(pre.pages, old_ll, old_j));
                    if old_j == list_idx - 1 {
                        assert(j == list_idx - 1);
                        assert(dlist_entry.prev == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().next == dlist_entry.next);
                    } else if old_j == list_idx + 1 {
                        assert(j == list_idx);
                        assert(dlist_entry.next == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().prev == dlist_entry.prev);
                    } else {
                        if dlist_entry.prev.is_some() {
                            let prev_id = dlist_entry.prev.unwrap();
                            assert(list_idx > 0);
                            assert(prev_id == old_ll[list_idx - 1]);
                            assert(pid != prev_id) by {
                                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx - 1);
                            }
                        }
                        if dlist_entry.next.is_some() {
                            let next_id = dlist_entry.next.unwrap();
                            assert(list_idx < old_ll.len() - 1);
                            assert(next_id == old_ll[list_idx + 1]);
                            assert(pid != next_id) by {
                                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx + 1);
                            }
                        }
                        assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                    }
                }
            } else {
                assert(post.unused_lists[i] == pre.unused_lists[i]);
                assert(post.unused_dlist_headers[i] == pre.unused_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let pid = post.unused_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                    pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                    assert(pid != page_id);
                    if dlist_entry.prev.is_some() {
                        let prev_id = dlist_entry.prev.unwrap();
                        assert(list_idx > 0);
                        assert(prev_id == old_ll[list_idx - 1]);
                        assert(pid != prev_id) by {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx - 1);
                        }
                    }
                    if dlist_entry.next.is_some() {
                        let next_id = dlist_entry.next.unwrap();
                        assert(list_idx < old_ll.len() - 1);
                        assert(next_id == old_ll[list_idx + 1]);
                        assert(pid != next_id) by {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx + 1);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                }
            }
        }

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists.index(i).index(j) == post.unused_lists.index(i).index(j)
        implies
            ({
                let pid = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(pid)
                &&& pid.idx != 0
                &&& post.pages[pid].is_used == false
                &&& (match post.pages[pid].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[pid].offset == Some(0nat)
                &&& post.pages[pid].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == pid
                &&& post.valid_unused_page(post.unused_lists[i][j], i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[pid].count.unwrap() as int)
            })
        by {
            let pid = post.unused_lists[i][j];
            if i == sbin_idx {
                let old_j = if j < list_idx { j } else { j + 1 };
                assert(0 <= old_j < old_ll.len());
                assert(old_j != list_idx);
                assert(pid == old_ll[old_j]);
                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
            } else {
                assert(pid == pre.unused_lists[i][j]);
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
            }
            assert(pid != page_id);
            if pid == last_id {
                assert(count > 1);
                assert(pre.pages[last_id].offset == Some((count - 1) as nat));
                assert(pre.pages[pid].offset == Some(0nat));
                assert(false);
            }
            assert(pre.valid_unused_page(pid, i, if i == sbin_idx {
                if j < list_idx { j } else { j + 1 }
            } else {
                j
            }));
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
            assert(post.pages[pid].dlist_entry.is_some());
        }
        assert(post.ll_inv_valid_unused());
    }

    pub proof fn attached_rec_at_unused_page(&self, pid: PageId, idx: int)
      requires
          self.invariant(),
          self.popped.is_No(),
          self.attached_rec(pid.segment_id, idx, false),
          self.good_range_unused(pid),
          idx >= 0,
          idx <= pid.idx,
      ensures
          self.attached_rec(pid.segment_id, pid.idx as int, false),
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        if idx == pid.idx {
        } else {
            assert(idx < pid.idx);
            if idx == SLICES_PER_SEGMENT {
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!self.attached_rec(pid.segment_id, idx, false));
                assert(false);
            } else {
                let cur = PageId { segment_id: pid.segment_id, idx: idx as nat };
                assert(cur.idx == idx);
                let count = self.pages[cur].count.unwrap();
                assert(count > 0);
                assert(idx + count <= SLICES_PER_SEGMENT);
                assert(self.attached_rec(pid.segment_id, idx + count, false));

                if idx + count > pid.idx {
                    assert(cur.segment_id == pid.segment_id);
                    assert(cur.idx <= pid.idx);
                    assert(pid.idx < cur.idx + count);
                    if self.pages[cur].is_used {
                        assert(self.good_range_used(cur));
                        assert(self.pages[pid].is_used == true);
                    } else {
                        assert(self.good_range_unused(cur));
                        assert(self.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
                        assert(self.pages[pid].offset == Some(0nat));
                        assert(pid.idx - cur.idx > 0);
                    }
                    assert(false);
                }
                assert(idx + count <= pid.idx);
                self.attached_rec_at_unused_page(pid, idx + count);
            }
        }
    }

    pub proof fn take_page_from_unused_queue_preserves_good_range_unused(
        pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, cur: PageId
    )
      requires
          pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.valid_unused_page(pid, sbin_idx, list_idx),
          pre.good_range_unused(cur),
          cur.segment_id == pid.segment_id,
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              let removed_count = pre.pages[pid].count.unwrap();
              cur.idx + cur_count <= pid.idx || pid.idx + removed_count <= cur.idx
          }),
      ensures
          post.good_range_unused(cur),
          post.pages[cur].count == pre.pages[cur].count,
          post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        reveal(State::good_range_unused);
        pre.take_page_from_unused_queue_page_facts(pid, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_dlist_facts(pid, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_last_id_not_removed_neighbors(pid, sbin_idx, list_idx);

        let cur_count = pre.pages[cur].count.unwrap();
        let removed_count = pre.pages[pid].count.unwrap();
        let last_id = PageId { idx: (pid.idx + removed_count - 1) as nat, ..pid };
        let removed_entry = pre.pages[pid].dlist_entry.unwrap();

        assert(cur_count > 0);
        assert(removed_count > 0);
        assert(post.pages.dom().contains(cur));
        assert(cur != pid);
        assert(cur != last_id);
        assert(post.pages[cur].count == pre.pages[cur].count);
        assert(post.pages[cur].is_used == pre.pages[cur].is_used);
        assert(post.pages[cur].offset == pre.pages[cur].offset);
        assert(post.pages[cur].full == pre.pages[cur].full);
        assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);
        assert(post.pages[cur].offset == Some(0nat));

        assert forall |q: PageId|
            #![trigger post.pages.dom().contains(q)]
            #![trigger post.pages.index(q)]
            q.segment_id == cur.segment_id
            && cur.idx <= q.idx < cur.idx + cur_count
        implies
            post.pages.dom().contains(q)
            && post.pages[q].is_used == false
            && post.pages[q].full.is_none()
            && post.pages[q].page_header_kind.is_none()
            && (post.pages[q].count.is_some() <==> q == cur)
            && (post.pages[q].dlist_entry.is_some() <==> q == cur)
            && post.pages[q].offset == (if q == cur || q == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                    Some((q.idx - cur.idx) as nat)
                } else {
                    None
                })
        by {
            assert(pre.pages.dom().contains(q));
            assert(pre.pages[q].is_used == false);
            assert(pre.pages[q].full.is_none());
            assert(pre.pages[q].page_header_kind.is_none());
            assert(pre.pages[q].count.is_some() <==> q == cur);
            assert(pre.pages[q].dlist_entry.is_some() <==> q == cur);
            assert(pre.pages[q].offset == (if q == cur || q == (PageId { segment_id: cur.segment_id, idx: (cur.idx + pre.pages[cur].count.unwrap() - 1) as nat }) {
                    Some((q.idx - cur.idx) as nat)
                } else {
                    None
                }));

            assert(q != pid);
            assert(q != last_id);
            match removed_entry.prev {
                Some(prev_id) => {
                    if q == prev_id {
                        assert(pre.pages[q].dlist_entry.is_some());
                        assert(q == cur);
                    }
                }
                None => { }
            }
            match removed_entry.next {
                Some(next_id) => {
                    if q == next_id {
                        assert(pre.pages[q].dlist_entry.is_some());
                        assert(q == cur);
                    }
                }
                None => { }
            }
            assert(post.pages[q].count == pre.pages[q].count);
            assert(post.pages[q].is_used == pre.pages[q].is_used);
            assert(post.pages[q].full == pre.pages[q].full);
            assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
            assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
        };
        assert(post.good_range_unused(cur));
    }

    pub proof fn take_page_from_unused_queue_preserves_good_range_used(
        pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, cur: PageId
    )
      requires
          pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.valid_unused_page(pid, sbin_idx, list_idx),
          pre.good_range_used(cur),
          cur.segment_id == pid.segment_id,
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              let removed_count = pre.pages[pid].count.unwrap();
              cur.idx + cur_count <= pid.idx || pid.idx + removed_count <= cur.idx
          }),
      ensures
          post.good_range_used(cur),
          post.pages[cur].count == pre.pages[cur].count,
          post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        reveal(State::good_range_used);
        pre.take_page_from_unused_queue_page_facts(pid, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_dlist_facts(pid, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_last_id_not_removed_neighbors(pid, sbin_idx, list_idx);

        let cur_count = pre.pages[cur].count.unwrap();
        let removed_count = pre.pages[pid].count.unwrap();
        let last_id = PageId { idx: (pid.idx + removed_count - 1) as nat, ..pid };
        let removed_entry = pre.pages[pid].dlist_entry.unwrap();

        assert(cur_count > 0);
        assert(removed_count > 0);
        assert(post.pages.dom().contains(cur));
        assert(cur != pid);
        assert(cur != last_id);
        assert(post.pages[cur].count == pre.pages[cur].count);
        assert(post.pages[cur].is_used == pre.pages[cur].is_used);
        assert(post.pages[cur].offset == pre.pages[cur].offset);
        assert(post.pages[cur].full == pre.pages[cur].full);
        assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);
        assert(post.pages[cur].dlist_entry.is_some() == pre.pages[cur].dlist_entry.is_some());
        assert(post.pages[cur].offset == Some(0nat));

        assert forall |q: PageId|
            #![trigger post.pages.dom().contains(q)]
            #![trigger post.pages.index(q)]
            q.segment_id == cur.segment_id
            && cur.idx <= q.idx < cur.idx + cur_count
        implies
            post.pages.dom().contains(q)
            && post.pages[q].is_used == true
            && post.pages[q].offset == Some((q.idx - cur.idx) as nat)
            && (post.pages[q].page_header_kind.is_some() <==> q == cur)
            && (q != cur ==> post.pages[q].dlist_entry.is_none())
            && (q != cur ==> post.pages[q].full.is_none())
        by {
            assert(pre.pages.dom().contains(q));
            assert(pre.pages[q].is_used == true);
            assert(pre.pages[q].offset == Some((q.idx - cur.idx) as nat));
            assert(pre.pages[q].page_header_kind.is_some() <==> q == cur);
            assert(q != cur ==> pre.pages[q].dlist_entry.is_none());
            assert(q != cur ==> pre.pages[q].full.is_none());

            assert(q != pid);
            assert(q != last_id);
            match removed_entry.prev {
                Some(prev_id) => {
                    if q == prev_id {
                        assert(pre.pages[q].is_used == false);
                        assert(false);
                    }
                }
                None => { }
            }
            match removed_entry.next {
                Some(next_id) => {
                    if q == next_id {
                        assert(pre.pages[q].is_used == false);
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages[q] == pre.pages[q]);
        };
        assert(post.good_range_used(cur));
    }

    pub proof fn take_page_from_unused_queue_inductive_attached_ranges(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures post.attached_ranges()
    {
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::popped_ranges_match);
        reveal(State::is_any_the_popped);
        reveal(State::page_id_of_popped);
        reveal(State::popped_len);

        if pre.popped.is_No() {
            pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
            let count = pre.pages[page_id].count.unwrap();
            assert(count > 0);
            assert(post.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, false));

            assert(Self::popped_ranges_match(pre, pre));
            assert(!pre.popped.is_SegmentFreeing());
            assert(!pre.popped.is_SegmentCreating());
            assert(pre.segments.dom() =~= pre.segments.dom());
            assert forall |pid: PageId|
                #![trigger pre.pages.dom().contains(pid)]
                #![trigger pre.pages[pid]]
                (pre.pages.dom().contains(pid) <==> pre.pages.dom().contains(pid))
                && (pre.pages.dom().contains(pid) && !pre.in_popped_range(pid) ==> {
                    &&& pre.pages.dom().contains(pid)
                    &&& pre.pages[pid].count == pre.pages[pid].count
                    &&& pre.pages[pid].dlist_entry.is_some() <==> pre.pages[pid].dlist_entry.is_some()
                    &&& pre.pages[pid].offset == pre.pages[pid].offset
                    &&& pre.pages[pid].is_used == pre.pages[pid].is_used
                    &&& pre.pages[pid].full == pre.pages[pid].full
                    &&& pre.pages[pid].page_header_kind == pre.pages[pid].page_header_kind
                })
            by { };
            Self::attached_ranges_all(pre, pre);
            assert(pre.segments.dom().contains(page_id.segment_id));
            assert(pre.attached_ranges_segment(page_id.segment_id));
            assert(pre.attached_rec0(page_id.segment_id, false));
            let first_id = PageId { segment_id: page_id.segment_id, idx: 0 };
            let first_count = pre.pages[first_id].count.unwrap();
            assert(pre.attached_rec(page_id.segment_id, first_count as int, false));
            assert(first_count <= page_id.idx) by {
                reveal(State::good_range0);
                if first_count > page_id.idx {
                    assert(pre.pages[page_id].offset == Some((page_id.idx - first_id.idx) as nat));
                    assert(pre.pages[page_id].offset == Some(0nat));
                    assert(page_id.idx != 0);
                    assert(false);
                }
            };
            pre.attached_rec_at_unused_page(page_id, first_count as int);
            Self::rec_take_page_from_unused_queue_prefix(pre, post, page_id, sbin_idx, list_idx, first_count as int);
            assert(post.attached_rec(page_id.segment_id, first_count as int, true));
            let removed_entry = pre.pages[page_id].dlist_entry.unwrap();
            let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
            assert forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                ({
                    let first_count = pre.pages[first_id].count.unwrap();
                    pid.segment_id == page_id.segment_id
                    && first_id.idx <= pid.idx < first_id.idx + first_count
                })
            implies
                post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
            by {
                if pid == page_id || pid == last_id {
                    assert(page_id.idx <= pid.idx);
                    assert(pid.idx < first_count);
                    assert(false);
                }
                match removed_entry.prev {
                    Some(prev_id) => {
                        if pid == prev_id {
                            assert(pre.pages[pid].dlist_entry.is_some());
                            assert(pre.good_range0(page_id.segment_id));
                            reveal(State::good_range0);
                            assert(pre.pages[pid].dlist_entry.is_none());
                            assert(false);
                        }
                    }
                    None => { }
                }
                match removed_entry.next {
                    Some(next_id) => {
                        if pid == next_id {
                            assert(pre.pages[pid].dlist_entry.is_some());
                            assert(pre.good_range0(page_id.segment_id));
                            reveal(State::good_range0);
                            assert(pre.pages[pid].dlist_entry.is_none());
                            assert(false);
                        }
                    }
                    None => { }
                }
                assert(post.pages.dom().contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            };
            Self::good_range0_same(pre, post, page_id.segment_id);
            assert(post.attached_rec0(page_id.segment_id, true));
            assert(post.attached_ranges_segment(page_id.segment_id));
            Self::attached_ranges_except(pre, post, page_id.segment_id);
            assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
                if sid == page_id.segment_id {
                    assert(post.attached_ranges_segment(sid));
                } else {
                    assert(post.attached_ranges_segment(sid));
                }
            };
            Self::attached_ranges_from_segments(post);
            assert(post.attached_ranges());
        } else {
            assert(pre.popped == Popped::SegmentFreeing(page_id.segment_id, page_id.idx as int));
            let count = pre.pages[page_id].count.unwrap();
            assert(post.popped == Popped::SegmentFreeing(page_id.segment_id, (page_id.idx + count) as int));
            Self::take_page_from_unused_queue_inv_segment_freeing(pre, post, page_id, sbin_idx, list_idx);
            assert(post.inv_segment_freeing());
            reveal(State::attached_ranges_segment);
            reveal(State::inv_segment_freeing);
            assert(0 < page_id.idx + count);
            reveal(State::attached_rec);
            if page_id.idx + count < SLICES_PER_SEGMENT {
                assert(post.attached_rec(page_id.segment_id, (page_id.idx + count) as int, false));
            } else {
                assert(page_id.idx + count == SLICES_PER_SEGMENT);
                assert(post.attached_rec(page_id.segment_id, (page_id.idx + count) as int, false));
            }
            assert(post.attached_ranges_segment(page_id.segment_id));
            Self::attached_ranges_except(pre, post, page_id.segment_id);
            assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
                if sid == page_id.segment_id {
                    assert(post.attached_ranges_segment(sid));
                } else {
                    assert(post.attached_ranges_segment(sid));
                }
            };
            Self::attached_ranges_from_segments(post);
            assert(post.attached_ranges());
        }
    }

    pub proof fn take_page_from_unused_queue_inductive_unusedinv2(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
          post.ll_inv_exists_in_some_list(),
        ensures post.ll_inv_valid_unused2()
    {
        reveal(State::ll_inv_valid_unused2);
    }

    pub proof fn ll_inv_exists_take_page_from_unused_queue(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          pre.invariant(),
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          //post.expect_out_of_lists(page_id),
          State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_basics);
        pre.unused_lists[sbin_idx].remove_ensures(list_idx);
        Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
        assert(post.unused_lists =~= pre.unused_lists.update(sbin_idx, pre.unused_lists[sbin_idx].remove(list_idx)));
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(pid != page_id);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].offset == Some(0nat));
            assert(!pre.pages[pid].is_used);
            assert(pre.pages[pid].count == post.pages[pid].count);
            assert(is_in_lls(pid, pre.unused_lists));
            Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
            assert(is_in_lls(pid, post.unused_lists));
        }
        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            if i == sbin_idx {
                let old_j = if j < list_idx { j } else { j + 1 };
                assert(0 <= old_j < pre.unused_lists[sbin_idx].len());
                assert(post.unused_lists[i][j] == pre.unused_lists[sbin_idx][old_j]);
                if old_j != list_idx {
                    pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                }
                let pid = post.unused_lists[i][j];
                assert(pid != page_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
            } else {
                assert(post.unused_lists[i][j] == pre.unused_lists[i][j]);
                let pid = post.unused_lists[i][j];
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(pid != page_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
            }
        }
    }

    pub proof fn take_page_from_unused_queue_inv_segment_freeing(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires
            pre.invariant(),
            State::take_page_from_unused_queue_strong(pre, post, page_id, sbin_idx, list_idx),
        ensures
            post.inv_segment_freeing(),
    {
        reveal(State::inv_segment_freeing);
        reveal(State::seg_free_prefix);
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        pre.take_page_from_unused_queue_page_facts(page_id, sbin_idx, list_idx);
        pre.take_page_from_unused_queue_dlist_facts(page_id, sbin_idx, list_idx);
        let count = pre.pages[page_id].count.unwrap();
        let last_id = PageId { idx: (page_id.idx + count - 1) as nat, ..page_id };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        match pre.popped {
            Popped::No => {
                assert(post.popped.is_VeryUnready());
                assert(post.inv_segment_freeing());
            }
            Popped::SegmentFreeing(segment_id, idx) => {
                assert(pre.inv_segment_freeing());
                assert(pre.segments.dom().contains(segment_id));
                assert(pre.segments[segment_id].used == 0);
                assert(0 < idx <= SLICES_PER_SEGMENT);
                assert(page_id.segment_id == segment_id);
                assert(page_id.idx == idx);
                assert(1 <= count);
                assert(page_id.idx + count <= SLICES_PER_SEGMENT);
                assert(idx + count <= SLICES_PER_SEGMENT);
                assert(post.popped == Popped::SegmentFreeing(segment_id, idx + count));
                assert(post.segments == pre.segments);
                assert(post.segments.dom().contains(segment_id));
                assert(post.segments[segment_id].used == 0);
                assert(0 < idx + count <= SLICES_PER_SEGMENT);
                assert forall |pid: PageId|
                    #![trigger post.pages.dom().contains(pid)]
                    #![trigger post.pages.index(pid)]
                    pid.segment_id == segment_id
                    && 0 <= pid.idx < idx + count
                implies
                    post.pages.dom().contains(pid)
                    && post.pages[pid].dlist_entry.is_none()
                    && post.pages[pid].count.is_none()
                    && post.pages[pid].offset.is_none()
                    && post.pages[pid].is_used == false
                    && post.pages[pid].full.is_none()
                    && post.pages[pid].page_header_kind.is_none()
                by {
                    assert(pid.segment_id == page_id.segment_id);
                    if pid.idx < idx {
                        assert(pre.seg_free_prefix(segment_id, idx));
                        assert(pre.pages.dom().contains(pid));
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(pre.pages[pid].count.is_none());
                        assert(pre.pages[pid].offset.is_none());
                        assert(pre.pages[pid].is_used == false);
                        assert(pre.pages[pid].full.is_none());
                        assert(pre.pages[pid].page_header_kind.is_none());
                        assert(pid != page_id);
                        assert(pid != last_id);
                        match dlist_entry.prev {
                            Some(prev_id) => {
                                if pid == prev_id {
                                    assert(pre.pages[pid].dlist_entry.is_some());
                                    assert(false);
                                }
                            }
                            None => { }
                        }
                        match dlist_entry.next {
                            Some(next_id) => {
                                if pid == next_id {
                                    assert(pre.pages[pid].dlist_entry.is_some());
                                    assert(false);
                                }
                            }
                            None => { }
                        }
                        assert(post.pages[pid] == pre.pages[pid]);
                    } else {
                        assert(idx <= pid.idx < idx + count);
                        assert(page_id.idx == idx);
                        assert(page_id.idx <= pid.idx < page_id.idx + count);
                        assert(pre.good_range_unused(page_id));
                        reveal(State::good_range_unused);
                        assert(pre.pages.dom().contains(pid));
                        assert(pre.pages[pid].is_used == false);
                        assert(pre.pages[pid].full.is_none());
                        assert(pre.pages[pid].page_header_kind.is_none());
                        assert(pre.pages[pid].count.is_some() <==> pid == page_id);
                        assert(pre.pages[pid].dlist_entry.is_some() <==> pid == page_id);
                        if pid == page_id {
                            assert(post.pages[pid].dlist_entry.is_none());
                            assert(post.pages[pid].count.is_none());
                            assert(post.pages[pid].offset.is_none());
                        } else if pid == last_id {
                            assert(post.pages[pid].offset.is_none());
                            assert(post.pages[pid].count.is_none());
                            assert(post.pages[pid].dlist_entry.is_none());
                        } else {
                            match dlist_entry.prev {
                                Some(prev_id) => {
                                    if pid == prev_id {
                                        assert(pre.pages[pid].dlist_entry.is_some());
                                        assert(pid != page_id);
                                        assert(false);
                                    }
                                }
                                None => { }
                            }
                            match dlist_entry.next {
                                Some(next_id) => {
                                    if pid == next_id {
                                        assert(pre.pages[pid].dlist_entry.is_some());
                                        assert(pid != page_id);
                                        assert(false);
                                    }
                                }
                                None => { }
                            }
                            assert(post.pages[pid] == pre.pages[pid]);
                        }
                    }
                };
                assert(post.seg_free_prefix(segment_id, idx + count));
                if idx + count < SLICES_PER_SEGMENT {
                    assert(idx < SLICES_PER_SEGMENT);
                    assert(pre.attached_rec(segment_id, idx, false));
                    assert(!Self::is_the_popped(segment_id, idx, pre.popped));
                    assert(!pre.pages[page_id].is_used);
                    assert(pre.good_range_unused(page_id));
                    assert(pre.attached_rec(segment_id, idx + count, false));
                    Self::rec_take_page_from_unused_queue_segment_freeing(
                        pre, post, page_id, sbin_idx, list_idx, idx + count);
                    assert(post.attached_rec(segment_id, idx + count, false));
                }
                assert(post.inv_segment_freeing());
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn rec_take_page_from_unused_queue_segment_freeing(
        pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, idx: int
    )
      requires
          pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.popped == Popped::SegmentFreeing(pid.segment_id, pid.idx as int),
          pre.attached_rec(pid.segment_id, idx, false),
          idx >= pid.idx + pre.pages[pid].count.unwrap(),
          idx >= 0,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, false)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        pre.take_page_from_unused_queue_page_facts(pid, sbin_idx, list_idx);
        let removed_count = pre.pages[pid].count.unwrap();
        let last_id = PageId { idx: (pid.idx + removed_count - 1) as nat, ..pid };
        assert(removed_count > 0);
        assert(post.popped == Popped::SegmentFreeing(pid.segment_id, (pid.idx + removed_count) as int));

        if idx == SLICES_PER_SEGMENT {
            assert(post.attached_rec(pid.segment_id, idx, false));
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(pid.segment_id, idx, false));
            assert(false);
        } else {
            let cur = PageId { segment_id: pid.segment_id, idx: idx as nat };
            assert(cur.idx == idx);
            let count = pre.pages[cur].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(pid.segment_id, idx + count, false));
            assert(pid.idx + removed_count <= idx);
            assert(cur != pid);
            assert(cur != last_id) by {
                if cur == last_id {
                    assert(last_id.idx == pid.idx + removed_count - 1);
                    assert(idx == pid.idx + removed_count - 1);
                    assert(pid.idx + removed_count <= idx);
                    assert(false);
                }
            };

            if pre.pages[cur].is_used {
                assert(pre.good_range_used(cur));
                Self::take_page_from_unused_queue_preserves_good_range_used(
                    pre, post, pid, sbin_idx, list_idx, cur);
                assert(post.pages[cur].is_used);
                assert(post.good_range_used(cur));
            } else {
                assert(pre.good_range_unused(cur));
                Self::take_page_from_unused_queue_preserves_good_range_unused(
                    pre, post, pid, sbin_idx, list_idx, cur);
                assert(!post.pages[cur].is_used);
                assert(post.good_range_unused(cur));
            }
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].count.unwrap() == count);
            Self::rec_take_page_from_unused_queue_segment_freeing(
                pre, post, pid, sbin_idx, list_idx, idx + count);
            assert(!Self::is_the_popped(pid.segment_id, idx, post.popped));
            assert(post.attached_rec(pid.segment_id, idx + count, false));
            assert(post.attached_rec(pid.segment_id, idx, false));
        }
    }

    pub proof fn rec_take_page_from_unused_queue_prefix(pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, idx: int)
      requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.attached_rec(pid.segment_id, idx, false),
          pre.popped.is_No(),
          idx >= 0,
          idx <= pid.idx,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, true)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        pre.take_page_from_unused_queue_page_facts(pid, sbin_idx, list_idx);
        let removed_count = pre.pages[pid].count.unwrap();
        if idx == pid.idx {
            Self::rec_take_page_from_unused_queue(pre, post, pid, sbin_idx, list_idx, idx);
            assert(post.attached_rec(pid.segment_id, idx, true));
        } else {
            assert(idx < pid.idx);
            if idx == SLICES_PER_SEGMENT {
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!pre.attached_rec(pid.segment_id, idx, false));
                assert(false);
            } else {
                let cur = PageId { segment_id: pid.segment_id, idx: idx as nat };
                let count = pre.pages[cur].count.unwrap();
                assert(count > 0);
                assert(idx + count <= SLICES_PER_SEGMENT);
                assert(pre.attached_rec(pid.segment_id, idx + count, false));
                if idx + count > pid.idx {
                    assert(cur.segment_id == pid.segment_id);
                    assert(cur.idx <= pid.idx < cur.idx + count);
                    if pre.pages[cur].is_used {
                        assert(pre.good_range_used(cur));
                        assert(pre.pages[pid].is_used == true);
                        assert(pre.pages[pid].is_used == false);
                        assert(false);
                    } else {
                        assert(pre.good_range_unused(cur));
                        let last_id = PageId { segment_id: cur.segment_id, idx: (cur.idx + count - 1) as nat };
                        if pid == last_id {
                            assert(pid.idx - cur.idx > 0);
                            assert(pre.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
                            assert(pre.pages[pid].offset == Some(0nat));
                            assert(false);
                        } else {
                            assert(pre.pages[pid].offset.is_none());
                            assert(pre.pages[pid].offset == Some(0nat));
                            assert(false);
                        }
                    }
                }
                assert(idx + count <= pid.idx);
                if pre.pages[cur].is_used {
                    assert(pre.good_range_used(cur));
                    Self::take_page_from_unused_queue_preserves_good_range_used(pre, post, pid, sbin_idx, list_idx, cur);
                    assert(post.good_range_used(cur));
                    assert(post.pages[cur].is_used);
                } else {
                    assert(pre.good_range_unused(cur));
                    Self::take_page_from_unused_queue_preserves_good_range_unused(pre, post, pid, sbin_idx, list_idx, cur);
                    assert(post.good_range_unused(cur));
                    assert(!post.pages[cur].is_used);
                }
                assert(post.pages[cur].count == pre.pages[cur].count);
                assert(post.pages[cur].count.unwrap() == count);
                Self::rec_take_page_from_unused_queue_prefix(pre, post, pid, sbin_idx, list_idx, idx + count);
                assert(!Self::is_the_popped(pid.segment_id, idx, post.popped));
                assert(post.attached_rec(pid.segment_id, idx + count, true));
                assert(post.attached_rec(pid.segment_id, idx, true));
            }
        }
    }

    pub proof fn rec_take_page_from_unused_queue(pre: Self, post: Self, pid: PageId, sbin_idx: int, list_idx: int, idx: int)
      requires pre.invariant(),
          State::take_page_from_unused_queue_strong(pre, post, pid, sbin_idx, list_idx),
          pre.attached_rec(pid.segment_id, idx, false),
          pre.popped.is_No(),
          idx >= 0,
          idx >= pid.idx,
          pid.idx < SLICES_PER_SEGMENT,
      ensures
          post.attached_rec(pid.segment_id, idx, idx <= pid.idx)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        pre.take_page_from_unused_queue_page_facts(pid, sbin_idx, list_idx);
        let removed_count = pre.pages[pid].count.unwrap();
        let last_id = PageId { idx: (pid.idx + removed_count - 1) as nat, ..pid };
        assert(removed_count > 0);
        assert(post.popped == Popped::VeryUnready(pid.segment_id, pid.idx as int, removed_count as int, false));

        if idx == SLICES_PER_SEGMENT {
            assert(!(idx <= pid.idx));
            assert(post.attached_rec(pid.segment_id, idx, false));
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(pid.segment_id, idx, false));
            assert(false);
        } else {
            let cur = PageId { segment_id: pid.segment_id, idx: idx as nat };
            assert(cur.idx == idx);
            let count = pre.pages[cur].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(pid.segment_id, idx + count, false));

            if idx == pid.idx {
                assert(cur == pid);
                assert(count == removed_count);
                assert(idx + removed_count > pid.idx);
                Self::rec_take_page_from_unused_queue(pre, post, pid, sbin_idx, list_idx, idx + removed_count);
                assert(post.attached_rec(pid.segment_id, idx + removed_count, false));
                assert(Self::is_the_popped(pid.segment_id, idx, post.popped));
                assert(post.popped_len() == removed_count);
                assert(post.attached_rec(pid.segment_id, idx, true));
            } else {
                assert(idx > pid.idx);
                if idx < pid.idx + removed_count {
                    assert(pid.segment_id == cur.segment_id);
                    assert(pid.idx <= cur.idx);
                    assert(cur.idx < pid.idx + removed_count);
                    assert(pre.pages[cur].is_used == false);
                    assert(pre.pages[cur].count.is_some() <==> cur == pid);
                    if pre.pages[cur].is_used {
                        assert(false);
                    } else {
                        assert(pre.good_range_unused(cur));
                        assert(pre.pages[cur].count.is_some());
                    }
                    assert(cur != pid);
                    assert(false);
                }
                assert(pid.idx + removed_count <= idx);
                if pre.pages[cur].is_used {
                    assert(pre.good_range_used(cur));
                    Self::take_page_from_unused_queue_preserves_good_range_used(
                        pre, post, pid, sbin_idx, list_idx, cur);
                    assert(post.pages[cur].is_used);
                    assert(post.good_range_used(cur));
                } else {
                    assert(pre.good_range_unused(cur));
                    Self::take_page_from_unused_queue_preserves_good_range_unused(
                        pre, post, pid, sbin_idx, list_idx, cur);
                    assert(!post.pages[cur].is_used);
                    assert(post.good_range_unused(cur));
                }
                assert(post.pages[cur].count == pre.pages[cur].count);
                assert(post.pages[cur].count.unwrap() == count);
                Self::rec_take_page_from_unused_queue(pre, post, pid, sbin_idx, list_idx, idx + count);
                assert(!(idx <= pid.idx));
                assert(!Self::is_the_popped(pid.segment_id, idx, post.popped));
                assert(post.attached_rec(pid.segment_id, idx + count, false));
                assert(post.attached_rec(pid.segment_id, idx, false));
            }
        }
    }

    #[verifier::spinoff_prover]
    #[inductive(split_page)]
    fn split_page_inductive(pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int) {
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        reveal(State::good_range_very_unready);
        reveal(State::attached_ranges);
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);

        pre.very_unready_popped_range_facts();
        let segment_id = page_id.segment_id;
        let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
        let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
        assert(pre.popped == Popped::VeryUnready(segment_id, page_id.idx as int, current_count, false));
        assert(post.popped == Popped::VeryUnready(segment_id, page_id.idx as int, target_count, false));
        assert(1 <= target_count < current_count);
        Self::split_page_tail_good_range_unused(pre, post, page_id, current_count, target_count, sbin_idx);
        assert(post.popped_basics());
        assert(post.good_range_very_unready(page_id));
        assert(post.inv_very_unready());

        pre.attached_ranges_very_unready_start();
        assert(pre.attached_rec(segment_id, page_id.idx as int, true));
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        assert(pre.attached_ranges_segment(segment_id));
        assert(pre.attached_rec0(segment_id, true));
        let first_id = PageId { segment_id, idx: 0 };
        let first_count = pre.pages[first_id].count.unwrap();
        assert(pre.good_range0(segment_id));
        assert(pre.attached_rec(segment_id, first_count as int, true));
        Self::rec_attached_to_very_unready_start(pre, first_count as int, true);
        assert(first_count <= page_id.idx);
        Self::rec_split_page(pre, post, page_id, current_count, target_count, sbin_idx, first_count as int, true);
        assert(post.attached_rec(segment_id, first_count as int, true));
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            ({
                let first_count = pre.pages[first_id].count.unwrap();
                pid.segment_id == segment_id
                && first_id.idx <= pid.idx < first_id.idx + first_count
            })
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == next_page_id || pid == last_page_id {
                assert(page_id.idx <= pid.idx);
                assert(pid.idx < first_count);
                assert(false);
            } else if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let old_first = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                if pid == old_first {
                    reveal(State::ll_inv_valid_unused);
                    reveal(State::valid_unused_page);
                    assert(pre.pages[old_first].dlist_entry.is_some());
                    assert(pre.pages[old_first].offset == Some(0nat));
                    assert(pre.good_range0(segment_id));
                    reveal(State::good_range0);
                    assert(pre.pages[pid].dlist_entry.is_none());
                    assert(false);
                }
                assert(post.pages.dom().contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            } else {
                assert(post.pages.dom().contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::good_range0_same(pre, post, segment_id);
        assert(post.attached_rec0(segment_id, true));
        assert(post.attached_ranges_segment(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if pid == next_page_id || pid == last_page_id {
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                if pid == first_id {
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_unused);
                    reveal(State::valid_unused_page);
                    assert(0 <= sbin_idx < pre.unused_lists.len());
                    assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], pre.unused_lists[sbin_idx]));
                    assert(pre.unused_lists[sbin_idx].len() != 0);
                    assert(pre.unused_lists[sbin_idx][0] == first_id);
                    assert(pre.valid_unused_page(first_id, sbin_idx, 0));
                    assert(pre.pages[first_id].is_used == false);
                    assert(false);
                }
                assert(post.pages[pid] == pre.pages[pid]);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());

        Self::split_page_ll_inv_valid_unused(pre, post, page_id, current_count, target_count, sbin_idx);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());
        Self::split_page_ll_inv_exists_in_some_list(pre, post, page_id, current_count, target_count, sbin_idx);
        assert(post.ll_inv_exists_in_some_list());
        reveal(State::ll_inv_valid_unused2);
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            if pid == next_page_id {
                assert(pre.pages[pid].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else if pid == last_page_id {
                assert(pre.pages[pid].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else {
                if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                    if pid == first_id {
                        assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                        assert(post.pages[pid].offset == pre.pages[pid].offset);
                    }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        };
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            assert(post.segments == pre.segments);
            if sid == segment_id {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
        };
        Self::count_is_right_preserve_all(pre, post);
        assert(post.count_is_right());
    }

    pub proof fn split_page_tail_good_range_unused(
        pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int
    )
      requires
          pre.invariant(),
          State::split_page_strong(pre, post, page_id, current_count, target_count, sbin_idx),
      ensures
          ({
              let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
              post.good_range_unused(next_page_id)
          }),
    {
        reveal(State::good_range_unused);
        pre.very_unready_popped_range_facts();

        let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
        let tail_count = current_count - target_count;
        let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };

        assert(pre.popped == Popped::VeryUnready(
            page_id.segment_id, page_id.idx as int, current_count, false));
        assert(1 <= target_count < current_count);
        assert(tail_count > 0);
        assert(next_page_id.idx == page_id.idx + target_count);
        assert(last_page_id.idx == next_page_id.idx + tail_count - 1);
        assert(next_page_id.idx + tail_count == page_id.idx + current_count);
        assert(next_page_id.idx + tail_count <= SLICES_PER_SEGMENT);
        assert(post.pages[next_page_id].count == Some(tail_count as nat));
        assert(post.pages[next_page_id].offset == Some(0nat));
        assert(post.pages[next_page_id].dlist_entry.is_some());
        assert(post.pages[next_page_id].is_used == false);
        assert(post.pages[next_page_id].full.is_none());
        assert(post.pages[next_page_id].page_header_kind.is_none());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == next_page_id.segment_id
            && next_page_id.idx <= pid.idx < next_page_id.idx + tail_count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == next_page_id)
            && (post.pages[pid].dlist_entry.is_some() <==> pid == next_page_id)
            && post.pages[pid].offset == (if pid == next_page_id || pid == last_page_id {
                    Some((pid.idx - next_page_id.idx) as nat)
                } else {
                    None
                })
        by {
            assert(pid.segment_id == page_id.segment_id);
            assert(page_id.idx <= pid.idx < page_id.idx + current_count);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == false);
            assert(pre.pages[pid].full.is_none());
            assert(pre.pages[pid].page_header_kind.is_none());
            assert(pre.pages[pid].count.is_none());
            assert(pre.pages[pid].dlist_entry.is_none());
            assert(pre.pages[pid].offset.is_none());
            if pid == next_page_id {
                assert(post.pages[pid].count == Some(tail_count as nat));
                assert(post.pages[pid].offset == Some(0nat));
                assert(post.pages[pid].dlist_entry.is_some());
            } else if pid == last_page_id {
                if tail_count > 1 {
                    assert(post.pages[pid].offset == Some((tail_count - 1) as nat));
                    assert(pid.idx - next_page_id.idx == tail_count - 1);
                } else {
                    assert(pid == next_page_id);
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.good_range_unused(next_page_id));
    }

    pub proof fn split_page_preserves_good_range_unused(
        pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int, cur: PageId
    )
      requires
          pre.invariant(),
          State::split_page_strong(pre, post, page_id, current_count, target_count, sbin_idx),
          pre.good_range_unused(cur),
          cur.segment_id == page_id.segment_id,
      ensures
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx
          }) ==> post.good_range_unused(cur),
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx
          }) ==> post.pages[cur].count == pre.pages[cur].count,
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx
          }) ==> post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        let cur_count = pre.pages[cur].count.unwrap();
        if page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx {
            reveal(State::good_range_unused);
            pre.very_unready_popped_range_facts();
            pre.good_range_disjoint_very_unready(cur);

            let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
            let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].is_used == pre.pages[cur].is_used);
            assert(post.pages[cur].offset == pre.pages[cur].offset);
            assert(post.pages[cur].full == pre.pages[cur].full);
            assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);

            assert forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                pid.segment_id == cur.segment_id
                && cur.idx <= pid.idx < cur.idx + cur_count
            implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && (post.pages[pid].count.is_some() <==> pid == cur)
                && (post.pages[pid].dlist_entry.is_some() <==> pid == cur)
                && post.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                        Some((pid.idx - cur.idx) as nat)
                    } else {
                        None
                    })
            by {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used == false);
                assert(pre.pages[pid].full.is_none());
                assert(pre.pages[pid].page_header_kind.is_none());
                assert(pre.pages[pid].count.is_some() <==> pid == cur);
                assert(pre.pages[pid].dlist_entry.is_some() <==> pid == cur);
                assert(pre.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + pre.pages[cur].count.unwrap() - 1) as nat }) {
                        Some((pid.idx - cur.idx) as nat)
                    } else {
                        None
                    }));
                if pid == next_page_id || pid == last_page_id {
                    assert(page_id.idx <= pid.idx < page_id.idx + current_count);
                    assert(false);
                } else {
                    assert(post.pages[pid].count == pre.pages[pid].count);
                    assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                    assert(post.pages[pid].full == pre.pages[pid].full);
                    assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                    assert(post.pages[pid].offset == pre.pages[pid].offset);
                    if post.pages[pid].dlist_entry != pre.pages[pid].dlist_entry {
                        assert(pre.unused_dlist_headers[sbin_idx].first.is_some());
                        let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                        assert(pid == first_id);
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pid == cur);
                    }
                }
                assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
            };
            assert(post.good_range_unused(cur));
        }
    }

    pub proof fn split_page_preserves_good_range_used(
        pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int, cur: PageId
    )
      requires
          pre.invariant(),
          State::split_page_strong(pre, post, page_id, current_count, target_count, sbin_idx),
          pre.good_range_used(cur),
          cur.segment_id == page_id.segment_id,
      ensures
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx
          }) ==> post.good_range_used(cur),
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx
          }) ==> post.pages[cur].count == pre.pages[cur].count,
          ({
              let cur_count = pre.pages[cur].count.unwrap();
              page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx
          }) ==> post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        let cur_count = pre.pages[cur].count.unwrap();
        if page_id.idx + current_count <= cur.idx || cur.idx + cur_count <= page_id.idx {
            reveal(State::good_range_used);
            pre.very_unready_popped_range_facts();
            pre.good_range_disjoint_very_unready(cur);

            let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
            let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].is_used == pre.pages[cur].is_used);
            assert(post.pages[cur].offset == pre.pages[cur].offset);
            assert(post.pages[cur].full == pre.pages[cur].full);
            assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);
            assert(post.pages[cur].dlist_entry.is_some() == pre.pages[cur].dlist_entry.is_some());

            assert forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                pid.segment_id == cur.segment_id
                && cur.idx <= pid.idx < cur.idx + cur_count
            implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == true
                && post.pages[pid].offset == Some((pid.idx - cur.idx) as nat)
                && (post.pages[pid].page_header_kind.is_some() <==> pid == cur)
                && (pid != cur ==> post.pages[pid].dlist_entry.is_none())
                && (pid != cur ==> post.pages[pid].full.is_none())
            by {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used == true);
                assert(pre.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
                assert(pre.pages[pid].page_header_kind.is_some() <==> pid == cur);
                assert(pid != cur ==> pre.pages[pid].dlist_entry.is_none());
                assert(pid != cur ==> pre.pages[pid].full.is_none());
                if pid == next_page_id || pid == last_page_id {
                    assert(page_id.idx <= pid.idx < page_id.idx + current_count);
                    assert(false);
                } else {
                    assert(post.pages[pid].count == pre.pages[pid].count);
                    assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                    assert(post.pages[pid].full == pre.pages[pid].full);
                    assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                    assert(post.pages[pid].offset == pre.pages[pid].offset);
                    if post.pages[pid].dlist_entry != pre.pages[pid].dlist_entry {
                        assert(pre.unused_dlist_headers[sbin_idx].first.is_some());
                        let first_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                        assert(pid == first_id);
                        assert(pre.pages[pid].is_used == false);
                        assert(pre.pages[pid].is_used == true);
                        assert(false);
                    }
                }
            };
            assert(post.good_range_used(cur));
        }
    }

    pub proof fn split_page_new_ids_not_old_unused_list_entry(
        pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int, i: int, j: int
    )
      requires
          pre.invariant(),
          State::split_page_strong(pre, post, page_id, current_count, target_count, sbin_idx),
          0 <= i < pre.unused_lists.len(),
          0 <= j < pre.unused_lists[i].len(),
      ensures
          ({
              let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
              let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
              pre.unused_lists[i][j] != next_page_id && pre.unused_lists[i][j] != last_page_id
          }),
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        pre.very_unready_popped_range_facts();
        let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
        let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
        let pid = pre.unused_lists[i][j];
        assert(pre.valid_unused_page(pid, i, j));
        assert(pre.pages[pid].count.is_some());
        if pid == next_page_id {
            assert(next_page_id.segment_id == page_id.segment_id);
            assert(page_id.idx <= next_page_id.idx < page_id.idx + current_count);
            assert(pre.pages[next_page_id].count.is_none());
            assert(false);
        }
        if pid == last_page_id {
            assert(last_page_id.segment_id == page_id.segment_id);
            assert(page_id.idx <= last_page_id.idx < page_id.idx + current_count);
            assert(pre.pages[last_page_id].count.is_none());
            assert(false);
        }
    }

    pub proof fn split_page_ll_inv_valid_unused(
        pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int
    )
      requires
          pre.invariant(),
          State::split_page_strong(pre, post, page_id, current_count, target_count, sbin_idx),
      ensures
          post.ll_inv_valid_unused(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        pre.very_unready_popped_range_facts();
        Self::split_page_tail_good_range_unused(pre, post, page_id, current_count, target_count, sbin_idx);

        let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
        let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
        let tail_count = current_count - target_count;
        let old_ll = pre.unused_lists[sbin_idx];
        let new_ll = old_ll.insert(0, next_page_id);
        old_ll.insert_ensures(0, next_page_id);
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(post.unused_lists =~= Self::insert_front(pre.unused_lists, sbin_idx, next_page_id));
        assert(post.unused_lists[sbin_idx] =~= new_ll);
        assert(post.pages[next_page_id].count == Some(tail_count as nat));
        assert(post.pages[next_page_id].offset == Some(0nat));
        assert(post.pages[next_page_id].dlist_entry.is_some());

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            if i == sbin_idx {
                assert(post.unused_lists[i] =~= new_ll);
                assert(post.unused_dlist_headers[i].first == Some(next_page_id));
                if old_ll.len() == 0 {
                    assert(new_ll.len() == 1);
                    assert(post.unused_dlist_headers[i].last == Some(next_page_id));
                } else {
                    assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                    assert(post.pages[old_ll[0]].dlist_entry.unwrap().prev == Some(next_page_id));
                    assert(post.unused_dlist_headers[i].last == pre.unused_dlist_headers[i].last);
                    assert(pre.unused_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                    assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                }

                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    if j == 0 {
                        assert(post.unused_lists[i][j] == next_page_id);
                        assert(post.pages[next_page_id].dlist_entry.unwrap().prev == None);
                        if old_ll.len() == 0 {
                            assert(get_next(post.unused_lists[i], j) == None);
                            assert(post.pages[next_page_id].dlist_entry.unwrap().next == None);
                        } else {
                            assert(post.unused_lists[i][1] == old_ll[0]);
                            assert(get_next(post.unused_lists[i], j) == Some(old_ll[0]));
                            assert(post.pages[next_page_id].dlist_entry.unwrap().next == pre.unused_dlist_headers[i].first);
                            assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                        }
                    } else {
                        let old_j = j - 1;
                        assert(0 <= old_j < old_ll.len());
                        assert(post.unused_lists[i][j] == old_ll[old_j]);
                        let pid = post.unused_lists[i][j];
                        Self::split_page_new_ids_not_old_unused_list_entry(
                            pre, post, page_id, current_count, target_count, sbin_idx, sbin_idx, old_j);
                        assert(pid != next_page_id);
                        assert(pid != last_page_id);
                        assert(valid_ll_i(pre.pages, old_ll, old_j));
                        if old_j == 0 {
                            assert(pre.unused_dlist_headers[i].first == Some(pid));
                            assert(post.pages[pid].dlist_entry.unwrap().prev == Some(next_page_id));
                            assert(get_prev(post.unused_lists[i], j) == Some(next_page_id));
                        } else {
                            let first_id = old_ll[0];
                            pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, 0);
                            assert(pid != first_id);
                            assert(post.pages[pid] == pre.pages[pid]);
                            assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                            assert(get_prev(post.unused_lists[i], j) == get_prev(old_ll, old_j));
                        }
                        assert(get_next(post.unused_lists[i], j) == get_next(old_ll, old_j));
                    }
                };
            } else {
                assert(post.unused_lists[i] == pre.unused_lists[i]);
                assert(post.unused_dlist_headers[i] == pre.unused_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let pid = post.unused_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                    Self::split_page_new_ids_not_old_unused_list_entry(
                        pre, post, page_id, current_count, target_count, sbin_idx, i, j);
                    assert(pid != next_page_id);
                    assert(pid != last_page_id);
                    if old_ll.len() != 0 {
                        let first_id = old_ll[0];
                        if pid == first_id {
                            pre.ll_unused_distinct(i, j, sbin_idx, 0);
                            assert(false);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                };
            }
        };

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists.index(i).index(j) == post.unused_lists.index(i).index(j)
        implies
            ({
                let pid = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(pid)
                &&& pid.idx != 0
                &&& post.pages[pid].is_used == false
                &&& (match post.pages[pid].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[pid].offset == Some(0nat)
                &&& post.pages[pid].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == pid
                &&& post.valid_unused_page(post.unused_lists[i][j], i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[pid].count.unwrap() as int)
            })
        by {
            let pid = post.unused_lists[i][j];
            if i == sbin_idx && j == 0 {
                assert(pid == next_page_id);
                assert(0 <= sbin_idx <= SEGMENT_BIN_MAX);
                assert(post.pages[pid].count == Some(tail_count as nat));
                assert(post.pages[pid].offset == Some(0nat));
                assert(post.pages[pid].dlist_entry.is_some());
                assert(sbin_idx == smallest_sbin_fitting_size(tail_count));
                assert(post.valid_unused_page(pid, i, j));
            } else {
                let old_j = if i == sbin_idx { j - 1 } else { j };
                if i == sbin_idx {
                    assert(j > 0);
                    assert(0 <= old_j < old_ll.len());
                    assert(pid == old_ll[old_j]);
                    Self::split_page_new_ids_not_old_unused_list_entry(
                        pre, post, page_id, current_count, target_count, sbin_idx, sbin_idx, old_j);
                } else {
                    assert(pid == pre.unused_lists[i][j]);
                    Self::split_page_new_ids_not_old_unused_list_entry(
                        pre, post, page_id, current_count, target_count, sbin_idx, i, j);
                    if old_ll.len() != 0 {
                        let first_id = old_ll[0];
                        if pid == first_id {
                            pre.ll_unused_distinct(i, j, sbin_idx, 0);
                            assert(false);
                        }
                    }
                }
                assert(pid != next_page_id);
                assert(pid != last_page_id);
                assert(pre.valid_unused_page(pid, i, old_j));
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
                assert(post.pages[pid].dlist_entry.is_some());
                assert(post.valid_unused_page(pid, i, j));
            }
        };
        assert(post.ll_inv_valid_unused());
    }

    pub proof fn split_page_ll_inv_exists_in_some_list(
        pre: Self, post: Self, page_id: PageId, current_count: int, target_count: int, sbin_idx: int
    )
      requires
          pre.invariant(),
          State::split_page_strong(pre, post, page_id, current_count, target_count, sbin_idx),
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        pre.very_unready_popped_range_facts();
        Self::split_page_ll_inv_valid_unused(pre, post, page_id, current_count, target_count, sbin_idx);

        let next_page_id = PageId { idx: (page_id.idx + target_count) as nat, ..page_id };
        let last_page_id = PageId { idx: (page_id.idx + current_count - 1) as nat, ..page_id };
        let tail_count = current_count - target_count;
        let old_ll = pre.unused_lists[sbin_idx];
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(post.unused_lists =~= Self::insert_front(pre.unused_lists, sbin_idx, next_page_id));
        assert(post.unused_lists[sbin_idx][0] == next_page_id);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if pid == next_page_id {
                assert(post.pages[pid].count == Some(tail_count as nat));
                assert(is_in_lls(pid, post.unused_lists));
            } else if pid == last_page_id {
                if tail_count > 1 {
                    assert(post.pages[pid].offset == Some((tail_count - 1) as nat));
                    assert(tail_count - 1 > 0);
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                } else {
                    assert(pid == next_page_id);
                    assert(false);
                }
            } else if pid.segment_id == page_id.segment_id
                && page_id.idx <= pid.idx < page_id.idx + current_count
            {
                if pid.idx < page_id.idx + target_count {
                    assert(post.in_popped_range(pid));
                    assert(false);
                } else {
                    assert(post.pages[pid].offset.is_none());
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                }
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(pre.pages[pid].count.is_some());
                assert(is_in_lls(pid, pre.unused_lists));
                reveal(State::get_list_idx);
                let pair = Self::get_list_idx(pre.unused_lists, pid);
                let i = pair.0;
                let j = pair.1;
                assert(0 <= i < pre.unused_lists.len());
                assert(0 <= j < pre.unused_lists[i].len());
                assert(pre.unused_lists[i][j] == pid);
                Self::ll_insert_front_preserves_list_at(
                    pre.unused_lists, post.unused_lists, sbin_idx, next_page_id, pid, i);
                assert(is_in_list_at(pid, post.unused_lists, i));
                assert(is_in_lls(pid, post.unused_lists));
            }
        };
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            if i == sbin_idx && j == 0 {
                assert(pid == next_page_id);
                assert(post.pages[pid].count == Some(tail_count as nat));
                assert(sbin_idx == smallest_sbin_fitting_size(tail_count));
            } else {
                let old_j = if i == sbin_idx { j - 1 } else { j };
                if i == sbin_idx {
                    assert(j > 0);
                    assert(0 <= old_j < old_ll.len());
                    assert(pid == old_ll[old_j]);
                    Self::split_page_new_ids_not_old_unused_list_entry(
                        pre, post, page_id, current_count, target_count, sbin_idx, sbin_idx, old_j);
                } else {
                    assert(pid == pre.unused_lists[i][j]);
                    Self::split_page_new_ids_not_old_unused_list_entry(
                        pre, post, page_id, current_count, target_count, sbin_idx, i, j);
                }
                assert(pid != next_page_id);
                assert(pid != last_page_id);
                assert(pre.valid_unused_page(pid, i, old_j));
                assert(post.pages[pid].count == pre.pages[pid].count);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
    }

    pub proof fn rec_split_page(pre: Self, post: Self, pid: PageId, current_count: int, target_count: int, sbin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::split_page_strong(pre, post, pid, current_count, target_count, sbin_idx),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
       reveal(State::attached_rec);
       reveal(State::is_the_popped);
       reveal(State::popped_len);
       reveal(State::page_id_of_popped);
       reveal(State::good_range_unused);
       reveal(State::good_range_used);

       pre.very_unready_popped_range_facts();
       let segment_id = pre.popped.get_VeryUnready_0();
       let start = pre.popped.get_VeryUnready_1();
       let old_count = pre.popped.get_VeryUnready_2();
       let new_count = target_count;
       let next_id = PageId { idx: (pid.idx + target_count) as nat, ..pid };
       assert(pre.popped == Popped::VeryUnready(pid.segment_id, pid.idx as int, current_count, false));
       assert(post.popped == Popped::VeryUnready(pid.segment_id, pid.idx as int, target_count, false));
       assert(segment_id == pid.segment_id);
       assert(start == pid.idx);
       assert(old_count == current_count);
       assert(1 <= target_count < current_count);
       assert(new_count > 0);
       assert(start + new_count <= SLICES_PER_SEGMENT);

       if idx == SLICES_PER_SEGMENT {
           assert(!sp);
           assert(post.attached_rec(segment_id, idx, sp));
       } else if idx > SLICES_PER_SEGMENT {
           assert(!pre.attached_rec(segment_id, idx, sp));
           assert(false);
       } else if Self::is_the_popped(segment_id, idx, pre.popped) {
           assert(idx == start);
           assert(sp);
           assert(pre.attached_rec(segment_id, start + current_count, false));
           Self::rec_split_page(pre, post, pid, current_count, target_count, sbin_idx, start + current_count, false);
           assert(post.attached_rec(segment_id, start + current_count, false));
           Self::split_page_tail_good_range_unused(pre, post, pid, current_count, target_count, sbin_idx);
           assert(next_id.idx == start + target_count);
           assert(post.good_range_unused(next_id));
           assert(post.pages[next_id].count == Some((current_count - target_count) as nat));
           assert(post.pages[next_id].count.unwrap() == current_count - target_count);
           assert(next_id.idx + post.pages[next_id].count.unwrap() == start + current_count);
           assert(!Self::is_the_popped(segment_id, next_id.idx as int, post.popped));
           assert(post.attached_rec(segment_id, next_id.idx as int, false));
           assert(Self::is_the_popped(segment_id, idx, post.popped));
           assert(post.popped_len() == target_count);
           assert(idx + post.popped_len() == next_id.idx);
           assert(post.attached_rec(segment_id, idx, true));
       } else {
           let cur = PageId { segment_id, idx: idx as nat };
           let count = pre.pages[cur].count.unwrap();
           assert(count > 0);
           assert(idx + count <= SLICES_PER_SEGMENT);
           assert(pre.attached_rec(segment_id, idx + count, sp));
           if pre.pages[cur].is_used {
               assert(pre.good_range_used(cur));
               pre.good_range_disjoint_very_unready(cur);
               assert(cur.idx + count <= pid.idx || pid.idx + current_count <= cur.idx);
               Self::split_page_preserves_good_range_used(
                   pre, post, pid, current_count, target_count, sbin_idx, cur);
               assert(post.pages[cur].is_used);
               assert(post.good_range_used(cur));
           } else {
               assert(pre.good_range_unused(cur));
               pre.good_range_disjoint_very_unready(cur);
               assert(cur.idx + count <= pid.idx || pid.idx + current_count <= cur.idx);
               Self::split_page_preserves_good_range_unused(
                   pre, post, pid, current_count, target_count, sbin_idx, cur);
               assert(!post.pages[cur].is_used);
               assert(post.good_range_unused(cur));
           }
           assert(post.pages[cur].count == pre.pages[cur].count);
           assert(post.pages[cur].count.unwrap() == count);
           Self::rec_split_page(pre, post, pid, current_count, target_count, sbin_idx, idx + count, sp);
           assert(!Self::is_the_popped(segment_id, idx, post.popped));
           assert(post.attached_rec(segment_id, idx + count, sp));
           assert(post.attached_rec(segment_id, idx, sp));
       }
    }


    #[inductive(allocate_popped)]
    fn allocate_popped_inductive(pre: Self, post: Self) {
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        reveal(State::inv_ready);
        reveal(State::good_range_very_unready);
        reveal(State::good_range_ready);
        reveal(State::data_for_used_header);
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_used2);
        reveal(State::does_count);

        let segment_id = pre.popped.get_VeryUnready_0();
        let idx = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: idx as nat };
        let changed_pages = Map::new(
            page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count as nat),
            |pid: PageId| PageData {
                count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                offset: Some((pid.idx - page_id.idx) as nat),
                dlist_entry: pre.pages[pid].dlist_entry,
                is_used: false,
                page_header_kind: None,
                full: None,
            }
        );
        let new_pages = pre.pages.union_prefer_right(changed_pages);

        pre.very_unready_popped_range_facts();
        assert(pre.popped == Popped::VeryUnready(segment_id, idx, count, false));
        assert(idx > 0);
        assert(count > 0);
        assert(page_id.idx == idx);
        assert(page_id.idx + count <= SLICES_PER_SEGMENT);
        assert(pre.pages.dom().contains(page_id));
        assert(pre.segments.dom().contains(segment_id));
        assert(post.pages == new_pages);
        assert(post.popped == Popped::Ready(page_id, true));
        assert(post.segments == pre.segments.insert(segment_id, SegmentData {
            used: pre.segments[segment_id].used + 1,
        }));

        assert(pre.pages.dom() =~= post.pages.dom()) by {
            vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
            assert forall |pid: PageId|
                changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
            by {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
            };
            assert(changed_pages.dom().subset_of(pre.pages.dom()));
            assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
        };
        assert(pre.segments.dom() =~= post.segments.dom());
        assert(post.page_id_domain());

        assert(post.popped_basics());
        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
                if pid == page_id {
                    assert(post.pages[pid].count == Some(count as nat));
                } else {
                    assert(pre.pages[pid].count.is_none());
                    assert(post.pages[pid].count == pre.pages[pid].count);
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.count_off0());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + count
        implies
            post.pages.dom().contains(pid)
            && !post.pages[pid].is_used
            && post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == page_id)
            && post.pages[pid].dlist_entry.is_none()
        by {
            assert(pre.pages.dom().contains(pid));
            assert(changed_pages.dom().contains(pid));
            assert(post.pages[pid] == changed_pages[pid]);
            if pid == page_id {
                assert(post.pages[pid].count.is_some());
            } else {
                assert(pre.pages[pid].count.is_none());
            }
            assert(pre.pages[pid].dlist_entry.is_none());
        };
        assert(post.good_range_ready(page_id));
        assert(post.pages[page_id].dlist_entry.is_none());
        assert(post.pages[page_id].full.is_none());
        assert(post.pages[page_id].page_header_kind.is_none());
        assert(post.inv_ready());
        assert(post.inv_very_unready());
        assert(post.inv_used());
        assert(Self::popped_ranges_match(pre, post)) by {
            reveal(State::popped_ranges_match);
            reveal(State::is_any_the_popped);
            reveal(State::page_id_of_popped);
            reveal(State::popped_len);
            assert(post.pages[page_id].count.unwrap() == count);
        };
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })
        by {
            if changed_pages.dom().contains(pid) {
                reveal(State::in_popped_range);
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
                assert(pre.in_popped_range(pid));
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_ranges_all(pre, post);
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());

        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
        implies
            post.pages[pid].dlist_entry.is_some()
            && post.pages[pid].full.is_some()
            && (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
            }
        };
        assert(post.data_for_used_header());
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
                assert(pre.used_lists == post.used_lists);
            }
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(pre.used_lists == post.used_lists);
            }
        };
        assert(post.ll_inv_valid_used2());

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
            && post.popped.is_Ready()
        implies
            post.unused_lists[i][j] != post.popped_page_id()
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            if pid == page_id {
                assert(pre.pages[pid].count.is_some());
                assert(pre.pages[pid].count.is_none());
                assert(false);
            }
        };
        assert(post.ready_popped_not_in_unused_lists());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
                assert(post.in_popped_range(pid));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(is_in_lls(pid, pre.unused_lists));
                assert(pre.unused_lists == post.unused_lists);
                assert(is_in_lls(pid, post.unused_lists));
            }
        };
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].count.is_some());
                assert(pre.pages[pid].count.is_none());
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            assert(pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid));
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].is_used == false);
                assert(pre.pages[pid].is_used == false);
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::ucount_preserve_all(pre, post);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            reveal(State::popped_ec);
            reveal(State::ec_of_popped);
            assert(pre.segments.dom().contains(sid));
            assert(pre.ucount(sid) == post.ucount(sid));
            if sid == segment_id {
                assert(post.segments[sid].used == pre.segments[sid].used + 1);
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 1);
            } else {
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
            assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
        };
        assert(post.count_is_right());
    }

    #[inductive(set_range_to_used)]
    fn set_range_to_used_inductive(pre: Self, post: Self, page_header_kind: PageHeaderKind) {
        reveal(State::popped_basics);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::good_range_ready);
        reveal(State::good_range_used);
        reveal(State::data_for_used_header);
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_used2);
        reveal(State::does_count);

        let page_id = pre.popped.get_Ready_0();
        let b = pre.popped.get_Ready_1();
        let count = pre.pages[page_id].count.unwrap();
        let changed_pages = Map::new(
            page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count),
            |pid: PageId| PageData {
                is_used: true,
                page_header_kind: if pid == page_id { Some(page_header_kind) } else { None },
                .. pre.pages[pid]
            }
        );
        let new_pages = pre.pages.union_prefer_right(changed_pages);

        pre.ready_popped_range_facts();
        assert(pre.popped == Popped::Ready(page_id, b));
        assert(post.popped == Popped::Used(page_id, b));
        assert(post.pages == new_pages);
        assert(post.segments == pre.segments);
        assert(pre.pages.dom() =~= post.pages.dom()) by {
            vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
            assert forall |pid: PageId|
                changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
            by {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
            };
            assert(changed_pages.dom().subset_of(pre.pages.dom()));
            assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
        };
        assert(post.page_id_domain());
        assert(post.popped_basics());

        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].count == pre.pages[pid].count);
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.count_off0());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == true
            && post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
            && (post.pages[pid].page_header_kind.is_some() <==> pid == page_id)
            && (pid != page_id ==> post.pages[pid].dlist_entry.is_none())
            && (pid != page_id ==> post.pages[pid].full.is_none())
        by {
            assert(pre.pages.dom().contains(pid));
            assert(changed_pages.dom().contains(pid));
            assert(post.pages[pid] == changed_pages[pid]);
            assert(pre.pages[pid].offset == Some((pid.idx - page_id.idx) as nat));
            if pid != page_id {
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].full.is_none());
            }
        };
        assert(post.good_range_used(page_id));
        assert(post.pages[page_id].dlist_entry.is_none());
        assert(post.pages[page_id].full.is_none());
        assert(post.inv_used());
        assert(post.inv_ready());
        assert(post.inv_very_unready());
        assert(Self::popped_ranges_match(pre, post)) by {
            reveal(State::popped_ranges_match);
            reveal(State::is_any_the_popped);
            reveal(State::page_id_of_popped);
            reveal(State::popped_len);
            assert(post.pages[page_id].count.unwrap() == count);
        };
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })
        by {
            if changed_pages.dom().contains(pid) {
                reveal(State::in_popped_range);
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
                assert(pre.in_popped_range(pid));
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_ranges_all(pre, post);
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(post.ready_popped_not_in_unused_lists());

        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
        implies
            post.pages[pid].dlist_entry.is_some()
            && post.pages[pid].full.is_some()
            && (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                if pid == page_id {
                    assert(pid == post.popped_page_id());
                    assert(false);
                } else {
                    assert(page_id.idx < pid.idx);
                    assert(pid.idx - page_id.idx > 0);
                    assert(post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat));
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
            }
        };
        assert(post.data_for_used_header());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                if pid == page_id {
                    assert(pid == post.popped_page_id());
                    assert(false);
                } else {
                    assert(page_id.idx < pid.idx);
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
                assert(pre.used_lists == post.used_lists);
            }
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                if pid == page_id {
                    assert(pid == post.popped_page_id());
                    assert(false);
                } else {
                    assert(page_id.idx < pid.idx);
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(pre.used_lists == post.used_lists);
            }
        };
        assert(post.ll_inv_valid_used2());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].is_used);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(is_in_lls(pid, pre.unused_lists));
                assert(pre.unused_lists == post.unused_lists);
                assert(is_in_lls(pid, post.unused_lists));
            }
        };
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].dlist_entry.is_some());
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert(!pre.does_count(page_id));
        assert(post.does_count(page_id));
        assert forall |pid: PageId| pid != page_id implies (pre.does_count(pid) <==> post.does_count(pid)) by {
            reveal(State::does_count);
            assert(pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid));
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
                assert(page_id.idx < pid.idx);
                assert(pid.idx - page_id.idx > 0);
                assert(post.pages[pid].offset != Some(0nat));
                assert(pre.pages[pid].is_used == false);
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(0 <= page_id.idx < SLICES_PER_SEGMENT);
        Self::ucount_inc1(pre, post, page_id);
        assert forall |pid: PageId| #![all_triggers] pid.segment_id != page_id.segment_id implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
        by {
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == page_id.segment_id);
                assert(false);
            }
        };
        Self::ucount_preserve_except(pre, post, page_id.segment_id);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            reveal(State::popped_ec);
            reveal(State::ec_of_popped);
            assert(pre.segments.dom().contains(sid));
            assert(post.segments[sid].used == pre.segments[sid].used);
            if sid == page_id.segment_id {
                assert(post.ucount(sid) == pre.ucount(sid) + 1);
                if b {
                    assert(pre.popped_ec(sid) == 1);
                    assert(post.popped_ec(sid) == 0);
                } else {
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == -1);
                }
            } else {
                assert(post.ucount(sid) == pre.ucount(sid));
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
            assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
        };
        assert(post.count_is_right());
    }

    #[inductive(set_range_to_not_used)]
    fn set_range_to_not_used_inductive(pre: Self, post: Self) {
        reveal(State::popped_basics);
        reveal(State::inv_used);
        reveal(State::inv_very_unready);
        reveal(State::good_range_used);
        reveal(State::good_range_very_unready);
        reveal(State::data_for_used_header);
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_used2);
        reveal(State::popped_ranges_match);
        reveal(State::is_any_the_popped);
        reveal(State::page_id_of_popped);
        reveal(State::popped_len);
        reveal(State::does_count);

        let page_id = pre.popped.get_Used_0();
        let b = pre.popped.get_Used_1();
        let count = pre.pages[page_id].count.unwrap();
        let changed_pages = Map::new(
            page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count),
            |pid: PageId| PageData {
                is_used: false,
                page_header_kind: None,
                offset: None,
                count: None,
                .. pre.pages[pid]
            }
        );
        let new_pages = pre.pages.union_prefer_right(changed_pages);

        pre.used_popped_range_facts();
        assert(pre.popped == Popped::Used(page_id, b));
        assert(post.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, b));
        assert(post.pages == new_pages);
        assert(post.segments == pre.segments);
        assert(pre.pages.dom() =~= post.pages.dom()) by {
            vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
            assert forall |pid: PageId|
                changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
            by {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
            };
            assert(changed_pages.dom().subset_of(pre.pages.dom()));
            assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
        };
        assert(post.page_id_domain());
        assert(post.popped_basics());

        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].count.is_none());
                assert(false);
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.count_off0());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + count
        implies
            post.pages.dom().contains(pid)
            && !post.pages[pid].is_used
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && post.pages[pid].count.is_none()
            && post.pages[pid].dlist_entry.is_none()
            && post.pages[pid].offset.is_none()
        by {
            assert(pre.pages.dom().contains(pid));
            assert(changed_pages.dom().contains(pid));
            assert(post.pages[pid] == changed_pages[pid]);
            if pid == page_id {
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].full.is_none());
            } else {
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].full.is_none());
            }
        };
        assert(post.good_range_very_unready(page_id));
        assert(post.inv_very_unready());
        assert(post.inv_ready());
        assert(post.inv_used());

        assert(Self::popped_ranges_match(pre, post));
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(pre.in_popped_range(pid));
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_ranges_all(pre, post);
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        assert(post.attached_ranges_segment(page_id.segment_id));
        assert(post.attached_rec0(page_id.segment_id, true));
        let first_id = PageId { segment_id: page_id.segment_id, idx: 0 };
        let first_count = post.pages[first_id].count.unwrap();
        assert(post.attached_rec(page_id.segment_id, first_count as int, true));
        Self::rec_attached_to_very_unready_start(post, first_count as int, true);
        assert(post.attached_rec(page_id.segment_id, page_id.idx as int, true));
        assert(post.attached_ranges());
        assert(post.ready_popped_not_in_unused_lists());

        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].is_used == true);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
        implies
            post.pages[pid].dlist_entry.is_some()
            && post.pages[pid].full.is_some()
            && (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(pid != page_id);
            }
        };
        assert(post.data_for_used_header());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(pid != page_id);
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
                assert(pre.used_lists == post.used_lists);
            }
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(pid != page_id);
                assert(pre.used_lists == post.used_lists);
            }
        };
        assert(post.ll_inv_valid_used2());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.in_popped_range(pid));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(pre.pages.dom().contains(pid));
                assert(pid != page_id);
                assert(is_in_lls(pid, pre.unused_lists));
                assert(pre.unused_lists == post.unused_lists);
                assert(is_in_lls(pid, post.unused_lists));
            }
        };
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].is_used == true);
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert(pre.does_count(page_id));
        assert(!post.does_count(page_id));
        assert forall |pid: PageId| pid != page_id implies (pre.does_count(pid) <==> post.does_count(pid)) by {
            reveal(State::does_count);
            assert(pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid));
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
                assert(page_id.idx < pid.idx);
                assert(pre.pages[pid].offset == Some((pid.idx - page_id.idx) as nat));
                assert(pre.pages[pid].offset != Some(0nat));
                assert(post.pages[pid].is_used == false);
            } else if pre.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(0 <= page_id.idx < SLICES_PER_SEGMENT);
        Self::ucount_dec1(pre, post, page_id);
        assert forall |pid: PageId| #![all_triggers] pid.segment_id != page_id.segment_id implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
        by {
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == page_id.segment_id);
                assert(false);
            }
        };
        Self::ucount_preserve_except(pre, post, page_id.segment_id);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            reveal(State::popped_ec);
            reveal(State::ec_of_popped);
            assert(pre.segments.dom().contains(sid));
            assert(post.segments[sid].used == pre.segments[sid].used);
            if sid == page_id.segment_id {
                assert(post.ucount(sid) == pre.ucount(sid) - 1);
                if b {
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == 1);
                } else {
                    assert(pre.popped_ec(sid) == -1);
                    assert(post.popped_ec(sid) == 0);
                }
            } else {
                assert(post.ucount(sid) == pre.ucount(sid));
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
            assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
        };
        assert(post.count_is_right());
    }

    #[verifier::spinoff_prover]
    #[inductive(into_used_list)]
    fn into_used_list_inductive(pre: Self, post: Self, bin_idx: int) {
        reveal(State::inv_used);
        reveal(State::good_range_used);
        reveal(State::popped_basics);
        reveal(State::count_off0);
        reveal(State::attached_ranges);
        let page_id = pre.popped.get_Used_0();
        assert(pre.popped == Popped::Used(page_id, true));
        assert(post.popped == Popped::No);
        assert(pre.good_range_used(page_id));
        let count = pre.pages[page_id].count.unwrap();
        assert(1 <= count);
        assert(page_id.idx + count <= SLICES_PER_SEGMENT);
        assert(post.popped_basics());
        assert(post.inv_used());
        assert(post.good_range_used(page_id));
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::in_popped_range);
        assert(pre.attached_ranges_segment(page_id.segment_id));
        assert(pre.attached_rec0(page_id.segment_id, true));
        let first_id0 = PageId { segment_id: page_id.segment_id, idx: 0 };
        let first_count0 = pre.pages[first_id0].count.unwrap();
        assert(pre.good_range0(page_id.segment_id));
        assert(pre.attached_rec(page_id.segment_id, first_count0 as int, true));
        if first_count0 > page_id.idx {
            reveal(State::good_range0);
            assert(first_id0.idx <= page_id.idx < first_id0.idx + first_count0);
            assert(pre.pages[page_id].is_used == false);
            assert(pre.pages[page_id].is_used == true);
            assert(false);
        }
        assert(first_count0 <= page_id.idx);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == page_id.segment_id
            && first_id0.idx <= pid.idx < first_id0.idx + first_count0
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == page_id {
                assert(page_id.idx < first_count0);
                assert(false);
            }
            if pre.used_dlist_headers[bin_idx].first.is_some() {
                let old_first = pre.used_dlist_headers[bin_idx].first.unwrap();
                if pid == old_first {
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_used);
                    reveal(State::valid_used_page);
                    pre.first_last_ll_stuff_used(bin_idx);
                    assert(pre.pages[old_first].is_used);
                    reveal(State::good_range0);
                    assert(pre.pages[pid].is_used == false);
                    assert(false);
                }
            }
            assert(post.pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::good_range0_same(pre, post, page_id.segment_id);
        assert(post.good_range0(page_id.segment_id));
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == page_id.segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
                && !post.in_popped_range(pid) ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            assert(post.popped == Popped::No);
            if pid == page_id {
                assert(pre.in_popped_range(pid));
            } else if pre.used_dlist_headers[bin_idx].first.is_some() {
                let old_first = pre.used_dlist_headers[bin_idx].first.unwrap();
                if pid == old_first {
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_used);
                    reveal(State::valid_used_page);
                    pre.first_last_ll_stuff_used(bin_idx);
                    assert(pre.pages[pid].dlist_entry.is_some());
                    assert(post.pages[pid].dlist_entry.is_some());
                    assert(pre.pages[pid].count == post.pages[pid].count);
                    assert(pre.pages[pid].offset == post.pages[pid].offset);
                    assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                    assert(pre.pages[pid].full == post.pages[pid].full);
                    assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_rec_used_popped_to_no(pre, post, page_id, first_count0 as int);
        assert(post.attached_rec0(page_id.segment_id, false));
        assert(post.attached_ranges_segment(page_id.segment_id));
        reveal(State::if_popped_or_other_then_for);
        assert(pre.if_popped_or_other_then_for(page_id.segment_id));
        assert(post.if_popped_or_other_then_for(page_id.segment_id));
        assert forall |pid: PageId|
            pid.segment_id != page_id.segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            if pre.used_dlist_headers[bin_idx].first.is_some() {
                let old_first = pre.used_dlist_headers[bin_idx].first.unwrap();
                if pid == old_first {
                    assert(pre.pages[pid].dlist_entry.is_some());
                    assert(post.pages[pid].dlist_entry.is_some());
                    assert(pre.pages[pid].count == post.pages[pid].count);
                    assert(pre.pages[pid].offset == post.pages[pid].offset);
                    assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                    assert(pre.pages[pid].full == post.pages[pid].full);
                    assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_ranges_except(pre, post, page_id.segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == page_id.segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            if pid == page_id {
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            } else {
                if pre.used_dlist_headers[bin_idx].first.is_some() {
                    let first_id = pre.used_dlist_headers[bin_idx].first.unwrap();
                    if pid == first_id {
                        assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                        assert(post.pages[pid].offset == pre.pages[pid].offset);
                    }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        }
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            reveal(State::popped_ec);
            reveal(State::ec_of_popped);
            assert(post.segments == pre.segments);
            assert(pre.popped == Popped::Used(page_id, true));
            assert(post.popped == Popped::No);
        }
        Self::count_is_right_preserve_all(pre, post);

        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            assert(pid != page_id);
            if pre.used_dlist_headers[bin_idx].first.is_some() {
                let first_id = pre.used_dlist_headers[bin_idx].first.unwrap();
                if pid == first_id {
                    assert(pre.pages[pid].is_used);
                    assert(false);
                }
            }
            assert(post.pages[pid] == pre.pages[pid]);
        }
        Self::unchanged_unused_ll(pre, post);
        reveal(State::data_for_unused_header);
        assert(post.ll_inv_valid_unused());
        Self::into_used_list_inductive_ll_inv_exists_in_some_list(pre, post, bin_idx);
        reveal(State::ll_inv_valid_unused2);
        assert(post.ll_inv_valid_unused2());
        Self::into_used_list_inductive_ll_inv_valid_used(pre, post, bin_idx);
        Self::into_used_list_inductive_ll_inv_valid_used2(pre, post, bin_idx);
    }

    pub proof fn popped_used_not_in_used_list(&self, i: int, j: int)
        requires
            self.invariant(),
            self.popped.is_Used(),
            0 <= i < self.used_lists.len(),
            0 <= j < self.used_lists[i].len(),
        ensures
            self.used_lists[i][j] != self.popped_page_id(),
    {
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);
        reveal(State::inv_used);
        let page_id = self.popped_page_id();
        let pid = self.used_lists[i][j];
        assert(self.valid_used_page(pid, i, j));
        if pid == page_id {
            assert(self.pages[pid].dlist_entry.is_some());
            assert(self.pages[page_id].dlist_entry.is_none());
            assert(false);
        }
    }

    proof fn into_used_list_inductive_ll_inv_exists_in_some_list(pre: Self, post: Self, bin_idx: int)
        requires
            pre.invariant(),
            State::into_used_list_strong(pre, post, bin_idx)
                || State::into_used_list_back_strong(pre, post, bin_idx),
        ensures
            post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        let page_id = pre.popped.get_Used_0();
        assert(pre.popped.is_Used());
        assert(post.popped.is_No());
        assert(pre.unused_lists == post.unused_lists);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(pid != page_id);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].offset == Some(0nat));
            assert(!pre.pages[pid].is_used);
            assert(pre.pages[pid].count == post.pages[pid].count);
            assert(is_in_lls(pid, pre.unused_lists));
            assert(is_in_lls(pid, post.unused_lists));
        }

        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            assert(!pre.pages[pid].is_used);
            assert(pid != page_id);
            assert(post.pages[pid].count == pre.pages[pid].count);
        }
    }

    proof fn into_used_list_inductive_ll_inv_valid_used(pre: Self, post: Self, bin_idx: int)
        requires
            pre.invariant(),
            State::into_used_list_strong(pre, post, bin_idx),
        ensures
            post.ll_inv_valid_used(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);
        reveal(State::inv_used);
        reveal(State::good_range_used);

        let page_id = pre.popped.get_Used_0();
        let old_ll = pre.used_lists[bin_idx];
        let new_ll = old_ll.insert(0, page_id);
        old_ll.insert_ensures(0, page_id);
        assert(pre.popped == Popped::Used(page_id, true));
        assert(post.used_lists =~= Self::insert_front(pre.used_lists, bin_idx, page_id));
        assert(pre.good_range_used(page_id));
        assert(pre.pages[page_id].dlist_entry.is_none());
        assert(post.pages[page_id].dlist_entry.is_some());
        assert(post.pages[page_id].full == Some(bin_idx == BIN_FULL));

        pre.first_last_ll_stuff_used(bin_idx);

        assert forall |i: int|
            #![trigger post.used_dlist_headers.index(i)]
            0 <= i < post.used_lists.len()
        implies
            valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            if i == bin_idx {
                assert(post.used_lists[i] == new_ll);
                assert(post.used_dlist_headers[i].first == Some(page_id));
                if old_ll.len() == 0 {
                    assert(pre.used_dlist_headers[i].first.is_none());
                    assert(pre.used_dlist_headers[i].last.is_none());
                    assert(new_ll.len() == 1);
                    assert(new_ll[0] == page_id);
                    assert(post.used_dlist_headers[i].last == Some(page_id));
                } else {
                    assert(pre.used_dlist_headers[i].first.is_some());
                    assert(pre.used_dlist_headers[i].last.is_some());
                    assert(pre.used_dlist_headers[i].first == Some(old_ll[0]));
                    assert(new_ll.len() == old_ll.len() + 1);
                    assert(new_ll[0] == page_id);
                    assert(new_ll[1] == old_ll[0]);
                    assert(post.used_dlist_headers[i].last == pre.used_dlist_headers[i].last);
                    assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                    assert(post.used_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                }
                assert forall |j: int|
                    0 <= j < post.used_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.used_lists[i], j)
                by {
                    if j == 0 {
                        assert(post.used_lists[i][j] == page_id);
                        assert(post.pages[page_id].dlist_entry.unwrap().prev == None);
                        if old_ll.len() == 0 {
                            assert(post.used_lists[i].len() == 1);
                            assert(get_next(post.used_lists[i], j) == None);
                            assert(post.pages[page_id].dlist_entry.unwrap().next == None);
                        } else {
                            assert(post.used_lists[i].len() > 1);
                            assert(post.used_lists[i][1] == old_ll[0]);
                            assert(get_next(post.used_lists[i], j) == Some(old_ll[0]));
                            assert(post.pages[page_id].dlist_entry.unwrap().next == pre.used_dlist_headers[bin_idx].first);
                            assert(pre.used_dlist_headers[bin_idx].first == Some(old_ll[0]));
                        }
                    } else {
                        let old_j = j - 1;
                        assert(0 <= old_j < old_ll.len());
                        assert(post.used_lists[i][j] == old_ll[old_j]);
                        let pid = post.used_lists[i][j];
                        pre.popped_used_not_in_used_list(bin_idx, old_j);
                        assert(pid != page_id);
                        assert(valid_ll_i(pre.pages, old_ll, old_j));
                        if old_j == 0 {
                            assert(pre.used_dlist_headers[bin_idx].first == Some(pid));
                            assert(post.pages[pid].dlist_entry.unwrap().prev == Some(page_id));
                            assert(get_prev(post.used_lists[i], j) == Some(page_id));
                        } else {
                            assert(pid != old_ll[0]) by {
                                pre.ll_used_distinct(bin_idx, old_j, bin_idx, 0);
                            }
                            assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                            assert(get_prev(post.used_lists[i], j) == get_prev(old_ll, old_j));
                        }
                        assert(get_next(post.used_lists[i], j) == get_next(old_ll, old_j));
                    }
                }
            } else {
                assert(post.used_lists[i] == pre.used_lists[i]);
                assert(post.used_dlist_headers[i] == pre.used_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
                assert forall |j: int|
                    0 <= j < post.used_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.used_lists[i], j)
                by {
                    let pid = post.used_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.used_lists[i], j));
                    pre.popped_used_not_in_used_list(i, j);
                    assert(pid != page_id);
                    if old_ll.len() != 0 {
                        let first_id = old_ll[0];
                        if pid == first_id {
                            pre.ll_used_distinct(i, j, bin_idx, 0);
                            assert(false);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                }
            }
        }

        assert forall |i: int, j: int|
            0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len()
            && #[trigger] post.used_lists.index(i).index(j) == post.used_lists.index(i).index(j)
        implies
            ({
                let pid = post.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& post.valid_used_page(pid, i, j)
                &&& post.pages[pid].count.is_some()
                &&& (post.popped.is_Ready() ==> pid != post.popped_page_id())
            })
        by {
            let pid = post.used_lists[i][j];
            if i == bin_idx && j == 0 {
                assert(pid == page_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].count.is_some());
                assert(post.pages[pid].offset == Some(0nat));
                assert(post.pages[pid].is_used);
                assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, bsize)) => {
                        assert(valid_bin_idx(bin));
                        assert(size_of_bin(bin) == bsize);
                        assert(bin_idx != BIN_FULL ==> bin_idx == bin);
                    }
                    None => { assert(false); }
                }
            } else {
                let old_j = if i == bin_idx { j - 1 } else { j };
                if i == bin_idx {
                    assert(0 <= old_j < old_ll.len());
                    assert(pid == old_ll[old_j]);
                    pre.popped_used_not_in_used_list(bin_idx, old_j);
                } else {
                    assert(pid == pre.used_lists[i][j]);
                    pre.popped_used_not_in_used_list(i, j);
                }
                assert(pid != page_id);
                assert(pre.valid_used_page(pid, i, old_j));
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
                assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                assert(post.pages[pid].dlist_entry.is_some());
                assert(!post.popped.is_Ready());
            }
        }
        assert(post.ll_inv_valid_used());
    }

    proof fn into_used_list_inductive_ll_inv_valid_used2(pre: Self, post: Self, bin_idx: int)
        requires
            pre.invariant(),
            State::into_used_list_strong(pre, post, bin_idx),
        ensures
            post.ll_inv_valid_used2(),
    {
        reveal(State::ll_inv_valid_used2);
        reveal(State::valid_used_page);
        let page_id = pre.popped.get_Used_0();
        assert(pre.popped == Popped::Used(page_id, true));
        assert(post.popped == Popped::No);
        assert(post.used_lists =~= Self::insert_front(pre.used_lists, bin_idx, page_id));

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if pid == page_id {
                assert(post.pages[pid].full == Some(bin_idx == BIN_FULL));
                assert(bin_idx == BIN_FULL);
                assert(0 <= bin_idx < post.used_lists.len()) by {
                    reveal(State::ll_basics);
                };
                assert(post.used_lists[bin_idx][0] == page_id);
                assert(is_in_list_at(pid, post.used_lists, BIN_FULL as int));
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used);
                assert(pre.pages[pid].offset == Some(0nat));
                assert(pre.pages[pid].full == post.pages[pid].full);
                assert(pre.pages[pid].full != Some(false));
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
                Self::ll_insert_front_preserves_list_at(
                    pre.used_lists, post.used_lists, bin_idx, page_id, pid, BIN_FULL as int);
                assert(is_in_list_at(pid, post.used_lists, BIN_FULL as int));
            }
        }

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if pid == page_id {
                assert(post.pages[pid].full == Some(bin_idx == BIN_FULL));
                assert(bin_idx != BIN_FULL);
                assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, _)) => {
                        assert(bin_idx == bin);
                        assert(0 <= bin_idx < post.used_lists.len()) by {
                            reveal(State::ll_basics);
                        };
                        assert(post.used_lists[bin_idx][0] == page_id);
                        assert(is_in_list_at(pid, post.used_lists, bin));
                    }
                    None => { assert(false); }
                }
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used);
                assert(pre.pages[pid].offset == Some(0nat));
                assert(pre.pages[pid].full == post.pages[pid].full);
                assert(pre.pages[pid].full != Some(true));
                assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, _)) => {
                        assert(is_in_list_at(pid, pre.used_lists, bin));
                        Self::ll_insert_front_preserves_list_at(
                            pre.used_lists, post.used_lists, bin_idx, page_id, pid, bin);
                        assert(is_in_list_at(pid, post.used_lists, bin));
                    }
                    None => { assert(false); }
                }
            }
        }
    }

    pub proof fn segment_creating_facts(&self, segment_id: SegmentId)
        requires
            self.invariant(),
            self.popped == Popped::SegmentCreating(segment_id),
        ensures
            self.segments.dom().contains(segment_id),
            self.segments[segment_id].used == 0,
            forall |pid: PageId|
                #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
                pid.segment_id == segment_id
                && pid.idx <= SLICES_PER_SEGMENT ==>
                    self.pages.dom().contains(pid)
                    && self.pages[pid].dlist_entry.is_none()
                    && self.pages[pid].count.is_none()
                    && self.pages[pid].offset.is_none()
                    && self.pages[pid].is_used == false
                    && self.pages[pid].full.is_none()
                    && self.pages[pid].page_header_kind.is_none(),
    {
        reveal(State::inv_segment_creating);
    }

    #[verifier::spinoff_prover]
    #[inductive(create_segment)]
    fn create_segment_inductive(pre: Self, post: Self, segment_id: SegmentId) {
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_used2);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);

        let new_pages = Map::new(
            page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1),
            |page_id: PageId| PageData {
                dlist_entry: None,
                count: None,
                offset: None,
                is_used: false,
                page_header_kind: None,
                full: None,
            });

        assert(pre.popped == Popped::No);
        assert(post.popped == Popped::SegmentCreating(segment_id));
        assert(post.segments == pre.segments.insert(segment_id, SegmentData { used: 0 }));
        assert(post.pages == pre.pages.union_prefer_right(new_pages));
        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);

        assert(post.pages.dom() =~= pre.pages.dom().union(new_pages.dom())) by {
            vstd::map_lib::lemma_union_dom(pre.pages, new_pages);
        };
        assert(pre.segments.dom() =~= post.segments.dom().remove(segment_id));

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            post.pages.dom().contains(pid)
        implies
            post.segments.dom().contains(pid.segment_id)
            && pid.idx <= SLICES_PER_SEGMENT
        by {
            if new_pages.dom().contains(pid) {
                assert(pid.segment_id == segment_id);
                assert(0 <= pid.idx < SLICES_PER_SEGMENT as nat + 1);
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(pre.segments.dom().contains(pid.segment_id));
            }
        };
        assert forall |pid: PageId|
            #![trigger post.segments.dom().contains(pid.segment_id)]
            post.segments.dom().contains(pid.segment_id)
            && pid.idx <= SLICES_PER_SEGMENT
        implies
            post.pages.dom().contains(pid)
        by {
            if pid.segment_id == segment_id {
                assert(0 <= pid.idx < SLICES_PER_SEGMENT as nat + 1);
                assert(new_pages.dom().contains(pid));
            } else {
                assert(pre.segments.dom().contains(pid.segment_id));
                assert(pre.pages.dom().contains(pid));
            }
        };
        assert(post.page_id_domain());

        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            if new_pages.dom().contains(pid) {
                assert(post.pages[pid] == new_pages[pid]);
                assert(post.pages[pid].count.is_none());
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.count_off0());
        assert(post.popped_basics());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == segment_id
            && pid.idx <= SLICES_PER_SEGMENT
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry.is_none()
            && post.pages[pid].count.is_none()
            && post.pages[pid].offset.is_none()
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
        by {
            assert(new_pages.dom().contains(pid));
            assert(post.pages[pid] == new_pages[pid]);
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && pid.segment_id != segment_id
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
        implies
            post.pages[pid].dlist_entry.is_some()
            && post.pages[pid].full.is_some()
            && (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
        by {
            assert(!new_pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
            assert(pre.pages.dom().contains(pid));
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && pid.segment_id != segment_id
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            assert(!new_pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
            assert(pre.pages.dom().contains(pid));
            assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && pid.segment_id != segment_id
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) => is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            assert(!new_pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
            assert(pre.pages.dom().contains(pid));
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && pid.segment_id != segment_id
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(!new_pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
            assert(pre.pages.dom().contains(pid));
            assert(pre.popped.is_No());
            assert(!pre.in_popped_range(pid));
            assert(is_in_lls(pid, pre.unused_lists));
        };
        assert(post.inv_segment_creating());
        assert(post.inv_very_unready());
        assert(post.inv_segment_freeing());
        assert(post.inv_ready());
        assert(post.inv_used());
        assert forall |sid: SegmentId| sid != segment_id && #[trigger] post.segments.dom().contains(sid) implies pre.segments.dom().contains(sid) by {
            assert(pre.segments.dom().contains(sid));
        };
        assert forall |pid: PageId| pid.segment_id != segment_id implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })
        by {
            assert(!new_pages.dom().contains(pid));
            if pre.pages.dom().contains(pid) || post.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        reveal(State::if_popped_or_other_then_for);
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                reveal(State::attached_ranges_segment);
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if new_pages.dom().contains(pid) {
                assert(post.pages[pid] == new_pages[pid]);
                assert(pid.segment_id == segment_id);
                assert(pre.segments.dom().contains(segment_id));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if new_pages.dom().contains(pid) {
                assert(pid.segment_id == segment_id);
                assert(pre.segments.dom().contains(segment_id));
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        assert(post.ready_popped_not_in_unused_lists());

        assert(post.ll_inv_valid_used2());
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId|
            pid.segment_id == segment_id
        implies
            !post.does_count(pid)
        by {
            reveal(State::does_count);
            if post.pages.dom().contains(pid) {
                assert(pid.idx <= SLICES_PER_SEGMENT);
                assert(post.pages[pid].is_used == false);
            }
        };
        post.ucount_eq0(segment_id);
        assert forall |pid: PageId| #![all_triggers] pid.segment_id != segment_id implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
        by {
            assert(!new_pages.dom().contains(pid));
            if pre.pages.dom().contains(pid) || post.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::ucount_preserve_except(pre, post, segment_id);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            if sid == segment_id {
                assert(post.segments[sid].used == 0);
                assert(post.ucount(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            } else {
                assert(pre.segments.dom().contains(sid));
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(post.ucount(sid) == pre.ucount(sid));
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
                assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
            }
        };
        assert(post.count_is_right());
    }

    #[verifier::spinoff_prover]
    #[inductive(forget_about_first_page)]
    fn forget_about_first_page_inductive(pre: Self, post: Self, count: int) {
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::good_range_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::attached_ranges);
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_used2);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);

        let segment_id = pre.popped.get_SegmentCreating_0();
        let page_id = PageId { segment_id, idx: 0 };
        let changed_pages = Map::new(
            page_id_range(segment_id, 0, count as nat),
            |pid: PageId| PageData {
                count: if pid == page_id { Some(count as nat) } else { pre.pages[pid].count },
                offset: Some((pid.idx - page_id.idx) as nat),
                dlist_entry: pre.pages[pid].dlist_entry,
                is_used: false,
                page_header_kind: None,
                full: None,
            }
        );
        let new_pages = pre.pages.union_prefer_right(changed_pages);

        assert(pre.popped == Popped::SegmentCreating(segment_id));
        pre.segment_creating_facts(segment_id);
        assert(1 <= count < SLICES_PER_SEGMENT);
        assert(page_id.idx == 0);
        assert(post.pages == new_pages);
        assert(post.segments == pre.segments.insert(segment_id, SegmentData {
            used: pre.segments[segment_id].used + 1,
        }));
        assert(post.popped == Popped::VeryUnready(segment_id, count, SLICES_PER_SEGMENT - count, true));
        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);

        assert(pre.pages.dom() =~= post.pages.dom()) by {
            vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
            assert forall |pid: PageId|
                changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
            by {
                assert(pid.segment_id == segment_id);
                assert(0 <= pid.idx < count);
                assert(pid.idx <= SLICES_PER_SEGMENT);
            };
            assert(changed_pages.dom().subset_of(pre.pages.dom()));
            assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
        };
        assert(pre.segments.dom() =~= post.segments.dom());
        assert(post.page_id_domain());

        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            if changed_pages.dom().contains(pid) {
                assert(pid.segment_id == segment_id);
                assert(0 <= pid.idx < count);
                assert(post.pages[pid] == changed_pages[pid]);
                if pid == page_id {
                    assert(post.pages[pid].count == Some(count as nat));
                } else {
                    assert(pre.pages[pid].count.is_none());
                    assert(post.pages[pid].count.is_none());
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.count_off0());
        assert(post.popped_basics());
        assert(post.inv_segment_creating());

        let tail_id = PageId { segment_id, idx: count as nat };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == segment_id
            && count <= pid.idx < SLICES_PER_SEGMENT
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && post.pages[pid].count.is_none()
            && post.pages[pid].dlist_entry.is_none()
            && post.pages[pid].offset.is_none()
        by {
            assert(!changed_pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
            assert(pid.idx <= SLICES_PER_SEGMENT);
        };
        assert(post.pages.dom().contains(tail_id));
        assert(post.pages[tail_id].offset.is_none());
        assert(post.pages[tail_id].count.is_none());
        assert(tail_id.idx + (SLICES_PER_SEGMENT - count) <= SLICES_PER_SEGMENT);
        assert(post.good_range_very_unready(tail_id));
        assert(post.inv_very_unready());

        assert(post.attached_rec(segment_id, SLICES_PER_SEGMENT as int, false));
        assert(post.attached_rec(segment_id, count, true));
        reveal(State::good_range0);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == segment_id
            && page_id.idx <= pid.idx < page_id.idx + count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == page_id)
            && post.pages[pid].dlist_entry.is_none()
            && post.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
        by {
            assert(changed_pages.dom().contains(pid));
            assert(post.pages[pid] == changed_pages[pid]);
            if pid == page_id {
                assert(post.pages[pid].count == Some(count as nat));
            } else {
                assert(pre.pages[pid].count.is_none());
            }
            assert(pre.pages[pid].dlist_entry.is_none());
        };
        assert(post.good_range0(segment_id));
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        assert(post.attached_rec0(segment_id, true));
        assert(post.attached_ranges_segment(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(post.inv_segment_freeing());
        assert(post.inv_ready());
        assert(post.inv_used());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(post.pages[pid] == changed_pages[pid]);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if changed_pages.dom().contains(pid) {
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        assert(post.ready_popped_not_in_unused_lists());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
        implies
            post.pages[pid].dlist_entry.is_some()
            && post.pages[pid].full.is_some()
            && (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
        by {
            if pid.segment_id == segment_id {
                if changed_pages.dom().contains(pid) {
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pid.idx <= SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].is_used == false);
                }
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.data_for_used_header());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if pid.segment_id == segment_id {
                if changed_pages.dom().contains(pid) {
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pid.idx <= SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].is_used == false);
                }
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
            }
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) => is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if pid.segment_id == segment_id {
                if changed_pages.dom().contains(pid) {
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pid.idx <= SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].is_used == false);
                }
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_valid_used2());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if pid.segment_id == segment_id {
                if changed_pages.dom().contains(pid) {
                    assert(post.pages[pid] == changed_pages[pid]);
                    assert(0 <= pid.idx < count);
                    assert(post.pages[pid].offset == Some(pid.idx as nat));
                    assert(pid.idx != 0);
                    assert(pid.idx as nat != 0nat);
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pid.idx <= SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].offset.is_none());
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(is_in_lls(pid, pre.unused_lists));
            }
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId|
            pid.segment_id == segment_id
        implies
            !post.does_count(pid)
        by {
            reveal(State::does_count);
            if post.pages.dom().contains(pid) {
                if changed_pages.dom().contains(pid) {
                    assert(post.pages[pid] == changed_pages[pid]);
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pid.idx <= SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].is_used == false);
                }
            }
        };
        post.ucount_eq0(segment_id);
        assert forall |pid: PageId| #![all_triggers] pid.segment_id != segment_id implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
        by {
            assert(!changed_pages.dom().contains(pid));
            if pre.pages.dom().contains(pid) || post.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::ucount_preserve_except(pre, post, segment_id);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            if sid == segment_id {
                assert(post.segments[sid].used == 1);
                assert(post.ucount(sid) == 0);
                assert(post.popped_ec(sid) == 1);
            } else {
                assert(pre.segments.dom().contains(sid));
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(post.ucount(sid) == pre.ucount(sid));
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
                assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
            }
        };
        assert(post.count_is_right());
    }

    #[verifier::spinoff_prover]
    #[inductive(free_to_unused_queue)]
    fn free_to_unused_queue_inductive(pre: Self, post: Self, sbin_idx: int) {
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        reveal(State::good_range_very_unready);
        reveal(State::attached_ranges);
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);

        pre.very_unready_popped_range_facts();
        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let ec = pre.popped.get_VeryUnready_3();
        let first_page = PageId { segment_id, idx: start as nat };
        let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };
        assert(pre.popped == Popped::VeryUnready(segment_id, start, count, ec));
        assert(post.popped == if ec { Popped::ExtraCount(segment_id) } else { Popped::No });
        assert(post.popped_basics());
        assert(post.inv_very_unready());
        pre.attached_ranges_very_unready_start();
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        assert(pre.attached_ranges_segment(segment_id));
        assert(pre.attached_rec0(segment_id, true));
        let first_id0 = PageId { segment_id, idx: 0 };
        let first_count0 = pre.pages[first_id0].count.unwrap();
        assert(pre.good_range0(segment_id));
        assert(pre.attached_rec(segment_id, first_count0 as int, true));
        Self::rec_attached_to_very_unready_start(pre, first_count0 as int, true);
        assert(first_count0 <= start);
        Self::rec_free_to_unused_queue(pre, post, sbin_idx, first_count0 as int, true);
        assert(post.attached_rec(segment_id, first_count0 as int, false));
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            ({
                let first_count0 = pre.pages[first_id0].count.unwrap();
                pid.segment_id == segment_id
                && first_id0.idx <= pid.idx < first_id0.idx + first_count0
            })
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == first_page || pid == last_page {
                assert(start <= pid.idx);
                assert(pid.idx < first_count0);
                assert(false);
            } else if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let old_first = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                if pid == old_first {
                    reveal(State::ll_inv_valid_unused);
                    reveal(State::valid_unused_page);
                    assert(pre.pages[old_first].dlist_entry.is_some());
                    assert(pre.good_range0(segment_id));
                    reveal(State::good_range0);
                    assert(pre.pages[pid].dlist_entry.is_none());
                    assert(false);
                }
                assert(post.pages.dom().contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            } else {
                assert(post.pages.dom().contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::good_range0_same(pre, post, segment_id);
        assert(post.attached_rec0(segment_id, false));
        assert(post.attached_ranges_segment(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if pid == first_page || pid == last_page {
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                if pid == queue_first_page_id {
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_unused);
                    reveal(State::valid_unused_page);
                    assert(0 <= sbin_idx < pre.unused_lists.len());
                    assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], pre.unused_lists[sbin_idx]));
                    assert(pre.unused_lists[sbin_idx].len() != 0);
                    assert(pre.unused_lists[sbin_idx][0] == queue_first_page_id);
                    assert(pre.valid_unused_page(queue_first_page_id, sbin_idx, 0));
                    assert(pre.pages[queue_first_page_id].is_used == false);
                    assert(false);
                }
                assert(post.pages[pid] == pre.pages[pid]);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        reveal(State::data_for_used_header);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || post.popped.is_ExtraCount()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
        implies
            post.pages[pid].dlist_entry.is_some()
            && post.pages[pid].full.is_some()
            && (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, size)) =>
                    valid_bin_idx(bin)
                    && size == size_of_bin(bin)
                    && bin == smallest_bin_fitting_size(size)
                    && size <= MEDIUM_OBJ_SIZE_MAX,
                None => false,
            })
        by {
            if pid.segment_id == segment_id && start <= pid.idx < start + count {
                if pid == first_page || pid == last_page {
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pre.pages[pid].is_used == false);
                }
                assert(false);
            } else {
                if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                    if pid == queue_first_page_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(post.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                assert(post.pages[pid] == pre.pages[pid]);
                reveal(State::in_popped_range);
                assert(!pre.in_popped_range(pid));
            }
        };
        assert(post.data_for_used_header());
        reveal(State::ll_inv_valid_used2);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || post.popped.is_ExtraCount()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if pid.segment_id == segment_id && start <= pid.idx < start + count {
                if pid == first_page || pid == last_page {
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pre.pages[pid].is_used == false);
                }
                assert(false);
            } else {
                if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                    if pid == queue_first_page_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(post.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                assert(post.pages[pid] == pre.pages[pid]);
                reveal(State::in_popped_range);
                assert(!pre.in_popped_range(pid));
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
                assert(post.used_lists == pre.used_lists);
            }
        };
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || post.popped.is_ExtraCount()
                || ((post.popped.is_Ready() || post.popped.is_VeryUnready())
                    && !post.in_popped_range(pid))
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if pid.segment_id == segment_id && start <= pid.idx < start + count {
                if pid == first_page || pid == last_page {
                    assert(post.pages[pid].is_used == false);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(pre.pages[pid].is_used == false);
                }
                assert(false);
            } else {
                if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                    if pid == queue_first_page_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(post.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                assert(post.pages[pid] == pre.pages[pid]);
                reveal(State::in_popped_range);
                assert(!pre.in_popped_range(pid));
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, _)) => {
                        assert(is_in_list_at(pid, pre.used_lists, bin));
                        assert(post.used_lists == pre.used_lists);
                    }
                    None => { assert(false); }
                }
            }
        };
        assert(post.ll_inv_valid_used2());

        Self::free_to_unused_queue_ll_inv_valid_unused(pre, post, sbin_idx);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());
        Self::free_to_unused_queue_ll_inv_exists_in_some_list(pre, post, sbin_idx);
        assert(post.ll_inv_exists_in_some_list());
        reveal(State::ll_inv_valid_unused2);
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            if pid == first_page {
                assert(pre.pages[pid].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else if pid == last_page {
                assert(pre.pages[pid].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else {
                if pre.unused_dlist_headers[sbin_idx].first.is_some() {
                    let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                    if pid == queue_first_page_id {
                        assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                        assert(post.pages[pid].offset == pre.pages[pid].offset);
                    }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        };
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            assert(post.segments == pre.segments);
            if sid == segment_id {
                if ec {
                    assert(pre.popped_ec(sid) == 1);
                    assert(post.popped_ec(sid) == 1);
                } else {
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == 0);
                }
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
        };
        Self::count_is_right_preserve_all(pre, post);
        assert(post.count_is_right());
    }

    pub proof fn free_to_unused_queue_good_range_unused(
        pre: Self, post: Self, sbin_idx: int
    )
      requires
          pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
      ensures
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let start = pre.popped.get_VeryUnready_1();
              let first_page = PageId { segment_id, idx: start as nat };
              post.good_range_unused(first_page)
          }),
    {
        reveal(State::good_range_unused);
        pre.very_unready_popped_range_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let first_page = PageId { segment_id, idx: start as nat };
        let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };

        assert(pre.popped == Popped::VeryUnready(segment_id, start, count, pre.popped.get_VeryUnready_3()));
        assert(first_page.idx == start);
        assert(count > 0);
        assert(first_page.idx + count <= SLICES_PER_SEGMENT);
        assert(last_page.idx == first_page.idx + count - 1);
        assert(post.pages[first_page].count == Some(count as nat));
        assert(post.pages[first_page].offset == Some(0nat));
        assert(post.pages[first_page].dlist_entry.is_some());
        assert(post.pages[first_page].is_used == false);
        assert(post.pages[first_page].full.is_none());
        assert(post.pages[first_page].page_header_kind.is_none());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == first_page.segment_id
            && first_page.idx <= pid.idx < first_page.idx + count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == first_page)
            && (post.pages[pid].dlist_entry.is_some() <==> pid == first_page)
            && post.pages[pid].offset == (if pid == first_page || pid == last_page {
                    Some((pid.idx - first_page.idx) as nat)
                } else {
                    None
                })
        by {
            assert(pid.segment_id == segment_id);
            assert(start <= pid.idx < start + count);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == false);
            assert(pre.pages[pid].full.is_none());
            assert(pre.pages[pid].page_header_kind.is_none());
            assert(pre.pages[pid].count.is_none());
            assert(pre.pages[pid].dlist_entry.is_none());
            assert(pre.pages[pid].offset.is_none());
            if pid == first_page {
                assert(post.pages[pid].count == Some(count as nat));
                assert(post.pages[pid].offset == Some(0nat));
                assert(post.pages[pid].dlist_entry.is_some());
            } else if pid == last_page {
                if count > 1 {
                    assert(post.pages[pid].offset == Some((count - 1) as nat));
                    assert(pid.idx - first_page.idx == count - 1);
                } else {
                    assert(pid == first_page);
                    assert(false);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.good_range_unused(first_page));
    }

    pub proof fn free_to_unused_queue_preserves_good_range_unused(
        pre: Self, post: Self, sbin_idx: int, cur: PageId
    )
      requires
          pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
          pre.good_range_unused(cur),
          cur.segment_id == pre.popped.get_VeryUnready_0(),
      ensures
          ({
              let start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let cur_count = pre.pages[cur].count.unwrap();
              start + old_count <= cur.idx || cur.idx + cur_count <= start
          }) ==> post.good_range_unused(cur),
          ({
              let start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let cur_count = pre.pages[cur].count.unwrap();
              start + old_count <= cur.idx || cur.idx + cur_count <= start
          }) ==> post.pages[cur].count == pre.pages[cur].count,
          ({
              let start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let cur_count = pre.pages[cur].count.unwrap();
              start + old_count <= cur.idx || cur.idx + cur_count <= start
          }) ==> post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        let start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let cur_count = pre.pages[cur].count.unwrap();
        if start + old_count <= cur.idx || cur.idx + cur_count <= start {
            reveal(State::good_range_unused);
            pre.very_unready_popped_range_facts();
            pre.good_range_disjoint_very_unready(cur);

            let segment_id = pre.popped.get_VeryUnready_0();
            let first_page = PageId { segment_id, idx: start as nat };
            let last_page = PageId { segment_id, idx: (first_page.idx + old_count - 1) as nat };
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].is_used == pre.pages[cur].is_used);
            assert(post.pages[cur].offset == pre.pages[cur].offset);
            assert(post.pages[cur].full == pre.pages[cur].full);
            assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);

            assert forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                pid.segment_id == cur.segment_id
                && cur.idx <= pid.idx < cur.idx + cur_count
            implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && (post.pages[pid].count.is_some() <==> pid == cur)
                && (post.pages[pid].dlist_entry.is_some() <==> pid == cur)
                && post.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                        Some((pid.idx - cur.idx) as nat)
                    } else {
                        None
                    })
            by {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used == false);
                assert(pre.pages[pid].full.is_none());
                assert(pre.pages[pid].page_header_kind.is_none());
                assert(pre.pages[pid].count.is_some() <==> pid == cur);
                assert(pre.pages[pid].dlist_entry.is_some() <==> pid == cur);
                assert(pre.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + pre.pages[cur].count.unwrap() - 1) as nat }) {
                        Some((pid.idx - cur.idx) as nat)
                    } else {
                        None
                    }));
                if pid == first_page || pid == last_page {
                    assert(start <= pid.idx < start + old_count);
                    assert(false);
                } else {
                    assert(post.pages[pid].count == pre.pages[pid].count);
                    assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                    assert(post.pages[pid].full == pre.pages[pid].full);
                    assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                    assert(post.pages[pid].offset == pre.pages[pid].offset);
                    if post.pages[pid].dlist_entry != pre.pages[pid].dlist_entry {
                        assert(pre.unused_dlist_headers[sbin_idx].first.is_some());
                        let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                        assert(pid == queue_first_page_id);
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pid == cur);
                    }
                }
                assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
            };
            assert(post.good_range_unused(cur));
        }
    }

    pub proof fn free_to_unused_queue_preserves_good_range_used(
        pre: Self, post: Self, sbin_idx: int, cur: PageId
    )
      requires
          pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
          pre.good_range_used(cur),
          cur.segment_id == pre.popped.get_VeryUnready_0(),
      ensures
          ({
              let start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let cur_count = pre.pages[cur].count.unwrap();
              start + old_count <= cur.idx || cur.idx + cur_count <= start
          }) ==> post.good_range_used(cur),
          ({
              let start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let cur_count = pre.pages[cur].count.unwrap();
              start + old_count <= cur.idx || cur.idx + cur_count <= start
          }) ==> post.pages[cur].count == pre.pages[cur].count,
          ({
              let start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let cur_count = pre.pages[cur].count.unwrap();
              start + old_count <= cur.idx || cur.idx + cur_count <= start
          }) ==> post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        let start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let cur_count = pre.pages[cur].count.unwrap();
        if start + old_count <= cur.idx || cur.idx + cur_count <= start {
            reveal(State::good_range_used);
            pre.very_unready_popped_range_facts();
            pre.good_range_disjoint_very_unready(cur);

            let segment_id = pre.popped.get_VeryUnready_0();
            let first_page = PageId { segment_id, idx: start as nat };
            let last_page = PageId { segment_id, idx: (first_page.idx + old_count - 1) as nat };
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].is_used == pre.pages[cur].is_used);
            assert(post.pages[cur].offset == pre.pages[cur].offset);
            assert(post.pages[cur].full == pre.pages[cur].full);
            assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);
            assert(post.pages[cur].dlist_entry.is_some() == pre.pages[cur].dlist_entry.is_some());

            assert forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                pid.segment_id == cur.segment_id
                && cur.idx <= pid.idx < cur.idx + cur_count
            implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == true
                && post.pages[pid].offset == Some((pid.idx - cur.idx) as nat)
                && (post.pages[pid].page_header_kind.is_some() <==> pid == cur)
                && (pid != cur ==> post.pages[pid].dlist_entry.is_none())
                && (pid != cur ==> post.pages[pid].full.is_none())
            by {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used == true);
                assert(pre.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
                assert(pre.pages[pid].page_header_kind.is_some() <==> pid == cur);
                assert(pid != cur ==> pre.pages[pid].dlist_entry.is_none());
                assert(pid != cur ==> pre.pages[pid].full.is_none());
                if pid == first_page || pid == last_page {
                    assert(start <= pid.idx < start + old_count);
                    assert(false);
                } else {
                    assert(post.pages[pid].count == pre.pages[pid].count);
                    assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                    assert(post.pages[pid].full == pre.pages[pid].full);
                    assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                    assert(post.pages[pid].offset == pre.pages[pid].offset);
                    if post.pages[pid].dlist_entry != pre.pages[pid].dlist_entry {
                        assert(pre.unused_dlist_headers[sbin_idx].first.is_some());
                        let queue_first_page_id = pre.unused_dlist_headers[sbin_idx].first.unwrap();
                        assert(pid == queue_first_page_id);
                        assert(pre.pages[pid].is_used == false);
                        assert(pre.pages[pid].is_used == true);
                        assert(false);
                    }
                }
            };
            assert(post.good_range_used(cur));
        }
    }

    pub proof fn free_to_unused_queue_new_ids_not_old_unused_list_entry(
        pre: Self, post: Self, sbin_idx: int, i: int, j: int
    )
      requires
          pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
          0 <= i < pre.unused_lists.len(),
          0 <= j < pre.unused_lists[i].len(),
      ensures
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let start = pre.popped.get_VeryUnready_1();
              let count = pre.popped.get_VeryUnready_2();
              let first_page = PageId { segment_id, idx: start as nat };
              let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };
              pre.unused_lists[i][j] != first_page && pre.unused_lists[i][j] != last_page
          }),
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        pre.very_unready_popped_range_facts();
        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let first_page = PageId { segment_id, idx: start as nat };
        let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };
        let pid = pre.unused_lists[i][j];
        assert(pre.valid_unused_page(pid, i, j));
        assert(pre.pages[pid].count.is_some());
        if pid == first_page {
            assert(start <= first_page.idx < start + count);
            assert(pre.pages[first_page].count.is_none());
            assert(false);
        }
        if pid == last_page {
            assert(start <= last_page.idx < start + count);
            assert(pre.pages[last_page].count.is_none());
            assert(false);
        }
    }

    pub proof fn free_to_unused_queue_ll_inv_valid_unused(
        pre: Self, post: Self, sbin_idx: int
    )
      requires
          pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
      ensures
          post.ll_inv_valid_unused(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        pre.very_unready_popped_range_facts();
        Self::free_to_unused_queue_good_range_unused(pre, post, sbin_idx);

        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let first_page = PageId { segment_id, idx: start as nat };
        let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };
        let old_ll = pre.unused_lists[sbin_idx];
        let new_ll = old_ll.insert(0, first_page);
        old_ll.insert_ensures(0, first_page);
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(post.unused_lists =~= Self::insert_front(pre.unused_lists, sbin_idx, first_page));
        assert(post.unused_lists[sbin_idx] =~= new_ll);
        assert(post.pages[first_page].count == Some(count as nat));
        assert(post.pages[first_page].offset == Some(0nat));
        assert(post.pages[first_page].dlist_entry.is_some());

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            if i == sbin_idx {
                assert(post.unused_lists[i] =~= new_ll);
                assert(post.unused_dlist_headers[i].first == Some(first_page));
                if old_ll.len() == 0 {
                    assert(new_ll.len() == 1);
                    assert(post.unused_dlist_headers[i].last == Some(first_page));
                } else {
                    assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                    assert(post.pages[old_ll[0]].dlist_entry.unwrap().prev == Some(first_page));
                    assert(post.unused_dlist_headers[i].last == pre.unused_dlist_headers[i].last);
                    assert(pre.unused_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                    assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                }

                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    if j == 0 {
                        assert(post.unused_lists[i][j] == first_page);
                        assert(post.pages[first_page].dlist_entry.unwrap().prev == None);
                        if old_ll.len() == 0 {
                            assert(get_next(post.unused_lists[i], j) == None);
                            assert(post.pages[first_page].dlist_entry.unwrap().next == None);
                        } else {
                            assert(post.unused_lists[i][1] == old_ll[0]);
                            assert(get_next(post.unused_lists[i], j) == Some(old_ll[0]));
                            assert(post.pages[first_page].dlist_entry.unwrap().next == pre.unused_dlist_headers[i].first);
                            assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                        }
                    } else {
                        let old_j = j - 1;
                        assert(0 <= old_j < old_ll.len());
                        assert(post.unused_lists[i][j] == old_ll[old_j]);
                        let pid = post.unused_lists[i][j];
                        Self::free_to_unused_queue_new_ids_not_old_unused_list_entry(
                            pre, post, sbin_idx, sbin_idx, old_j);
                        assert(pid != first_page);
                        assert(pid != last_page);
                        assert(valid_ll_i(pre.pages, old_ll, old_j));
                        if old_j == 0 {
                            assert(pre.unused_dlist_headers[i].first == Some(pid));
                            assert(post.pages[pid].dlist_entry.unwrap().prev == Some(first_page));
                            assert(get_prev(post.unused_lists[i], j) == Some(first_page));
                        } else {
                            let old_first = old_ll[0];
                            pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, 0);
                            assert(pid != old_first);
                            assert(post.pages[pid] == pre.pages[pid]);
                            assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                            assert(get_prev(post.unused_lists[i], j) == get_prev(old_ll, old_j));
                        }
                        assert(get_next(post.unused_lists[i], j) == get_next(old_ll, old_j));
                    }
                };
            } else {
                assert(post.unused_lists[i] == pre.unused_lists[i]);
                assert(post.unused_dlist_headers[i] == pre.unused_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let pid = post.unused_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                    Self::free_to_unused_queue_new_ids_not_old_unused_list_entry(
                        pre, post, sbin_idx, i, j);
                    assert(pid != first_page);
                    assert(pid != last_page);
                    if old_ll.len() != 0 {
                        let old_first = old_ll[0];
                        if pid == old_first {
                            pre.ll_unused_distinct(i, j, sbin_idx, 0);
                            assert(false);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                };
            }
        };

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists.index(i).index(j) == post.unused_lists.index(i).index(j)
        implies
            ({
                let pid = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(pid)
                &&& pid.idx != 0
                &&& post.pages[pid].is_used == false
                &&& (match post.pages[pid].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[pid].offset == Some(0nat)
                &&& post.pages[pid].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == pid
                &&& post.valid_unused_page(post.unused_lists[i][j], i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[pid].count.unwrap() as int)
            })
        by {
            let pid = post.unused_lists[i][j];
            if i == sbin_idx && j == 0 {
                assert(pid == first_page);
                assert(0 <= sbin_idx <= SEGMENT_BIN_MAX);
                assert(post.pages[pid].count == Some(count as nat));
                assert(post.pages[pid].offset == Some(0nat));
                assert(post.pages[pid].dlist_entry.is_some());
                assert(sbin_idx == smallest_sbin_fitting_size(count));
                assert(post.valid_unused_page(pid, i, j));
            } else {
                let old_j = if i == sbin_idx { j - 1 } else { j };
                if i == sbin_idx {
                    assert(j > 0);
                    assert(0 <= old_j < old_ll.len());
                    assert(pid == old_ll[old_j]);
                    Self::free_to_unused_queue_new_ids_not_old_unused_list_entry(
                        pre, post, sbin_idx, sbin_idx, old_j);
                } else {
                    assert(pid == pre.unused_lists[i][j]);
                    Self::free_to_unused_queue_new_ids_not_old_unused_list_entry(
                        pre, post, sbin_idx, i, j);
                    if old_ll.len() != 0 {
                        let old_first = old_ll[0];
                        if pid == old_first {
                            pre.ll_unused_distinct(i, j, sbin_idx, 0);
                            assert(false);
                        }
                    }
                }
                assert(pid != first_page);
                assert(pid != last_page);
                assert(pre.valid_unused_page(pid, i, old_j));
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
                assert(post.pages[pid].dlist_entry.is_some());
                assert(post.valid_unused_page(pid, i, j));
            }
        };
        assert(post.ll_inv_valid_unused());
    }

    pub proof fn free_to_unused_queue_ll_inv_exists_in_some_list(
        pre: Self, post: Self, sbin_idx: int
    )
      requires
          pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        pre.very_unready_popped_range_facts();
        Self::free_to_unused_queue_ll_inv_valid_unused(pre, post, sbin_idx);

        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        let first_page = PageId { segment_id, idx: start as nat };
        let last_page = PageId { segment_id, idx: (first_page.idx + count - 1) as nat };
        let old_ll = pre.unused_lists[sbin_idx];
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(post.unused_lists =~= Self::insert_front(pre.unused_lists, sbin_idx, first_page));
        assert(post.unused_lists[sbin_idx][0] == first_page);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if pid == first_page {
                assert(post.pages[pid].count == Some(count as nat));
                assert(is_in_lls(pid, post.unused_lists));
            } else if pid == last_page {
                if count > 1 {
                    assert(post.pages[pid].offset == Some((count - 1) as nat));
                    assert(count - 1 > 0);
                    assert(post.pages[pid].offset != Some(0nat));
                    assert(false);
                } else {
                    assert(pid == first_page);
                    assert(false);
                }
            } else if pid.segment_id == segment_id
                && start <= pid.idx < start + count
            {
                assert(post.pages[pid].offset.is_none());
                assert(post.pages[pid].offset != Some(0nat));
                assert(false);
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(!pre.in_popped_range(pid));
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(pre.pages[pid].count.is_some());
                assert(is_in_lls(pid, pre.unused_lists));
                reveal(State::get_list_idx);
                let pair = Self::get_list_idx(pre.unused_lists, pid);
                let i = pair.0;
                let j = pair.1;
                assert(0 <= i < pre.unused_lists.len());
                assert(0 <= j < pre.unused_lists[i].len());
                assert(pre.unused_lists[i][j] == pid);
                Self::ll_insert_front_preserves_list_at(
                    pre.unused_lists, post.unused_lists, sbin_idx, first_page, pid, i);
                assert(is_in_list_at(pid, post.unused_lists, i));
                assert(is_in_lls(pid, post.unused_lists));
            }
        };
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            if i == sbin_idx && j == 0 {
                assert(pid == first_page);
                assert(post.pages[pid].count == Some(count as nat));
                assert(sbin_idx == smallest_sbin_fitting_size(count));
            } else {
                let old_j = if i == sbin_idx { j - 1 } else { j };
                if i == sbin_idx {
                    assert(j > 0);
                    assert(0 <= old_j < old_ll.len());
                    assert(pid == old_ll[old_j]);
                    Self::free_to_unused_queue_new_ids_not_old_unused_list_entry(
                        pre, post, sbin_idx, sbin_idx, old_j);
                } else {
                    assert(pid == pre.unused_lists[i][j]);
                    Self::free_to_unused_queue_new_ids_not_old_unused_list_entry(
                        pre, post, sbin_idx, i, j);
                }
                assert(pid != first_page);
                assert(pid != last_page);
                assert(pre.valid_unused_page(pid, i, old_j));
                assert(post.pages[pid].count == pre.pages[pid].count);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
    }

    pub proof fn rec_free_to_unused_queue(pre: Self, post: Self, sbin_idx: int, idx: int, sp: bool)
      requires pre.invariant(),
          State::free_to_unused_queue_strong(pre, post, sbin_idx),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, false)
      decreases SLICES_PER_SEGMENT - idx
    {
       reveal(State::attached_rec);
       reveal(State::is_the_popped);
       reveal(State::popped_len);
       reveal(State::page_id_of_popped);
       reveal(State::good_range_unused);
       reveal(State::good_range_used);

       pre.very_unready_popped_range_facts();
       let segment_id = pre.popped.get_VeryUnready_0();
       let start = pre.popped.get_VeryUnready_1();
       let old_count = pre.popped.get_VeryUnready_2();
       let ec = pre.popped.get_VeryUnready_3();
       let first_page = PageId { segment_id, idx: start as nat };
       assert(pre.popped == Popped::VeryUnready(segment_id, start, old_count, ec));
       assert(post.popped == if ec { Popped::ExtraCount(segment_id) } else { Popped::No });
       assert(first_page.idx == start);
       assert(old_count > 0);
       assert(start + old_count <= SLICES_PER_SEGMENT);

       if idx == SLICES_PER_SEGMENT {
           assert(post.attached_rec(segment_id, idx, false));
       } else if idx > SLICES_PER_SEGMENT {
           assert(!pre.attached_rec(segment_id, idx, sp));
           assert(false);
       } else if Self::is_the_popped(segment_id, idx, pre.popped) {
           assert(idx == start);
           assert(sp);
           assert(pre.attached_rec(segment_id, start + old_count, false));
           Self::rec_free_to_unused_queue(pre, post, sbin_idx, start + old_count, false);
           assert(post.attached_rec(segment_id, start + old_count, false));
           Self::free_to_unused_queue_good_range_unused(pre, post, sbin_idx);
           assert(post.good_range_unused(first_page));
           assert(post.pages[first_page].count == Some(old_count as nat));
           assert(post.pages[first_page].count.unwrap() == old_count);
           assert(!Self::is_the_popped(segment_id, idx, post.popped));
           assert(post.attached_rec(segment_id, idx, false));
       } else {
           let cur = PageId { segment_id, idx: idx as nat };
           let count = pre.pages[cur].count.unwrap();
           assert(count > 0);
           assert(idx + count <= SLICES_PER_SEGMENT);
           assert(pre.attached_rec(segment_id, idx + count, sp));
           if pre.pages[cur].is_used {
               assert(pre.good_range_used(cur));
               pre.good_range_disjoint_very_unready(cur);
               assert(start + old_count <= cur.idx || cur.idx + count <= start);
               Self::free_to_unused_queue_preserves_good_range_used(pre, post, sbin_idx, cur);
               assert(post.pages[cur].is_used);
               assert(post.good_range_used(cur));
           } else {
               assert(pre.good_range_unused(cur));
               pre.good_range_disjoint_very_unready(cur);
               assert(start + old_count <= cur.idx || cur.idx + count <= start);
               Self::free_to_unused_queue_preserves_good_range_unused(pre, post, sbin_idx, cur);
               assert(!post.pages[cur].is_used);
               assert(post.good_range_unused(cur));
           }
           assert(post.pages[cur].count == pre.pages[cur].count);
           assert(post.pages[cur].count.unwrap() == count);
           Self::rec_free_to_unused_queue(pre, post, sbin_idx, idx + count, sp);
           assert(!Self::is_the_popped(segment_id, idx, post.popped));
           assert(post.attached_rec(segment_id, idx + count, false));
           assert(post.attached_rec(segment_id, idx, false));
       }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        reveal(State::ll_basics);
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::end_is_unused);
        reveal(State::count_is_right);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_inv_valid_used);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::attached_ranges);
        reveal(State::does_count);

        assert(post.ll_basics());
        assert(post.page_id_domain());
        assert(post.count_off0());
        assert(post.end_is_unused());
        assert(post.count_is_right());
        assert(post.popped_basics());
        assert(post.inv_segment_creating());
        assert(post.inv_very_unready());
        assert(post.inv_segment_freeing());
        assert(post.inv_ready());
        assert(post.inv_used());
        assert(post.attached_ranges());

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(post.unused_lists[i].len() == 0);
            assert(post.unused_dlist_headers[i].first == None);
            assert(post.unused_dlist_headers[i].last == None);
        };
        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
        implies
            ({
                let page_id = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(page_id)
                &&& page_id.idx != 0
                &&& post.pages[page_id].is_used == false
                &&& (match post.pages[page_id].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[page_id].offset == Some(0nat)
                &&& post.pages[page_id].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == page_id
                &&& post.valid_unused_page(page_id, i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[page_id].count.unwrap() as int)
            })
        by {
            assert(post.unused_lists[i].len() == 0);
            assert(false);
        };
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());

        assert forall |i: int|
            #![trigger post.used_dlist_headers.index(i)]
            0 <= i < post.used_lists.len()
        implies
            valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            assert(post.used_lists[i].len() == 0);
            assert(post.used_dlist_headers[i].first == None);
            assert(post.used_dlist_headers[i].last == None);
        };
        assert forall |i: int, j: int|
            0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len()
            && #[trigger] post.used_lists[i][j] == post.used_lists[i][j]
        implies
            ({
                let page_id = post.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& post.valid_used_page(page_id, i, j)
                &&& post.pages[page_id].count.is_some()
                &&& (post.popped.is_Ready() ==> page_id != post.popped_page_id())
            })
        by {
            assert(post.used_lists[i].len() == 0);
            assert(false);
        };
        assert(post.ll_inv_valid_used());
        assert(post.data_for_used_header());
        assert(post.ready_popped_not_in_unused_lists());
        assert(post.ll_inv_valid_used2());
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());
    }

    #[verifier::spinoff_prover]
    #[inductive(out_of_used_list)]
    fn out_of_used_list_inductive(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int) {
        reveal(State::inv_used);
        reveal(State::good_range_used);
        reveal(State::attached_ranges);
        reveal(State::popped_basics);
        reveal(State::count_off0);
        reveal(State::valid_used_page);
        assert(post.popped == Popped::Used(page_id, true));
        assert(pre.valid_used_page(page_id, bin_idx, list_idx));
        reveal(State::ll_basics);
        pre.used_ll_stuff(bin_idx, list_idx);
        assert(pre.pages[page_id].count.is_some());
        let count = pre.pages[page_id].count.unwrap();
        assert(1 <= count);
        assert(page_id.idx + count <= SLICES_PER_SEGMENT);
        assert(page_id.idx != 0);
        assert(post.pages[page_id].count == pre.pages[page_id].count);
        assert(post.pages[page_id].offset == Some(0nat));
        assert(post.pages[page_id].is_used);
        assert(post.pages.dom().contains(page_id));
        assert(post.popped_basics());
        pre.used_header_has_good_range(page_id);
        assert(pre.good_range_used(page_id));
        reveal(State::good_range_used);
        assert forall |q: PageId|
            #![trigger post.pages.dom().contains(q)]
            #![trigger post.pages.index(q)]
            q.segment_id == page_id.segment_id
            && page_id.idx <= q.idx < page_id.idx + count
        implies
            post.pages.dom().contains(q)
            && post.pages[q].is_used == true
            && post.pages[q].offset == Some((q.idx - page_id.idx) as nat)
            && (post.pages[q].page_header_kind.is_some() <==> q == page_id)
            && (q != page_id ==> post.pages[q].dlist_entry.is_none())
            && (q != page_id ==> post.pages[q].full.is_none())
        by {
            assert(pre.pages.dom().contains(q));
            assert(pre.pages[q].is_used == true);
            assert(pre.pages[q].offset == Some((q.idx - page_id.idx) as nat));
            assert(pre.pages[q].page_header_kind.is_some() <==> q == page_id);
            assert(q != page_id ==> pre.pages[q].dlist_entry.is_none());
            assert(q != page_id ==> pre.pages[q].full.is_none());
            if q == page_id {
                assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
            } else {
                let removed_entry = pre.pages[page_id].dlist_entry.unwrap();
                match removed_entry.prev {
                    Some(prev_id) => {
                        if q == prev_id {
                            assert(pre.pages[q].dlist_entry.is_some());
                            assert(pre.pages[q].dlist_entry.is_none());
                            assert(false);
                        }
                    }
                    None => { }
                }
                match removed_entry.next {
                    Some(next_id) => {
                        if q == next_id {
                            assert(pre.pages[q].dlist_entry.is_some());
                            assert(pre.pages[q].dlist_entry.is_none());
                            assert(false);
                        }
                    }
                    None => { }
                }
                assert(post.pages[q] == pre.pages[q]);
            }
        }
        assert(post.good_range_used(page_id));
        assert(post.pages[page_id].dlist_entry.is_none());
        assert(post.pages[page_id].full.is_none());
        assert(post.inv_used());
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::in_popped_range);
        assert(pre.attached_ranges_segment(page_id.segment_id));
        assert(pre.attached_rec0(page_id.segment_id, false));
        let first_id0 = PageId { segment_id: page_id.segment_id, idx: 0 };
        let first_count0 = pre.pages[first_id0].count.unwrap();
        assert(pre.good_range0(page_id.segment_id));
        assert(pre.attached_rec(page_id.segment_id, first_count0 as int, false));
        if first_count0 > page_id.idx {
            reveal(State::good_range0);
            assert(first_id0.idx <= page_id.idx < first_id0.idx + first_count0);
            assert(pre.pages[page_id].is_used == false);
            assert(pre.pages[page_id].is_used == true);
            assert(false);
        }
        assert(first_count0 <= page_id.idx);
        let removed_entry0 = pre.pages[page_id].dlist_entry.unwrap();
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == page_id.segment_id
            && first_id0.idx <= pid.idx < first_id0.idx + first_count0
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == page_id {
                assert(page_id.idx < first_count0);
                assert(false);
            }
            match removed_entry0.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        reveal(State::good_range0);
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(false);
                    }
                }
                None => { }
            }
            match removed_entry0.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        reveal(State::good_range0);
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::good_range0_same(pre, post, page_id.segment_id);
        assert(post.good_range0(page_id.segment_id));
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == page_id.segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
                && !post.in_popped_range(pid) ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            assert(pre.popped == Popped::No);
            if pid == page_id {
                assert(post.in_popped_range(pid));
            } else {
                match removed_entry0.prev {
                    Some(prev_id) => {
                        if pid == prev_id {
                            assert(pre.pages[pid].dlist_entry.is_some());
                            assert(post.pages[pid].dlist_entry.is_some());
                            assert(pre.pages[pid].count == post.pages[pid].count);
                            assert(pre.pages[pid].offset == post.pages[pid].offset);
                            assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                            assert(pre.pages[pid].full == post.pages[pid].full);
                            assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                        }
                    }
                    None => { }
                }
                match removed_entry0.next {
                    Some(next_id) => {
                        if pid == next_id {
                            assert(pre.pages[pid].dlist_entry.is_some());
                            assert(post.pages[pid].dlist_entry.is_some());
                            assert(pre.pages[pid].count == post.pages[pid].count);
                            assert(pre.pages[pid].offset == post.pages[pid].offset);
                            assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                            assert(pre.pages[pid].full == post.pages[pid].full);
                            assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                        }
                    }
                    None => { }
                }
                if pid != removed_entry0.prev.unwrap_or(page_id) && pid != removed_entry0.next.unwrap_or(page_id) {
                    assert(post.pages[pid] == pre.pages[pid]);
                }
            }
        };
        Self::attached_rec_no_to_used_popped(pre, post, page_id, first_count0 as int);
        assert(post.attached_rec0(page_id.segment_id, true));
        assert(post.attached_ranges_segment(page_id.segment_id));
        reveal(State::if_popped_or_other_then_for);
        assert(pre.if_popped_or_other_then_for(page_id.segment_id));
        assert(post.if_popped_or_other_then_for(page_id.segment_id));
        assert forall |pid: PageId|
            pid.segment_id != page_id.segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            match removed_entry0.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(post.pages[pid].dlist_entry.is_some());
                        assert(pre.pages[pid].count == post.pages[pid].count);
                        assert(pre.pages[pid].offset == post.pages[pid].offset);
                        assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                        assert(pre.pages[pid].full == post.pages[pid].full);
                        assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                    }
                }
                None => { }
            }
            match removed_entry0.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(post.pages[pid].dlist_entry.is_some());
                        assert(pre.pages[pid].count == post.pages[pid].count);
                        assert(pre.pages[pid].offset == post.pages[pid].offset);
                        assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                        assert(pre.pages[pid].full == post.pages[pid].full);
                        assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                    }
                }
                None => { }
            }
            if pid != removed_entry0.prev.unwrap_or(page_id) && pid != removed_entry0.next.unwrap_or(page_id) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_ranges_except(pre, post, page_id.segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == page_id.segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            assert(pid != page_id);
            let removed_entry = pre.pages[page_id].dlist_entry.unwrap();
            match removed_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].is_used);
                        assert(false);
                    }
                }
                None => { }
            }
            match removed_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].is_used);
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages[pid] == pre.pages[pid]);
        }
        Self::unchanged_unused_ll(pre, post);
        reveal(State::data_for_unused_header);
        assert(post.ll_inv_valid_unused());
        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            if pid == page_id {
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            } else {
                let removed_entry = pre.pages[page_id].dlist_entry.unwrap();
                match removed_entry.prev {
                    Some(prev_id) => {
                        if pid == prev_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                match removed_entry.next {
                    Some(next_id) => {
                        if pid == next_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        }
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            reveal(State::popped_ec);
            reveal(State::ec_of_popped);
            assert(post.segments == pre.segments);
            assert(pre.popped == Popped::No);
            assert(post.popped == Popped::Used(page_id, true));
        }
        Self::count_is_right_preserve_all(pre, post);
        Self::out_of_used_list_inductive_ll_inv_valid_used(pre, post, page_id, bin_idx, list_idx);
        Self::out_of_used_list_inductive_ll_inv_valid_used2(pre, post, page_id, bin_idx, list_idx);
        Self::out_of_used_list_inductive_ll_inv_exists_in_some_list(pre, post, page_id, bin_idx, list_idx);
    }

    proof fn out_of_used_list_inductive_ll_inv_valid_used(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_valid_used(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);

        let old_ll = pre.used_lists[bin_idx];
        let new_ll = old_ll.remove(list_idx);
        old_ll.remove_ensures(list_idx);
        assert(pre.valid_used_page(page_id, bin_idx, list_idx));
        assert(old_ll[list_idx] == page_id);
        assert(pre.pages[page_id].dlist_entry.is_some());
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert(valid_ll(pre.pages, pre.used_dlist_headers[bin_idx], old_ll));
        assert(valid_ll_i(pre.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));
        assert(post.used_lists =~= pre.used_lists.update(bin_idx, new_ll));

        assert forall |i: int|
            #![trigger post.used_dlist_headers.index(i)]
            0 <= i < post.used_lists.len()
        implies
            valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            if i == bin_idx {
                assert(post.used_lists[i] == new_ll);
                if new_ll.len() == 0 {
                    assert(old_ll.len() == 1);
                    assert(list_idx == 0);
                    assert(dlist_entry.prev.is_none());
                    assert(dlist_entry.next.is_none());
                    assert(post.used_dlist_headers[i].first.is_none());
                    assert(post.used_dlist_headers[i].last.is_none());
                } else {
                    if list_idx == 0 {
                        assert(dlist_entry.prev.is_none());
                        assert(dlist_entry.next == Some(old_ll[1]));
                        assert(new_ll[0] == old_ll[1]);
                        assert(post.used_dlist_headers[i].first == Some(new_ll[0]));
                    } else {
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[0] == old_ll[0]);
                        assert(pre.used_dlist_headers[i].first == Some(old_ll[0]));
                        assert(post.used_dlist_headers[i].first == Some(new_ll[0]));
                    }
                    if list_idx == old_ll.len() - 1 {
                        assert(dlist_entry.next.is_none());
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[list_idx - 1]);
                        assert(post.used_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    } else {
                        assert(dlist_entry.next == Some(old_ll[list_idx + 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                        assert(pre.used_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                        assert(post.used_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    }
                }
                assert forall |j: int|
                    0 <= j < post.used_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.used_lists[i], j)
                by {
                    let old_j = if j < list_idx { j } else { j + 1 };
                    assert(0 <= old_j < old_ll.len());
                    assert(old_j != list_idx);
                    assert(post.used_lists[i][j] == old_ll[old_j]);
                    let pid = post.used_lists[i][j];
                    pre.ll_used_distinct(bin_idx, old_j, bin_idx, list_idx);
                    assert(pid != page_id);
                    assert(valid_ll_i(pre.pages, old_ll, old_j));
                    if old_j == list_idx - 1 {
                        assert(j == list_idx - 1);
                        assert(dlist_entry.prev == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().next == dlist_entry.next);
                    } else if old_j == list_idx + 1 {
                        assert(j == list_idx);
                        assert(dlist_entry.next == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().prev == dlist_entry.prev);
                    } else {
                        if dlist_entry.prev.is_some() {
                            let prev_id = dlist_entry.prev.unwrap();
                            assert(list_idx > 0);
                            assert(prev_id == old_ll[list_idx - 1]);
                            assert(pid != prev_id) by {
                                pre.ll_used_distinct(bin_idx, old_j, bin_idx, list_idx - 1);
                            }
                        }
                        if dlist_entry.next.is_some() {
                            let next_id = dlist_entry.next.unwrap();
                            assert(list_idx < old_ll.len() - 1);
                            assert(next_id == old_ll[list_idx + 1]);
                            assert(pid != next_id) by {
                                pre.ll_used_distinct(bin_idx, old_j, bin_idx, list_idx + 1);
                            }
                        }
                        assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                    }
                }
            } else {
                assert(post.used_lists[i] == pre.used_lists[i]);
                assert(post.used_dlist_headers[i] == pre.used_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
                assert forall |j: int|
                    0 <= j < post.used_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.used_lists[i], j)
                by {
                    let pid = post.used_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.used_lists[i], j));
                    pre.ll_used_distinct(i, j, bin_idx, list_idx);
                    assert(pid != page_id);
                    if dlist_entry.prev.is_some() {
                        let prev_id = dlist_entry.prev.unwrap();
                        assert(list_idx > 0);
                        assert(prev_id == old_ll[list_idx - 1]);
                        assert(pid != prev_id) by {
                            pre.ll_used_distinct(i, j, bin_idx, list_idx - 1);
                        }
                    }
                    if dlist_entry.next.is_some() {
                        let next_id = dlist_entry.next.unwrap();
                        assert(list_idx < old_ll.len() - 1);
                        assert(next_id == old_ll[list_idx + 1]);
                        assert(pid != next_id) by {
                            pre.ll_used_distinct(i, j, bin_idx, list_idx + 1);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                }
            }
        }

        assert forall |i: int, j: int|
            0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len()
            && #[trigger] post.used_lists.index(i).index(j) == post.used_lists.index(i).index(j)
        implies
            ({
                let pid = post.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& post.valid_used_page(pid, i, j)
                &&& post.pages[pid].count.is_some()
                &&& (post.popped.is_Ready() ==> pid != post.popped_page_id())
            })
        by {
            let pid = post.used_lists[i][j];
            let old_j = if i == bin_idx {
                if j < list_idx { j } else { j + 1 }
            } else {
                j
            };
            if i == bin_idx {
                assert(0 <= old_j < old_ll.len());
                assert(old_j != list_idx);
                assert(pid == old_ll[old_j]);
                pre.ll_used_distinct(bin_idx, old_j, bin_idx, list_idx);
            } else {
                assert(pid == pre.used_lists[i][j]);
                pre.ll_used_distinct(i, j, bin_idx, list_idx);
            }
            assert(pid != page_id);
            assert(pre.valid_used_page(pid, i, old_j));
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
            assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
            assert(post.pages[pid].dlist_entry.is_some());
            assert(!post.popped.is_Ready());
        }
        assert(post.ll_inv_valid_used());
    }

    proof fn out_of_used_list_inductive_ll_inv_valid_used2(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_valid_used2(),
    {
        reveal(State::ll_inv_valid_used2);
        reveal(State::valid_used_page);
        assert(pre.popped.is_No());
        assert(post.popped == Popped::Used(page_id, true));
        assert(post.used_lists =~= pre.used_lists.update(bin_idx, pre.used_lists[bin_idx].remove(list_idx)));
        assert(pre.valid_used_page(page_id, bin_idx, list_idx));
        assert(pre.used_lists[bin_idx][list_idx] == page_id);
        pre.used_lists[bin_idx].remove_ensures(list_idx);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            assert(pid != page_id);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used);
            assert(pre.pages[pid].offset == Some(0nat));
            assert(pre.pages[pid].full == post.pages[pid].full);
            assert(pre.pages[pid].full != Some(false));
            assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
            Self::ll_remove_preserves_list_at(pre.used_lists, post.used_lists, bin_idx, list_idx, pid, BIN_FULL as int);
            assert(is_in_list_at(pid, post.used_lists, BIN_FULL as int));
        }

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            assert(pid != page_id);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used);
            assert(pre.pages[pid].offset == Some(0nat));
            assert(pre.pages[pid].full == post.pages[pid].full);
            assert(pre.pages[pid].full != Some(true));
            assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
            match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) => {
                    assert(is_in_list_at(pid, pre.used_lists, bin));
                    Self::ll_remove_preserves_list_at(pre.used_lists, post.used_lists, bin_idx, list_idx, pid, bin);
                    assert(is_in_list_at(pid, post.used_lists, bin));
                }
                None => {
                    assert(false);
                }
            }
        }
    }

    proof fn out_of_used_list_inductive_ll_inv_exists_in_some_list(pre: Self, post: Self, page_id: PageId, bin_idx: int, list_idx: int)
        requires pre.invariant(),
          State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx)
        ensures
          post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        assert(post.popped.is_Used());
        assert(post.unused_lists == pre.unused_lists);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(pid != page_id);
            assert(pre.popped.is_No());
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].offset == Some(0nat));
            assert(!pre.pages[pid].is_used);
            assert(pre.pages[pid].count == post.pages[pid].count);
            assert(is_in_lls(pid, pre.unused_lists));
            assert(pre.unused_lists == post.unused_lists);
            assert(is_in_lls(pid, post.unused_lists));
        }

        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(post.unused_lists[i][j] == pre.unused_lists[i][j]);
            assert(pre.pages[pid].is_used == false);
            assert(pid != page_id);
            assert(post.pages[pid].count == pre.pages[pid].count);
        }
    }

    pub proof fn merge_with_after_page_dom(&self)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() + self.popped.get_VeryUnready_2() < SLICES_PER_SEGMENT,
        ensures ({
            let segment_id = self.popped.get_VeryUnready_0();
            let cur_start = self.popped.get_VeryUnready_1();
            let cur_count = self.popped.get_VeryUnready_2();
            let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
            &&& 0 <= cur_start
            &&& 0 <= cur_count
            &&& 0 <= cur_start + cur_count
            &&& page_id.idx < SLICES_PER_SEGMENT
            &&& self.pages.dom().contains(page_id)
        })
    {
        reveal(State::inv_very_unready);
        self.get_count_bound_very_unready();
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let cur_count = self.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        assert(0 <= cur_start);
        assert(0 <= cur_count);
        assert(0 <= cur_start + cur_count);
        assert(page_id.idx < SLICES_PER_SEGMENT);
        let _stuff_after = self.get_stuff_after();
        assert(self.pages.dom().contains(page_id));
    }

    #[verifier::rlimit(200)]
    pub proof fn set_range_to_not_used_page_facts(pre: Self, post: Self)
        requires
            pre.invariant(),
            State::set_range_to_not_used_strong(pre, post),
        ensures ({
            let page_id = pre.popped.get_Used_0();
            let b = pre.popped.get_Used_1();
            let count = pre.pages[page_id].count.unwrap();
            let changed_range = page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count);
            &&& post.pages.dom() =~= pre.pages.dom()
            &&& post.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, b)
            &&& post.segments == pre.segments
            &&& (forall |pid: PageId| #[trigger] changed_range.contains(pid) ==>
                post.pages[pid] == PageData {
                    is_used: false,
                    page_header_kind: None,
                    offset: None,
                    count: None,
                    .. pre.pages[pid]
                })
            &&& (forall |pid: PageId| pre.pages.dom().contains(pid) && !#[trigger] changed_range.contains(pid) ==>
                post.pages[pid] == pre.pages[pid])
        })
    {
        let page_id = pre.popped.get_Used_0();
        let b = pre.popped.get_Used_1();
        pre.used_popped_range_facts();
        let count = pre.pages[page_id].count.unwrap();
        let changed_range = page_id_range(page_id.segment_id, page_id.idx, page_id.idx + count);
        let changed_pages = Map::new(
            changed_range,
            |pid: PageId| PageData {
                is_used: false,
                page_header_kind: None,
                offset: None,
                count: None,
                .. pre.pages[pid]
            }
        );
        let new_pages = pre.pages.union_prefer_right(changed_pages);
        assert(post.pages == new_pages);
        assert(post.popped == Popped::VeryUnready(page_id.segment_id, page_id.idx as int, count as int, b));
        assert(post.segments == pre.segments);
        assert(pre.pages.dom() =~= post.pages.dom()) by {
            vstd::map_lib::lemma_union_dom(pre.pages, changed_pages);
            assert forall |pid: PageId|
                changed_pages.dom().contains(pid) implies pre.pages.dom().contains(pid)
            by {
                assert(pid.segment_id == page_id.segment_id);
                assert(page_id.idx <= pid.idx < page_id.idx + count);
            };
            assert(changed_pages.dom().subset_of(pre.pages.dom()));
            assert(pre.pages.dom().union(changed_pages.dom()) =~= pre.pages.dom());
        };
        assert forall |pid: PageId| #[trigger] changed_range.contains(pid) implies
            post.pages[pid] == PageData {
                is_used: false,
                page_header_kind: None,
                offset: None,
                count: None,
                .. pre.pages[pid]
            }
        by {
            assert(changed_pages.dom().contains(pid));
            assert(new_pages[pid] == changed_pages[pid]);
        };
        assert forall |pid: PageId| pre.pages.dom().contains(pid) && !#[trigger] changed_range.contains(pid) implies
            post.pages[pid] == pre.pages[pid]
        by {
            assert(!changed_pages.dom().contains(pid));
            assert(new_pages[pid] == pre.pages[pid]);
        };
    }

    pub proof fn merge_with_after_page_facts(&self)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() + self.popped.get_VeryUnready_2() < SLICES_PER_SEGMENT,
            ({
                let segment_id = self.popped.get_VeryUnready_0();
                let cur_start = self.popped.get_VeryUnready_1();
                let cur_count = self.popped.get_VeryUnready_2();
                let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                !self.pages[page_id].is_used
            }),
        ensures ({
            let segment_id = self.popped.get_VeryUnready_0();
            let cur_start = self.popped.get_VeryUnready_1();
            let cur_count = self.popped.get_VeryUnready_2();
            let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
            let n_count = self.pages[page_id].count.unwrap();
            let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
            let sbin_idx = smallest_sbin_fitting_size(n_count as int);
            let pair = Self::get_list_idx(self.unused_lists, page_id);
            let list_idx = pair.1;
            &&& self.pages.dom().contains(page_id)
            &&& page_id.idx == cur_start + cur_count
            &&& self.pages[page_id].count.is_some()
            &&& 1 <= n_count <= SLICES_PER_SEGMENT
            &&& cur_count + n_count <= SLICES_PER_SEGMENT
            &&& self.pages[page_id].dlist_entry.is_some()
            &&& self.good_range_unused(page_id)
            &&& 0 <= pair.0 < self.unused_lists.len()
            &&& 0 <= list_idx < self.unused_lists[pair.0].len()
            &&& self.unused_lists[pair.0][list_idx] == page_id
            &&& pair.0 == sbin_idx
            &&& 0 <= sbin_idx <= SEGMENT_BIN_MAX
            &&& 0 <= sbin_idx < self.unused_lists.len()
            &&& 0 <= list_idx < self.unused_lists[sbin_idx].len()
            &&& self.unused_lists[sbin_idx][list_idx] == page_id
            &&& self.valid_unused_page(page_id, sbin_idx, list_idx)
            &&& final_id.segment_id == page_id.segment_id
            &&& final_id.idx == page_id.idx + n_count - 1
            &&& self.pages.dom().contains(final_id)
            &&& self.pages[final_id].is_used == false
        })
    {
        self.merge_with_after_page_dom();
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let cur_count = self.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        assert(page_id.idx == cur_start + cur_count);

        let stuff_after = self.get_stuff_after();
        assert(self.good_range_unused(page_id));
        assert(self.pages[page_id].dlist_entry.is_some());
        reveal(State::good_range_unused);
        assert(self.pages[page_id].count.is_some());
        let n_count = self.pages[page_id].count.unwrap();
        assert(page_id.idx + n_count <= SLICES_PER_SEGMENT);
        assert(cur_count + n_count <= SLICES_PER_SEGMENT);

        reveal(State::get_list_idx);
        let sbin_idx = smallest_sbin_fitting_size(n_count as int);
        let pair = Self::get_list_idx(self.unused_lists, page_id);
        let list_idx = pair.1;
        assert(0 <= stuff_after.0 < self.unused_lists.len());
        assert(0 <= stuff_after.1 < self.unused_lists[stuff_after.0].len());
        assert(self.unused_lists[stuff_after.0][stuff_after.1] == page_id);
        assert(0 <= pair.0 < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[pair.0].len());
        assert(self.unused_lists[pair.0][list_idx] == page_id);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_basics);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx <= SEGMENT_BIN_MAX);
        assert(0 <= sbin_idx < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[sbin_idx].len());
        assert(self.unused_lists[sbin_idx][list_idx] == page_id);
        assert(1 <= n_count <= SLICES_PER_SEGMENT);
        assert(self.valid_unused_page(page_id, sbin_idx, list_idx));

        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
        assert(0 <= cur_start + cur_count + n_count - 1);
        assert(final_id.segment_id == page_id.segment_id);
        assert(final_id.idx == page_id.idx + n_count - 1);
        assert(page_id.idx <= final_id.idx);
        assert(final_id.idx < page_id.idx + n_count);
        assert(self.pages.dom().contains(final_id));
        assert(self.pages[final_id].is_used == false);
    }

    pub proof fn merge_with_after_dlist_facts(&self)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() + self.popped.get_VeryUnready_2() < SLICES_PER_SEGMENT,
            ({
                let segment_id = self.popped.get_VeryUnready_0();
                let cur_start = self.popped.get_VeryUnready_1();
                let cur_count = self.popped.get_VeryUnready_2();
                let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                !self.pages[page_id].is_used
            }),
        ensures ({
            let segment_id = self.popped.get_VeryUnready_0();
            let cur_start = self.popped.get_VeryUnready_1();
            let cur_count = self.popped.get_VeryUnready_2();
            let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
            let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
            &&& (match dlist_entry.prev {
                Some(prev_page_id) =>
                    prev_page_id != page_id
                    && self.pages.dom().contains(prev_page_id)
                    && self.pages[prev_page_id].dlist_entry.is_some()
                    && self.pages[prev_page_id].is_used == false,
                None => true,
            })
            &&& (match dlist_entry.next {
                Some(next_page_id) =>
                    next_page_id != page_id
                    && self.pages.dom().contains(next_page_id)
                    && self.pages[next_page_id].dlist_entry.is_some()
                    && self.pages[next_page_id].is_used == false,
                None => true,
            })
            &&& (dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap())
        })
    {
        self.merge_with_after_page_facts();
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let cur_count = self.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        let n_count = self.pages[page_id].count.unwrap();
        let sbin_idx = smallest_sbin_fitting_size(n_count as int);
        let pair = Self::get_list_idx(self.unused_lists, page_id);
        let list_idx = pair.1;
        let old_ll = self.unused_lists[sbin_idx];
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();

        reveal(State::ll_inv_valid_unused);
        assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(self.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));

        match dlist_entry.prev {
            Some(prev_page_id) => {
                assert(list_idx != 0);
                assert(prev_page_id == old_ll[list_idx - 1]);
                assert(0 <= list_idx - 1 < old_ll.len());
                assert(self.unused_lists[sbin_idx][list_idx - 1] == prev_page_id);
                assert(self.pages.dom().contains(prev_page_id));
                assert(self.pages[prev_page_id].dlist_entry.is_some());
                assert(self.pages[prev_page_id].is_used == false);
                assert(list_idx - 1 != list_idx);
                self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx);
                assert(prev_page_id != page_id);
            }
            None => { }
        }

        match dlist_entry.next {
            Some(next_page_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_page_id == old_ll[list_idx + 1]);
                assert(0 <= list_idx + 1 < old_ll.len());
                assert(self.unused_lists[sbin_idx][list_idx + 1] == next_page_id);
                assert(self.pages.dom().contains(next_page_id));
                assert(self.pages[next_page_id].dlist_entry.is_some());
                assert(self.pages[next_page_id].is_used == false);
                assert(list_idx + 1 != list_idx);
                self.ll_unused_distinct(sbin_idx, list_idx + 1, sbin_idx, list_idx);
                assert(next_page_id != page_id);
            }
            None => { }
        }

        if dlist_entry.prev.is_some() && dlist_entry.next.is_some() {
            let prev_page_id = dlist_entry.prev.unwrap();
            let next_page_id = dlist_entry.next.unwrap();
            assert(list_idx != 0);
            assert(list_idx != old_ll.len() - 1);
            assert(prev_page_id == old_ll[list_idx - 1]);
            assert(next_page_id == old_ll[list_idx + 1]);
            assert(0 <= list_idx - 1 < old_ll.len());
            assert(0 <= list_idx + 1 < old_ll.len());
            assert(list_idx - 1 != list_idx + 1);
            self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx + 1);
            assert(prev_page_id != next_page_id);
        }
    }

    pub proof fn merge_with_after_count_is_right(pre: Self, post: Self)
        requires
            pre.invariant(),
            State::merge_with_after_strong(pre, post),
        ensures
            post.count_is_right(),
    {
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        pre.merge_with_after_page_facts();
        pre.merge_with_after_dlist_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let b = pre.popped.get_VeryUnready_3();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            if pid == page_id {
                assert(pre.pages[page_id].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else if pid == final_id {
                assert(pre.pages[final_id].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else {
                match dlist_entry.prev {
                    Some(prev_id) => {
                        if pid == prev_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                match dlist_entry.next {
                    Some(next_id) => {
                        if pid == next_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        }

        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            assert(post.segments == pre.segments);
            assert(pre.popped == Popped::VeryUnready(segment_id, cur_start, cur_count, b));
            assert(post.popped == Popped::VeryUnready(segment_id, cur_start, (cur_count + n_count) as int, b));
            if b {
                if sid == segment_id {
                    assert(pre.popped_ec(sid) == 1);
                    assert(post.popped_ec(sid) == 1);
                } else {
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == 0);
                }
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
        }

        Self::count_is_right_preserve_all(pre, post);
    }

    pub proof fn merge_with_before_page_dom(&self)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() > 1,
        ensures ({
            let segment_id = self.popped.get_VeryUnready_0();
            let cur_start = self.popped.get_VeryUnready_1();
            let cur_count = self.popped.get_VeryUnready_2();
            let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
            &&& 0 <= cur_start
            &&& 0 <= cur_count
            &&& cur_start + cur_count <= SLICES_PER_SEGMENT
            &&& last_id.idx == cur_start - 1
            &&& self.pages.dom().contains(last_id)
            &&& self.pages[last_id].offset.is_some()
        })
    {
        reveal(State::inv_very_unready);
        self.get_count_bound_very_unready();
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let cur_count = self.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        assert(cur_start >= 1);
        let _stuff_before = self.get_stuff_before();
        assert(last_id.idx == cur_start - 1);
        assert(self.pages.dom().contains(last_id));
        assert(self.pages[last_id].offset.is_some());
        assert(0 <= cur_count);
        assert(cur_start + cur_count <= SLICES_PER_SEGMENT);
    }

    pub proof fn merge_with_before_page_facts(&self)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() > 1,
            ({
                let segment_id = self.popped.get_VeryUnready_0();
                let cur_start = self.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let offset = self.pages[last_id].offset.unwrap();
                let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
                &&& self.pages[last_id].offset.is_some()
                &&& last_id.idx - offset > 0
                &&& !self.pages[page_id].is_used
            }),
        ensures ({
            let segment_id = self.popped.get_VeryUnready_0();
            let cur_start = self.popped.get_VeryUnready_1();
            let cur_count = self.popped.get_VeryUnready_2();
            let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
            let offset = self.pages[last_id].offset.unwrap();
            let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
            let p_count = self.pages[page_id].count.unwrap();
            let sbin_idx = smallest_sbin_fitting_size(p_count as int);
            let pair = Self::get_list_idx(self.unused_lists, page_id);
            let list_idx = pair.1;
            &&& self.pages.dom().contains(last_id)
            &&& self.pages[last_id].offset.is_some()
            &&& !self.pages[last_id].is_used
            &&& self.pages.dom().contains(page_id)
            &&& page_id.idx != 0
            &&& self.pages[page_id].offset == Some(0nat)
            &&& self.pages[page_id].count.is_some()
            &&& self.pages[page_id].count == Some(offset + 1)
            &&& p_count == offset + 1
            &&& 1 <= p_count <= SLICES_PER_SEGMENT
            &&& cur_count + p_count <= SLICES_PER_SEGMENT
            &&& self.pages[page_id].dlist_entry.is_some()
            &&& self.good_range_unused(page_id)
            &&& 0 <= pair.0 < self.unused_lists.len()
            &&& 0 <= list_idx < self.unused_lists[pair.0].len()
            &&& self.unused_lists[pair.0][list_idx] == page_id
            &&& pair.0 == sbin_idx
            &&& 0 <= sbin_idx <= SEGMENT_BIN_MAX
            &&& 0 <= sbin_idx < self.unused_lists.len()
            &&& 0 <= list_idx < self.unused_lists[sbin_idx].len()
            &&& self.unused_lists[sbin_idx][list_idx] == page_id
            &&& self.valid_unused_page(page_id, sbin_idx, list_idx)
            &&& last_id.segment_id == page_id.segment_id
            &&& last_id.idx == page_id.idx + p_count - 1
            &&& page_id.idx + p_count == cur_start
        })
    {
        self.merge_with_before_page_dom();
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let cur_count = self.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = self.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        assert(last_id.idx == cur_start - 1);
        assert(page_id.idx == last_id.idx - offset);
        assert(page_id.idx != 0);

        let stuff_before = self.get_stuff_before();
        assert(self.pages.dom().contains(page_id));
        assert(self.pages[page_id].offset == Some(0nat));
        assert(self.pages[page_id].count == Some(offset + 1));
        assert(self.pages[page_id].count.is_some());
        let p_count = self.pages[page_id].count.unwrap();
        assert(p_count == offset + 1);
        assert(page_id.idx + p_count == cur_start);
        assert(cur_count + p_count <= SLICES_PER_SEGMENT);

        assert(self.good_range_unused(page_id));
        reveal(State::good_range_unused);
        assert(1 <= p_count <= SLICES_PER_SEGMENT);
        assert(self.pages[page_id].dlist_entry.is_some());

        assert(last_id.segment_id == page_id.segment_id);
        assert(last_id.idx == page_id.idx + p_count - 1);
        assert(page_id.idx <= last_id.idx < page_id.idx + p_count);
        assert(self.pages.dom().contains(last_id));
        assert(self.pages[last_id].is_used == false);

        reveal(State::get_list_idx);
        let sbin_idx = smallest_sbin_fitting_size(p_count as int);
        let pair = Self::get_list_idx(self.unused_lists, page_id);
        let list_idx = pair.1;
        assert(0 <= stuff_before.0 < self.unused_lists.len());
        assert(0 <= stuff_before.1 < self.unused_lists[stuff_before.0].len());
        assert(self.unused_lists[stuff_before.0][stuff_before.1] == page_id);
        assert(0 <= pair.0 < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[pair.0].len());
        assert(self.unused_lists[pair.0][list_idx] == page_id);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_basics);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx <= SEGMENT_BIN_MAX);
        assert(0 <= sbin_idx < self.unused_lists.len());
        assert(0 <= list_idx < self.unused_lists[sbin_idx].len());
        assert(self.unused_lists[sbin_idx][list_idx] == page_id);
        assert(self.valid_unused_page(page_id, sbin_idx, list_idx));
    }

    pub proof fn merge_with_before_last_id_not_unused_list_entry(
        &self, page_id: PageId, sbin_idx: int, list_idx: int, i: int, j: int
    )
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() > 1,
            0 <= sbin_idx < self.unused_lists.len(),
            0 <= list_idx < self.unused_lists[sbin_idx].len(),
            0 <= i < self.unused_lists.len(),
            0 <= j < self.unused_lists[i].len(),
            i != sbin_idx || j != list_idx,
            self.unused_lists[sbin_idx][list_idx] == page_id,
            self.valid_unused_page(page_id, sbin_idx, list_idx),
            self.good_range_unused(page_id),
            ({
                let segment_id = self.popped.get_VeryUnready_0();
                let cur_start = self.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let p_count = self.pages[page_id].count.unwrap();
                &&& last_id.segment_id == page_id.segment_id
                &&& last_id.idx == page_id.idx + p_count - 1
            }),
        ensures
            ({
                let segment_id = self.popped.get_VeryUnready_0();
                let cur_start = self.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                self.unused_lists[i][j] != last_id
            })
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        reveal(State::good_range_unused);
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let p_count = self.pages[page_id].count.unwrap();
        let pid = self.unused_lists[i][j];
        assert(1 <= p_count);
        assert(valid_ll(self.pages, self.unused_dlist_headers[i], self.unused_lists[i]));
        assert(valid_ll_i(self.pages, self.unused_lists[i], j));
        if pid == last_id {
            if p_count == 1 {
                assert(last_id == page_id);
                self.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(false);
            } else {
                assert(last_id.segment_id == page_id.segment_id);
                assert(last_id.idx == page_id.idx + p_count - 1);
                assert(page_id.idx <= last_id.idx < page_id.idx + p_count);
                assert(last_id != page_id);
                assert(self.pages[last_id].dlist_entry.is_none());
                assert(self.pages[pid].dlist_entry.is_some());
                assert(false);
            }
        }
    }

    pub proof fn merge_with_before_dlist_facts(&self)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            self.popped.get_VeryUnready_1() > 1,
            ({
                let segment_id = self.popped.get_VeryUnready_0();
                let cur_start = self.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let offset = self.pages[last_id].offset.unwrap();
                let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
                &&& self.pages[last_id].offset.is_some()
                &&& last_id.idx - offset > 0
                &&& !self.pages[page_id].is_used
            }),
        ensures ({
            let segment_id = self.popped.get_VeryUnready_0();
            let cur_start = self.popped.get_VeryUnready_1();
            let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
            let offset = self.pages[last_id].offset.unwrap();
            let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
            let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
            &&& (match dlist_entry.prev {
                Some(prev_page_id) =>
                    prev_page_id != page_id
                    && self.pages.dom().contains(prev_page_id)
                    && self.pages[prev_page_id].dlist_entry.is_some()
                    && self.pages[prev_page_id].is_used == false
                    && prev_page_id != last_id,
                None => true,
            })
            &&& (match dlist_entry.next {
                Some(next_page_id) =>
                    next_page_id != page_id
                    && self.pages.dom().contains(next_page_id)
                    && self.pages[next_page_id].dlist_entry.is_some()
                    && self.pages[next_page_id].is_used == false
                    && next_page_id != last_id,
                None => true,
            })
            &&& (dlist_entry.prev.is_some() && dlist_entry.next.is_some() ==>
                dlist_entry.prev.unwrap() != dlist_entry.next.unwrap())
        })
    {
        self.merge_with_before_page_facts();
        let segment_id = self.popped.get_VeryUnready_0();
        let cur_start = self.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = self.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = self.pages[page_id].count.unwrap();
        let sbin_idx = smallest_sbin_fitting_size(p_count as int);
        let pair = Self::get_list_idx(self.unused_lists, page_id);
        let list_idx = pair.1;
        let old_ll = self.unused_lists[sbin_idx];
        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();

        reveal(State::ll_inv_valid_unused);
        assert(valid_ll(self.pages, self.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(self.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));

        match dlist_entry.prev {
            Some(prev_page_id) => {
                assert(list_idx != 0);
                assert(prev_page_id == old_ll[list_idx - 1]);
                assert(0 <= list_idx - 1 < old_ll.len());
                assert(self.unused_lists[sbin_idx][list_idx - 1] == prev_page_id);
                assert(self.pages.dom().contains(prev_page_id));
                assert(self.pages[prev_page_id].dlist_entry.is_some());
                assert(self.pages[prev_page_id].is_used == false);
                assert(list_idx - 1 != list_idx);
                self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx);
                assert(prev_page_id != page_id);
                self.merge_with_before_last_id_not_unused_list_entry(
                    page_id, sbin_idx, list_idx, sbin_idx, list_idx - 1);
                assert(prev_page_id != last_id);
            }
            None => { }
        }

        match dlist_entry.next {
            Some(next_page_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_page_id == old_ll[list_idx + 1]);
                assert(0 <= list_idx + 1 < old_ll.len());
                assert(self.unused_lists[sbin_idx][list_idx + 1] == next_page_id);
                assert(self.pages.dom().contains(next_page_id));
                assert(self.pages[next_page_id].dlist_entry.is_some());
                assert(self.pages[next_page_id].is_used == false);
                assert(list_idx + 1 != list_idx);
                self.ll_unused_distinct(sbin_idx, list_idx + 1, sbin_idx, list_idx);
                assert(next_page_id != page_id);
                self.merge_with_before_last_id_not_unused_list_entry(
                    page_id, sbin_idx, list_idx, sbin_idx, list_idx + 1);
                assert(next_page_id != last_id);
            }
            None => { }
        }

        if dlist_entry.prev.is_some() && dlist_entry.next.is_some() {
            let prev_page_id = dlist_entry.prev.unwrap();
            let next_page_id = dlist_entry.next.unwrap();
            assert(list_idx != 0);
            assert(list_idx != old_ll.len() - 1);
            assert(prev_page_id == old_ll[list_idx - 1]);
            assert(next_page_id == old_ll[list_idx + 1]);
            assert(0 <= list_idx - 1 < old_ll.len());
            assert(0 <= list_idx + 1 < old_ll.len());
            assert(list_idx - 1 != list_idx + 1);
            self.ll_unused_distinct(sbin_idx, list_idx - 1, sbin_idx, list_idx + 1);
            assert(prev_page_id != next_page_id);
        }
    }

    pub proof fn merge_with_before_count_is_right(pre: Self, post: Self)
        requires
            pre.invariant(),
            State::merge_with_before_strong(pre, post),
        ensures
            post.count_is_right(),
    {
        reveal(State::does_count);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        pre.merge_with_before_page_facts();
        pre.merge_with_before_dlist_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let b = pre.popped.get_VeryUnready_3();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            if pid == page_id {
                assert(pre.pages[page_id].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else if pid == last_id {
                assert(pre.pages[last_id].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else {
                match dlist_entry.prev {
                    Some(prev_id) => {
                        if pid == prev_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                match dlist_entry.next {
                    Some(next_id) => {
                        if pid == next_id {
                            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                            assert(post.pages[pid].offset == pre.pages[pid].offset);
                        }
                    }
                    None => { }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        }

        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            assert(post.segments == pre.segments);
            assert(pre.popped == Popped::VeryUnready(segment_id, cur_start, cur_count, b));
            assert(post.popped == Popped::VeryUnready(segment_id, page_id.idx as int, (cur_count + p_count) as int, b));
            if b {
                if sid == segment_id {
                    assert(pre.popped_ec(sid) == 1);
                    assert(post.popped_ec(sid) == 1);
                } else {
                    assert(pre.popped_ec(sid) == 0);
                    assert(post.popped_ec(sid) == 0);
                }
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
            }
        }

        Self::count_is_right_preserve_all(pre, post);
    }

    #[inductive(merge_with_after)]
    #[verifier::spinoff_prover]
    fn merge_with_after_inductive(pre: Self, post: Self) {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };

        reveal(State::inv_very_unready);
        pre.get_count_bound_very_unready();
        assert(0 <= cur_start);
        assert(0 <= cur_count);
        assert(0 < cur_start);
        assert(0 <= cur_start + cur_count);
        assert(page_id.idx < SLICES_PER_SEGMENT);
        assert(pre.pages.dom().contains(page_id));
        assert(!pre.pages[page_id].is_used);

        let stuff_after = pre.get_stuff_after();
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };

        assert(pre.good_range_unused(page_id));
        assert(0 <= stuff_after.0 < pre.unused_lists.len());
        assert(0 <= stuff_after.1 < pre.unused_lists[stuff_after.0].len());
        assert(pre.unused_lists[stuff_after.0][stuff_after.1] == page_id);

        reveal(State::get_list_idx);
        let pair = Self::get_list_idx(pre.unused_lists, page_id);
        let sbin_idx = smallest_sbin_fitting_size(n_count as int);
        let list_idx = pair.1;
        assert(0 <= pair.0 < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[pair.0].len());
        assert(pre.unused_lists[pair.0][list_idx] == page_id);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[sbin_idx].len());
        assert(pre.unused_lists[sbin_idx][list_idx] == page_id);
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        assert(1 <= n_count);
        assert(page_id == PageId { segment_id, idx: (cur_start + cur_count) as nat });
        assert(post.pages[page_id].offset.is_none());
        assert(final_id.segment_id == page_id.segment_id);
        assert(0 <= cur_start + cur_count + n_count - 1);
        assert(final_id.idx == page_id.idx + n_count - 1);

        Self::merge_with_after_ll_inv_valid_unused(pre, post);
        Self::ll_inv_exists_merge_with_after(pre, post, page_id, sbin_idx, list_idx);

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            assert(pid != page_id);
            assert(pid != final_id);
        }
        Self::unchanged_used_ll(pre, post);
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        assert(pre.attached_ranges());
        pre.attached_ranges_very_unready_start();
        assert(pre.attached_rec(segment_id, cur_start, true));
        assert(pre.attached_ranges_segment(segment_id));
        assert(pre.attached_rec0(segment_id, true));
        let first_id = PageId { segment_id, idx: 0 };
        let first_count = pre.pages[first_id].count.unwrap();
        assert(pre.good_range0(segment_id));
        assert(pre.attached_rec(segment_id, first_count as int, true));
        Self::rec_attached_to_very_unready_start(pre, first_count as int, true);
        assert(first_count <= cur_start);
        Self::rec_merge_with_after(pre, post, first_count as int, true);
        assert(post.attached_rec(segment_id, first_count as int, true));
        let removed_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            ({
                let first_count = pre.pages[first_id].count.unwrap();
                pid.segment_id == segment_id
                && first_id.idx <= pid.idx < first_id.idx + first_count
            })
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == page_id || pid == final_id {
                assert(cur_start <= pid.idx);
                assert(pid.idx < first_count);
                assert(false);
            }
            match removed_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pre.good_range0(segment_id));
                        reveal(State::good_range0);
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(false);
                    }
                }
                None => { }
            }
            match removed_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pre.good_range0(segment_id));
                        reveal(State::good_range0);
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::good_range0_same(pre, post, segment_id);
        assert(post.attached_rec0(segment_id, true));
        assert(post.attached_ranges_segment(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        Self::merge_with_after_count_is_right(pre, post);
    }

    pub proof fn merge_with_after_final_id_not_old_unused_list_entry(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int, i: int, j: int
    )
        requires
            pre.invariant(),
            State::merge_with_after_strong(pre, post),
            0 <= sbin_idx < pre.unused_lists.len(),
            0 <= list_idx < pre.unused_lists[sbin_idx].len(),
            0 <= i < pre.unused_lists.len(),
            0 <= j < pre.unused_lists[i].len(),
            i != sbin_idx || j != list_idx,
            pre.unused_lists[sbin_idx][list_idx] == page_id,
            pre.valid_unused_page(page_id, sbin_idx, list_idx),
            pre.good_range_unused(page_id),
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let cur_count = pre.popped.get_VeryUnready_2();
                let n_count = pre.pages[page_id].count.unwrap();
                let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
                &&& page_id == PageId { segment_id, idx: (cur_start + cur_count) as nat }
                &&& final_id.segment_id == page_id.segment_id
                &&& final_id.idx == page_id.idx + n_count - 1
            }),
        ensures
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let cur_count = pre.popped.get_VeryUnready_2();
                let n_count = pre.pages[page_id].count.unwrap();
                let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
                pre.unused_lists[i][j] != final_id
            })
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        reveal(State::good_range_unused);
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
        let pid = pre.unused_lists[i][j];
        assert(1 <= n_count);
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
        assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
        if pid == final_id {
            if n_count == 1 {
                assert(final_id == page_id);
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(false);
            } else {
                assert(final_id.segment_id == page_id.segment_id);
                assert(final_id.idx == page_id.idx + n_count - 1);
                assert(page_id.idx <= final_id.idx < page_id.idx + n_count);
                assert(final_id != page_id);
                assert(pre.pages[final_id].dlist_entry.is_none());
                assert(pre.pages[pid].dlist_entry.is_some());
                assert(false);
            }
        }
    }

    pub proof fn merge_with_after_final_id_not_removed_neighbors(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires
            pre.invariant(),
            State::merge_with_after_strong(pre, post),
            0 <= sbin_idx < pre.unused_lists.len(),
            0 <= list_idx < pre.unused_lists[sbin_idx].len(),
            pre.unused_lists[sbin_idx][list_idx] == page_id,
            pre.valid_unused_page(page_id, sbin_idx, list_idx),
            pre.good_range_unused(page_id),
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let cur_count = pre.popped.get_VeryUnready_2();
                let n_count = pre.pages[page_id].count.unwrap();
                let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
                &&& page_id == PageId { segment_id, idx: (cur_start + cur_count) as nat }
                &&& final_id.segment_id == page_id.segment_id
                &&& final_id.idx == page_id.idx + n_count - 1
            }),
        ensures
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let cur_count = pre.popped.get_VeryUnready_2();
                let n_count = pre.pages[page_id].count.unwrap();
                let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
                let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
                dlist_entry.prev != Some(final_id) && dlist_entry.next != Some(final_id)
            })
    {
        reveal(State::ll_inv_valid_unused);
        let old_ll = pre.unused_lists[sbin_idx];
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(pre.pages, old_ll, list_idx));
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };

        match dlist_entry.prev {
            Some(prev_id) => {
                assert(list_idx != 0);
                assert(prev_id == old_ll[list_idx - 1]);
                Self::merge_with_after_final_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, list_idx - 1);
                assert(prev_id != final_id);
            }
            None => { }
        }
        match dlist_entry.next {
            Some(next_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_id == old_ll[list_idx + 1]);
                Self::merge_with_after_final_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, list_idx + 1);
                assert(next_id != final_id);
            }
            None => { }
        }
    }

    pub proof fn merge_with_after_ll_inv_valid_unused(pre: Self, post: Self)
        requires pre.invariant(),
            State::merge_with_after_strong(pre, post),
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let cur_count = pre.popped.get_VeryUnready_2();
                let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                let n_count = pre.pages[page_id].count.unwrap();
                let sbin_idx = smallest_sbin_fitting_size(n_count as int);
                let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
                let pair = Self::get_list_idx(pre.unused_lists, page_id);
                let list_idx = pair.1;
                &&& pre.good_range_unused(page_id)
                &&& 0 <= pair.0 < pre.unused_lists.len()
                &&& 0 <= list_idx < pre.unused_lists[pair.0].len()
                &&& pre.unused_lists[pair.0][list_idx] == page_id
                &&& pair.0 == sbin_idx
                &&& pre.valid_unused_page(page_id, sbin_idx, list_idx)
                &&& final_id.segment_id == page_id.segment_id
                &&& final_id.idx == page_id.idx + n_count - 1
            }),
        ensures
            post.ll_inv_valid_unused()
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
        let sbin_idx = smallest_sbin_fitting_size(n_count as int);

        assert(pre.good_range_unused(page_id));
        reveal(State::get_list_idx);
        let pair = Self::get_list_idx(pre.unused_lists, page_id);
        let list_idx = pair.1;
        assert(0 <= pair.0 < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[pair.0].len());
        assert(pre.unused_lists[pair.0][list_idx] == page_id);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[sbin_idx].len());
        assert(pre.unused_lists[sbin_idx][list_idx] == page_id);
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));

        Self::merge_with_after_final_id_not_removed_neighbors(pre, post, page_id, sbin_idx, list_idx);

        let old_ll = pre.unused_lists[sbin_idx];
        let new_ll = old_ll.remove(list_idx);
        old_ll.remove_ensures(list_idx);
        assert(old_ll[list_idx] == page_id);
        assert(pre.pages[page_id].dlist_entry.is_some());
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(pre.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));
        assert(post.unused_lists =~= pre.unused_lists.update(sbin_idx, new_ll));

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            if i == sbin_idx {
                assert(post.unused_lists[i] == new_ll);
                if new_ll.len() == 0 {
                    assert(old_ll.len() == 1);
                    assert(list_idx == 0);
                    assert(dlist_entry.prev.is_none());
                    assert(dlist_entry.next.is_none());
                    assert(post.unused_dlist_headers[i].first.is_none());
                    assert(post.unused_dlist_headers[i].last.is_none());
                } else {
                    if list_idx == 0 {
                        assert(dlist_entry.prev.is_none());
                        assert(dlist_entry.next == Some(old_ll[1]));
                        assert(new_ll[0] == old_ll[1]);
                        assert(post.unused_dlist_headers[i].first == Some(new_ll[0]));
                    } else {
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[0] == old_ll[0]);
                        assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                        assert(post.unused_dlist_headers[i].first == Some(new_ll[0]));
                    }
                    if list_idx == old_ll.len() - 1 {
                        assert(dlist_entry.next.is_none());
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[list_idx - 1]);
                        assert(post.unused_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    } else {
                        assert(dlist_entry.next == Some(old_ll[list_idx + 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                        assert(pre.unused_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                        assert(post.unused_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    }
                }
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let old_j = if j < list_idx { j } else { j + 1 };
                    assert(0 <= old_j < old_ll.len());
                    assert(old_j != list_idx);
                    assert(post.unused_lists[i][j] == old_ll[old_j]);
                    let pid = post.unused_lists[i][j];
                    Self::merge_with_after_final_id_not_old_unused_list_entry(
                        pre, post, page_id, sbin_idx, list_idx, sbin_idx, old_j);
                    pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                    assert(pid != page_id);
                    assert(pid != final_id);
                    assert(valid_ll_i(pre.pages, old_ll, old_j));
                    if old_j == list_idx - 1 {
                        assert(j == list_idx - 1);
                        assert(dlist_entry.prev == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().next == dlist_entry.next);
                    } else if old_j == list_idx + 1 {
                        assert(j == list_idx);
                        assert(dlist_entry.next == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().prev == dlist_entry.prev);
                    } else {
                        if dlist_entry.prev.is_some() {
                            let prev_id = dlist_entry.prev.unwrap();
                            assert(list_idx > 0);
                            assert(prev_id == old_ll[list_idx - 1]);
                            assert(pid != prev_id) by {
                                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx - 1);
                            }
                        }
                        if dlist_entry.next.is_some() {
                            let next_id = dlist_entry.next.unwrap();
                            assert(list_idx < old_ll.len() - 1);
                            assert(next_id == old_ll[list_idx + 1]);
                            assert(pid != next_id) by {
                                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx + 1);
                            }
                        }
                        assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                    }
                }
            } else {
                assert(post.unused_lists[i] == pre.unused_lists[i]);
                assert(post.unused_dlist_headers[i] == pre.unused_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let pid = post.unused_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                    pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                    Self::merge_with_after_final_id_not_old_unused_list_entry(
                        pre, post, page_id, sbin_idx, list_idx, i, j);
                    assert(pid != page_id);
                    assert(pid != final_id);
                    if dlist_entry.prev.is_some() {
                        let prev_id = dlist_entry.prev.unwrap();
                        assert(list_idx > 0);
                        assert(prev_id == old_ll[list_idx - 1]);
                        assert(pid != prev_id) by {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx - 1);
                        }
                    }
                    if dlist_entry.next.is_some() {
                        let next_id = dlist_entry.next.unwrap();
                        assert(list_idx < old_ll.len() - 1);
                        assert(next_id == old_ll[list_idx + 1]);
                        assert(pid != next_id) by {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx + 1);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                }
            }
        }

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists.index(i).index(j) == post.unused_lists.index(i).index(j)
        implies
            ({
                let pid = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(pid)
                &&& pid.idx != 0
                &&& post.pages[pid].is_used == false
                &&& (match post.pages[pid].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[pid].offset == Some(0nat)
                &&& post.pages[pid].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == pid
                &&& post.valid_unused_page(post.unused_lists[i][j], i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[pid].count.unwrap() as int)
            })
        by {
            let pid = post.unused_lists[i][j];
            let old_j = if i == sbin_idx {
                if j < list_idx { j } else { j + 1 }
            } else {
                j
            };
            if i == sbin_idx {
                assert(0 <= old_j < old_ll.len());
                assert(old_j != list_idx);
                assert(pid == old_ll[old_j]);
                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                Self::merge_with_after_final_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, old_j);
            } else {
                assert(pid == pre.unused_lists[i][j]);
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                Self::merge_with_after_final_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, i, j);
            }
            assert(pid != page_id);
            assert(pid != final_id);
            assert(pre.valid_unused_page(pid, i, old_j));
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
            assert(post.pages[pid].dlist_entry.is_some());
        }
        assert(post.ll_inv_valid_unused());
    }

    pub proof fn sp_true_implies_le(&self, idx: int)
      requires self.invariant(),
          self.popped.is_VeryUnready(),
          self.attached_rec(self.popped.get_VeryUnready_0(), idx, true),
          idx >= 0,
      ensures
          idx <= self.popped.get_VeryUnready_1()
      decreases SLICES_PER_SEGMENT - idx
    {
        self.get_count_bound_very_unready();
        self.rec_valid_page_before(idx, true);
    }

    pub proof fn attached_rec_at_unused_page_very_unready(&self, pid: PageId, idx: int)
      requires
          self.invariant(),
          self.popped.is_VeryUnready(),
          pid.segment_id == self.popped.get_VeryUnready_0(),
          pid.idx < self.popped.get_VeryUnready_1(),
          self.attached_rec(pid.segment_id, idx, true),
          self.good_range_unused(pid),
          idx >= 0,
          idx <= pid.idx,
      ensures
          self.attached_rec(pid.segment_id, pid.idx as int, true),
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);
        self.get_count_bound_very_unready();

        let start = self.popped.get_VeryUnready_1();
        if idx == pid.idx {
        } else {
            assert(idx < pid.idx);
            if idx == SLICES_PER_SEGMENT {
                assert(pid.idx < start);
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!self.attached_rec(pid.segment_id, idx, true));
                assert(false);
            } else if Self::is_the_popped(pid.segment_id, idx, self.popped) {
                assert(idx == start);
                assert(pid.idx < start);
                assert(false);
            } else {
                let cur = PageId { segment_id: pid.segment_id, idx: idx as nat };
                assert(cur.idx == idx);
                let count = self.pages[cur].count.unwrap();
                assert(count > 0);
                assert(idx + count <= SLICES_PER_SEGMENT);
                assert(self.attached_rec(pid.segment_id, idx + count, true));

                if idx + count > pid.idx {
                    assert(cur.segment_id == pid.segment_id);
                    assert(cur.idx <= pid.idx);
                    assert(pid.idx < cur.idx + count);
                    if self.pages[cur].is_used {
                        assert(self.good_range_used(cur));
                        assert(self.pages[pid].is_used == true);
                    } else {
                        assert(self.good_range_unused(cur));
                        assert(self.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
                        assert(self.pages[pid].offset == Some(0nat));
                        assert(pid.idx - cur.idx > 0);
                    }
                    assert(false);
                }
                assert(idx + count <= pid.idx);
                self.attached_rec_at_unused_page_very_unready(pid, idx + count);
            }
        }
    }

    pub proof fn merge_with_after_preserves_good_range_unused(pre: Self, post: Self, cur: PageId)
      requires
          pre.invariant(),
          State::merge_with_after_strong(pre, post),
          pre.good_range_unused(cur),
          cur.segment_id == pre.popped.get_VeryUnready_0(),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let page_id = PageId { segment_id, idx: (cur_start + old_count) as nat };
              let n_count = pre.pages[page_id].count.unwrap();
              let cur_count = pre.pages[cur].count.unwrap();
              cur.idx + cur_count <= cur_start || cur_start + old_count + n_count <= cur.idx
          }),
      ensures
          post.good_range_unused(cur),
          post.pages[cur].count == pre.pages[cur].count,
          post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        reveal(State::good_range_unused);
        pre.merge_with_after_page_facts();
        pre.merge_with_after_dlist_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + old_count) as nat };
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + old_count + n_count - 1) as nat };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        let cur_count = pre.pages[cur].count.unwrap();

        assert(cur.idx + cur_count <= cur_start || cur_start + old_count + n_count <= cur.idx);
        assert(cur != page_id);
        assert(cur != final_id);
        assert(post.pages[cur].count == pre.pages[cur].count);
        assert(post.pages[cur].is_used == pre.pages[cur].is_used);
        assert(post.pages[cur].offset == pre.pages[cur].offset);
        assert(post.pages[cur].full == pre.pages[cur].full);
        assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == cur.segment_id
            && cur.idx <= pid.idx < cur.idx + cur_count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == cur)
            && (post.pages[pid].dlist_entry.is_some() <==> pid == cur)
            && post.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                    Some((pid.idx - cur.idx) as nat)
                } else {
                    None
                })
        by {
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == false);
            assert(pre.pages[pid].full.is_none());
            assert(pre.pages[pid].page_header_kind.is_none());
            assert(pre.pages[pid].count.is_some() <==> pid == cur);
            assert(pre.pages[pid].dlist_entry.is_some() <==> pid == cur);
            assert(pre.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + pre.pages[cur].count.unwrap() - 1) as nat }) {
                    Some((pid.idx - cur.idx) as nat)
                } else {
                    None
                }));

            if pid == page_id || pid == final_id {
                if cur.idx + cur_count <= cur_start {
                    assert(pid.idx < cur_start);
                    assert(pid.idx >= cur_start + old_count);
                } else {
                    assert(cur_start + old_count + n_count <= cur.idx);
                    assert(pid.idx < cur.idx);
                }
                assert(false);
            }
            match dlist_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pid == cur);
                    }
                }
                None => { }
            }
            match dlist_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pid == cur);
                    }
                }
                None => { }
            }
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].full == pre.pages[pid].full);
            assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
            assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
        };
        assert(post.good_range_unused(cur));
    }

    pub proof fn merge_with_after_preserves_good_range_used(pre: Self, post: Self, cur: PageId)
      requires
          pre.invariant(),
          State::merge_with_after_strong(pre, post),
          pre.good_range_used(cur),
          cur.segment_id == pre.popped.get_VeryUnready_0(),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let page_id = PageId { segment_id, idx: (cur_start + old_count) as nat };
              let n_count = pre.pages[page_id].count.unwrap();
              let cur_count = pre.pages[cur].count.unwrap();
              cur.idx + cur_count <= cur_start || cur_start + old_count + n_count <= cur.idx
          }),
      ensures
          post.good_range_used(cur),
          post.pages[cur].count == pre.pages[cur].count,
          post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        reveal(State::good_range_used);
        pre.merge_with_after_page_facts();
        pre.merge_with_after_dlist_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let page_id = PageId { segment_id, idx: (cur_start + old_count) as nat };
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + old_count + n_count - 1) as nat };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        let cur_count = pre.pages[cur].count.unwrap();

        assert(cur.idx + cur_count <= cur_start || cur_start + old_count + n_count <= cur.idx);
        assert(cur != page_id);
        assert(cur != final_id);
        assert(post.pages[cur].count == pre.pages[cur].count);
        assert(post.pages[cur].is_used == pre.pages[cur].is_used);
        assert(post.pages[cur].offset == pre.pages[cur].offset);
        assert(post.pages[cur].full == pre.pages[cur].full);
        assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);
        assert(post.pages[cur].dlist_entry.is_some() == pre.pages[cur].dlist_entry.is_some());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == cur.segment_id
            && cur.idx <= pid.idx < cur.idx + cur_count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == true
            && post.pages[pid].offset == Some((pid.idx - cur.idx) as nat)
            && (post.pages[pid].page_header_kind.is_some() <==> pid == cur)
            && (pid != cur ==> post.pages[pid].dlist_entry.is_none())
            && (pid != cur ==> post.pages[pid].full.is_none())
        by {
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == true);
            assert(pre.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
            assert(pre.pages[pid].page_header_kind.is_some() <==> pid == cur);
            assert(pid != cur ==> pre.pages[pid].dlist_entry.is_none());
            assert(pid != cur ==> pre.pages[pid].full.is_none());

            if pid == page_id || pid == final_id {
                if cur.idx + cur_count <= cur_start {
                    assert(pid.idx < cur_start);
                    assert(pid.idx >= cur_start + old_count);
                } else {
                    assert(cur_start + old_count + n_count <= cur.idx);
                    assert(pid.idx < cur.idx);
                }
                assert(false);
            }
            match dlist_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                None => { }
            }
            match dlist_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].full == pre.pages[pid].full);
            assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
        };
        assert(post.good_range_used(cur));
    }

    pub proof fn rec_merge_with_after(pre: Self, post: Self, idx: int, sp: bool)
      requires pre.invariant(),
          State::merge_with_after_strong(pre, post),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp),
          idx >= 0,
          //sp ==> idx <= pre.popped.get_VeryUnready_1(),
          !sp ==> idx >= pre.popped.get_VeryUnready_1() + post.popped_len(),
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        pre.very_unready_popped_range_facts();
        pre.merge_with_after_page_facts();
        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let ec = pre.popped.get_VeryUnready_3();
        let page_id = PageId { segment_id, idx: (start + old_count) as nat };
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (start + old_count + n_count - 1) as nat };
        assert(pre.popped == Popped::VeryUnready(segment_id, start, old_count, ec));
        assert(post.popped == Popped::VeryUnready(segment_id, start, (old_count + n_count) as int, ec));
        assert(page_id.idx == start + old_count);
        assert(post.popped_len() == old_count + n_count);
        assert(start + old_count + n_count <= SLICES_PER_SEGMENT);

        if idx == SLICES_PER_SEGMENT {
            assert(!sp);
            assert(post.attached_rec(segment_id, idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(segment_id, idx, sp));
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            assert(idx == start);
            assert(sp);
            assert(pre.attached_rec(segment_id, start + old_count, false));
            assert(!Self::is_the_popped(segment_id, page_id.idx as int, pre.popped));
            assert(!pre.pages[page_id].is_used);
            assert(pre.good_range_unused(page_id));
            assert(pre.pages[page_id].count == Some(n_count));
            assert(pre.attached_rec(segment_id, start + old_count + n_count, false));
            Self::rec_merge_with_after(pre, post, start + old_count + n_count, false);
            assert(post.attached_rec(segment_id, start + old_count + n_count, false));
            assert(Self::is_the_popped(segment_id, idx, post.popped));
            assert(idx + post.popped_len() == start + old_count + n_count);
            assert(post.attached_rec(segment_id, idx, true));
        } else {
            let cur = PageId { segment_id, idx: idx as nat };
            let count = pre.pages[cur].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(segment_id, idx + count, sp));
            if sp {
                pre.sp_true_implies_le(idx + count);
                assert(idx + count <= start);
            } else {
                assert(start + post.popped_len() <= idx);
                assert(start + old_count + n_count <= idx);
            }
            if pre.pages[cur].is_used {
                assert(pre.good_range_used(cur));
                Self::merge_with_after_preserves_good_range_used(pre, post, cur);
                assert(post.pages[cur].is_used);
                assert(post.good_range_used(cur));
            } else {
                assert(pre.good_range_unused(cur));
                Self::merge_with_after_preserves_good_range_unused(pre, post, cur);
                assert(!post.pages[cur].is_used);
                assert(post.good_range_unused(cur));
            }
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].count.unwrap() == count);
            Self::rec_merge_with_after(pre, post, idx + count, sp);
            assert(!Self::is_the_popped(segment_id, idx, post.popped));
            assert(post.attached_rec(segment_id, idx + count, sp));
            assert(post.attached_rec(segment_id, idx, sp));
        }
    }

    pub proof fn merge_with_before_preserves_good_range_unused(pre: Self, post: Self, cur: PageId)
      requires
          pre.invariant(),
          State::merge_with_before_strong(pre, post),
          pre.good_range_unused(cur),
          cur.segment_id == pre.popped.get_VeryUnready_0(),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
              let offset = pre.pages[last_id].offset.unwrap();
              let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
              let cur_count = pre.pages[cur].count.unwrap();
              cur.idx + cur_count <= page_id.idx || cur_start + old_count <= cur.idx
          }),
      ensures
          post.good_range_unused(cur),
          post.pages[cur].count == pre.pages[cur].count,
          post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        reveal(State::good_range_unused);
        pre.merge_with_before_page_facts();
        pre.merge_with_before_dlist_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        let cur_count = pre.pages[cur].count.unwrap();

        assert(cur.idx + cur_count <= page_id.idx || cur_start + old_count <= cur.idx);
        assert(cur != page_id);
        assert(cur != last_id);
        assert(post.pages[cur].count == pre.pages[cur].count);
        assert(post.pages[cur].is_used == pre.pages[cur].is_used);
        assert(post.pages[cur].offset == pre.pages[cur].offset);
        assert(post.pages[cur].full == pre.pages[cur].full);
        assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == cur.segment_id
            && cur.idx <= pid.idx < cur.idx + cur_count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
            && (post.pages[pid].count.is_some() <==> pid == cur)
            && (post.pages[pid].dlist_entry.is_some() <==> pid == cur)
            && post.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                    Some((pid.idx - cur.idx) as nat)
                } else {
                    None
                })
        by {
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == false);
            assert(pre.pages[pid].full.is_none());
            assert(pre.pages[pid].page_header_kind.is_none());
            assert(pre.pages[pid].count.is_some() <==> pid == cur);
            assert(pre.pages[pid].dlist_entry.is_some() <==> pid == cur);
            assert(pre.pages[pid].offset == (if pid == cur || pid == (PageId { segment_id: cur.segment_id, idx: (cur.idx + pre.pages[cur].count.unwrap() - 1) as nat }) {
                    Some((pid.idx - cur.idx) as nat)
                } else {
                    None
                }));

            if pid == page_id || pid == last_id {
                if cur.idx + cur_count <= page_id.idx {
                    assert(pid.idx < page_id.idx);
                } else {
                    assert(cur_start + old_count <= cur.idx);
                    assert(pid.idx < cur.idx);
                }
                assert(false);
            }
            match dlist_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pid == cur);
                    }
                }
                None => { }
            }
            match dlist_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pid == cur);
                    }
                }
                None => { }
            }
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].full == pre.pages[pid].full);
            assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
            assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
        };
        assert(post.good_range_unused(cur));
    }

    pub proof fn merge_with_before_preserves_good_range_used(pre: Self, post: Self, cur: PageId)
      requires
          pre.invariant(),
          State::merge_with_before_strong(pre, post),
          pre.good_range_used(cur),
          cur.segment_id == pre.popped.get_VeryUnready_0(),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let old_count = pre.popped.get_VeryUnready_2();
              let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
              let offset = pre.pages[last_id].offset.unwrap();
              let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
              let cur_count = pre.pages[cur].count.unwrap();
              cur.idx + cur_count <= page_id.idx || cur_start + old_count <= cur.idx
          }),
      ensures
          post.good_range_used(cur),
          post.pages[cur].count == pre.pages[cur].count,
          post.pages[cur].is_used == pre.pages[cur].is_used,
    {
        reveal(State::good_range_used);
        pre.merge_with_before_page_facts();
        pre.merge_with_before_dlist_facts();

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        let cur_count = pre.pages[cur].count.unwrap();

        assert(cur.idx + cur_count <= page_id.idx || cur_start + old_count <= cur.idx);
        assert(cur != page_id);
        assert(cur != last_id);
        assert(post.pages[cur].count == pre.pages[cur].count);
        assert(post.pages[cur].is_used == pre.pages[cur].is_used);
        assert(post.pages[cur].offset == pre.pages[cur].offset);
        assert(post.pages[cur].full == pre.pages[cur].full);
        assert(post.pages[cur].page_header_kind == pre.pages[cur].page_header_kind);
        assert(post.pages[cur].dlist_entry.is_some() == pre.pages[cur].dlist_entry.is_some());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == cur.segment_id
            && cur.idx <= pid.idx < cur.idx + cur_count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].is_used == true
            && post.pages[pid].offset == Some((pid.idx - cur.idx) as nat)
            && (post.pages[pid].page_header_kind.is_some() <==> pid == cur)
            && (pid != cur ==> post.pages[pid].dlist_entry.is_none())
            && (pid != cur ==> post.pages[pid].full.is_none())
        by {
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].is_used == true);
            assert(pre.pages[pid].offset == Some((pid.idx - cur.idx) as nat));
            assert(pre.pages[pid].page_header_kind.is_some() <==> pid == cur);
            assert(pid != cur ==> pre.pages[pid].dlist_entry.is_none());
            assert(pid != cur ==> pre.pages[pid].full.is_none());

            if pid == page_id || pid == last_id {
                if cur.idx + cur_count <= page_id.idx {
                    assert(pid.idx < page_id.idx);
                } else {
                    assert(cur_start + old_count <= cur.idx);
                    assert(pid.idx < cur.idx);
                }
                assert(false);
            }
            match dlist_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                None => { }
            }
            match dlist_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].is_used == false);
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].full == pre.pages[pid].full);
            assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
        };
        assert(post.good_range_used(cur));
    }

    pub proof fn rec_merge_with_before(pre: Self, post: Self, idx: int, sp: bool)
      requires pre.invariant(),
          State::merge_with_before_strong(pre, post),
          pre.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp),
          idx >= 0,
          //sp ==> idx <= pre.popped.get_VeryUnready_1(),
          idx != pre.popped.get_VeryUnready_1(),
          !sp ==> idx >= pre.popped.get_VeryUnready_1() + pre.popped_len(),
      ensures
          post.attached_rec(pre.popped.get_VeryUnready_0(), idx, sp)
      decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        pre.very_unready_popped_range_facts();
        pre.merge_with_before_page_facts();
        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let ec = pre.popped.get_VeryUnready_3();
        let last_id = PageId { segment_id, idx: (start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();
        assert(pre.popped == Popped::VeryUnready(segment_id, start, old_count, ec));
        assert(post.popped == Popped::VeryUnready(segment_id, page_id.idx as int, (old_count + p_count) as int, ec));
        assert(page_id.idx + p_count == start);
        assert(post.popped_len() == old_count + p_count);
        assert(page_id.idx + post.popped_len() == start + old_count);

        if idx == SLICES_PER_SEGMENT {
            assert(!sp);
            assert(post.attached_rec(segment_id, idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(segment_id, idx, sp));
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            assert(idx == start);
            assert(false);
        } else {
            let cur = PageId { segment_id, idx: idx as nat };
            let count = pre.pages[cur].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(segment_id, idx + count, sp));
            if idx == page_id.idx {
                assert(cur == page_id);
                assert(count == p_count);
                assert(idx + count == start);
                if !sp {
                    assert(start + old_count <= idx);
                    assert(false);
                }
                assert(sp);
                assert(pre.attached_rec(segment_id, start, true));
                assert(Self::is_the_popped(segment_id, start, pre.popped));
                assert(pre.attached_rec(segment_id, start + old_count, false));
                Self::rec_merge_with_before(pre, post, start + old_count, false);
                assert(post.attached_rec(segment_id, start + old_count, false));
                assert(Self::is_the_popped(segment_id, idx, post.popped));
                assert(idx + post.popped_len() == start + old_count);
                assert(post.attached_rec(segment_id, idx, true));
            } else {
                if sp {
                    pre.sp_true_implies_le(idx);
                    assert(idx <= start);
                    assert(idx != start);
                    assert(idx < start);
                    if !(idx + count <= page_id.idx) {
                        assert(page_id.idx < idx + count);
                        assert(pre.good_range_unused(page_id));
                        if idx < page_id.idx {
                            assert(cur.idx <= page_id.idx);
                            assert(page_id.idx < cur.idx + count);
                            if pre.pages[cur].is_used {
                                assert(pre.good_range_used(cur));
                                assert(pre.pages[page_id].is_used == true);
                                assert(false);
                            } else {
                                assert(pre.good_range_unused(cur));
                                assert(pre.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                                assert(pre.pages[page_id].offset == Some(0nat));
                                assert(page_id.idx - cur.idx > 0);
                                assert(false);
                            }
                        } else {
                            assert(page_id.idx < idx);
                            assert(page_id.idx <= cur.idx);
                            assert(cur.idx < page_id.idx + p_count);
                            assert(pre.pages[cur].count.is_some());
                            assert(cur != page_id);
                            assert(false);
                        }
                    }
                    assert(idx + count <= page_id.idx);
                } else {
                    assert(start + old_count <= idx);
                }

                if pre.pages[cur].is_used {
                    assert(pre.good_range_used(cur));
                    Self::merge_with_before_preserves_good_range_used(pre, post, cur);
                    assert(post.pages[cur].is_used);
                    assert(post.good_range_used(cur));
                } else {
                    assert(pre.good_range_unused(cur));
                    Self::merge_with_before_preserves_good_range_unused(pre, post, cur);
                    assert(!post.pages[cur].is_used);
                    assert(post.good_range_unused(cur));
                }
                assert(post.pages[cur].count == pre.pages[cur].count);
                assert(post.pages[cur].count.unwrap() == count);
                assert(idx + count != start);
                Self::rec_merge_with_before(pre, post, idx + count, sp);
                assert(!Self::is_the_popped(segment_id, idx, post.popped));
                assert(post.attached_rec(segment_id, idx + count, sp));
                assert(post.attached_rec(segment_id, idx, sp));
            }
        }
    }


    pub proof fn ll_inv_exists_merge_with_after(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          pre.invariant(),
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          post.pages[page_id].offset.is_none(),
          State::merge_with_after_strong(pre, post),
          pre.valid_unused_page(page_id, sbin_idx, list_idx),
          pre.good_range_unused(page_id),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let cur_count = pre.popped.get_VeryUnready_2();
              let cur_id = PageId { segment_id, idx: cur_start as nat };
              let n_count = pre.pages[page_id].count.unwrap();
              page_id == PageId { segment_id, idx: (cur_start + cur_count) as nat }
               && sbin_idx == smallest_sbin_fitting_size(n_count as int)
               && list_idx == Self::get_list_idx(pre.unused_lists, page_id).1
               && ({
                   let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
                   final_id.segment_id == page_id.segment_id
                   && final_id.idx == page_id.idx + n_count - 1
               })
          }),
          page_id == pre.unused_lists[sbin_idx][list_idx],
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_basics);
        pre.unused_lists[sbin_idx].remove_ensures(list_idx);
        Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
        assert(post.unused_lists =~= pre.unused_lists.update(sbin_idx, pre.unused_lists[sbin_idx].remove(list_idx)));
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        assert(pre.good_range_unused(page_id));
        Self::merge_with_after_final_id_not_removed_neighbors(pre, post, page_id, sbin_idx, list_idx);

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let n_count = pre.pages[page_id].count.unwrap();
        let final_id = PageId { segment_id, idx: (cur_start + cur_count + n_count - 1) as nat };
        assert(post.pages[final_id].offset.is_none());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(pid != page_id);
            assert(pid != final_id);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].offset == Some(0nat));
            assert(!pre.pages[pid].is_used);
            assert(pre.pages[pid].count == post.pages[pid].count);
            assert(is_in_lls(pid, pre.unused_lists));
            Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
            assert(is_in_lls(pid, post.unused_lists));
        }
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            if i == sbin_idx {
                let old_j = if j < list_idx { j } else { j + 1 };
                assert(0 <= old_j < pre.unused_lists[sbin_idx].len());
                assert(post.unused_lists[i][j] == pre.unused_lists[sbin_idx][old_j]);
                if old_j != list_idx {
                    pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                }
                let pid = post.unused_lists[i][j];
                assert(pid != page_id);
                Self::merge_with_after_final_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, old_j);
                assert(pid != final_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
            } else {
                assert(post.unused_lists[i][j] == pre.unused_lists[i][j]);
                let pid = post.unused_lists[i][j];
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(pid != page_id);
                Self::merge_with_after_final_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, i, j);
                assert(pid != final_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
            }
        }
    }

    pub proof fn merge_with_before_last_id_not_old_unused_list_entry(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int, i: int, j: int
    )
        requires
            pre.invariant(),
            State::merge_with_before_strong(pre, post),
            0 <= sbin_idx < pre.unused_lists.len(),
            0 <= list_idx < pre.unused_lists[sbin_idx].len(),
            0 <= i < pre.unused_lists.len(),
            0 <= j < pre.unused_lists[i].len(),
            i != sbin_idx || j != list_idx,
            pre.unused_lists[sbin_idx][list_idx] == page_id,
            pre.valid_unused_page(page_id, sbin_idx, list_idx),
            pre.good_range_unused(page_id),
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let p_count = pre.pages[page_id].count.unwrap();
                &&& page_id == PageId { segment_id, idx: (last_id.idx - pre.pages[last_id].offset.unwrap()) as nat }
                &&& last_id.segment_id == page_id.segment_id
                &&& last_id.idx == page_id.idx + p_count - 1
            }),
        ensures
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                pre.unused_lists[i][j] != last_id
            })
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);
        reveal(State::good_range_unused);
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let p_count = pre.pages[page_id].count.unwrap();
        let pid = pre.unused_lists[i][j];
        assert(1 <= p_count);
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
        assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
        if pid == last_id {
            if p_count == 1 {
                assert(last_id == page_id);
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(false);
            } else {
                assert(last_id.segment_id == page_id.segment_id);
                assert(last_id.idx == page_id.idx + p_count - 1);
                assert(page_id.idx <= last_id.idx < page_id.idx + p_count);
                assert(last_id != page_id);
                assert(pre.pages[last_id].dlist_entry.is_none());
                assert(pre.pages[pid].dlist_entry.is_some());
                assert(false);
            }
        }
    }

    pub proof fn merge_with_before_last_id_not_removed_neighbors(
        pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int
    )
        requires
            pre.invariant(),
            State::merge_with_before_strong(pre, post),
            0 <= sbin_idx < pre.unused_lists.len(),
            0 <= list_idx < pre.unused_lists[sbin_idx].len(),
            pre.unused_lists[sbin_idx][list_idx] == page_id,
            pre.valid_unused_page(page_id, sbin_idx, list_idx),
            pre.good_range_unused(page_id),
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let p_count = pre.pages[page_id].count.unwrap();
                &&& page_id == PageId { segment_id, idx: (last_id.idx - pre.pages[last_id].offset.unwrap()) as nat }
                &&& last_id.segment_id == page_id.segment_id
                &&& last_id.idx == page_id.idx + p_count - 1
            }),
        ensures
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
                dlist_entry.prev != Some(last_id) && dlist_entry.next != Some(last_id)
            })
    {
        reveal(State::ll_inv_valid_unused);
        let old_ll = pre.unused_lists[sbin_idx];
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(pre.pages, old_ll, list_idx));
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };

        match dlist_entry.prev {
            Some(prev_id) => {
                assert(list_idx != 0);
                assert(prev_id == old_ll[list_idx - 1]);
                Self::merge_with_before_last_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, list_idx - 1);
                assert(prev_id != last_id);
            }
            None => { }
        }
        match dlist_entry.next {
            Some(next_id) => {
                assert(list_idx != old_ll.len() - 1);
                assert(next_id == old_ll[list_idx + 1]);
                Self::merge_with_before_last_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, list_idx + 1);
                assert(next_id != last_id);
            }
            None => { }
        }
    }

    pub proof fn ll_inv_exists_merge_with_before(pre: Self, post: Self, page_id: PageId, sbin_idx: int, list_idx: int)
      requires
          pre.invariant(),
          0 <= sbin_idx < pre.unused_lists.len(),
          0 <= list_idx < pre.unused_lists[sbin_idx].len(),
          pre.ll_inv_exists_in_some_list(),
          post.pages[page_id].offset.is_none(),
          State::merge_with_before_strong(pre, post),
          pre.valid_unused_page(page_id, sbin_idx, list_idx),
          pre.good_range_unused(page_id),
          ({
              let segment_id = pre.popped.get_VeryUnready_0();
              let cur_start = pre.popped.get_VeryUnready_1();
              let cur_count = pre.popped.get_VeryUnready_2();
              let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
              let offset = pre.pages[last_id].offset.unwrap();
              let p_count = pre.pages[page_id].count.unwrap();
              page_id == PageId { segment_id, idx: (last_id.idx - offset) as nat }
               && sbin_idx == smallest_sbin_fitting_size(p_count as int)
               && list_idx == Self::get_list_idx(pre.unused_lists, page_id).1
               && last_id.segment_id == page_id.segment_id
               && last_id.idx == page_id.idx + p_count - 1
          }),
          page_id == pre.unused_lists[sbin_idx][list_idx],
      ensures
          post.ll_inv_exists_in_some_list(),
    {
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_basics);
        pre.unused_lists[sbin_idx].remove_ensures(list_idx);
        Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
        assert(post.unused_lists =~= pre.unused_lists.update(sbin_idx, pre.unused_lists[sbin_idx].remove(list_idx)));
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        assert(pre.good_range_unused(page_id));
        Self::merge_with_before_last_id_not_removed_neighbors(pre, post, page_id, sbin_idx, list_idx);

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        assert(post.pages[last_id].offset.is_none());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(pid != page_id);
            assert(pid != last_id);
            assert(pre.pages.dom().contains(pid));
            assert(pre.pages[pid].offset == Some(0nat));
            assert(!pre.pages[pid].is_used);
            assert(pre.pages[pid].count == post.pages[pid].count);
            assert(is_in_lls(pid, pre.unused_lists));
            Self::ll_remove(pre.unused_lists, post.unused_lists, sbin_idx, list_idx);
            assert(is_in_lls(pid, post.unused_lists));
        }
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            if i == sbin_idx {
                let old_j = if j < list_idx { j } else { j + 1 };
                assert(0 <= old_j < pre.unused_lists[sbin_idx].len());
                assert(post.unused_lists[i][j] == pre.unused_lists[sbin_idx][old_j]);
                if old_j != list_idx {
                    pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                }
                let pid = post.unused_lists[i][j];
                assert(pid != page_id);
                Self::merge_with_before_last_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, old_j);
                assert(pid != last_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
            } else {
                assert(post.unused_lists[i][j] == pre.unused_lists[i][j]);
                let pid = post.unused_lists[i][j];
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                assert(pid != page_id);
                Self::merge_with_before_last_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, i, j);
                assert(pid != last_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
            }
        }
    }



    #[inductive(merge_with_before)]
    #[verifier::spinoff_prover]
    fn merge_with_before_inductive(pre: Self, post: Self) {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);

        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let cur_count = pre.popped.get_VeryUnready_2();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };

        reveal(State::inv_very_unready);
        pre.get_count_bound_very_unready();
        assert(0 <= cur_start);
        assert(0 <= cur_count);
        assert(cur_start > 1);
        assert(pre.pages.dom().contains(last_id));
        assert(pre.pages[last_id].offset.is_some());
        assert(last_id.idx - offset > 0);
        assert(page_id.idx != 0);

        let stuff_before = pre.get_stuff_before();
        assert(pre.pages.dom().contains(page_id));
        assert(!pre.pages[page_id].is_used);

        let p_count = pre.pages[page_id].count.unwrap();

        assert(pre.good_range_unused(page_id));
        assert(pre.pages[page_id].dlist_entry.is_some());
        assert(pre.pages[page_id].count.unwrap() == offset + 1);
        assert(p_count == offset + 1);
        assert(last_id.segment_id == page_id.segment_id);
        assert(last_id.idx == page_id.idx + p_count - 1);
        assert(0 <= stuff_before.0 < pre.unused_lists.len());
        assert(0 <= stuff_before.1 < pre.unused_lists[stuff_before.0].len());
        assert(pre.unused_lists[stuff_before.0][stuff_before.1] == page_id);

        reveal(State::get_list_idx);
        let pair = Self::get_list_idx(pre.unused_lists, page_id);
        let sbin_idx = smallest_sbin_fitting_size(p_count as int);
        let list_idx = pair.1;
        assert(0 <= pair.0 < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[pair.0].len());
        assert(pre.unused_lists[pair.0][list_idx] == page_id);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[sbin_idx].len());
        assert(pre.unused_lists[sbin_idx][list_idx] == page_id);
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));
        assert(1 <= p_count);
        assert(post.pages[page_id].offset.is_none());
        assert(post.pages[last_id].offset.is_none());

        Self::merge_with_before_ll_inv_valid_unused(pre, post);
        Self::ll_inv_exists_merge_with_before(pre, post, page_id, sbin_idx, list_idx);

        assert(pre.used_lists == post.used_lists);
        assert(pre.used_dlist_headers == post.used_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            assert(pid != page_id);
            assert(pid != last_id);
        }
        Self::unchanged_used_ll(pre, post);
        Self::merge_with_before_inductive_attached_ranges(pre, post);
        Self::merge_with_before_count_is_right(pre, post);
    }

    pub proof fn merge_with_before_ll_inv_valid_unused(pre: Self, post: Self)
        requires pre.invariant(),
            State::merge_with_before_strong(pre, post),
            ({
                let segment_id = pre.popped.get_VeryUnready_0();
                let cur_start = pre.popped.get_VeryUnready_1();
                let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                let offset = pre.pages[last_id].offset.unwrap();
                let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
                let p_count = pre.pages[page_id].count.unwrap();
                let sbin_idx = smallest_sbin_fitting_size(p_count as int);
                let pair = Self::get_list_idx(pre.unused_lists, page_id);
                let list_idx = pair.1;
                &&& pre.good_range_unused(page_id)
                &&& 0 <= pair.0 < pre.unused_lists.len()
                &&& 0 <= list_idx < pre.unused_lists[pair.0].len()
                &&& pre.unused_lists[pair.0][list_idx] == page_id
                &&& pair.0 == sbin_idx
                &&& pre.valid_unused_page(page_id, sbin_idx, list_idx)
                &&& last_id.segment_id == page_id.segment_id
                &&& last_id.idx == page_id.idx + p_count - 1
            }),
        ensures
            post.ll_inv_valid_unused()
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_unused);
        let segment_id = pre.popped.get_VeryUnready_0();
        let cur_start = pre.popped.get_VeryUnready_1();
        let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();
        let sbin_idx = smallest_sbin_fitting_size(p_count as int);

        assert(pre.good_range_unused(page_id));
        reveal(State::get_list_idx);
        let pair = Self::get_list_idx(pre.unused_lists, page_id);
        let list_idx = pair.1;
        assert(0 <= pair.0 < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[pair.0].len());
        assert(pre.unused_lists[pair.0][list_idx] == page_id);
        assert(pair.0 == sbin_idx);
        assert(0 <= sbin_idx < pre.unused_lists.len());
        assert(0 <= list_idx < pre.unused_lists[sbin_idx].len());
        assert(pre.unused_lists[sbin_idx][list_idx] == page_id);
        assert(pre.valid_unused_page(page_id, sbin_idx, list_idx));

        Self::merge_with_before_last_id_not_removed_neighbors(pre, post, page_id, sbin_idx, list_idx);

        let old_ll = pre.unused_lists[sbin_idx];
        let new_ll = old_ll.remove(list_idx);
        old_ll.remove_ensures(list_idx);
        assert(old_ll[list_idx] == page_id);
        assert(pre.pages[page_id].dlist_entry.is_some());
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert(valid_ll(pre.pages, pre.unused_dlist_headers[sbin_idx], old_ll));
        assert(valid_ll_i(pre.pages, old_ll, list_idx));
        assert(dlist_entry.prev == get_prev(old_ll, list_idx));
        assert(dlist_entry.next == get_next(old_ll, list_idx));
        assert(post.unused_lists =~= pre.unused_lists.update(sbin_idx, new_ll));

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            if i == sbin_idx {
                assert(post.unused_lists[i] == new_ll);
                if new_ll.len() == 0 {
                    assert(old_ll.len() == 1);
                    assert(list_idx == 0);
                    assert(dlist_entry.prev.is_none());
                    assert(dlist_entry.next.is_none());
                    assert(post.unused_dlist_headers[i].first.is_none());
                    assert(post.unused_dlist_headers[i].last.is_none());
                } else {
                    if list_idx == 0 {
                        assert(dlist_entry.prev.is_none());
                        assert(dlist_entry.next == Some(old_ll[1]));
                        assert(new_ll[0] == old_ll[1]);
                        assert(post.unused_dlist_headers[i].first == Some(new_ll[0]));
                    } else {
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[0] == old_ll[0]);
                        assert(pre.unused_dlist_headers[i].first == Some(old_ll[0]));
                        assert(post.unused_dlist_headers[i].first == Some(new_ll[0]));
                    }
                    if list_idx == old_ll.len() - 1 {
                        assert(dlist_entry.next.is_none());
                        assert(dlist_entry.prev == Some(old_ll[list_idx - 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[list_idx - 1]);
                        assert(post.unused_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    } else {
                        assert(dlist_entry.next == Some(old_ll[list_idx + 1]));
                        assert(new_ll[new_ll.len() - 1] == old_ll[old_ll.len() - 1]);
                        assert(pre.unused_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                        assert(post.unused_dlist_headers[i].last == Some(new_ll[new_ll.len() - 1]));
                    }
                }
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let old_j = if j < list_idx { j } else { j + 1 };
                    assert(0 <= old_j < old_ll.len());
                    assert(old_j != list_idx);
                    assert(post.unused_lists[i][j] == old_ll[old_j]);
                    let pid = post.unused_lists[i][j];
                    Self::merge_with_before_last_id_not_old_unused_list_entry(
                        pre, post, page_id, sbin_idx, list_idx, sbin_idx, old_j);
                    pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                    assert(pid != page_id);
                    assert(pid != last_id);
                    assert(valid_ll_i(pre.pages, old_ll, old_j));
                    if old_j == list_idx - 1 {
                        assert(j == list_idx - 1);
                        assert(dlist_entry.prev == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().next == dlist_entry.next);
                    } else if old_j == list_idx + 1 {
                        assert(j == list_idx);
                        assert(dlist_entry.next == Some(pid));
                        assert(post.pages[pid].dlist_entry.unwrap().prev == dlist_entry.prev);
                    } else {
                        if dlist_entry.prev.is_some() {
                            let prev_id = dlist_entry.prev.unwrap();
                            assert(list_idx > 0);
                            assert(prev_id == old_ll[list_idx - 1]);
                            assert(pid != prev_id) by {
                                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx - 1);
                            }
                        }
                        if dlist_entry.next.is_some() {
                            let next_id = dlist_entry.next.unwrap();
                            assert(list_idx < old_ll.len() - 1);
                            assert(next_id == old_ll[list_idx + 1]);
                            assert(pid != next_id) by {
                                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx + 1);
                            }
                        }
                        assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                    }
                }
            } else {
                assert(post.unused_lists[i] == pre.unused_lists[i]);
                assert(post.unused_dlist_headers[i] == pre.unused_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
                assert forall |j: int|
                    0 <= j < post.unused_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.unused_lists[i], j)
                by {
                    let pid = post.unused_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                    pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                    Self::merge_with_before_last_id_not_old_unused_list_entry(
                        pre, post, page_id, sbin_idx, list_idx, i, j);
                    assert(pid != page_id);
                    assert(pid != last_id);
                    if dlist_entry.prev.is_some() {
                        let prev_id = dlist_entry.prev.unwrap();
                        assert(list_idx > 0);
                        assert(prev_id == old_ll[list_idx - 1]);
                        assert(pid != prev_id) by {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx - 1);
                        }
                    }
                    if dlist_entry.next.is_some() {
                        let next_id = dlist_entry.next.unwrap();
                        assert(list_idx < old_ll.len() - 1);
                        assert(next_id == old_ll[list_idx + 1]);
                        assert(pid != next_id) by {
                            pre.ll_unused_distinct(i, j, sbin_idx, list_idx + 1);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                }
            }
        }

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists.index(i).index(j) == post.unused_lists.index(i).index(j)
        implies
            ({
                let pid = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(pid)
                &&& pid.idx != 0
                &&& post.pages[pid].is_used == false
                &&& (match post.pages[pid].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[pid].offset == Some(0nat)
                &&& post.pages[pid].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == pid
                &&& post.valid_unused_page(post.unused_lists[i][j], i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[pid].count.unwrap() as int)
            })
        by {
            let pid = post.unused_lists[i][j];
            let old_j = if i == sbin_idx {
                if j < list_idx { j } else { j + 1 }
            } else {
                j
            };
            if i == sbin_idx {
                assert(0 <= old_j < old_ll.len());
                assert(old_j != list_idx);
                assert(pid == old_ll[old_j]);
                pre.ll_unused_distinct(sbin_idx, old_j, sbin_idx, list_idx);
                Self::merge_with_before_last_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, sbin_idx, old_j);
            } else {
                assert(pid == pre.unused_lists[i][j]);
                pre.ll_unused_distinct(i, j, sbin_idx, list_idx);
                Self::merge_with_before_last_id_not_old_unused_list_entry(
                    pre, post, page_id, sbin_idx, list_idx, i, j);
            }
            assert(pid != page_id);
            assert(pid != last_id);
            assert(pre.valid_unused_page(pid, i, old_j));
            assert(post.pages[pid].is_used == pre.pages[pid].is_used);
            assert(post.pages[pid].count == pre.pages[pid].count);
            assert(post.pages[pid].offset == pre.pages[pid].offset);
            assert(post.pages[pid].dlist_entry.is_some());
        }
        assert(post.ll_inv_valid_unused());
    }

    pub proof fn merge_with_before_inductive_attached_ranges(
        pre: Self, post: Self,
    )
        requires pre.invariant(),
          State::merge_with_before_strong(pre, post),
        ensures post.attached_ranges()
    {
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::good_range0);
        reveal(State::good_range_unused);
        reveal(State::popped_ranges_match);
        reveal(State::is_any_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);

        pre.merge_with_before_page_facts();
        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let old_count = pre.popped.get_VeryUnready_2();
        let ec = pre.popped.get_VeryUnready_3();
        let last_id = PageId { segment_id, idx: (start - 1) as nat };
        let offset = pre.pages[last_id].offset.unwrap();
        let page_id = PageId { segment_id, idx: (last_id.idx - offset) as nat };
        let p_count = pre.pages[page_id].count.unwrap();
        assert(pre.popped == Popped::VeryUnready(segment_id, start, old_count, ec));
        assert(post.popped == Popped::VeryUnready(segment_id, page_id.idx as int, (old_count + p_count) as int, ec));
        assert(pre.attached_ranges());
        pre.attached_ranges_very_unready_start();
        assert(pre.attached_rec(segment_id, start, true));
        assert(pre.good_range_unused(page_id));
        assert(page_id.idx + p_count == start);
        assert(page_id.idx < start);

        assert(Self::popped_ranges_match(pre, pre));
        assert(pre.segments.dom() =~= pre.segments.dom());
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            (pre.pages.dom().contains(pid) <==> pre.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) && !pre.in_popped_range(pid) ==> {
                &&& pre.pages.dom().contains(pid)
                &&& pre.pages[pid].count == pre.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> pre.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == pre.pages[pid].offset
                &&& pre.pages[pid].is_used == pre.pages[pid].is_used
                &&& pre.pages[pid].full == pre.pages[pid].full
                &&& pre.pages[pid].page_header_kind == pre.pages[pid].page_header_kind
            })
        by { };
        Self::attached_ranges_all(pre, pre);
        assert(pre.segments.dom().contains(segment_id));
        assert(pre.attached_ranges_segment(segment_id));
        assert(pre.attached_rec0(segment_id, true));
        assert(pre.good_range0(segment_id));

        let first_id = PageId { segment_id, idx: 0 };
        let first_count = pre.pages[first_id].count.unwrap();
        assert(pre.pages.dom().contains(first_id));
        assert(pre.pages[first_id].count == Some(first_count));
        assert(pre.attached_rec(segment_id, first_count as int, true));
        if first_count > page_id.idx {
            assert(page_id.idx < first_count);
            assert(first_id.idx <= page_id.idx < first_id.idx + first_count);
            assert(pre.pages[page_id].count.is_some());
            assert(page_id != first_id);
            assert(false);
        }
        assert(first_count <= page_id.idx);
        pre.attached_rec_at_unused_page_very_unready(page_id, first_count as int);
        assert(pre.attached_rec(segment_id, page_id.idx as int, true));

        Self::rec_merge_with_before(pre, post, first_count as int, true);
        assert(post.attached_rec(segment_id, first_count as int, true));
        let dlist_entry = pre.pages[page_id].dlist_entry.unwrap();
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            ({
                let first_count = pre.pages[first_id].count.unwrap();
                pid.segment_id == segment_id
                && first_id.idx <= pid.idx < first_id.idx + first_count
            })
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == page_id || pid == last_id {
                assert(page_id.idx <= pid.idx);
                assert(pid.idx < first_count);
                assert(false);
            }
            match dlist_entry.prev {
                Some(prev_id) => {
                    if pid == prev_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pre.good_range0(segment_id));
                        reveal(State::good_range0);
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(false);
                    }
                }
                None => { }
            }
            match dlist_entry.next {
                Some(next_id) => {
                    if pid == next_id {
                        assert(pre.pages[pid].dlist_entry.is_some());
                        assert(pre.good_range0(segment_id));
                        reveal(State::good_range0);
                        assert(pre.pages[pid].dlist_entry.is_none());
                        assert(false);
                    }
                }
                None => { }
            }
            assert(post.pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::good_range0_same(pre, post, segment_id);
        assert(post.attached_rec0(segment_id, true));
        assert(post.attached_ranges_segment(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
    }

    #[inductive(segment_freeing_start)]
    fn segment_freeing_start_inductive(pre: Self, post: Self, segment_id: SegmentId) {
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::end_is_unused);
        reveal(State::count_is_right);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::seg_free_prefix);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        reveal(State::does_count);

        let first_id = PageId { segment_id, idx: 0 };
        assert(pre.popped == Popped::No);
        assert(pre.segments.dom().contains(segment_id));
        assert(pre.segments[segment_id].used == 0);
        assert(pre.popped_ec(segment_id) == 0);
        assert(pre.segments[segment_id].used == pre.popped_ec(segment_id));
        assert(pre.pages.dom().contains(first_id));
        assert(pre.pages[first_id].offset == Some(0nat));
        assert(!pre.pages[first_id].is_used);
        assert(pre.pages[first_id].count.is_some());
        let count = pre.pages[first_id].count.unwrap();
        assert(1 <= count);
        assert(first_id.idx + count <= SLICES_PER_SEGMENT);

        let new_page_map = Map::<PageId, PageData>::new(
            page_id_range(segment_id, 0, count),
            |page_id: PageId| PageData {
                dlist_entry: None,
                count: None,
                offset: None,
                is_used: false,
                full: None,
                page_header_kind: None,
            }
        );
        assert(post.pages == pre.pages.union_prefer_right(new_page_map));
        assert(post.segments == pre.segments);
        assert(post.popped == Popped::SegmentFreeing(segment_id, count as int));
        assert(post.unused_lists == pre.unused_lists);
        assert(post.unused_dlist_headers == pre.unused_dlist_headers);
        assert(post.used_lists == pre.used_lists);
        assert(post.used_dlist_headers == pre.used_dlist_headers);

        assert(pre.pages.dom() =~= post.pages.dom()) by {
            vstd::map_lib::lemma_union_dom(pre.pages, new_page_map);
            assert forall |pid: PageId|
                new_page_map.dom().contains(pid) implies pre.pages.dom().contains(pid)
            by {
                assert(pid.segment_id == segment_id);
                assert(0 <= pid.idx < count);
                assert(pid.idx <= SLICES_PER_SEGMENT);
            };
            assert(new_page_map.dom().subset_of(pre.pages.dom()));
            assert(pre.pages.dom().union(new_page_map.dom()) =~= pre.pages.dom());
        };
        assert(post.page_id_domain());
        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            if new_page_map.dom().contains(pid) {
                assert(post.pages[pid] == new_page_map[pid]);
                assert(post.pages[pid].count.is_none());
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.count_off0());
        assert(post.popped_basics());
        assert(post.inv_segment_creating());
        assert(post.inv_very_unready());

        assert(Self::popped_ranges_match(pre, pre)) by {
            reveal(State::popped_ranges_match);
            reveal(State::is_any_the_popped);
        };
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            (pre.pages.dom().contains(pid) <==> pre.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) && !pre.in_popped_range(pid) ==> {
                &&& pre.pages.dom().contains(pid)
                &&& pre.pages[pid].count == pre.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> pre.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == pre.pages[pid].offset
                &&& pre.pages[pid].is_used == pre.pages[pid].is_used
                &&& pre.pages[pid].full == pre.pages[pid].full
                &&& pre.pages[pid].page_header_kind == pre.pages[pid].page_header_kind
            })
        by { };
        Self::attached_ranges_all(pre, pre);
        assert(pre.attached_ranges_segment(segment_id));
        assert(pre.attached_rec0(segment_id, false));
        assert(pre.good_range0(segment_id));
        assert(pre.attached_rec(segment_id, count as int, false));

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == segment_id
            && 0 <= pid.idx < count
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry.is_none()
            && post.pages[pid].count.is_none()
            && post.pages[pid].offset.is_none()
            && post.pages[pid].is_used == false
            && post.pages[pid].full.is_none()
            && post.pages[pid].page_header_kind.is_none()
        by {
            assert(new_page_map.dom().contains(pid));
            assert(post.pages[pid] == new_page_map[pid]);
        };
        assert(post.seg_free_prefix(segment_id, count as int));
        if count < SLICES_PER_SEGMENT {
            assert(Self::popped_ranges_match_for_sid(pre, post, segment_id)) by {
                reveal(State::popped_ranges_match_for_sid);
                reveal(State::popped_for_seg);
                reveal(State::popped_len);
                reveal(State::page_id_of_popped);
            };
            assert forall |pid: PageId|
                #![trigger pre.pages.dom().contains(pid)]
                #![trigger post.pages.dom().contains(pid)]
                #![trigger pre.pages[pid]]
                #![trigger post.pages[pid]]
                pid.segment_id == segment_id
            implies
                (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                && (pre.pages.dom().contains(pid) ==> (
                    (!pre.in_popped_range(pid) && pid.idx >= count ==> {
                    &&& post.pages.dom().contains(pid)
                    &&& pre.pages[pid].count == post.pages[pid].count
                    &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                    &&& pre.pages[pid].offset == post.pages[pid].offset
                    &&& pre.pages[pid].is_used == post.pages[pid].is_used
                    &&& pre.pages[pid].full == post.pages[pid].full
                    &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
                })))
            by {
                if new_page_map.dom().contains(pid) {
                    assert(0 <= pid.idx < count);
                        assert(pre.pages.dom().contains(pid));
                        assert(post.pages.dom().contains(pid));
                        if pre.pages.dom().contains(pid) && !pre.in_popped_range(pid) && pid.idx >= count {
                            assert(false);
                        }
                    } else {
                        if pre.pages.dom().contains(pid) || post.pages.dom().contains(pid) {
                            assert(post.pages[pid] == pre.pages[pid]);
                        }
                    }
                };
            Self::attached_rec_same(pre, post, segment_id, count as int, false);
            assert(post.attached_rec(segment_id, count as int, false));
        }
        assert(post.inv_segment_freeing());
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec);
        if count < SLICES_PER_SEGMENT {
            assert(post.attached_rec(segment_id, count as int, false));
        } else {
            assert(count == SLICES_PER_SEGMENT);
            assert(post.attached_rec(segment_id, count as int, false));
        }
        assert(post.attached_ranges_segment(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(post.inv_ready());
        assert(post.inv_used());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if new_page_map.dom().contains(pid) {
                assert(0 <= pid.idx < count);
                reveal(State::good_range0);
                assert(pre.pages[pid].is_used == false);
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        assert(post.data_for_used_header());
        assert(post.ll_inv_valid_used2());
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            if new_page_map.dom().contains(pid) {
                reveal(State::good_range0);
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(post.pages[pid] == new_page_map[pid]);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());
        assert(post.ready_popped_not_in_unused_lists());

        reveal(State::ll_inv_exists_in_some_list);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            if new_page_map.dom().contains(pid) {
                assert(post.pages[pid] == new_page_map[pid]);
                assert(post.pages[pid].offset.is_none());
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
                assert(is_in_lls(pid, pre.unused_lists));
            }
        };
        assert forall |i: int, j: int| #![trigger post.unused_lists[i][j]]
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            if new_page_map.dom().contains(pid) {
                reveal(State::ll_inv_valid_unused);
                reveal(State::valid_unused_page);
                assert(pre.valid_unused_page(pid, i, j));
                reveal(State::good_range0);
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].dlist_entry.is_some());
                assert(false);
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            if new_page_map.dom().contains(pid) {
                reveal(State::good_range0);
                assert(pre.pages[pid].is_used == false);
                assert(post.pages[pid].is_used == false);
            } else {
                if pre.pages.dom().contains(pid) || post.pages.dom().contains(pid) {
                    assert(post.pages[pid] == pre.pages[pid]);
                }
            }
        };
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            assert(post.segments == pre.segments);
            assert(pre.popped_ec(sid) == 0);
            assert(post.popped_ec(sid) == 0);
        };
        Self::count_is_right_preserve_all(pre, post);
        assert(post.count_is_right());

        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
            && !(match post.popped {
                Popped::SegmentCreating(psid) => psid == sid,
                Popped::SegmentFreeing(psid, _) => psid == sid,
                _ => false,
            })
            && post.segments[sid].used == post.popped_ec(sid)
        implies
            ({
                let page_id = PageId { segment_id: sid, idx: 0 };
                &&& post.pages.dom().contains(page_id)
                &&& post.pages[page_id].offset == Some(0nat)
                &&& !post.pages[page_id].is_used
                &&& post.pages[page_id].count.is_some()
            })
        by {
            let page_id = PageId { segment_id: sid, idx: 0 };
            assert(sid != segment_id);
            assert(pre.pages[page_id] == post.pages[page_id]);
            assert(pre.segments[sid].used == pre.popped_ec(sid));
        };
        assert(post.end_is_unused());
    }

    #[inductive(segment_freeing_finish)]
    fn segment_freeing_finish_inductive(pre: Self, post: Self) {
        reveal(State::ll_basics);
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::end_is_unused);
        reveal(State::count_is_right);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::seg_free_prefix);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_unused);
        reveal(State::ll_inv_valid_used);
        reveal(State::ll_inv_valid_used2);
        reveal(State::ll_inv_exists_in_some_list);
        reveal(State::valid_unused_page);
        reveal(State::valid_used_page);
        reveal(State::attached_ranges);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        reveal(State::does_count);

        let segment_id = pre.popped.get_SegmentFreeing_0();
        let keys = page_id_range(segment_id, 0, SLICES_PER_SEGMENT as nat + 1);
        assert(pre.popped == Popped::SegmentFreeing(segment_id, SLICES_PER_SEGMENT as int));
        assert(post.popped == Popped::No);
        assert(post.segments == pre.segments.remove(segment_id));
        assert(post.pages == pre.pages.remove_keys(keys));
        assert(post.unused_lists == pre.unused_lists);
        assert(post.unused_dlist_headers == pre.unused_dlist_headers);
        assert(post.used_lists == pre.used_lists);
        assert(post.used_dlist_headers == pre.used_dlist_headers);
        assert(pre.segments.dom().contains(segment_id));
        assert(pre.segments[segment_id].used == 0);
        assert(pre.seg_free_prefix(segment_id, SLICES_PER_SEGMENT as int));
        assert(pre.popped_ec(segment_id) == 0);
        assert(pre.ucount(segment_id) == 0) by {
            assert(pre.segments[segment_id].used == pre.ucount(segment_id) as int + pre.popped_ec(segment_id));
        };

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            post.pages.dom().contains(pid)
        implies
            post.segments.dom().contains(pid.segment_id)
            && pid.idx <= SLICES_PER_SEGMENT
        by {
            assert(pre.pages.dom().contains(pid));
            assert(!keys.contains(pid));
            assert(pre.segments.dom().contains(pid.segment_id));
            if pid.segment_id == segment_id {
                assert(keys.contains(pid));
                assert(false);
            }
        };
        assert forall |pid: PageId|
            #![trigger post.segments.dom().contains(pid.segment_id)]
            post.segments.dom().contains(pid.segment_id)
            && pid.idx <= SLICES_PER_SEGMENT
        implies
            post.pages.dom().contains(pid)
        by {
            assert(pre.segments.dom().contains(pid.segment_id));
            assert(pid.segment_id != segment_id);
            assert(pre.pages.dom().contains(pid));
            assert(!keys.contains(pid));
        };
        assert(post.page_id_domain());
        assert forall |pid: PageId|
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && post.pages[pid].count.is_some()
        implies
            ({
                let pcount = post.pages[pid].count.unwrap();
                &&& 1 <= pcount
                &&& pid.idx + pcount <= SLICES_PER_SEGMENT
            })
        by {
            assert(pre.pages.dom().contains(pid));
            assert(!keys.contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
        };
        assert(post.count_off0());
        assert(post.popped_basics());
        assert(post.inv_segment_creating());
        assert(post.inv_very_unready());
        assert(post.inv_segment_freeing());
        reveal(State::attached_ranges);
        reveal(State::if_popped_or_other_then_for);
        assert forall |sid: SegmentId| sid != segment_id && post.segments.dom().contains(sid) implies pre.segments.dom().contains(sid) by {
            assert(pre.segments.dom().contains(sid));
        };
        assert forall |pid: PageId|
            pid.segment_id != segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            assert(!keys.contains(pid));
            if pre.pages.dom().contains(pid) || post.pages.dom().contains(pid) {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(pre.if_popped_or_other_then_for(segment_id));
        assert(post.if_popped_or_other_then_for(segment_id));
        Self::attached_ranges_except(pre, post, segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            assert(sid != segment_id);
            assert(post.attached_ranges_segment(sid));
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(post.inv_ready());
        assert(post.inv_used());

        assert forall |i: int|
            #![trigger post.used_dlist_headers.index(i)]
            0 <= i < post.used_lists.len()
        implies
            valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
            assert forall |j: int|
                0 <= j < post.used_lists[i].len()
            implies
                valid_ll_i(post.pages, post.used_lists[i], j)
            by {
                let pid = post.used_lists[i][j];
                assert(pid == pre.used_lists[i][j]);
                assert(pre.valid_used_page(pid, i, j));
                if pid.segment_id == segment_id {
                    assert(pre.pages[pid].count.is_some());
                    let pcount = pre.pages[pid].count.unwrap();
                    assert(1 <= pcount);
                    assert(pid.idx + pcount <= SLICES_PER_SEGMENT);
                    assert(pid.idx < SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].is_used == false);
                    assert(pre.pages[pid].is_used == true);
                    assert(false);
                } else {
                    assert(!keys.contains(pid));
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(valid_ll_i(pre.pages, pre.used_lists[i], j));
                }
            };
        };
        assert forall |i: int, j: int|
            0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len()
            && #[trigger] post.used_lists[i][j] == post.used_lists[i][j]
        implies
            ({
                let page_id = post.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& post.valid_used_page(page_id, i, j)
                &&& post.pages[page_id].count.is_some()
                &&& (post.popped.is_Ready() ==> page_id != post.popped_page_id())
            })
        by {
            let pid = post.used_lists[i][j];
            assert(pid == pre.used_lists[i][j]);
            assert(pre.valid_used_page(pid, i, j));
            if pid.segment_id == segment_id {
                assert(pre.pages[pid].count.is_some());
                let pcount = pre.pages[pid].count.unwrap();
                assert(1 <= pcount);
                assert(pid.idx + pcount <= SLICES_PER_SEGMENT);
                assert(pid.idx < SLICES_PER_SEGMENT);
                assert(pre.pages[pid].is_used == false);
                assert(pre.pages[pid].is_used == true);
                assert(false);
            } else {
                assert(!keys.contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_valid_used());
        assert(post.data_for_used_header());
        assert(post.ll_inv_valid_used2());

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert forall |j: int|
                0 <= j < post.unused_lists[i].len()
            implies
                valid_ll_i(post.pages, post.unused_lists[i], j)
            by {
                let pid = post.unused_lists[i][j];
                assert(pid == pre.unused_lists[i][j]);
                assert(pre.valid_unused_page(pid, i, j));
                if pid.segment_id == segment_id {
                    assert(pre.pages[pid].count.is_some());
                    let pcount = pre.pages[pid].count.unwrap();
                    assert(1 <= pcount);
                    assert(pid.idx + pcount <= SLICES_PER_SEGMENT);
                    assert(pid.idx < SLICES_PER_SEGMENT);
                    assert(pre.pages[pid].count.is_none());
                    assert(pre.pages[pid].dlist_entry.is_none());
                    assert(pre.pages[pid].dlist_entry.is_some());
                    assert(false);
                } else {
                    assert(!keys.contains(pid));
                    assert(post.pages[pid] == pre.pages[pid]);
                    assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                }
            };
        };
        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
        implies
            ({
                let page_id = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(page_id)
                &&& page_id.idx != 0
                &&& post.pages[page_id].is_used == false
                &&& (match post.pages[page_id].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[page_id].offset == Some(0nat)
                &&& post.pages[page_id].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == page_id
                &&& post.valid_unused_page(page_id, i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[page_id].count.unwrap() as int)
            })
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            if pid.segment_id == segment_id {
                assert(pre.pages[pid].count.is_some());
                let pcount = pre.pages[pid].count.unwrap();
                assert(1 <= pcount);
                assert(pid.idx + pcount <= SLICES_PER_SEGMENT);
                assert(pid.idx < SLICES_PER_SEGMENT);
                assert(pre.pages[pid].count.is_none());
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].dlist_entry.is_some());
                assert(false);
            } else {
                assert(!keys.contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());
        assert(post.ready_popped_not_in_unused_lists());

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(pre.pages.dom().contains(pid));
            assert(!keys.contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
            assert(is_in_lls(pid, pre.unused_lists));
        };
        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(pid, i, j));
            if pid.segment_id == segment_id {
                assert(pre.pages[pid].count.is_some());
                let pcount = pre.pages[pid].count.unwrap();
                assert(1 <= pcount);
                assert(pid.idx + pcount <= SLICES_PER_SEGMENT);
                assert(pid.idx < SLICES_PER_SEGMENT);
                assert(pre.pages[pid].count.is_none());
                assert(false);
            } else {
                assert(!keys.contains(pid));
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());

        assert forall |pid: PageId| #![all_triggers] pid.segment_id != segment_id implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
        by {
            assert(!keys.contains(pid));
        };
        Self::ucount_preserve_except(pre, post, segment_id);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            assert(sid != segment_id);
            assert(pre.segments.dom().contains(sid));
            assert(post.segments[sid].used == pre.segments[sid].used);
            assert(post.ucount(sid) == pre.ucount(sid));
            assert(pre.popped_ec(sid) == 0);
            assert(post.popped_ec(sid) == 0);
            assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
        };
        assert(post.count_is_right());
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
            && !(match post.popped {
                Popped::SegmentCreating(psid) => psid == sid,
                Popped::SegmentFreeing(psid, _) => psid == sid,
                _ => false,
            })
            && post.segments[sid].used == post.popped_ec(sid)
        implies
            ({
                let page_id = PageId { segment_id: sid, idx: 0 };
                &&& post.pages.dom().contains(page_id)
                &&& post.pages[page_id].offset == Some(0nat)
                &&& !post.pages[page_id].is_used
                &&& post.pages[page_id].count.is_some()
            })
        by {
            let page_id = PageId { segment_id: sid, idx: 0 };
            assert(sid != segment_id);
            assert(pre.pages[page_id] == post.pages[page_id]);
            assert(pre.segments[sid].used == pre.popped_ec(sid));
        };
        assert(post.end_is_unused());
    }

    #[verifier::spinoff_prover]
    #[inductive(into_used_list_back)]
    fn into_used_list_back_inductive(pre: Self, post: Self, bin_idx: int) {
        reveal(State::inv_used);
        reveal(State::good_range_used);
        reveal(State::popped_basics);
        reveal(State::count_off0);
        reveal(State::attached_ranges);
        let page_id = pre.popped.get_Used_0();
        assert(pre.popped == Popped::Used(page_id, true));
        assert(post.popped == Popped::No);
        assert(pre.good_range_used(page_id));
        let count = pre.pages[page_id].count.unwrap();
        assert(1 <= count);
        assert(page_id.idx + count <= SLICES_PER_SEGMENT);
        assert(post.popped_basics());
        assert(post.inv_used());
        assert(post.good_range_used(page_id));
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::in_popped_range);
        assert(pre.attached_ranges_segment(page_id.segment_id));
        assert(pre.attached_rec0(page_id.segment_id, true));
        let first_id0 = PageId { segment_id: page_id.segment_id, idx: 0 };
        let first_count0 = pre.pages[first_id0].count.unwrap();
        assert(pre.good_range0(page_id.segment_id));
        assert(pre.attached_rec(page_id.segment_id, first_count0 as int, true));
        if first_count0 > page_id.idx {
            reveal(State::good_range0);
            assert(first_id0.idx <= page_id.idx < first_id0.idx + first_count0);
            assert(pre.pages[page_id].is_used == false);
            assert(pre.pages[page_id].is_used == true);
            assert(false);
        }
        assert(first_count0 <= page_id.idx);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            pid.segment_id == page_id.segment_id
            && first_id0.idx <= pid.idx < first_id0.idx + first_count0
        implies
            post.pages.dom().contains(pid) && post.pages[pid] == pre.pages[pid]
        by {
            if pid == page_id {
                assert(page_id.idx < first_count0);
                assert(false);
            }
            if pre.used_dlist_headers[bin_idx].last.is_some() {
                let old_last = pre.used_dlist_headers[bin_idx].last.unwrap();
                if pid == old_last {
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_used);
                    reveal(State::valid_used_page);
                    pre.first_last_ll_stuff_used(bin_idx);
                    assert(pre.pages[old_last].is_used);
                    reveal(State::good_range0);
                    assert(pre.pages[pid].is_used == false);
                    assert(false);
                }
            }
            assert(post.pages.dom().contains(pid));
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::good_range0_same(pre, post, page_id.segment_id);
        assert(post.good_range0(page_id.segment_id));
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == page_id.segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
                && !post.in_popped_range(pid) ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            assert(post.popped == Popped::No);
            if pid == page_id {
                assert(pre.in_popped_range(pid));
            } else if pre.used_dlist_headers[bin_idx].last.is_some() {
                let old_last = pre.used_dlist_headers[bin_idx].last.unwrap();
                if pid == old_last {
                    reveal(State::ll_basics);
                    reveal(State::ll_inv_valid_used);
                    reveal(State::valid_used_page);
                    pre.first_last_ll_stuff_used(bin_idx);
                    assert(pre.pages[pid].dlist_entry.is_some());
                    assert(post.pages[pid].dlist_entry.is_some());
                    assert(pre.pages[pid].count == post.pages[pid].count);
                    assert(pre.pages[pid].offset == post.pages[pid].offset);
                    assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                    assert(pre.pages[pid].full == post.pages[pid].full);
                    assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_rec_used_popped_to_no(pre, post, page_id, first_count0 as int);
        assert(post.attached_rec0(page_id.segment_id, false));
        assert(post.attached_ranges_segment(page_id.segment_id));
        reveal(State::if_popped_or_other_then_for);
        assert(pre.if_popped_or_other_then_for(page_id.segment_id));
        assert(post.if_popped_or_other_then_for(page_id.segment_id));
        assert forall |pid: PageId|
            pid.segment_id != page_id.segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              })
        by {
            if pre.used_dlist_headers[bin_idx].last.is_some() {
                let old_last = pre.used_dlist_headers[bin_idx].last.unwrap();
                if pid == old_last {
                    assert(pre.pages[pid].dlist_entry.is_some());
                    assert(post.pages[pid].dlist_entry.is_some());
                    assert(pre.pages[pid].count == post.pages[pid].count);
                    assert(pre.pages[pid].offset == post.pages[pid].offset);
                    assert(pre.pages[pid].is_used == post.pages[pid].is_used);
                    assert(pre.pages[pid].full == post.pages[pid].full);
                    assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                } else {
                    assert(post.pages[pid] == pre.pages[pid]);
                }
            } else {
                assert(post.pages[pid] == pre.pages[pid]);
            }
        };
        Self::attached_ranges_except(pre, post, page_id.segment_id);
        assert forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) implies post.attached_ranges_segment(sid) by {
            if sid == page_id.segment_id {
                assert(post.attached_ranges_segment(sid));
            } else {
                assert(post.attached_ranges_segment(sid));
            }
        };
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by {
            reveal(State::does_count);
            if pid == page_id {
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            } else {
                if pre.used_dlist_headers[bin_idx].last.is_some() {
                    let last_id = pre.used_dlist_headers[bin_idx].last.unwrap();
                    if pid == last_id {
                        assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                        assert(post.pages[pid].offset == pre.pages[pid].offset);
                    }
                }
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
            }
        }
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            pre.segments.dom().contains(sid)
            && post.segments[sid].used == pre.segments[sid].used
            && post.popped_ec(sid) == pre.popped_ec(sid)
        by {
            reveal(State::popped_ec);
            reveal(State::ec_of_popped);
            assert(post.segments == pre.segments);
            assert(pre.popped == Popped::Used(page_id, true));
            assert(post.popped == Popped::No);
        }
        Self::count_is_right_preserve_all(pre, post);

        assert(pre.unused_lists == post.unused_lists);
        assert(pre.unused_dlist_headers == post.unused_dlist_headers);
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by {
            assert(pid != page_id);
            if pre.used_dlist_headers[bin_idx].last.is_some() {
                let last_id = pre.used_dlist_headers[bin_idx].last.unwrap();
                if pid == last_id {
                    assert(pre.pages[pid].is_used);
                    assert(false);
                }
            }
            assert(post.pages[pid] == pre.pages[pid]);
        }
        Self::unchanged_unused_ll(pre, post);
        reveal(State::data_for_unused_header);
        assert(post.ll_inv_valid_unused());
        Self::into_used_list_inductive_ll_inv_exists_in_some_list(pre, post, bin_idx);
        reveal(State::ll_inv_valid_unused2);
        assert(post.ll_inv_valid_unused2());
        Self::into_used_list_back_inductive_ll_inv_valid_used(pre, post, bin_idx);
        Self::into_used_list_back_inductive_ll_inv_valid_used2(pre, post, bin_idx);
    }

    proof fn into_used_list_back_inductive_ll_inv_valid_used(pre: Self, post: Self, bin_idx: int)
        requires
            pre.invariant(),
            State::into_used_list_back_strong(pre, post, bin_idx),
        ensures
            post.ll_inv_valid_used(),
    {
        reveal(State::ll_basics);
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);
        reveal(State::inv_used);
        reveal(State::good_range_used);

        let page_id = pre.popped.get_Used_0();
        let old_ll = pre.used_lists[bin_idx];
        let new_ll = old_ll.push(page_id);
        assert(pre.popped == Popped::Used(page_id, true));
        assert(post.used_lists =~= Self::insert_back(pre.used_lists, bin_idx, page_id));
        assert(pre.good_range_used(page_id));
        assert(pre.pages[page_id].dlist_entry.is_none());
        assert(post.pages[page_id].dlist_entry.is_some());
        assert(post.pages[page_id].full == Some(bin_idx == BIN_FULL));

        pre.first_last_ll_stuff_used(bin_idx);

        assert forall |i: int|
            #![trigger post.used_dlist_headers.index(i)]
            0 <= i < post.used_lists.len()
        implies
            valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            if i == bin_idx {
                assert(post.used_lists[i] == new_ll);
                assert(post.used_dlist_headers[i].last == Some(page_id));
                if old_ll.len() == 0 {
                    assert(pre.used_dlist_headers[i].first.is_none());
                    assert(pre.used_dlist_headers[i].last.is_none());
                    assert(new_ll.len() == 1);
                    assert(new_ll[0] == page_id);
                    assert(post.used_dlist_headers[i].first == Some(page_id));
                } else {
                    assert(pre.used_dlist_headers[i].first.is_some());
                    assert(pre.used_dlist_headers[i].last.is_some());
                    assert(pre.used_dlist_headers[i].last == Some(old_ll[old_ll.len() - 1]));
                    assert(new_ll.len() == old_ll.len() + 1);
                    assert(new_ll[old_ll.len() as int] == page_id);
                    assert(new_ll[0] == old_ll[0]);
                    assert(post.used_dlist_headers[i].first == pre.used_dlist_headers[i].first);
                    assert(post.used_dlist_headers[i].first == Some(new_ll[0]));
                }
                assert forall |j: int|
                    0 <= j < post.used_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.used_lists[i], j)
                by {
                    if j == old_ll.len() {
                        assert(post.used_lists[i][j] == page_id);
                        assert(post.pages[page_id].dlist_entry.unwrap().next == None);
                        assert(get_next(post.used_lists[i], j) == None);
                        if old_ll.len() == 0 {
                            assert(post.pages[page_id].dlist_entry.unwrap().prev == None);
                            assert(get_prev(post.used_lists[i], j) == None);
                        } else {
                            let old_last = old_ll[old_ll.len() - 1];
                            assert(pre.used_dlist_headers[bin_idx].last == Some(old_last));
                            assert(post.pages[page_id].dlist_entry.unwrap().prev == Some(old_last));
                            assert(get_prev(post.used_lists[i], j) == Some(old_last));
                        }
                    } else {
                        let old_j = j;
                        assert(0 <= old_j < old_ll.len());
                        assert(post.used_lists[i][j] == old_ll[old_j]);
                        let pid = post.used_lists[i][j];
                        pre.popped_used_not_in_used_list(bin_idx, old_j);
                        assert(pid != page_id);
                        assert(valid_ll_i(pre.pages, old_ll, old_j));
                        if old_j == old_ll.len() - 1 {
                            assert(pre.used_dlist_headers[bin_idx].last == Some(pid));
                            assert(post.pages[pid].dlist_entry.unwrap().next == Some(page_id));
                            assert(get_next(post.used_lists[i], j) == Some(page_id));
                        } else {
                            pre.ll_used_distinct(bin_idx, old_j, bin_idx, old_ll.len() - 1);
                            assert(pid != old_ll[old_ll.len() - 1]);
                            assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                            assert(get_next(post.used_lists[i], j) == get_next(old_ll, old_j));
                        }
                        assert(get_prev(post.used_lists[i], j) == get_prev(old_ll, old_j));
                    }
                }
            } else {
                assert(post.used_lists[i] == pre.used_lists[i]);
                assert(post.used_dlist_headers[i] == pre.used_dlist_headers[i]);
                assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
                assert forall |j: int|
                    0 <= j < post.used_lists[i].len()
                implies
                    valid_ll_i(post.pages, post.used_lists[i], j)
                by {
                    let pid = post.used_lists[i][j];
                    assert(valid_ll_i(pre.pages, pre.used_lists[i], j));
                    pre.popped_used_not_in_used_list(i, j);
                    assert(pid != page_id);
                    if old_ll.len() != 0 {
                        let last_id = old_ll[old_ll.len() - 1];
                        if pid == last_id {
                            pre.ll_used_distinct(i, j, bin_idx, old_ll.len() - 1);
                            assert(false);
                        }
                    }
                    assert(post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry);
                }
            }
        }

        assert forall |i: int, j: int|
            0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len()
            && #[trigger] post.used_lists.index(i).index(j) == post.used_lists.index(i).index(j)
        implies
            ({
                let pid = post.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& post.valid_used_page(pid, i, j)
                &&& post.pages[pid].count.is_some()
                &&& (post.popped.is_Ready() ==> pid != post.popped_page_id())
            })
        by {
            let pid = post.used_lists[i][j];
            if i == bin_idx && j == old_ll.len() {
                assert(pid == page_id);
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].count.is_some());
                assert(post.pages[pid].offset == Some(0nat));
                assert(post.pages[pid].is_used);
                assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, bsize)) => {
                        assert(valid_bin_idx(bin));
                        assert(size_of_bin(bin) == bsize);
                        assert(bin_idx != BIN_FULL ==> bin_idx == bin);
                    }
                    None => { assert(false); }
                }
            } else {
                let old_j = j;
                if i == bin_idx {
                    assert(0 <= old_j < old_ll.len());
                    assert(pid == old_ll[old_j]);
                    pre.popped_used_not_in_used_list(bin_idx, old_j);
                } else {
                    assert(pid == pre.used_lists[i][j]);
                    pre.popped_used_not_in_used_list(i, j);
                }
                assert(pid != page_id);
                assert(pre.valid_used_page(pid, i, old_j));
                assert(post.pages[pid].is_used == pre.pages[pid].is_used);
                assert(post.pages[pid].count == pre.pages[pid].count);
                assert(post.pages[pid].offset == pre.pages[pid].offset);
                assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                assert(post.pages[pid].dlist_entry.is_some());
                assert(!post.popped.is_Ready());
            }
        }
        assert(post.ll_inv_valid_used());
    }

    proof fn into_used_list_back_inductive_ll_inv_valid_used2(pre: Self, post: Self, bin_idx: int)
        requires
            pre.invariant(),
            State::into_used_list_back_strong(pre, post, bin_idx),
        ensures
            post.ll_inv_valid_used2(),
    {
        reveal(State::ll_inv_valid_used2);
        reveal(State::valid_used_page);
        let page_id = pre.popped.get_Used_0();
        let old_ll = pre.used_lists[bin_idx];
        assert(pre.popped == Popped::Used(page_id, true));
        assert(post.popped == Popped::No);
        assert(post.used_lists =~= Self::insert_back(pre.used_lists, bin_idx, page_id));

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(false)
        implies
            is_in_list_at(pid, post.used_lists, BIN_FULL as int)
        by {
            if pid == page_id {
                assert(post.pages[pid].full == Some(bin_idx == BIN_FULL));
                assert(bin_idx == BIN_FULL);
                assert(0 <= bin_idx < post.used_lists.len()) by {
                    reveal(State::ll_basics);
                };
                assert(post.used_lists[bin_idx][old_ll.len() as int] == page_id);
                assert(is_in_list_at(pid, post.used_lists, BIN_FULL as int));
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used);
                assert(pre.pages[pid].offset == Some(0nat));
                assert(pre.pages[pid].full == post.pages[pid].full);
                assert(pre.pages[pid].full != Some(false));
                assert(is_in_list_at(pid, pre.used_lists, BIN_FULL as int));
                Self::ll_insert_back_preserves_list_at(
                    pre.used_lists, post.used_lists, bin_idx, page_id, pid, BIN_FULL as int);
                assert(is_in_list_at(pid, post.used_lists, BIN_FULL as int));
            }
        }

        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No()
                || (post.popped.is_Used() && pid != post.popped_page_id()))
            && post.pages[pid].is_used
            && post.pages[pid].offset == Some(0nat)
            && post.pages[pid].full != Some(true)
        implies
            (match post.pages[pid].page_header_kind {
                Some(PageHeaderKind::Normal(bin, _)) =>
                    is_in_list_at(pid, post.used_lists, bin),
                None => false,
            })
        by {
            if pid == page_id {
                assert(post.pages[pid].full == Some(bin_idx == BIN_FULL));
                assert(bin_idx != BIN_FULL);
                assert(post.pages[pid].page_header_kind == pre.pages[pid].page_header_kind);
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, _)) => {
                        assert(bin_idx == bin);
                        assert(0 <= bin_idx < post.used_lists.len()) by {
                            reveal(State::ll_basics);
                        };
                        assert(post.used_lists[bin_idx][old_ll.len() as int] == page_id);
                        assert(is_in_list_at(pid, post.used_lists, bin));
                    }
                    None => { assert(false); }
                }
            } else {
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used);
                assert(pre.pages[pid].offset == Some(0nat));
                assert(pre.pages[pid].full == post.pages[pid].full);
                assert(pre.pages[pid].full != Some(true));
                assert(pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind);
                match post.pages[pid].page_header_kind {
                    Some(PageHeaderKind::Normal(bin, _)) => {
                        assert(is_in_list_at(pid, pre.used_lists, bin));
                        Self::ll_insert_back_preserves_list_at(
                            pre.used_lists, post.used_lists, bin_idx, page_id, pid, bin);
                        assert(is_in_list_at(pid, post.used_lists, bin));
                    }
                    None => { assert(false); }
                }
            }
        }
    }

    pub proof fn preserved_by_into_used_list_back(pre: Self, post: Self,
        bin_idx: int, other_page_id: PageId, other_bin_idx: int, other_list_idx: int)
        requires State::into_used_list_back_strong(pre, post, bin_idx),
            pre.invariant(),
            pre.valid_used_page(other_page_id, other_bin_idx, other_list_idx)
        ensures
            post.valid_used_page(other_page_id, other_bin_idx, other_list_idx)
    {
        reveal(State::valid_used_page);
        assert(pre.pages[other_page_id].dlist_entry.is_some());
        assert(pre.popped.is_Used());
        let page_id = pre.popped.get_Used_0();
        assert(pre.pages[page_id].dlist_entry.is_none());
        assert(other_page_id != page_id);

        if pre.used_dlist_headers[bin_idx].last.is_some() {
            let last_id = pre.used_dlist_headers[bin_idx].last.unwrap();
            if other_page_id == last_id {
                assert(post.pages[other_page_id].dlist_entry.is_some());
            } else {
                assert(post.pages[other_page_id] == pre.pages[other_page_id]);
            }
        } else {
            assert(post.pages[other_page_id] == pre.pages[other_page_id]);
        }

        if other_bin_idx == bin_idx {
            assert(post.used_lists[other_bin_idx][other_list_idx]
                == pre.used_lists[other_bin_idx][other_list_idx]);
        } else {
            assert(post.used_lists[other_bin_idx] == pre.used_lists[other_bin_idx]);
        }
    }

    pub proof fn preserved_by_out_of_used_list(pre: Self, post: Self,
        page_id: PageId, bin_idx: int, list_idx: int,
        next_page_id: PageId)
        requires State::out_of_used_list_strong(pre, post, page_id, bin_idx, list_idx),
            pre.invariant(),
            pre.valid_used_page(next_page_id, bin_idx, list_idx + 1)
        ensures
            post.valid_used_page(next_page_id, bin_idx, list_idx)
    {
        reveal(State::valid_used_page);
        pre.used_lists[bin_idx].remove_ensures(list_idx);
        assert(pre.valid_used_page(page_id, bin_idx, list_idx));
        pre.ll_used_distinct(bin_idx, list_idx, bin_idx, list_idx + 1);
        assert(next_page_id != page_id);
        assert(post.used_lists[bin_idx] == pre.used_lists[bin_idx].remove(list_idx));
        assert(post.used_lists[bin_idx][list_idx] == pre.used_lists[bin_idx][list_idx + 1]);
        assert(post.used_lists[bin_idx][list_idx] == next_page_id);
        assert(post.pages[next_page_id].is_used == pre.pages[next_page_id].is_used);
        assert(post.pages[next_page_id].offset == pre.pages[next_page_id].offset);
        assert(post.pages[next_page_id].page_header_kind == pre.pages[next_page_id].page_header_kind);
        assert(post.pages[next_page_id].dlist_entry.is_some());
    }

    #[inductive(forget_about_first_page2)]
    fn forget_about_first_page2_inductive(pre: Self, post: Self) {
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::end_is_unused);
        reveal(State::count_is_right);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::good_range_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::attached_ranges);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        reveal(State::does_count);

        let segment_id = pre.popped.get_VeryUnready_0();
        let start = pre.popped.get_VeryUnready_1();
        let count = pre.popped.get_VeryUnready_2();
        assert(pre.popped == Popped::VeryUnready(segment_id, start, count, true));
        assert(post.popped == Popped::VeryUnready(segment_id, start, count, false));
        assert(post.pages == pre.pages);
        assert(post.segments == pre.segments.insert(segment_id, SegmentData {
            used: pre.segments[segment_id].used - 1,
        }));
        assert(post.unused_lists == pre.unused_lists);
        assert(post.unused_dlist_headers == pre.unused_dlist_headers);
        assert(post.used_lists == pre.used_lists);
        assert(post.used_dlist_headers == pre.used_dlist_headers);

        assert(post.segments.dom() =~= pre.segments.dom());
        assert(post.page_id_domain());
        assert(post.count_off0());
        assert(post.popped_basics());
        assert(post.inv_segment_creating());
        assert(post.inv_very_unready());

        assert(Self::popped_ranges_match_for_sid(pre, post, segment_id)) by {
            reveal(State::popped_ranges_match_for_sid);
            reveal(State::popped_for_seg);
            reveal(State::popped_len);
            reveal(State::page_id_of_popped);
        };
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == segment_id
        implies
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> (
                (!pre.in_popped_range(pid) && pid.idx >= start ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })))
        by { };
        pre.attached_ranges_very_unready_start();
        assert(pre.attached_rec(segment_id, start, true));
        Self::attached_rec_same(pre, post, segment_id, start, true);
        assert(Self::popped_ranges_match(pre, post)) by {
            reveal(State::popped_ranges_match);
            reveal(State::is_any_the_popped);
            reveal(State::popped_len);
            reveal(State::page_id_of_popped);
        };
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })
        by {
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::attached_ranges_all(pre, post);
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(post.inv_segment_freeing());
        assert(post.inv_ready());
        assert(post.inv_used());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by { };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        assert(post.data_for_used_header());
        assert(post.ll_inv_valid_used2());
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by { };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());
        reveal(State::ll_inv_exists_in_some_list);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(post.pages[pid] == pre.pages[pid]);
            reveal(State::in_popped_range);
            assert(!pre.in_popped_range(pid));
            assert(is_in_lls(pid, pre.unused_lists));
        };
        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(post.pages[pid] == pre.pages[pid]);
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());
        assert(post.ready_popped_not_in_unused_lists());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by { };
        Self::ucount_preserve_all(pre, post);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            assert(pre.segments.dom().contains(sid));
            assert(pre.ucount(sid) == post.ucount(sid));
            if sid == segment_id {
                assert(pre.popped_ec(sid) == 1);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used - 1);
                assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
            }
        };
        assert(post.count_is_right());
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
            && !(match post.popped {
                Popped::SegmentCreating(psid) => psid == sid,
                Popped::SegmentFreeing(psid, _) => psid == sid,
                _ => false,
            })
            && post.segments[sid].used == post.popped_ec(sid)
        implies
            ({
                let page_id = PageId { segment_id: sid, idx: 0 };
                &&& post.pages.dom().contains(page_id)
                &&& post.pages[page_id].offset == Some(0nat)
                &&& !post.pages[page_id].is_used
                &&& post.pages[page_id].count.is_some()
            })
        by {
            let page_id = PageId { segment_id: sid, idx: 0 };
            if sid == segment_id {
                assert(pre.popped_ec(sid) == 1);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used - 1);
                assert(pre.segments[sid].used == pre.popped_ec(sid));
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(pre.segments[sid].used == pre.popped_ec(sid));
            }
            assert(pre.pages[page_id] == post.pages[page_id]);
        };
        assert(post.end_is_unused());
    }

    #[inductive(clear_ec)]
    fn clear_ec_inductive(pre: Self, post: Self) {
        reveal(State::page_id_domain);
        reveal(State::count_off0);
        reveal(State::end_is_unused);
        reveal(State::count_is_right);
        reveal(State::popped_basics);
        reveal(State::inv_segment_creating);
        reveal(State::inv_very_unready);
        reveal(State::inv_segment_freeing);
        reveal(State::inv_ready);
        reveal(State::inv_used);
        reveal(State::attached_ranges);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        reveal(State::does_count);

        let segment_id = pre.popped.get_ExtraCount_0();
        assert(pre.popped == Popped::ExtraCount(segment_id));
        assert(post.popped == Popped::No);
        assert(post.pages == pre.pages);
        assert(post.segments == pre.segments.insert(segment_id, SegmentData {
            used: pre.segments[segment_id].used - 1,
        }));
        assert(post.unused_lists == pre.unused_lists);
        assert(post.unused_dlist_headers == pre.unused_dlist_headers);
        assert(post.used_lists == pre.used_lists);
        assert(post.used_dlist_headers == pre.used_dlist_headers);

        assert(post.segments.dom() =~= pre.segments.dom());
        assert(post.page_id_domain());
        assert(post.count_off0());
        assert(post.popped_basics());
        assert(post.inv_segment_creating());
        assert(post.inv_very_unready());
        assert(Self::popped_ranges_match(pre, post)) by {
            reveal(State::popped_ranges_match);
            reveal(State::is_any_the_popped);
        };
        assert forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
            })
        by {
            assert(post.pages[pid] == pre.pages[pid]);
        };
        Self::attached_ranges_all(pre, post);
        Self::attached_ranges_from_segments(post);
        assert(post.attached_ranges());
        assert(post.inv_segment_freeing());
        assert(post.inv_ready());
        assert(post.inv_used());

        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by { };
        Self::unchanged_used_ll(pre, post);
        assert(post.ll_inv_valid_used());
        assert(post.data_for_used_header());
        assert(post.ll_inv_valid_used2());
        assert forall |pid: PageId|
            pre.pages.dom().contains(pid)
            && !pre.pages[pid].is_used
        implies
            post.pages.dom().contains(pid)
            && post.pages[pid].dlist_entry == pre.pages[pid].dlist_entry
        by { };
        Self::unchanged_unused_ll(pre, post);
        assert(post.ll_inv_valid_unused());
        assert(post.data_for_unused_header());
        reveal(State::ll_inv_exists_in_some_list);
        assert forall |pid: PageId|
            #![trigger post.pages.dom().contains(pid)]
            #![trigger post.pages.index(pid)]
            post.pages.dom().contains(pid)
            && (post.popped.is_No() || post.popped.is_ExtraCount()
                || post.popped.is_Ready() || post.popped.is_Used()
                || post.popped.is_VeryUnready() || post.popped.is_SegmentFreeing())
            && !post.in_popped_range(pid)
            && post.pages[pid].offset == Some(0nat)
            && !post.pages[pid].is_used
            && pid.idx != 0
        implies
            post.pages[pid].count.is_some()
            && is_in_lls(pid, post.unused_lists)
        by {
            assert(post.pages[pid] == pre.pages[pid]);
            assert(is_in_lls(pid, pre.unused_lists));
        };
        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists[i][j] == post.unused_lists[i][j]
        implies
            i == smallest_sbin_fitting_size(
                post.pages[post.unused_lists[i][j]].count.unwrap() as int)
        by {
            let pid = post.unused_lists[i][j];
            assert(pid == pre.unused_lists[i][j]);
            assert(post.pages[pid] == pre.pages[pid]);
        };
        assert(post.ll_inv_exists_in_some_list());
        assert(post.ll_inv_valid_unused2());
        assert(post.ready_popped_not_in_unused_lists());

        assert forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid) by { };
        Self::ucount_preserve_all(pre, post);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            assert(pre.segments.dom().contains(sid));
            assert(pre.ucount(sid) == post.ucount(sid));
            if sid == segment_id {
                assert(pre.popped_ec(sid) == 1);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used - 1);
                assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
            }
        };
        assert(post.count_is_right());
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
            && !(match post.popped {
                Popped::SegmentCreating(psid) => psid == sid,
                Popped::SegmentFreeing(psid, _) => psid == sid,
                _ => false,
            })
            && post.segments[sid].used == post.popped_ec(sid)
        implies
            ({
                let page_id = PageId { segment_id: sid, idx: 0 };
                &&& post.pages.dom().contains(page_id)
                &&& post.pages[page_id].offset == Some(0nat)
                &&& !post.pages[page_id].is_used
                &&& post.pages[page_id].count.is_some()
            })
        by {
            let page_id = PageId { segment_id: sid, idx: 0 };
            if sid == segment_id {
                assert(pre.popped_ec(sid) == 1);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used - 1);
                assert(pre.segments[sid].used == pre.popped_ec(sid));
            } else {
                assert(pre.popped_ec(sid) == 0);
                assert(post.popped_ec(sid) == 0);
                assert(post.segments[sid].used == pre.segments[sid].used);
                assert(pre.segments[sid].used == pre.popped_ec(sid));
            }
            assert(pre.pages[page_id] == post.pages[page_id]);
        };
        assert(post.end_is_unused());
    }

    pub proof fn used_ll_stuff(&self, i: int, j: int)
        requires self.invariant(),
            0 <= i < self.used_lists.len(),
            0 <= j < self.used_lists[i].len(),
        ensures
            self.pages.dom().contains(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].is_used == true,
            self.pages[self.used_lists[i][j]].count.is_some(),
            self.pages[self.used_lists[i][j]].dlist_entry.is_some(),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev != Some(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next != Some(self.used_lists[i][j]),
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev != self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next,

            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap())
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == true,
            self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.is_some() ==>
                self.pages.dom().contains(self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap())
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.used_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == true,

    {
        reveal(State::data_for_used_header);
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);

        let page_id = self.used_lists[i][j];
        let ll = self.used_lists[i];
        assert(valid_ll(self.pages, self.used_dlist_headers[i], ll));
        assert(self.valid_used_page(page_id, i, j));
        assert(self.pages.dom().contains(page_id));
        assert(self.pages[page_id].is_used == true);
        assert(self.pages[page_id].count.is_some());
        assert(self.pages[page_id].dlist_entry.is_some());
        assert(valid_ll_i(self.pages, ll, j));

        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        assert(dlist_entry.prev == get_prev(ll, j));
        assert(dlist_entry.next == get_next(ll, j));

        match dlist_entry.prev {
            Some(prev_page_id) => {
                assert(j != 0);
                assert(prev_page_id == ll[j - 1]);
                assert(0 <= j - 1 < ll.len());
                assert(self.used_lists[i][j - 1] == prev_page_id);
                assert(self.valid_used_page(prev_page_id, i, j - 1));
                assert(self.pages.dom().contains(prev_page_id));
                assert(self.pages[prev_page_id].dlist_entry.is_some());
                assert(self.pages[prev_page_id].is_used == true);
                valid_ll_distinct(self.pages, self.used_dlist_headers[i], ll, j - 1, j);
                assert(prev_page_id != page_id);
            }
            None => { }
        }

        match dlist_entry.next {
            Some(next_page_id) => {
                assert(j != ll.len() - 1);
                assert(next_page_id == ll[j + 1]);
                assert(0 <= j + 1 < ll.len());
                assert(self.used_lists[i][j + 1] == next_page_id);
                assert(self.valid_used_page(next_page_id, i, j + 1));
                assert(self.pages.dom().contains(next_page_id));
                assert(self.pages[next_page_id].dlist_entry.is_some());
                assert(self.pages[next_page_id].is_used == true);
                valid_ll_distinct(self.pages, self.used_dlist_headers[i], ll, j, j + 1);
                assert(next_page_id != page_id);
            }
            None => { }
        }

        if dlist_entry.prev.is_some() {
            if dlist_entry.next.is_some() {
                let prev_page_id = dlist_entry.prev.unwrap();
                let next_page_id = dlist_entry.next.unwrap();
                assert(j != 0);
                assert(j != ll.len() - 1);
                assert(prev_page_id == ll[j - 1]);
                assert(next_page_id == ll[j + 1]);
                assert(0 <= j - 1 < ll.len());
                assert(0 <= j + 1 < ll.len());
                valid_ll_distinct(self.pages, self.used_dlist_headers[i], ll, j - 1, j + 1);
                assert(prev_page_id != next_page_id);
            }
        }
    }

    pub proof fn unused_ll_stuff(&self, i: int, j: int)
        requires self.invariant(),
            0 <= i < self.unused_lists.len(),
            0 <= j < self.unused_lists[i].len(),
        ensures
            self.pages.dom().contains(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].is_used == false,
            self.pages[self.unused_lists[i][j]].count.is_some(),
            self.pages[self.unused_lists[i][j]].dlist_entry.is_some(),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev != Some(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next != Some(self.unused_lists[i][j]),
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev != self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next,

            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.is_some() ==>
                self.pages.dom().contains(self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap())
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().prev.unwrap()].is_used == false,
            self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.is_some() ==>
                self.pages.dom().contains(self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap())
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap()].dlist_entry.is_some()
                && self.pages[self.pages[self.unused_lists[i][j]].dlist_entry.unwrap().next.unwrap()].is_used == false,
    {
        reveal(State::data_for_unused_header);
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);

        let page_id = self.unused_lists[i][j];
        let ll = self.unused_lists[i];
        assert(valid_ll(self.pages, self.unused_dlist_headers[i], ll));
        assert(self.valid_unused_page(page_id, i, j));
        assert(self.pages.dom().contains(page_id));
        assert(self.pages[page_id].is_used == false);
        assert(self.pages[page_id].count.is_some());
        assert(self.pages[page_id].dlist_entry.is_some());
        assert(valid_ll_i(self.pages, ll, j));

        let dlist_entry = self.pages[page_id].dlist_entry.unwrap();
        assert(dlist_entry.prev == get_prev(ll, j));
        assert(dlist_entry.next == get_next(ll, j));

        match dlist_entry.prev {
            Some(prev_page_id) => {
                assert(j != 0);
                assert(prev_page_id == ll[j - 1]);
                assert(0 <= j - 1 < ll.len());
                assert(self.unused_lists[i][j - 1] == prev_page_id);
                assert(self.valid_unused_page(prev_page_id, i, j - 1));
                assert(self.pages.dom().contains(prev_page_id));
                assert(self.pages[prev_page_id].dlist_entry.is_some());
                assert(self.pages[prev_page_id].is_used == false);
                valid_ll_distinct(self.pages, self.unused_dlist_headers[i], ll, j - 1, j);
                assert(prev_page_id != page_id);
            }
            None => { }
        }

        match dlist_entry.next {
            Some(next_page_id) => {
                assert(j != ll.len() - 1);
                assert(next_page_id == ll[j + 1]);
                assert(0 <= j + 1 < ll.len());
                assert(self.unused_lists[i][j + 1] == next_page_id);
                assert(self.valid_unused_page(next_page_id, i, j + 1));
                assert(self.pages.dom().contains(next_page_id));
                assert(self.pages[next_page_id].dlist_entry.is_some());
                assert(self.pages[next_page_id].is_used == false);
                valid_ll_distinct(self.pages, self.unused_dlist_headers[i], ll, j, j + 1);
                assert(next_page_id != page_id);
            }
            None => { }
        }

        if dlist_entry.prev.is_some() {
            if dlist_entry.next.is_some() {
                let prev_page_id = dlist_entry.prev.unwrap();
                let next_page_id = dlist_entry.next.unwrap();
                assert(j != 0);
                assert(j != ll.len() - 1);
                assert(prev_page_id == ll[j - 1]);
                assert(next_page_id == ll[j + 1]);
                assert(0 <= j - 1 < ll.len());
                assert(0 <= j + 1 < ll.len());
                valid_ll_distinct(self.pages, self.unused_dlist_headers[i], ll, j - 1, j + 1);
                assert(prev_page_id != next_page_id);
            }
        }
    }

    pub closed spec fn page_id_of_popped(p: Popped) -> PageId {
        match p {
            Popped::Ready(page_id, _) => page_id,
            Popped::Used(page_id, _) => page_id,
            Popped::VeryUnready(segment_id, idx, _, _) => PageId { segment_id, idx: idx as nat },
            _ => arbitrary(),
        }
    }

    pub closed spec fn popped_page_id(&self) -> PageId {
        Self::page_id_of_popped(self.popped)
    }

    pub closed spec fn expect_out_of_lists(&self, pid: PageId) -> bool {
        match self.popped {
            Popped::No => false,
            Popped::ExtraCount(_) => false,
            Popped::Ready(page_id, _) => pid == page_id,
            Popped::Used(page_id, _) => pid == page_id,
            Popped::SegmentCreating(segment_id) => false,
            Popped::SegmentFreeing(segment_id, idx) => pid.segment_id == segment_id && pid.idx < idx,
            Popped::VeryUnready(segment_id, start, _, _) => false,
        }
    }

    pub closed spec fn ec_of_popped(p: Popped, segment_id: SegmentId) -> int {
        match p {
            Popped::No => 0,
            Popped::Ready(p, b) => if p.segment_id == segment_id && b { 1 } else { 0 },
            Popped::Used(p, b) => if p.segment_id == segment_id {
                if b { 0 } else { -1 }
              } else { 0 }
            Popped::SegmentCreating(_) => 0,
            Popped::VeryUnready(sid, _, _, b) => if segment_id == sid && b { 1 } else { 0 },
            Popped::SegmentFreeing(_, _) => 0,
            Popped::ExtraCount(sid) => if segment_id == sid { 1 } else { 0 },
        }
    }

    pub closed spec fn popped_ec(&self, segment_id: SegmentId) -> int {
        Self::ec_of_popped(self.popped, segment_id)
    }

    #[verifier::opaque]
    pub closed spec fn ucount(&self, segment_id: SegmentId) -> nat {
        self.ucount_sum(segment_id, SLICES_PER_SEGMENT as int)
    }

    pub closed spec fn ucount_sum(&self, segment_id: SegmentId, idx: int) -> nat
        decreases idx
    {
        if idx <= 0 {
            0
        } else {
            self.ucount_sum(segment_id, idx - 1)
              + self.one_count(PageId { segment_id, idx: (idx - 1) as nat })
        }
    }

    pub proof fn first_last_ll_stuff_unused(&self, i: int)
        requires self.invariant(),
            0 <= i < self.unused_lists.len(),
        ensures
            (self.popped.is_Ready())
              ==>
                self.unused_dlist_headers[i].first != Some(self.popped_page_id())
                && self.unused_dlist_headers[i].last != Some(self.popped_page_id()),
            (match self.unused_dlist_headers[i].first {
                Some(first_id) => self.pages.dom().contains(first_id)
                  && is_unused_header(self.pages[first_id])
                  && self.pages[first_id].dlist_entry.is_some(),
                None => true,
            }),
            (match self.unused_dlist_headers[i].last {
                Some(last_id) => self.pages.dom().contains(last_id)
                  && is_unused_header(self.pages[last_id])
                  && self.pages[last_id].dlist_entry.is_some(),
                None => true,
            }),
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::ready_popped_not_in_unused_lists);
        reveal(State::valid_unused_page);

        let header = self.unused_dlist_headers[i];
        let ll = self.unused_lists[i];
        assert(valid_ll(self.pages, header, ll));

        match header.first {
            Some(first_id) => {
                assert(ll.len() != 0);
                assert(ll[0] == first_id);
                assert(0 <= 0 < ll.len());
                assert(self.unused_lists[i][0] == first_id);
                assert(self.valid_unused_page(first_id, i, 0));
                assert(self.pages.dom().contains(first_id));
                assert(self.pages[first_id].is_used == false);
                assert(self.pages[first_id].offset == Some(0nat));
                assert(self.pages[first_id].dlist_entry.is_some());
                assert(is_unused_header(self.pages[first_id]));
                if self.popped.is_Ready() {
                    assert(first_id != self.popped_page_id());
                }

                match header.last {
                    Some(_) => { }
                    None => {
                        assert(ll.len() == 0);
                        assert(false);
                    }
                }
            }
            None => {
                assert(ll.len() == 0);
                match header.last {
                    Some(_) => {
                        assert(ll.len() != 0);
                        assert(false);
                    }
                    None => { }
                }
            }
        }

        match header.last {
            Some(last_id) => {
                assert(ll.len() != 0);
                let last_idx = ll.len() - 1;
                assert(0 <= last_idx < ll.len());
                assert(ll[last_idx] == last_id);
                assert(self.unused_lists[i][last_idx] == last_id);
                assert(self.valid_unused_page(last_id, i, last_idx));
                assert(self.pages.dom().contains(last_id));
                assert(self.pages[last_id].is_used == false);
                assert(self.pages[last_id].offset == Some(0nat));
                assert(self.pages[last_id].dlist_entry.is_some());
                assert(is_unused_header(self.pages[last_id]));
                if self.popped.is_Ready() {
                    assert(last_id != self.popped_page_id());
                }
            }
            None => { }
        }
    }

    pub proof fn first_last_ll_stuff_used(&self, i: int)
        requires self.invariant(),
            0 <= i < self.used_lists.len(),
        ensures
            (self.popped.is_Ready())
              ==>
                self.used_dlist_headers[i].first != Some(self.popped_page_id())
                && self.used_dlist_headers[i].last != Some(self.popped_page_id()),
            self.used_dlist_headers[i].first.is_some() <==>
                self.used_dlist_headers[i].last.is_some(),
            (match self.used_dlist_headers[i].first {
                Some(first_id) => self.pages.dom().contains(first_id)
                  && is_used_header(self.pages[first_id])
                  && self.pages[first_id].dlist_entry.is_some(),
                None => true,
            }),
            (match self.used_dlist_headers[i].last {
                Some(last_id) => self.pages.dom().contains(last_id)
                  && is_used_header(self.pages[last_id])
                  && self.pages[last_id].dlist_entry.is_some(),
                None => true,
            }),
    {
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);

        let header = self.used_dlist_headers[i];
        let ll = self.used_lists[i];
        assert(valid_ll(self.pages, header, ll));

        match header.first {
            Some(first_id) => {
                assert(ll.len() != 0);
                assert(ll[0] == first_id);
                assert(0 <= 0 < ll.len());
                assert(self.used_lists[i][0] == first_id);
                assert(self.valid_used_page(first_id, i, 0));
                assert(self.pages.dom().contains(first_id));
                assert(self.pages[first_id].is_used == true);
                assert(self.pages[first_id].offset == Some(0nat));
                assert(self.pages[first_id].dlist_entry.is_some());
                assert(is_used_header(self.pages[first_id]));
                if self.popped.is_Ready() {
                    assert(first_id != self.popped_page_id());
                }

                match header.last {
                    Some(_) => { }
                    None => {
                        assert(ll.len() == 0);
                        assert(false);
                    }
                }
            }
            None => {
                assert(ll.len() == 0);
                match header.last {
                    Some(_) => {
                        assert(ll.len() != 0);
                        assert(false);
                    }
                    None => { }
                }
            }
        }
        assert(header.first.is_some() <==> header.last.is_some());

        match header.last {
            Some(last_id) => {
                assert(ll.len() != 0);
                let last_idx = ll.len() - 1;
                assert(0 <= last_idx < ll.len());
                assert(ll[last_idx] == last_id);
                assert(self.used_lists[i][last_idx] == last_id);
                assert(self.valid_used_page(last_id, i, last_idx));
                assert(self.pages.dom().contains(last_id));
                assert(self.pages[last_id].is_used == true);
                assert(self.pages[last_id].offset == Some(0nat));
                assert(self.pages[last_id].dlist_entry.is_some());
                assert(is_used_header(self.pages[last_id]));
                if self.popped.is_Ready() {
                    assert(last_id != self.popped_page_id());
                }
            }
            None => { }
        }
    }

    /*pub proof fn lemma_range_not_header(&self, page_id: PageId, next_id: PageId)
        requires
            self.invariant(),
            self.popped.is_VeryUnready(),
            page_id.segment_id == next_id.segment_id,
            self.pages.dom().contains(page_id),
            page_id.idx == self.popped.get_VeryUnready_1(),
            next_id.segment_id == page_id.segment_id,
            page_id.idx < next_id.idx < page_id.idx + self.popped.get_VeryUnready_2(),
        ensures
            self.pages[next_id].offset != Some(0nat)
    {
        if page_id.segment_id == self.popped.get_VeryUnready_0()
            && page_id.idx == self.popped.get_VeryUnready_1()
        {
            assert(self.pages[next_id].offset != Some(0nat));
        } else if page_id.idx == 0 {
            assert(self.pages[next_id].offset != Some(0nat));
        } else {
            assert(self.pages[next_id].offset != Some(0nat));
            /*if self.pages[page_id].is_used {
                self.lemma_range_used(page_id);
                assert(self.pages[next_id].offset != Some(0nat));
            } else {
                self.lemma_range_not_used(page_id);
                assert(self.pages[next_id].offset != Some(0nat));
            }*/
        }
    }*/

    pub proof fn lemma_range_not_used(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_unused_header(self.pages[page_id]),
            page_id.idx != 0,
            match self.popped {
                //Popped::SegmentFreeing(sid, idx) =>
                //    page_id.segment_id == sid ==> idx <= page_id.idx,
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            }
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_unused(page_id),
    {
        reveal(State::page_id_domain);
        reveal(State::popped_basics);
        reveal(State::in_popped_range);
        assert(page_id.idx <= SLICES_PER_SEGMENT);
        assert(!self.in_popped_range(page_id)) by {
            if self.in_popped_range(page_id) {
                match self.popped {
                    Popped::Ready(pid, _) => {
                        self.ready_popped_range_facts();
                        let count = self.pages[pid].count.unwrap();
                        assert(pid.segment_id == page_id.segment_id);
                        assert(pid.idx <= page_id.idx < pid.idx + count);
                        assert(self.pages[page_id].offset == Some((page_id.idx - pid.idx) as nat));
                        if pid == page_id {
                            assert(false);
                        } else {
                            assert(page_id.idx - pid.idx > 0);
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        }
                    }
                    Popped::Used(pid, _) => {
                        self.used_popped_range_facts();
                        let count = self.pages[pid].count.unwrap();
                        assert(pid.segment_id == page_id.segment_id);
                        assert(pid.idx <= page_id.idx < pid.idx + count);
                        assert(self.pages[page_id].is_used);
                        assert(false);
                    }
                    Popped::VeryUnready(segment_id, start, count, _) => {
                        self.very_unready_popped_range_facts();
                        assert(segment_id == page_id.segment_id);
                        assert(start <= page_id.idx < start + count);
                        assert(self.pages[page_id].offset.is_none());
                        assert(self.pages[page_id].offset == Some(0nat));
                        assert(false);
                    }
                    _ => {
                        assert(false);
                    }
                }
            }
        };

        reveal(State::ll_inv_exists_in_some_list);
        assert(self.pages[page_id].count.is_some());
        reveal(State::count_off0);
        let page_count = self.pages[page_id].count.unwrap();
        assert(1 <= page_count);
        assert(page_id.idx + page_count <= SLICES_PER_SEGMENT);
        assert(page_id.idx != SLICES_PER_SEGMENT);

        match self.popped {
            Popped::SegmentCreating(segment_id) => {
                if page_id.segment_id == segment_id {
                    self.segment_creating_facts(segment_id);
                    assert(self.pages[page_id].offset.is_none());
                    assert(self.pages[page_id].offset == Some(0nat));
                    assert(false);
                } else {
                    let s = *self;
                    assert forall |sid: SegmentId|
                        sid != segment_id && #[trigger] s.segments.dom().contains(sid)
                    implies s.segments.dom().contains(sid) by { };
                    assert forall |pid: PageId|
                        pid.segment_id != segment_id
                    implies
                        (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                        && (s.pages.dom().contains(pid) ==> {
                            &&& s.pages[pid].count == s.pages[pid].count
                            &&& (s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some())
                            &&& s.pages[pid].offset == s.pages[pid].offset
                            &&& s.pages[pid].is_used == s.pages[pid].is_used
                            &&& s.pages[pid].full == s.pages[pid].full
                            &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                        })
                    by { };
                    reveal(State::if_popped_or_other_then_for);
                    assert(s.if_popped_or_other_then_for(segment_id));
                    Self::attached_ranges_except(s, s, segment_id);
                    assert(s.attached_ranges_segment(page_id.segment_id));
                    assert(self.attached_ranges_segment(page_id.segment_id));
                }
            }
            Popped::SegmentFreeing(segment_id, idx) => {
                if page_id.segment_id == segment_id {
                    reveal(State::inv_segment_freeing);
                    reveal(State::seg_free_prefix);
                    if page_id.idx < idx {
                        assert(self.pages[page_id].offset.is_none());
                        assert(self.pages[page_id].offset == Some(0nat));
                        assert(false);
                    }
                    assert(idx <= page_id.idx);
                    if idx == SLICES_PER_SEGMENT {
                        assert(page_id.idx == SLICES_PER_SEGMENT);
                        assert(false);
                    }
                    assert(idx < SLICES_PER_SEGMENT);
                    assert(self.attached_rec(segment_id, idx, false));
                    self.rec_lemma_range_not_used(page_id, idx, false);
                    return;
                } else {
                    let s = *self;
                    assert forall |sid: SegmentId|
                        sid != segment_id && #[trigger] s.segments.dom().contains(sid)
                    implies s.segments.dom().contains(sid) by { };
                    assert forall |pid: PageId|
                        pid.segment_id != segment_id
                    implies
                        (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                        && (s.pages.dom().contains(pid) ==> {
                            &&& s.pages[pid].count == s.pages[pid].count
                            &&& (s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some())
                            &&& s.pages[pid].offset == s.pages[pid].offset
                            &&& s.pages[pid].is_used == s.pages[pid].is_used
                            &&& s.pages[pid].full == s.pages[pid].full
                            &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                        })
                    by { };
                    reveal(State::if_popped_or_other_then_for);
                    assert(s.if_popped_or_other_then_for(segment_id));
                    Self::attached_ranges_except(s, s, segment_id);
                    assert(s.attached_ranges_segment(page_id.segment_id));
                    assert(self.attached_ranges_segment(page_id.segment_id));
                }
            }
            _ => {
                let s = *self;
                assert(Self::popped_ranges_match(s, s)) by {
                    reveal(State::popped_ranges_match);
                    reveal(State::is_any_the_popped);
                };
                assert(s.segments.dom() =~= s.segments.dom());
                assert forall |pid: PageId|
                    #![trigger s.pages.dom().contains(pid)]
                    #![trigger s.pages[pid]]
                    (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                    && (s.pages.dom().contains(pid) && !s.in_popped_range(pid) ==> {
                        &&& s.pages.dom().contains(pid)
                        &&& s.pages[pid].count == s.pages[pid].count
                        &&& s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some()
                        &&& s.pages[pid].offset == s.pages[pid].offset
                        &&& s.pages[pid].is_used == s.pages[pid].is_used
                        &&& s.pages[pid].full == s.pages[pid].full
                        &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                    })
                by { };
                Self::attached_ranges_all(s, s);
                assert(s.attached_ranges_segment(page_id.segment_id));
                assert(self.attached_ranges_segment(page_id.segment_id));
            }
        }

        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::good_range0);
        let first_id = PageId { segment_id: page_id.segment_id, idx: 0 };
        let first_count = self.pages[first_id].count.unwrap();
        let sp = self.popped_for_seg(page_id.segment_id);
        assert(self.good_range0(page_id.segment_id));
        assert(self.attached_rec(page_id.segment_id, first_count as int, sp));
        if first_count > page_id.idx {
            assert(first_id.segment_id == page_id.segment_id);
            assert(first_id.idx <= page_id.idx < first_id.idx + first_count);
            assert(self.pages[page_id].offset == Some((page_id.idx - first_id.idx) as nat));
            assert(page_id.idx != 0);
            assert(page_id.idx - first_id.idx > 0);
            assert(self.pages[page_id].offset == Some(0nat));
            assert(false);
        }
        assert(first_count <= page_id.idx);
        self.rec_lemma_range_not_used(page_id, first_count as int, sp);
    }

    pub proof fn lemma_range_used(&self, page_id: PageId)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            match self.popped {
                Popped::Used(pid, _) => pid != page_id,
                _ => true,
            },
        ensures
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
    {
        reveal(State::page_id_domain);
        reveal(State::popped_basics);
        reveal(State::in_popped_range);
        assert(page_id.idx <= SLICES_PER_SEGMENT);
        assert(!self.in_popped_range(page_id)) by {
            if self.in_popped_range(page_id) {
                match self.popped {
                    Popped::Ready(pid, _) => {
                        self.ready_popped_range_facts();
                        let count = self.pages[pid].count.unwrap();
                        assert(pid.segment_id == page_id.segment_id);
                        assert(pid.idx <= page_id.idx < pid.idx + count);
                        assert(self.pages[page_id].is_used == false);
                        assert(self.pages[page_id].is_used == true);
                        assert(false);
                    }
                    Popped::Used(pid, _) => {
                        self.used_popped_range_facts();
                        let count = self.pages[pid].count.unwrap();
                        assert(pid.segment_id == page_id.segment_id);
                        assert(pid.idx <= page_id.idx < pid.idx + count);
                        assert(pid != page_id);
                        assert(page_id.idx - pid.idx > 0);
                        assert(self.pages[page_id].offset == Some((page_id.idx - pid.idx) as nat));
                        assert(self.pages[page_id].offset == Some(0nat));
                        assert(false);
                    }
                    Popped::VeryUnready(segment_id, start, count, _) => {
                        self.very_unready_popped_range_facts();
                        assert(segment_id == page_id.segment_id);
                        assert(start <= page_id.idx < start + count);
                        assert(self.pages[page_id].is_used == false);
                        assert(self.pages[page_id].is_used == true);
                        assert(false);
                    }
                    _ => {
                        assert(false);
                    }
                }
            }
        };

        match self.popped {
            Popped::SegmentCreating(segment_id) => {
                reveal(State::inv_segment_creating);
                if page_id.segment_id == segment_id {
                    self.segment_creating_facts(segment_id);
                    assert(self.pages[page_id].is_used == false);
                    assert(false);
                } else {
                    assert(self.pages[page_id].dlist_entry.is_some());
                    assert(self.pages[page_id].full.is_some());
                    match self.pages[page_id].full {
                        Some(full) => {
                            if full {
                                assert(self.pages[page_id].full != Some(false));
                                assert(is_in_list_at(page_id, self.used_lists, BIN_FULL as int));
                                let list_idx = choose |j: int|
                                    0 <= (BIN_FULL as int) < self.used_lists.len()
                                    && 0 <= j < self.used_lists[BIN_FULL as int].len()
                                    && self.used_lists[BIN_FULL as int][j] == page_id;
                                reveal(State::ll_inv_valid_used);
                                assert(self.valid_used_page(page_id, BIN_FULL as int, list_idx));
                            } else {
                                match self.pages[page_id].page_header_kind {
                                    Some(PageHeaderKind::Normal(bin, _)) => {
                                        assert(self.pages[page_id].full != Some(true));
                                        assert(is_in_list_at(page_id, self.used_lists, bin));
                                        let list_idx = choose |j: int|
                                            0 <= bin < self.used_lists.len()
                                            && 0 <= j < self.used_lists[bin].len()
                                            && self.used_lists[bin][j] == page_id;
                                        reveal(State::ll_inv_valid_used);
                                        assert(self.valid_used_page(page_id, bin, list_idx));
                                    }
                                    None => { assert(false); }
                                }
                            }
                        }
                        None => { assert(false); }
                    }
                }
            }
            _ => {
                reveal(State::data_for_used_header);
                reveal(State::ll_inv_valid_used2);
                assert(self.pages[page_id].dlist_entry.is_some());
                assert(self.pages[page_id].full.is_some());
                match self.pages[page_id].full {
                    Some(full) => {
                        if full {
                            assert(self.pages[page_id].full != Some(false));
                            assert(is_in_list_at(page_id, self.used_lists, BIN_FULL as int));
                            let list_idx = choose |j: int|
                                0 <= (BIN_FULL as int) < self.used_lists.len()
                                && 0 <= j < self.used_lists[BIN_FULL as int].len()
                                && self.used_lists[BIN_FULL as int][j] == page_id;
                            reveal(State::ll_inv_valid_used);
                            assert(self.valid_used_page(page_id, BIN_FULL as int, list_idx));
                        } else {
                            match self.pages[page_id].page_header_kind {
                                Some(PageHeaderKind::Normal(bin, _)) => {
                                    assert(self.pages[page_id].full != Some(true));
                                    assert(is_in_list_at(page_id, self.used_lists, bin));
                                    let list_idx = choose |j: int|
                                        0 <= bin < self.used_lists.len()
                                        && 0 <= j < self.used_lists[bin].len()
                                        && self.used_lists[bin][j] == page_id;
                                    reveal(State::ll_inv_valid_used);
                                    assert(self.valid_used_page(page_id, bin, list_idx));
                                }
                                None => { assert(false); }
                            }
                        }
                    }
                    None => { assert(false); }
                }
            }
        }
        assert(self.pages[page_id].count.is_some());
        reveal(State::count_off0);
        let page_count = self.pages[page_id].count.unwrap();
        assert(1 <= page_count);
        assert(page_id.idx + page_count <= SLICES_PER_SEGMENT);
        assert(page_id.idx != SLICES_PER_SEGMENT);

        match self.popped {
            Popped::SegmentCreating(segment_id) => {
                if page_id.segment_id == segment_id {
                    self.segment_creating_facts(segment_id);
                    assert(self.pages[page_id].is_used == false);
                    assert(false);
                } else {
                    let s = *self;
                    assert forall |sid: SegmentId|
                        sid != segment_id && #[trigger] s.segments.dom().contains(sid)
                    implies s.segments.dom().contains(sid) by { };
                    assert forall |pid: PageId|
                        pid.segment_id != segment_id
                    implies
                        (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                        && (s.pages.dom().contains(pid) ==> {
                            &&& s.pages[pid].count == s.pages[pid].count
                            &&& (s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some())
                            &&& s.pages[pid].offset == s.pages[pid].offset
                            &&& s.pages[pid].is_used == s.pages[pid].is_used
                            &&& s.pages[pid].full == s.pages[pid].full
                            &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                        })
                    by { };
                    reveal(State::if_popped_or_other_then_for);
                    assert(s.if_popped_or_other_then_for(segment_id));
                    Self::attached_ranges_except(s, s, segment_id);
                    assert(s.attached_ranges_segment(page_id.segment_id));
                    assert(self.attached_ranges_segment(page_id.segment_id));
                }
            }
            Popped::SegmentFreeing(segment_id, idx) => {
                if page_id.segment_id == segment_id {
                    reveal(State::inv_segment_freeing);
                    reveal(State::seg_free_prefix);
                    if page_id.idx < idx {
                        assert(self.pages[page_id].is_used == false);
                        assert(false);
                    }
                    assert(idx <= page_id.idx);
                    if idx == SLICES_PER_SEGMENT {
                        assert(page_id.idx == SLICES_PER_SEGMENT);
                        assert(false);
                    }
                    assert(idx < SLICES_PER_SEGMENT);
                    assert(self.attached_rec(segment_id, idx, false));
                    self.rec_lemma_range_used(page_id, idx, false);
                    return;
                } else {
                    let s = *self;
                    assert forall |sid: SegmentId|
                        sid != segment_id && #[trigger] s.segments.dom().contains(sid)
                    implies s.segments.dom().contains(sid) by { };
                    assert forall |pid: PageId|
                        pid.segment_id != segment_id
                    implies
                        (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                        && (s.pages.dom().contains(pid) ==> {
                            &&& s.pages[pid].count == s.pages[pid].count
                            &&& (s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some())
                            &&& s.pages[pid].offset == s.pages[pid].offset
                            &&& s.pages[pid].is_used == s.pages[pid].is_used
                            &&& s.pages[pid].full == s.pages[pid].full
                            &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                        })
                    by { };
                    reveal(State::if_popped_or_other_then_for);
                    assert(s.if_popped_or_other_then_for(segment_id));
                    Self::attached_ranges_except(s, s, segment_id);
                    assert(s.attached_ranges_segment(page_id.segment_id));
                    assert(self.attached_ranges_segment(page_id.segment_id));
                }
            }
            _ => {
                let s = *self;
                assert(Self::popped_ranges_match(s, s)) by {
                    reveal(State::popped_ranges_match);
                    reveal(State::is_any_the_popped);
                };
                assert(s.segments.dom() =~= s.segments.dom());
                assert forall |pid: PageId|
                    #![trigger s.pages.dom().contains(pid)]
                    #![trigger s.pages[pid]]
                    (s.pages.dom().contains(pid) <==> s.pages.dom().contains(pid))
                    && (s.pages.dom().contains(pid) && !s.in_popped_range(pid) ==> {
                        &&& s.pages.dom().contains(pid)
                        &&& s.pages[pid].count == s.pages[pid].count
                        &&& s.pages[pid].dlist_entry.is_some() <==> s.pages[pid].dlist_entry.is_some()
                        &&& s.pages[pid].offset == s.pages[pid].offset
                        &&& s.pages[pid].is_used == s.pages[pid].is_used
                        &&& s.pages[pid].full == s.pages[pid].full
                        &&& s.pages[pid].page_header_kind == s.pages[pid].page_header_kind
                    })
                by { };
                Self::attached_ranges_all(s, s);
                assert(s.attached_ranges_segment(page_id.segment_id));
                assert(self.attached_ranges_segment(page_id.segment_id));
            }
        }

        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::good_range0);
        let first_id = PageId { segment_id: page_id.segment_id, idx: 0 };
        let first_count = self.pages[first_id].count.unwrap();
        let sp = self.popped_for_seg(page_id.segment_id);
        assert(self.good_range0(page_id.segment_id));
        assert(self.attached_rec(page_id.segment_id, first_count as int, sp));
        if first_count > page_id.idx {
            assert(first_id.segment_id == page_id.segment_id);
            assert(first_id.idx <= page_id.idx < first_id.idx + first_count);
            assert(self.pages[page_id].is_used == false);
            assert(false);
        }
        assert(first_count <= page_id.idx);
        self.rec_lemma_range_used(page_id, first_count as int, sp);
    }

    pub proof fn rec_lemma_range_used(&self, page_id: PageId, idx: int, sp: bool)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_used_header(self.pages[page_id]),
            page_id.idx != SLICES_PER_SEGMENT,
            0 <= idx <= page_id.idx,
            match self.popped {
                Popped::Used(pid, _) => pid != page_id,
                _ => true,
            },
            self.attached_rec(page_id.segment_id, idx, sp),
        ensures 
            self.pages[page_id].count.is_some(),
            self.good_range_used(page_id),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::page_id_domain);
        reveal(State::good_range_used);
        reveal(State::good_range_unused);
        reveal(State::good_range_ready);
        reveal(State::good_range_very_unready);

        let segment_id = page_id.segment_id;
        assert(page_id.idx <= SLICES_PER_SEGMENT);
        if idx == page_id.idx {
            assert(idx != SLICES_PER_SEGMENT);
            if idx == SLICES_PER_SEGMENT {
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!self.attached_rec(segment_id, idx, sp));
                assert(false);
            } else if Self::is_the_popped(segment_id, idx, self.popped) {
                match self.popped {
                    Popped::Ready(pid, _) => {
                        self.ready_popped_range_facts();
                        assert(pid == page_id);
                        assert(self.pages[page_id].is_used == false);
                        assert(false);
                    }
                    Popped::Used(pid, _) => {
                        assert(pid == page_id);
                        assert(false);
                    }
                    Popped::VeryUnready(_, _, _, _) => {
                        self.very_unready_popped_range_facts();
                        assert(self.pages[page_id].offset.is_none());
                        assert(self.pages[page_id].offset == Some(0nat));
                        assert(false);
                    }
                    _ => {
                        assert(false);
                    }
                }
            } else {
                assert(self.pages[page_id].is_used == true);
                assert(self.good_range_used(page_id));
            }
        } else {
            assert(idx < page_id.idx);
            if idx == SLICES_PER_SEGMENT {
                assert(page_id.idx > SLICES_PER_SEGMENT);
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!self.attached_rec(segment_id, idx, sp));
                assert(false);
            } else if Self::is_the_popped(segment_id, idx, self.popped) {
                let next_idx = idx + self.popped_len();
                assert(next_idx <= SLICES_PER_SEGMENT);
                if next_idx > page_id.idx {
                    match self.popped {
                        Popped::Ready(pid, _) => {
                            self.ready_popped_range_facts();
                            let count = self.pages[pid].count.unwrap();
                            assert(pid.segment_id == segment_id);
                            assert(pid.idx == idx);
                            assert(count == self.popped_len());
                            assert(pid.idx <= page_id.idx < pid.idx + count);
                            assert(self.pages[page_id].is_used == false);
                            assert(false);
                        }
                        Popped::Used(pid, _) => {
                            self.used_popped_range_facts();
                            let count = self.pages[pid].count.unwrap();
                            assert(pid.segment_id == segment_id);
                            assert(pid.idx == idx);
                            assert(count == self.popped_len());
                            assert(pid.idx <= page_id.idx < pid.idx + count);
                            assert(pid != page_id);
                            assert(page_id.idx - pid.idx > 0);
                            assert(self.pages[page_id].offset == Some((page_id.idx - pid.idx) as nat));
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        }
                        Popped::VeryUnready(sid, start, count, _) => {
                            self.very_unready_popped_range_facts();
                            assert(sid == segment_id);
                            assert(start == idx);
                            assert(count == self.popped_len());
                            assert(start <= page_id.idx < start + count);
                            assert(self.pages[page_id].is_used == false);
                            assert(false);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
                assert(next_idx <= page_id.idx);
                self.rec_lemma_range_used(page_id, next_idx, false);
            } else {
                let cur = PageId { segment_id, idx: idx as nat };
                let count = self.pages[cur].count.unwrap();
                assert(count > 0);
                assert(idx + count <= SLICES_PER_SEGMENT);
                assert(self.attached_rec(segment_id, idx + count, sp));
                if idx + count > page_id.idx {
                    assert(cur.segment_id == page_id.segment_id);
                    assert(cur.idx <= page_id.idx < cur.idx + count);
                    if self.pages[cur].is_used {
                        assert(self.good_range_used(cur));
                        assert(page_id.idx - cur.idx > 0);
                        assert(self.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                        assert(self.pages[page_id].offset == Some(0nat));
                        assert(false);
                    } else {
                        assert(self.good_range_unused(cur));
                        let last_id = PageId { segment_id, idx: (idx + count - 1) as nat };
                        if page_id == last_id {
                            assert(page_id.idx - cur.idx > 0);
                            assert(self.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        } else {
                            assert(self.pages[page_id].offset.is_none());
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        }
                    }
                }
                assert(idx + count <= page_id.idx);
                self.rec_lemma_range_used(page_id, idx + count, sp);
            }
        }
    }

    pub proof fn rec_lemma_range_not_used(&self, page_id: PageId, idx: int, sp: bool)
        requires self.invariant(), self.pages.dom().contains(page_id),
            is_unused_header(self.pages[page_id]),
            0 <= idx <= page_id.idx,
            page_id.idx != SLICES_PER_SEGMENT,
            match self.popped {
                //Popped::SegmentFreeing(sid, idx) =>
                //    page_id.segment_id == sid ==> idx <= page_id.idx,
                Popped::Ready(pid, _) => pid != page_id,
                _ => true,
            },
            self.attached_rec(page_id.segment_id, idx, sp)
        ensures 
            self.pages[page_id].count.is_some(),
            self.good_range_unused(page_id),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::page_id_domain);
        reveal(State::good_range_used);
        reveal(State::good_range_unused);
        reveal(State::good_range_ready);
        reveal(State::good_range_very_unready);

        let segment_id = page_id.segment_id;
        assert(page_id.idx <= SLICES_PER_SEGMENT);
        if idx == page_id.idx {
            assert(idx != SLICES_PER_SEGMENT);
            if idx == SLICES_PER_SEGMENT {
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!self.attached_rec(segment_id, idx, sp));
                assert(false);
            } else if Self::is_the_popped(segment_id, idx, self.popped) {
                match self.popped {
                    Popped::Ready(pid, _) => {
                        assert(pid == page_id);
                        assert(false);
                    }
                    Popped::Used(pid, _) => {
                        self.used_popped_range_facts();
                        assert(pid == page_id);
                        assert(self.pages[page_id].is_used == true);
                        assert(false);
                    }
                    Popped::VeryUnready(_, _, _, _) => {
                        self.very_unready_popped_range_facts();
                        assert(self.pages[page_id].offset.is_none());
                        assert(self.pages[page_id].offset == Some(0nat));
                        assert(false);
                    }
                    _ => {
                        assert(false);
                    }
                }
            } else {
                assert(self.pages[page_id].is_used == false);
                assert(self.good_range_unused(page_id));
            }
        } else {
            assert(idx < page_id.idx);
            if idx == SLICES_PER_SEGMENT {
                assert(page_id.idx > SLICES_PER_SEGMENT);
                assert(false);
            } else if idx > SLICES_PER_SEGMENT {
                assert(!self.attached_rec(segment_id, idx, sp));
                assert(false);
            } else if Self::is_the_popped(segment_id, idx, self.popped) {
                let next_idx = idx + self.popped_len();
                assert(next_idx <= SLICES_PER_SEGMENT);
                if next_idx > page_id.idx {
                    match self.popped {
                        Popped::Ready(pid, _) => {
                            self.ready_popped_range_facts();
                            let count = self.pages[pid].count.unwrap();
                            assert(pid.segment_id == segment_id);
                            assert(pid.idx == idx);
                            assert(count == self.popped_len());
                            assert(pid.idx <= page_id.idx < pid.idx + count);
                            assert(pid != page_id);
                            assert(page_id.idx - pid.idx > 0);
                            assert(self.pages[page_id].offset == Some((page_id.idx - pid.idx) as nat));
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        }
                        Popped::Used(pid, _) => {
                            self.used_popped_range_facts();
                            let count = self.pages[pid].count.unwrap();
                            assert(pid.segment_id == segment_id);
                            assert(pid.idx == idx);
                            assert(count == self.popped_len());
                            assert(pid.idx <= page_id.idx < pid.idx + count);
                            assert(self.pages[page_id].is_used == true);
                            assert(false);
                        }
                        Popped::VeryUnready(sid, start, count, _) => {
                            self.very_unready_popped_range_facts();
                            assert(sid == segment_id);
                            assert(start == idx);
                            assert(count == self.popped_len());
                            assert(start <= page_id.idx < start + count);
                            assert(self.pages[page_id].offset.is_none());
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                }
                assert(next_idx <= page_id.idx);
                self.rec_lemma_range_not_used(page_id, next_idx, false);
            } else {
                let cur = PageId { segment_id, idx: idx as nat };
                let count = self.pages[cur].count.unwrap();
                assert(count > 0);
                assert(idx + count <= SLICES_PER_SEGMENT);
                assert(self.attached_rec(segment_id, idx + count, sp));
                if idx + count > page_id.idx {
                    assert(cur.segment_id == page_id.segment_id);
                    assert(cur.idx <= page_id.idx < cur.idx + count);
                    if self.pages[cur].is_used {
                        assert(self.good_range_used(cur));
                        assert(self.pages[page_id].is_used == true);
                        assert(false);
                    } else {
                        assert(self.good_range_unused(cur));
                        let last_id = PageId { segment_id, idx: (idx + count - 1) as nat };
                        if page_id == last_id {
                            assert(page_id.idx - cur.idx > 0);
                            assert(self.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        } else {
                            assert(self.pages[page_id].offset.is_none());
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        }
                    }
                }
                assert(idx + count <= page_id.idx);
                self.rec_lemma_range_not_used(page_id, idx + count, sp);
            }
        }
    }

    pub proof fn get_stuff_after(&self) -> (r: (int, int))
        requires self.invariant(),
        ensures
          match self.popped {
              Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                  let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
                  page_id.idx < SLICES_PER_SEGMENT ==> (
                      self.pages.dom().contains(page_id)
                      && (!self.pages[page_id].is_used ==> self.good_range_unused(page_id)
                          && self.pages[page_id].dlist_entry.is_some()
                          && 0 <= r.0 < self.unused_lists.len()
                          && 0 <= r.1 < self.unused_lists[r.0].len()
                          && self.unused_lists[r.0][r.1] == page_id
                      )
                  )
              }
              _ => true,
          },
    {
        match self.popped {
           Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
               reveal(State::inv_very_unready);
               self.get_count_bound_very_unready();
               assert(0 <= cur_start);
               assert(0 <= cur_count);
               assert(0 <= cur_start + cur_count);

               let page_id = PageId { segment_id, idx: (cur_start + cur_count) as nat };
               if page_id.idx < SLICES_PER_SEGMENT {
                   self.valid_page_after();
                   assert(self.pages.dom().contains(page_id));
                   assert(self.pages[page_id].offset == Some(0nat));

                   if !self.pages[page_id].is_used {
                       assert(0 < cur_start);
                       assert(page_id.idx != 0);
                       assert(is_unused_header(self.pages[page_id]));
                       self.lemma_range_not_used(page_id);
                       assert(self.good_range_unused(page_id));
                       self.unused_is_in_sbin(page_id);

                       let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
                       let pair = Self::get_list_idx(self.unused_lists, page_id);
                       let list_idx = pair.1;
                       assert(self.valid_unused_page(page_id, sbin_idx, list_idx));
                       reveal(State::valid_unused_page);
                       reveal(State::ll_basics);
                       assert(0 <= sbin_idx <= SEGMENT_BIN_MAX);
                       assert(0 <= sbin_idx < self.unused_lists.len());
                       assert(0 <= list_idx < self.unused_lists[sbin_idx].len());
                       assert(self.unused_lists[sbin_idx][list_idx] == page_id);
                       assert(self.pages[page_id].dlist_entry.is_some());
                       (sbin_idx, list_idx)
                   } else {
                       (0, 0)
                   }
               } else {
                   (0, 0)
               }
           }
           _ => (0, 0),
        }
    }

    pub proof fn get_stuff_before(&self) -> (r: (int, int))
        requires self.invariant(),
        ensures
          match self.popped {
              Popped::VeryUnready(segment_id, cur_start, cur_count, _) => {
                  cur_start >= 1 && ({
                    let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
                      self.pages.dom().contains(last_id)
                      && self.pages[last_id].offset.is_some()
                      && cur_start - 1 - self.pages[last_id].offset.unwrap() >= 0
                      && ({
                        let page_id = PageId { segment_id, idx: (cur_start - 1 - self.pages[last_id].offset.unwrap()) as nat };
                        self.pages.dom().contains(page_id)
                          && (!self.pages[page_id].is_used && page_id.idx != 0 ==> self.good_range_unused(page_id)
                              && self.pages[page_id].dlist_entry.is_some()
                              && 0 <= r.0 < self.unused_lists.len()
                              && 0 <= r.1 < self.unused_lists[r.0].len()
                              && self.unused_lists[r.0][r.1] == page_id
                              && self.pages[page_id].count.unwrap()
                                  == self.pages[last_id].offset.unwrap() + 1
                          )
                      })
                  })
              }
              _ => true,
          },
    {
        match self.popped {
           Popped::VeryUnready(segment_id, cur_start, _cur_count, _) => {
               reveal(State::inv_very_unready);
               self.get_count_bound_very_unready();
               assert(0 < cur_start);
               assert(cur_start >= 1);

               self.valid_page_before();
               let last_id = PageId { segment_id, idx: (cur_start - 1) as nat };
               assert(self.pages.dom().contains(last_id));
               assert(self.pages[last_id].offset.is_some());
               let offset = self.pages[last_id].offset.unwrap();
               assert(last_id.idx == cur_start - 1);
               assert(cur_start - 1 - offset >= 0);

               let page_id = PageId { segment_id, idx: (cur_start - 1 - offset) as nat };
               assert(page_id == PageId { segment_id, idx: (last_id.idx - offset) as nat });
               assert(self.pages.dom().contains(page_id));
               assert(self.pages[page_id].offset == Some(0nat));
               assert(self.pages[page_id].count == Some(offset + 1));

               if !self.pages[page_id].is_used && page_id.idx != 0 {
                   assert(is_unused_header(self.pages[page_id]));
                   self.lemma_range_not_used(page_id);
                   assert(self.good_range_unused(page_id));
                   self.unused_is_in_sbin(page_id);

                   let sbin_idx = smallest_sbin_fitting_size(self.pages[page_id].count.unwrap() as int);
                   let pair = Self::get_list_idx(self.unused_lists, page_id);
                   let list_idx = pair.1;
                   assert(self.valid_unused_page(page_id, sbin_idx, list_idx));
                   reveal(State::valid_unused_page);
                   reveal(State::ll_basics);
                   assert(0 <= sbin_idx <= SEGMENT_BIN_MAX);
                   assert(0 <= sbin_idx < self.unused_lists.len());
                   assert(0 <= list_idx < self.unused_lists[sbin_idx].len());
                   assert(self.unused_lists[sbin_idx][list_idx] == page_id);
                   assert(self.pages[page_id].dlist_entry.is_some());
                   assert(self.pages[page_id].count.unwrap() == offset + 1);
                   (sbin_idx, list_idx)
               } else {
                   (0, 0)
               }
           }
           _ => (0, 0),
        }
    }

    /*
    pub proof fn lemma_range_not_used_very_unready(&self)
        requires self.invariant(), self.popped.is_VeryUnready(),
        ensures match self.popped {
            Popped::VeryUnready(segment_id, start, count, _) => {
                (forall |pid| #![trigger self.pages.dom().contains(pid)]
                    #![trigger self.pages.index(pid)]
                  pid.segment_id == segment_id
                  && start <= pid.idx < start + count ==> 
                    self.pages.dom().contains(pid)
                    && self.pages[pid].is_used == false)
            }
            _ => false,
        }
    {
    }
    */

    pub closed spec fn good_range_very_unready(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset.is_none()
        &&& self.pages[page_id].count.is_none()
        &&& ({ let count = self.popped.get_VeryUnready_2();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && self.pages[pid].count.is_none()
                && self.pages[pid].dlist_entry.is_none()
                && self.pages[pid].offset.is_none()
           )
        })
    }

    pub closed spec fn good_range0(&self, segment_id: SegmentId) -> bool
    {
        let page_id = PageId { segment_id, idx: 0 }; {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && (self.pages[pid].count.is_some() <==> pid == page_id)
                && self.pages[pid].dlist_entry.is_none()
                && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
            )
        })
        }
    }

    pub closed spec fn good_range_unused(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                && (self.pages[pid].count.is_some() <==> pid == page_id)
                && (self.pages[pid].dlist_entry.is_some() <==> pid == page_id)
                && self.pages[pid].offset == (if pid == page_id || pid == (PageId { segment_id: page_id.segment_id, idx: (page_id.idx + self.pages[page_id].count.unwrap() - 1) as nat }) {
                            Some((pid.idx - page_id.idx) as nat)
                        } else {
                            None
                        })
            )
        })
    }

    pub closed spec fn good_range_ready(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==>
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == false
                && self.pages[pid].full.is_none()
                && self.pages[pid].page_header_kind.is_none()
                  && (self.pages[pid].count.is_some() <==> pid == page_id)
                  && self.pages[pid].dlist_entry.is_none()
                  && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
              )
        })
    }

    pub closed spec fn good_range_used(&self, page_id: PageId) -> bool
    {
        &&& self.pages.dom().contains(page_id)
        &&& self.pages[page_id].offset == Some(0nat)
        &&& self.pages[page_id].count.is_some()
        &&& ({ let count = self.pages[page_id].count.unwrap();
            page_id.idx + count <= SLICES_PER_SEGMENT
            && (forall |pid| #![trigger self.pages.dom().contains(pid)]
                #![trigger self.pages.index(pid)]
              pid.segment_id == page_id.segment_id
              && page_id.idx <= pid.idx < page_id.idx + count ==> 
                self.pages.dom().contains(pid)
                && self.pages[pid].is_used == true
                && self.pages[pid].offset == Some((pid.idx - page_id.idx) as nat)
                //&& (self.pages[pid].count.is_some() <==> pid == page_id)
                && (self.pages[pid].page_header_kind.is_some() <==> pid == page_id)
                && (pid != page_id ==> self.pages[pid].dlist_entry.is_none())
                && (pid != page_id ==> self.pages[pid].full.is_none())
            )
        })
    }

    pub proof fn lemma_used_bound(&self, segment_id: SegmentId)
        requires self.segments.dom().contains(segment_id),
            self.invariant(),
        ensures self.segments[segment_id].used <= SLICES_PER_SEGMENT + 1,
    {
        reveal(State::count_is_right);
        reveal(State::popped_ec);
        reveal(State::ec_of_popped);
        reveal(State::ucount);

        self.ucount_sum_le(segment_id, SLICES_PER_SEGMENT as int);
        assert(self.ucount(segment_id) <= SLICES_PER_SEGMENT);
        assert(self.popped_ec(segment_id) <= 1) by {
            match self.popped {
                Popped::No => { }
                Popped::Ready(_, _) => { }
                Popped::Used(_, _) => { }
                Popped::SegmentCreating(_) => { }
                Popped::VeryUnready(_, _, _, _) => { }
                Popped::SegmentFreeing(_, _) => { }
                Popped::ExtraCount(_) => { }
            }
        };
        assert(self.segments[segment_id].used == self.ucount(segment_id) as int + self.popped_ec(segment_id));
    }

    pub proof fn ucount_sum_le(&self, segment_id: SegmentId, idx: int)
        requires idx >= 0,
        ensures self.ucount_sum(segment_id, idx) <= idx
        decreases idx,
    {
        reveal(State::ucount_sum);
        reveal(State::one_count);
        if idx > 0 {
            self.ucount_sum_le(segment_id, idx - 1);
            let page_id = PageId { segment_id, idx: (idx - 1) as nat };
            assert(self.one_count(page_id) <= 1);
        }
    }

    pub proof fn count_is_right_preserve_all(pre: Self, post: Self)
        requires
            pre.invariant(),
            forall |pid: PageId| pre.does_count(pid) <==> post.does_count(pid),
            forall |sid: SegmentId|
                #![trigger post.segments.dom().contains(sid)]
                post.segments.dom().contains(sid) ==>
                    pre.segments.dom().contains(sid)
                    && post.segments[sid].used == pre.segments[sid].used
                    && post.popped_ec(sid) == pre.popped_ec(sid),
        ensures
            post.count_is_right(),
    {
        reveal(State::count_is_right);
        Self::ucount_preserve_all(pre, post);
        assert forall |sid: SegmentId|
            #![trigger post.segments.dom().contains(sid)]
            post.segments.dom().contains(sid)
        implies
            post.segments[sid].used == post.ucount(sid) as int + post.popped_ec(sid)
        by {
            assert(pre.segments.dom().contains(sid));
            assert(post.segments[sid].used == pre.segments[sid].used);
            assert(post.popped_ec(sid) == pre.popped_ec(sid));
            assert(pre.ucount(sid) == post.ucount(sid));
            assert(pre.segments[sid].used == pre.ucount(sid) as int + pre.popped_ec(sid));
        }
    }

    pub proof fn ucount_preserve_except(pre: Self, post: Self, esid: SegmentId)
        requires
          forall |pid: PageId| #![all_triggers] pid.segment_id != esid ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid]),
          //pre.if_popped_then_for(esid),
          //post.if_popped_then_for(esid),
        ensures
          forall |sid: SegmentId| sid != esid ==> pre.ucount(sid) == post.ucount(sid)
    {
        reveal(State::ucount);
        assert forall |sid: SegmentId| sid != esid implies pre.ucount(sid) == post.ucount(sid) by {
            assert forall |pid: PageId| #![all_triggers] pid.segment_id == sid implies
                (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
            by {
                assert(pid.segment_id != esid);
            };
            Self::ucount_sum_preserve(pre, post, sid, SLICES_PER_SEGMENT as int);
        };
    }

    pub proof fn ucount_preserve_all(pre: Self, post: Self)
        requires
          forall |pid: PageId|
            pre.does_count(pid) <==> post.does_count(pid),
        ensures
          forall |sid: SegmentId| pre.ucount(sid) == post.ucount(sid)
    {
        reveal(State::ucount);
        assert forall |sid: SegmentId| pre.ucount(sid) == post.ucount(sid) by {
            Self::ucount_sum_preserve(pre, post, sid, SLICES_PER_SEGMENT as int);
        };
    }

    pub proof fn ucount_sum_preserve(pre: Self, post: Self, segment_id: SegmentId, idx: int)
        requires
            idx >= 0,
            (forall |pid: PageId| #![all_triggers] pid.segment_id == segment_id ==>
              (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
              && (pre.pages.dom().contains(pid) ==> pre.pages[pid] == post.pages[pid])
            ) || (
              forall |pid: PageId|
                pre.does_count(pid) <==> post.does_count(pid)
            ),
        ensures
            pre.ucount_sum(segment_id, idx) == post.ucount_sum(segment_id, idx)
        decreases idx,
    {
        reveal(State::ucount_sum);
        reveal(State::one_count);
        reveal(State::does_count);
        if idx > 0 {
            let pid = PageId { segment_id, idx: (idx - 1) as nat };
            Self::ucount_sum_preserve(pre, post, segment_id, idx - 1);
            assert(pre.one_count(pid) == post.one_count(pid)) by {
                if pre.does_count(pid) {
                    assert(post.does_count(pid));
                } else {
                    assert(!post.does_count(pid));
                }
            };
        }
    }

    pub closed spec fn one_count(&self, page_id: PageId) -> nat {
        if self.does_count(page_id) { 1 } else { 0 }
    }

    pub closed spec fn does_count(&self, page_id: PageId) -> bool {
        self.pages.dom().contains(page_id)
          && page_id.idx != 0
          && self.pages[page_id].is_used
          && self.pages[page_id].offset == Some(0nat)
    }

    pub proof fn ucount_inc1(pre: Self, post: Self, page_id: PageId)
        requires
            0 <= page_id.idx < SLICES_PER_SEGMENT,
            forall |pid: PageId| pid != page_id ==>
              (pre.does_count(pid) <==> post.does_count(pid)),
            !pre.does_count(page_id),
            post.does_count(page_id),
        ensures
            post.ucount(page_id.segment_id) == pre.ucount(page_id.segment_id) + 1
    {
        reveal(State::ucount);
        Self::ucount_sum_inc1(pre, post, page_id, SLICES_PER_SEGMENT as int);
        assert(page_id.idx < SLICES_PER_SEGMENT as int);
    }

    pub proof fn ucount_sum_inc1(pre: Self, post: Self, page_id: PageId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid != page_id ==>
                (pre.does_count(pid) <==> post.does_count(pid)),
            !pre.does_count(page_id),
            post.does_count(page_id),
        ensures
            pre.ucount_sum(page_id.segment_id, idx) + (if page_id.idx < idx { 1int } else { 0 }) == post.ucount_sum(page_id.segment_id, idx)
        decreases idx,
    {
        reveal(State::ucount_sum);
        reveal(State::one_count);
        if idx > 0 {
            let pid = PageId { segment_id: page_id.segment_id, idx: (idx - 1) as nat };
            Self::ucount_sum_inc1(pre, post, page_id, idx - 1);
            if pid == page_id {
                assert(!pre.does_count(pid));
                assert(post.does_count(pid));
                assert(pre.one_count(pid) == 0);
                assert(post.one_count(pid) == 1);
                assert(page_id.idx == idx - 1);
                assert(!(page_id.idx < idx - 1));
                assert(page_id.idx < idx);
            } else {
                assert(pre.does_count(pid) <==> post.does_count(pid));
                assert(pre.one_count(pid) == post.one_count(pid));
                if page_id.idx < idx {
                    assert(page_id.idx != idx - 1);
                    assert(page_id.idx < idx - 1);
                } else {
                    assert(!(page_id.idx < idx - 1));
                }
            }
        } else {
            assert(idx == 0);
            assert(!(page_id.idx < idx));
        }
    }

    pub proof fn ucount_dec1(pre: Self, post: Self, page_id: PageId)
        requires
            0 <= page_id.idx < SLICES_PER_SEGMENT,
            forall |pid: PageId| pid != page_id ==>
              (pre.does_count(pid) <==> post.does_count(pid)),
            pre.does_count(page_id),
            !post.does_count(page_id),
        ensures
            post.ucount(page_id.segment_id) == pre.ucount(page_id.segment_id) - 1
    {
        reveal(State::ucount);
        Self::ucount_sum_dec1(pre, post, page_id, SLICES_PER_SEGMENT as int);
        assert(page_id.idx < SLICES_PER_SEGMENT as int);
    }

    pub proof fn ucount_sum_dec1(pre: Self, post: Self, page_id: PageId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid != page_id ==>
                (pre.does_count(pid) <==> post.does_count(pid)),
            pre.does_count(page_id),
            !post.does_count(page_id),
        ensures
            pre.ucount_sum(page_id.segment_id, idx) - (if page_id.idx < idx { 1int } else { 0 }) == post.ucount_sum(page_id.segment_id, idx)
        decreases idx,
    {
        reveal(State::ucount_sum);
        reveal(State::one_count);
        if idx > 0 {
            let pid = PageId { segment_id: page_id.segment_id, idx: (idx - 1) as nat };
            Self::ucount_sum_dec1(pre, post, page_id, idx - 1);
            if pid == page_id {
                assert(pre.does_count(pid));
                assert(!post.does_count(pid));
                assert(pre.one_count(pid) == 1);
                assert(post.one_count(pid) == 0);
                assert(page_id.idx == idx - 1);
                assert(!(page_id.idx < idx - 1));
                assert(page_id.idx < idx);
            } else {
                assert(pre.does_count(pid) <==> post.does_count(pid));
                assert(pre.one_count(pid) == post.one_count(pid));
                if page_id.idx < idx {
                    assert(page_id.idx != idx - 1);
                    assert(page_id.idx < idx - 1);
                } else {
                    assert(!(page_id.idx < idx - 1));
                }
            }
        } else {
            assert(idx == 0);
            assert(!(page_id.idx < idx));
        }
    }

    pub proof fn ucount_eq0(&self, sid: SegmentId)
        requires
          forall |pid: PageId| pid.segment_id == sid ==>
              !self.does_count(pid)
        ensures
            self.ucount(sid) == 0
    {
        reveal(State::ucount);
        self.ucount_sum_eq0(sid, SLICES_PER_SEGMENT as int);
    }

    pub proof fn ucount_sum_eq0(&self, sid: SegmentId, idx: int)
        requires
            idx >= 0,
            forall |pid: PageId| pid.segment_id == sid ==> !self.does_count(pid)
        ensures
            self.ucount_sum(sid, idx) == 0
        decreases idx,
    {
        reveal(State::ucount_sum);
        reveal(State::one_count);
        if idx > 0 {
            self.ucount_sum_eq0(sid, idx - 1);
            let pid = PageId { segment_id: sid, idx: (idx - 1) as nat };
            assert(!self.does_count(pid));
            assert(self.one_count(pid) == 0);
        }
    }

    pub proof fn ucount_eq0_inverse(&self, page_id: PageId)
        requires self.ucount(page_id.segment_id) == 0,
            0 <= page_id.idx < SLICES_PER_SEGMENT,
        ensures
            !self.does_count(page_id)
    {
        reveal(State::ucount);
        self.ucount_sum_eq0_inverse(page_id, SLICES_PER_SEGMENT as int);
    }

    pub proof fn ucount_sum_eq0_inverse(&self, page_id: PageId, idx: int)
        requires self.ucount_sum(page_id.segment_id, idx) == 0,
            0 <= page_id.idx < idx,
        ensures
            !self.does_count(page_id)
        decreases idx,
    {
        reveal(State::ucount_sum);
        reveal(State::one_count);
        let pid = PageId { segment_id: page_id.segment_id, idx: (idx - 1) as nat };
        assert(idx > 0);
        assert(self.ucount_sum(page_id.segment_id, idx - 1) == 0);
        assert(self.one_count(pid) == 0);
        if pid == page_id {
            if self.does_count(page_id) {
                assert(self.one_count(page_id) == 1);
                assert(false);
            }
        } else {
            assert(page_id.idx != idx - 1);
            assert(page_id.idx < idx - 1);
            self.ucount_sum_eq0_inverse(page_id, idx - 1);
        }
    }


    pub proof fn attached_ranges_except(pre: Self, post: Self, esid: SegmentId)
        requires
          pre.invariant(),
          forall |sid: SegmentId| sid != esid && post.segments.dom().contains(sid) ==> pre.segments.dom().contains(sid),
          forall |pid: PageId| pid.segment_id != esid ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> {
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
          pre.if_popped_or_other_then_for(esid),
          post.if_popped_or_other_then_for(esid),
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
        ensures
          forall |sid: SegmentId| sid != esid && #[trigger] post.segments.dom().contains(sid) ==> post.attached_ranges_segment(sid)
    {
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::good_range0);
        reveal(State::if_popped_or_other_then_for);
        reveal(State::popped_ranges_match_for_sid);
        reveal(State::popped_for_seg);
        reveal(State::in_popped_range);

        assert forall |sid: SegmentId|
            sid != esid && #[trigger] post.segments.dom().contains(sid)
        implies
            post.attached_ranges_segment(sid)
        by {
            assert(pre.segments.dom().contains(sid));
            assert(pre.attached_ranges_segment(sid));
            assert(!pre.popped_for_seg(sid));
            assert(!post.popped_for_seg(sid));

            let first_id = PageId { segment_id: sid, idx: 0 };
            assert(pre.attached_rec0(sid, false));
            assert(pre.good_range0(sid));
            let first_count = pre.pages[first_id].count.unwrap();
            assert(post.pages.dom().contains(first_id));
            assert(post.pages[first_id].count == pre.pages[first_id].count);
            assert(post.pages[first_id].count.unwrap() == first_count);

            assert forall |pid: PageId|
                #![trigger pre.pages.dom().contains(pid)]
                #![trigger post.pages.dom().contains(pid)]
                #![trigger pre.pages[pid]]
                #![trigger post.pages[pid]]
                pid.segment_id == sid
            implies
                (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                && (pre.pages.dom().contains(pid) ==> (
                    (!pre.in_popped_range(pid) && pid.idx >= first_count ==> {
                    &&& post.pages.dom().contains(pid)
                    &&& pre.pages[pid].count == post.pages[pid].count
                    &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                    &&& pre.pages[pid].offset == post.pages[pid].offset
                    &&& pre.pages[pid].is_used == post.pages[pid].is_used
                    &&& pre.pages[pid].full == post.pages[pid].full
                    &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
                })))
            by {
                assert(pid.segment_id != esid);
            };

            assert(Self::popped_ranges_match_for_sid(pre, post, sid));
            Self::attached_rec_same(pre, post, sid, first_count as int, false);
            assert(post.attached_rec(sid, first_count as int, false));

            assert forall |pid: PageId|
                #![trigger post.pages.dom().contains(pid)]
                #![trigger post.pages.index(pid)]
                pid.segment_id == sid
                && first_id.idx <= pid.idx < first_id.idx + first_count
            implies
                post.pages.dom().contains(pid)
                && post.pages[pid].is_used == false
                && post.pages[pid].full.is_none()
                && post.pages[pid].page_header_kind.is_none()
                && (post.pages[pid].count.is_some() <==> pid == first_id)
                && post.pages[pid].dlist_entry.is_none()
                && post.pages[pid].offset == Some((pid.idx - first_id.idx) as nat)
            by {
                assert(pid.segment_id != esid);
                assert(!pre.in_popped_range(pid));
                assert(pre.pages.dom().contains(pid));
                assert(pre.pages[pid].is_used == false);
                assert(pre.pages[pid].full.is_none());
                assert(pre.pages[pid].page_header_kind.is_none());
                assert(pre.pages[pid].count.is_some() <==> pid == first_id);
                assert(pre.pages[pid].dlist_entry.is_none());
                assert(pre.pages[pid].offset == Some((pid.idx - first_id.idx) as nat));
            };
            assert(post.good_range0(sid));
            assert(post.attached_rec0(sid, false));
            assert(post.attached_ranges_segment(sid));
        };
    }

    pub open spec fn in_popped_range(&self, pid: PageId) -> bool {
        match self.popped {
            Popped::No | Popped::ExtraCount(_)
              | Popped::SegmentFreeing(..)
              | Popped::SegmentCreating(..) => false,
            Popped::VeryUnready(segment_id, idx, count, _) =>
                pid.segment_id == segment_id && idx <= pid.idx < idx + count,
            Popped::Ready(page_id, _)
              | Popped::Used(page_id, _) => {
                  pid.segment_id == page_id.segment_id
                    && page_id.idx <= pid.idx < page_id.idx + self.pages[page_id].count.unwrap()
            }
        }
    }

    pub proof fn attached_ranges_all(pre: Self, post: Self)
        requires
          pre.invariant(),
          Self::popped_ranges_match(pre, post),
          !pre.popped.is_SegmentFreeing(),
          !pre.popped.is_SegmentCreating(),
          !post.popped.is_SegmentFreeing(),
          pre.segments.dom() =~= post.segments.dom(),
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
            ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
        ensures
          forall |sid: SegmentId| #[trigger] post.segments.dom().contains(sid) ==> post.attached_ranges_segment(sid)
    {
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::good_range0);
        reveal(State::popped_ranges_match);
        reveal(State::popped_ranges_match_for_sid);
        reveal(State::popped_for_seg);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::is_any_the_popped);
        reveal(State::in_popped_range);

        assert forall |sid: SegmentId|
            #[trigger] post.segments.dom().contains(sid)
        implies
            post.attached_ranges_segment(sid)
        by {
            assert(pre.segments.dom().contains(sid));
            assert(pre.attached_ranges_segment(sid));
            if post.popped.is_SegmentCreating() && post.popped.get_SegmentCreating_0() == sid {
                assert(post.attached_ranges_segment(sid));
            } else {
                let sp = pre.popped_for_seg(sid);
                assert(post.popped_for_seg(sid) == sp);
                assert(pre.attached_rec0(sid, sp));
                assert(pre.good_range0(sid));
                let first_id = PageId { segment_id: sid, idx: 0 };
                let first_count = pre.pages[first_id].count.unwrap();

                assert forall |pid: PageId|
                    #![trigger pre.pages.dom().contains(pid)]
                    #![trigger post.pages.dom().contains(pid)]
                    #![trigger pre.pages[pid]]
                    #![trigger post.pages[pid]]
                    pid.segment_id == sid
                implies
                    (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                    && (pre.pages.dom().contains(pid) ==> (
                        (!pre.in_popped_range(pid) && pid.idx >= first_count ==> {
                        &&& post.pages.dom().contains(pid)
                        &&& pre.pages[pid].count == post.pages[pid].count
                        &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                        &&& pre.pages[pid].offset == post.pages[pid].offset
                        &&& pre.pages[pid].is_used == post.pages[pid].is_used
                        &&& pre.pages[pid].full == post.pages[pid].full
                        &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
                    })))
                by { };

                if sp {
                    Self::attached_rec_same(pre, pre, sid, first_count as int, sp);
                    assert(first_count <= Self::page_id_of_popped(pre.popped).idx);
                }

                assert forall |pid: PageId|
                    #![trigger post.pages.dom().contains(pid)]
                    #![trigger post.pages.index(pid)]
                    pid.segment_id == sid
                    && first_id.idx <= pid.idx < first_id.idx + first_count
                implies
                    post.pages.dom().contains(pid)
                    && post.pages[pid].is_used == false
                    && post.pages[pid].full.is_none()
                    && post.pages[pid].page_header_kind.is_none()
                    && (post.pages[pid].count.is_some() <==> pid == first_id)
                    && post.pages[pid].dlist_entry.is_none()
                    && post.pages[pid].offset == Some((pid.idx - first_id.idx) as nat)
                by {
                    assert(pre.pages.dom().contains(pid));
                    assert(pre.pages[pid].is_used == false);
                    assert(pre.pages[pid].full.is_none());
                    assert(pre.pages[pid].page_header_kind.is_none());
                    assert(pre.pages[pid].count.is_some() <==> pid == first_id);
                    assert(pre.pages[pid].dlist_entry.is_none());
                    assert(pre.pages[pid].offset == Some((pid.idx - first_id.idx) as nat));
                    assert(!pre.in_popped_range(pid)) by {
                        if pre.in_popped_range(pid) {
                            assert(pre.popped_for_seg(sid));
                            assert(sp);
                            assert(first_count <= Self::page_id_of_popped(pre.popped).idx);
                            assert(pid.idx < first_count);
                            assert(false);
                        }
                    };
                };
                assert(post.good_range0(sid));
                assert(post.pages[first_id].count == pre.pages[first_id].count);
                assert(post.pages[first_id].count.unwrap() == first_count);
                Self::attached_rec_same(pre, post, sid, first_count as int, sp);
                assert(post.attached_rec(sid, first_count as int, sp));
                assert(post.attached_rec0(sid, sp));
                assert(post.attached_ranges_segment(sid));
            }
        };
    }

    pub proof fn attached_rec_same(
        pre: State, post: State,
        segment_id: SegmentId, idx: int, sp: bool
    )
        requires
          pre.invariant(),
          pre.attached_rec(segment_id, idx, sp),
          Self::popped_ranges_match_for_sid(pre, post, segment_id)
            || (!sp
                && (pre.popped_for_seg(segment_id) ==>
                    idx >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len())
                && (post.popped_for_seg(segment_id) ==>
                    post.popped_len() > 0
                    && idx >= Self::page_id_of_popped(post.popped).idx + post.popped_len())),
          match pre.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          match post.popped {
              Popped::VeryUnready(_, i, _, _) => i >= 0,
              _ => true,
          },
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == segment_id ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid) ==> (
                (!pre.in_popped_range(pid) && pid.idx >= idx ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some()
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }))),

          !sp ==> pre.popped_for_seg(segment_id) ==>
              idx >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len(),
          idx >= 0,

        ensures post.attached_rec(segment_id, idx, sp),
          sp ==> pre.popped_for_seg(segment_id) ==>
              idx <= Self::page_id_of_popped(pre.popped).idx

        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_ranges_match_for_sid);
        reveal(State::popped_for_seg);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::in_popped_range);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);

        if idx == SLICES_PER_SEGMENT {
            assert(!sp);
            assert(post.attached_rec(segment_id, idx, sp));
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(segment_id, idx, sp));
            assert(false);
        } else if Self::is_the_popped(segment_id, idx, pre.popped) {
            assert(sp);
            assert(pre.popped_for_seg(segment_id));
            assert(post.popped_for_seg(segment_id));
            assert(pre.popped_len() == post.popped_len());
            assert(Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped));
            assert(Self::is_the_popped(segment_id, idx, post.popped));
            assert(pre.attached_rec(segment_id, idx + pre.popped_len(), false));
            assert(idx + pre.popped_len() >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len());
            Self::attached_rec_same(pre, post, segment_id, idx + pre.popped_len(), false);
            assert(post.attached_rec(segment_id, idx + post.popped_len(), false));
            assert(post.attached_rec(segment_id, idx, sp));
        } else {
            let page_id = PageId { segment_id, idx: idx as nat };
            let count = pre.pages[page_id].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(segment_id, idx + count, sp));
            Self::attached_rec_same(pre, post, segment_id, idx + count, sp);
            assert(post.attached_rec(segment_id, idx + count, sp));
            if sp && pre.popped_for_seg(segment_id) {
                assert(idx + count <= Self::page_id_of_popped(pre.popped).idx);
                assert(idx <= Self::page_id_of_popped(pre.popped).idx);
            }

            assert(!Self::is_the_popped(segment_id, idx, post.popped)) by {
                if Self::is_the_popped(segment_id, idx, post.popped) {
                    assert(post.popped_for_seg(segment_id));
                    if Self::popped_ranges_match_for_sid(pre, post, segment_id) {
                        assert(pre.popped_for_seg(segment_id));
                        assert(Self::page_id_of_popped(pre.popped) == Self::page_id_of_popped(post.popped));
                        assert(Self::is_the_popped(segment_id, idx, pre.popped));
                    } else {
                        assert(!sp);
                        assert(post.popped_len() > 0);
                        assert(idx >= Self::page_id_of_popped(post.popped).idx + post.popped_len());
                        assert(idx == Self::page_id_of_popped(post.popped).idx);
                        assert(post.popped_len() <= 0);
                    }
                    assert(false);
                }
            };

            assert(!pre.in_popped_range(page_id)) by {
                if pre.in_popped_range(page_id) {
                    assert(pre.popped_for_seg(segment_id));
                    if sp {
                        assert(idx + count <= Self::page_id_of_popped(pre.popped).idx);
                        assert(Self::page_id_of_popped(pre.popped).idx <= idx);
                        assert(count <= 0);
                        assert(false);
                    } else {
                        assert(idx >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len());
                        assert(idx < Self::page_id_of_popped(pre.popped).idx + pre.popped_len());
                        assert(false);
                    }
                }
            };
            assert(post.pages.dom().contains(page_id));
            assert(post.pages[page_id].count == pre.pages[page_id].count);
            assert(post.pages[page_id].count.unwrap() == count);
            assert(post.pages[page_id].is_used == pre.pages[page_id].is_used);

            assert forall |q: PageId|
                #![trigger post.pages.dom().contains(q)]
                #![trigger post.pages.index(q)]
                q.segment_id == segment_id
                && page_id.idx <= q.idx < page_id.idx + count
            implies
                !pre.in_popped_range(q)
            by {
                assert(q.idx >= idx);
                if pre.in_popped_range(q) {
                    assert(pre.popped_for_seg(segment_id));
                    if sp {
                        assert(idx + count <= Self::page_id_of_popped(pre.popped).idx);
                        assert(q.idx < idx + count);
                        assert(q.idx < Self::page_id_of_popped(pre.popped).idx);
                        assert(false);
                    } else {
                        assert(idx >= Self::page_id_of_popped(pre.popped).idx + pre.popped_len());
                        assert(Self::page_id_of_popped(pre.popped).idx <= q.idx);
                        assert(q.idx < Self::page_id_of_popped(pre.popped).idx + pre.popped_len());
                        assert(false);
                    }
                }
            };

            if pre.pages[page_id].is_used {
                assert(pre.good_range_used(page_id));
                assert forall |q: PageId|
                    #![trigger post.pages.dom().contains(q)]
                    #![trigger post.pages.index(q)]
                    q.segment_id == segment_id
                    && page_id.idx <= q.idx < page_id.idx + count
                implies
                    post.pages.dom().contains(q)
                    && post.pages[q].is_used == true
                    && post.pages[q].offset == Some((q.idx - page_id.idx) as nat)
                    && (post.pages[q].page_header_kind.is_some() <==> q == page_id)
                    && (q != page_id ==> post.pages[q].dlist_entry.is_none())
                    && (q != page_id ==> post.pages[q].full.is_none())
                by {
                    assert(!pre.in_popped_range(q));
                    assert(q.idx >= idx);
                    assert(pre.pages.dom().contains(q));
                    assert(pre.pages[q].is_used == true);
                    assert(pre.pages[q].offset == Some((q.idx - page_id.idx) as nat));
                    assert(pre.pages[q].page_header_kind.is_some() <==> q == page_id);
                    assert(q != page_id ==> pre.pages[q].dlist_entry.is_none());
                    assert(q != page_id ==> pre.pages[q].full.is_none());
                    assert(post.pages.dom().contains(q));
                    assert(post.pages[q].is_used == pre.pages[q].is_used);
                    assert(post.pages[q].offset == pre.pages[q].offset);
                    assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
                    assert(post.pages[q].full == pre.pages[q].full);
                    assert(pre.pages[q].dlist_entry.is_some() <==> post.pages[q].dlist_entry.is_some());
                };
                assert(post.good_range_used(page_id));
            } else {
                assert(pre.good_range_unused(page_id));
                assert forall |q: PageId|
                    #![trigger post.pages.dom().contains(q)]
                    #![trigger post.pages.index(q)]
                    q.segment_id == segment_id
                    && page_id.idx <= q.idx < page_id.idx + count
                implies
                    post.pages.dom().contains(q)
                    && post.pages[q].is_used == false
                    && post.pages[q].full.is_none()
                    && post.pages[q].page_header_kind.is_none()
                    && (post.pages[q].count.is_some() <==> q == page_id)
                    && (post.pages[q].dlist_entry.is_some() <==> q == page_id)
                    && post.pages[q].offset == (if q == page_id || q == (PageId { segment_id: page_id.segment_id, idx: (page_id.idx + post.pages[page_id].count.unwrap() - 1) as nat }) {
                            Some((q.idx - page_id.idx) as nat)
                        } else {
                            None
                        })
                by {
                    assert(!pre.in_popped_range(q));
                    assert(q.idx >= idx);
                    assert(pre.pages.dom().contains(q));
                    assert(pre.pages[q].is_used == false);
                    assert(pre.pages[q].full.is_none());
                    assert(pre.pages[q].page_header_kind.is_none());
                    assert(pre.pages[q].count.is_some() <==> q == page_id);
                    assert(pre.pages[q].dlist_entry.is_some() <==> q == page_id);
                    assert(post.pages.dom().contains(q));
                    assert(post.pages[q].is_used == pre.pages[q].is_used);
                    assert(post.pages[q].full == pre.pages[q].full);
                    assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
                    assert(post.pages[q].count == pre.pages[q].count);
                    assert(pre.pages[q].dlist_entry.is_some() <==> post.pages[q].dlist_entry.is_some());
                    assert(post.pages[q].offset == pre.pages[q].offset);
                    assert(post.pages[page_id].count.unwrap() == pre.pages[page_id].count.unwrap());
                };
                assert(post.good_range_unused(page_id));
            }
            assert(post.attached_rec(segment_id, idx, sp));
        }
    }

    pub proof fn attached_rec_used_popped_to_no(
        pre: State, post: State, page_id: PageId, idx: int
    )
        requires
          pre.invariant(),
          pre.popped == Popped::Used(page_id, true),
          post.popped == Popped::No,
          pre.attached_rec(page_id.segment_id, idx, true),
          post.good_range_used(page_id),
          post.pages[page_id].count == pre.pages[page_id].count,
          idx >= 0,
          idx <= page_id.idx,
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == page_id.segment_id ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
                && !post.in_popped_range(pid) ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
        ensures post.attached_rec(page_id.segment_id, idx, false),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::in_popped_range);
        reveal(State::popped_for_seg);
        reveal(State::good_range_used);
        reveal(State::good_range_unused);
        reveal(State::inv_used);

        let segment_id = page_id.segment_id;
        assert(pre.good_range_used(page_id));
        let popped_count = pre.pages[page_id].count.unwrap();
        assert(popped_count > 0);
        assert(page_id.idx + popped_count <= SLICES_PER_SEGMENT);

        if idx == SLICES_PER_SEGMENT {
            assert(page_id.idx < SLICES_PER_SEGMENT);
            assert(false);
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(segment_id, idx, true));
            assert(false);
        } else if idx == page_id.idx {
            assert(Self::is_the_popped(segment_id, idx, pre.popped));
            assert(pre.popped_len() == popped_count as int);
            assert(pre.attached_rec(segment_id, idx + pre.popped_len(), false));
            assert(post.pages[page_id].count.unwrap() == popped_count);
            assert(post.pages[page_id].is_used == true);
            assert(post.pages[page_id].count.unwrap() > 0);

            assert forall |pid: PageId|
                #![trigger pre.pages.dom().contains(pid)]
                #![trigger post.pages.dom().contains(pid)]
                #![trigger pre.pages[pid]]
                #![trigger post.pages[pid]]
                pid.segment_id == segment_id
            implies
                (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                && (pre.pages.dom().contains(pid) ==> (
                    (!pre.in_popped_range(pid) && pid.idx >= idx + pre.popped_len() ==> {
                    &&& post.pages.dom().contains(pid)
                    &&& pre.pages[pid].count == post.pages[pid].count
                    &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                    &&& pre.pages[pid].offset == post.pages[pid].offset
                    &&& pre.pages[pid].is_used == post.pages[pid].is_used
                    &&& pre.pages[pid].full == post.pages[pid].full
                    &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
                  })))
            by {
                if pre.pages.dom().contains(pid) && !pre.in_popped_range(pid) && pid.idx >= idx + pre.popped_len() {
                    assert(!post.in_popped_range(pid));
                }
            };
            Self::attached_rec_same(pre, post, segment_id, idx + pre.popped_len(), false);
            assert(post.attached_rec(segment_id, idx + post.pages[page_id].count.unwrap(), false));
            assert(!Self::is_the_popped(segment_id, idx, post.popped));
            assert(post.attached_rec(segment_id, idx, false));
        } else {
            assert(idx < page_id.idx);
            assert(!Self::is_the_popped(segment_id, idx, pre.popped));
            let cur = PageId { segment_id, idx: idx as nat };
            let count = pre.pages[cur].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(segment_id, idx + count, true));
            if idx + count > page_id.idx {
                assert(cur.segment_id == page_id.segment_id);
                assert(cur.idx <= page_id.idx);
                assert(page_id.idx < cur.idx + count);
                if pre.pages[cur].is_used {
                    assert(pre.good_range_used(cur));
                    assert(pre.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                    assert(pre.pages[page_id].offset == Some(0nat));
                    assert(page_id.idx - cur.idx > 0);
                } else {
                    assert(pre.good_range_unused(cur));
                    assert(pre.pages[page_id].is_used == false);
                    assert(pre.pages[page_id].is_used == true);
                }
                assert(false);
            }
            assert(idx + count <= page_id.idx);
            Self::attached_rec_used_popped_to_no(pre, post, page_id, idx + count);
            assert(post.attached_rec(segment_id, idx + count, false));
            assert(!Self::is_the_popped(segment_id, idx, post.popped));
            assert(!pre.in_popped_range(cur));
            assert(!post.in_popped_range(cur));
            assert(post.pages.dom().contains(cur));
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].count.unwrap() == count);
            assert(post.pages[cur].is_used == pre.pages[cur].is_used);

            assert forall |q: PageId|
                #![trigger post.pages.dom().contains(q)]
                #![trigger post.pages.index(q)]
                q.segment_id == segment_id
                && cur.idx <= q.idx < cur.idx + count
            implies
                !pre.in_popped_range(q) && !post.in_popped_range(q)
            by {
                assert(q.idx < idx + count);
                assert(idx + count <= page_id.idx);
                if pre.in_popped_range(q) {
                    assert(page_id.idx <= q.idx);
                    assert(false);
                }
                assert(post.popped == Popped::No);
            };

            if pre.pages[cur].is_used {
                assert(pre.good_range_used(cur));
                assert forall |q: PageId|
                    #![trigger post.pages.dom().contains(q)]
                    #![trigger post.pages.index(q)]
                    q.segment_id == segment_id
                    && cur.idx <= q.idx < cur.idx + count
                implies
                    post.pages.dom().contains(q)
                    && post.pages[q].is_used == true
                    && post.pages[q].offset == Some((q.idx - cur.idx) as nat)
                    && (post.pages[q].page_header_kind.is_some() <==> q == cur)
                    && (q != cur ==> post.pages[q].dlist_entry.is_none())
                    && (q != cur ==> post.pages[q].full.is_none())
                by {
                    assert(!pre.in_popped_range(q));
                    assert(!post.in_popped_range(q));
                    assert(pre.pages.dom().contains(q));
                    assert(pre.pages[q].is_used == true);
                    assert(pre.pages[q].offset == Some((q.idx - cur.idx) as nat));
                    assert(pre.pages[q].page_header_kind.is_some() <==> q == cur);
                    assert(q != cur ==> pre.pages[q].dlist_entry.is_none());
                    assert(q != cur ==> pre.pages[q].full.is_none());
                    assert(post.pages.dom().contains(q));
                    assert(post.pages[q].is_used == pre.pages[q].is_used);
                    assert(post.pages[q].offset == pre.pages[q].offset);
                    assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
                    assert(post.pages[q].full == pre.pages[q].full);
                    assert(pre.pages[q].dlist_entry.is_some() <==> post.pages[q].dlist_entry.is_some());
                };
                assert(post.good_range_used(cur));
            } else {
                assert(pre.good_range_unused(cur));
                assert forall |q: PageId|
                    #![trigger post.pages.dom().contains(q)]
                    #![trigger post.pages.index(q)]
                    q.segment_id == segment_id
                    && cur.idx <= q.idx < cur.idx + count
                implies
                    post.pages.dom().contains(q)
                    && post.pages[q].is_used == false
                    && post.pages[q].full.is_none()
                    && post.pages[q].page_header_kind.is_none()
                    && (post.pages[q].count.is_some() <==> q == cur)
                    && (post.pages[q].dlist_entry.is_some() <==> q == cur)
                    && post.pages[q].offset == (if q == cur || q == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                            Some((q.idx - cur.idx) as nat)
                        } else {
                            None
                        })
                by {
                    assert(!pre.in_popped_range(q));
                    assert(!post.in_popped_range(q));
                    assert(pre.pages.dom().contains(q));
                    assert(pre.pages[q].is_used == false);
                    assert(pre.pages[q].full.is_none());
                    assert(pre.pages[q].page_header_kind.is_none());
                    assert(pre.pages[q].count.is_some() <==> q == cur);
                    assert(pre.pages[q].dlist_entry.is_some() <==> q == cur);
                    assert(post.pages.dom().contains(q));
                    assert(post.pages[q].is_used == pre.pages[q].is_used);
                    assert(post.pages[q].full == pre.pages[q].full);
                    assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
                    assert(post.pages[q].count == pre.pages[q].count);
                    assert(pre.pages[q].dlist_entry.is_some() <==> post.pages[q].dlist_entry.is_some());
                    assert(post.pages[q].offset == pre.pages[q].offset);
                    assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
                };
                assert(post.good_range_unused(cur));
            }
            assert(post.attached_rec(segment_id, idx, false));
        }
    }

    pub proof fn attached_rec_no_to_used_popped(
        pre: State, post: State, page_id: PageId, idx: int
    )
        requires
          pre.invariant(),
          pre.popped == Popped::No,
          post.popped == Popped::Used(page_id, true),
          pre.attached_rec(page_id.segment_id, idx, false),
          pre.pages[page_id].is_used == true,
          pre.pages[page_id].offset == Some(0nat),
          post.good_range_used(page_id),
          post.pages[page_id].count == pre.pages[page_id].count,
          idx >= 0,
          idx <= page_id.idx,
          forall |pid: PageId|
            #![trigger pre.pages.dom().contains(pid)]
            #![trigger post.pages.dom().contains(pid)]
            #![trigger pre.pages[pid]]
            #![trigger post.pages[pid]]
            pid.segment_id == page_id.segment_id ==>
            (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
            && (pre.pages.dom().contains(pid)
                && !pre.in_popped_range(pid)
                && !post.in_popped_range(pid) ==> {
                &&& post.pages.dom().contains(pid)
                &&& pre.pages[pid].count == post.pages[pid].count
                &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                &&& pre.pages[pid].offset == post.pages[pid].offset
                &&& pre.pages[pid].is_used == post.pages[pid].is_used
                &&& pre.pages[pid].full == post.pages[pid].full
                &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
              }),
        ensures post.attached_rec(page_id.segment_id, idx, true),
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::in_popped_range);
        reveal(State::popped_for_seg);
        reveal(State::good_range_used);
        reveal(State::good_range_unused);

        let segment_id = page_id.segment_id;
        assert(post.pages[page_id].count.unwrap() == pre.pages[page_id].count.unwrap());
        let popped_count = post.pages[page_id].count.unwrap();
        assert(popped_count > 0);
        assert(page_id.idx + popped_count <= SLICES_PER_SEGMENT);

        if idx == SLICES_PER_SEGMENT {
            assert(page_id.idx < SLICES_PER_SEGMENT);
            assert(false);
        } else if idx > SLICES_PER_SEGMENT {
            assert(!pre.attached_rec(segment_id, idx, false));
            assert(false);
        } else if idx == page_id.idx {
            assert(!Self::is_the_popped(segment_id, idx, pre.popped));
            assert(pre.pages[page_id].is_used == true);
            assert(pre.good_range_used(page_id));
            assert(pre.attached_rec(segment_id, idx + pre.pages[page_id].count.unwrap(), false));
            assert(post.popped_len() == popped_count as int);

            assert forall |pid: PageId|
                #![trigger pre.pages.dom().contains(pid)]
                #![trigger post.pages.dom().contains(pid)]
                #![trigger pre.pages[pid]]
                #![trigger post.pages[pid]]
                pid.segment_id == segment_id
            implies
                (pre.pages.dom().contains(pid) <==> post.pages.dom().contains(pid))
                && (pre.pages.dom().contains(pid) ==> (
                    (!pre.in_popped_range(pid) && pid.idx >= idx + pre.pages[page_id].count.unwrap() ==> {
                    &&& post.pages.dom().contains(pid)
                    &&& pre.pages[pid].count == post.pages[pid].count
                    &&& (pre.pages[pid].dlist_entry.is_some() <==> post.pages[pid].dlist_entry.is_some())
                    &&& pre.pages[pid].offset == post.pages[pid].offset
                    &&& pre.pages[pid].is_used == post.pages[pid].is_used
                    &&& pre.pages[pid].full == post.pages[pid].full
                    &&& pre.pages[pid].page_header_kind == post.pages[pid].page_header_kind
                  })))
            by {
                if pre.pages.dom().contains(pid) && !pre.in_popped_range(pid) && pid.idx >= idx + pre.pages[page_id].count.unwrap() {
                    assert(!post.in_popped_range(pid));
                }
            };
            Self::attached_rec_same(pre, post, segment_id, idx + pre.pages[page_id].count.unwrap(), false);
            assert(post.attached_rec(segment_id, idx + post.popped_len(), false));
            assert(Self::is_the_popped(segment_id, idx, post.popped));
            assert(post.attached_rec(segment_id, idx, true));
        } else {
            assert(idx < page_id.idx);
            assert(!Self::is_the_popped(segment_id, idx, pre.popped));
            assert(!Self::is_the_popped(segment_id, idx, post.popped));
            let cur = PageId { segment_id, idx: idx as nat };
            let count = pre.pages[cur].count.unwrap();
            assert(count > 0);
            assert(idx + count <= SLICES_PER_SEGMENT);
            assert(pre.attached_rec(segment_id, idx + count, false));
            if idx + count > page_id.idx {
                assert(cur.segment_id == page_id.segment_id);
                assert(cur.idx <= page_id.idx);
                assert(page_id.idx < cur.idx + count);
                if pre.pages[cur].is_used {
                    assert(pre.good_range_used(cur));
                    assert(pre.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                    assert(pre.pages[page_id].offset == Some(0nat));
                    assert(page_id.idx - cur.idx > 0);
                } else {
                    assert(pre.good_range_unused(cur));
                    assert(pre.pages[page_id].is_used == false);
                    assert(pre.pages[page_id].is_used == true);
                }
                assert(false);
            }
            assert(idx + count <= page_id.idx);
            Self::attached_rec_no_to_used_popped(pre, post, page_id, idx + count);
            assert(post.attached_rec(segment_id, idx + count, true));
            assert(!pre.in_popped_range(cur));
            assert(!post.in_popped_range(cur));
            assert(post.pages.dom().contains(cur));
            assert(post.pages[cur].count == pre.pages[cur].count);
            assert(post.pages[cur].count.unwrap() == count);
            assert(post.pages[cur].is_used == pre.pages[cur].is_used);

            assert forall |q: PageId|
                #![trigger post.pages.dom().contains(q)]
                #![trigger post.pages.index(q)]
                q.segment_id == segment_id
                && cur.idx <= q.idx < cur.idx + count
            implies
                !pre.in_popped_range(q) && !post.in_popped_range(q)
            by {
                assert(q.idx < idx + count);
                assert(idx + count <= page_id.idx);
                assert(pre.popped == Popped::No);
                if post.in_popped_range(q) {
                    assert(page_id.idx <= q.idx);
                    assert(false);
                }
            };

            if pre.pages[cur].is_used {
                assert(pre.good_range_used(cur));
                assert forall |q: PageId|
                    #![trigger post.pages.dom().contains(q)]
                    #![trigger post.pages.index(q)]
                    q.segment_id == segment_id
                    && cur.idx <= q.idx < cur.idx + count
                implies
                    post.pages.dom().contains(q)
                    && post.pages[q].is_used == true
                    && post.pages[q].offset == Some((q.idx - cur.idx) as nat)
                    && (post.pages[q].page_header_kind.is_some() <==> q == cur)
                    && (q != cur ==> post.pages[q].dlist_entry.is_none())
                    && (q != cur ==> post.pages[q].full.is_none())
                by {
                    assert(!pre.in_popped_range(q));
                    assert(!post.in_popped_range(q));
                    assert(pre.pages.dom().contains(q));
                    assert(pre.pages[q].is_used == true);
                    assert(pre.pages[q].offset == Some((q.idx - cur.idx) as nat));
                    assert(pre.pages[q].page_header_kind.is_some() <==> q == cur);
                    assert(q != cur ==> pre.pages[q].dlist_entry.is_none());
                    assert(q != cur ==> pre.pages[q].full.is_none());
                    assert(post.pages.dom().contains(q));
                    assert(post.pages[q].is_used == pre.pages[q].is_used);
                    assert(post.pages[q].offset == pre.pages[q].offset);
                    assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
                    assert(post.pages[q].full == pre.pages[q].full);
                    assert(pre.pages[q].dlist_entry.is_some() <==> post.pages[q].dlist_entry.is_some());
                };
                assert(post.good_range_used(cur));
            } else {
                assert(pre.good_range_unused(cur));
                assert forall |q: PageId|
                    #![trigger post.pages.dom().contains(q)]
                    #![trigger post.pages.index(q)]
                    q.segment_id == segment_id
                    && cur.idx <= q.idx < cur.idx + count
                implies
                    post.pages.dom().contains(q)
                    && post.pages[q].is_used == false
                    && post.pages[q].full.is_none()
                    && post.pages[q].page_header_kind.is_none()
                    && (post.pages[q].count.is_some() <==> q == cur)
                    && (post.pages[q].dlist_entry.is_some() <==> q == cur)
                    && post.pages[q].offset == (if q == cur || q == (PageId { segment_id: cur.segment_id, idx: (cur.idx + post.pages[cur].count.unwrap() - 1) as nat }) {
                            Some((q.idx - cur.idx) as nat)
                        } else {
                            None
                        })
                by {
                    assert(!pre.in_popped_range(q));
                    assert(!post.in_popped_range(q));
                    assert(pre.pages.dom().contains(q));
                    assert(pre.pages[q].is_used == false);
                    assert(pre.pages[q].full.is_none());
                    assert(pre.pages[q].page_header_kind.is_none());
                    assert(pre.pages[q].count.is_some() <==> q == cur);
                    assert(pre.pages[q].dlist_entry.is_some() <==> q == cur);
                    assert(post.pages.dom().contains(q));
                    assert(post.pages[q].is_used == pre.pages[q].is_used);
                    assert(post.pages[q].full == pre.pages[q].full);
                    assert(post.pages[q].page_header_kind == pre.pages[q].page_header_kind);
                    assert(post.pages[q].count == pre.pages[q].count);
                    assert(pre.pages[q].dlist_entry.is_some() <==> post.pages[q].dlist_entry.is_some());
                    assert(post.pages[q].offset == pre.pages[q].offset);
                    assert(post.pages[cur].count.unwrap() == pre.pages[cur].count.unwrap());
                };
                assert(post.good_range_unused(cur));
            }
            assert(post.attached_rec(segment_id, idx, true));
        }
    }


    pub closed spec fn if_popped_or_other_then_for(&self, segment_id: SegmentId) -> bool {
        match self.popped {
            Popped::No => true,
            Popped::Ready(page_id, _)
                | Popped::Used(page_id, _)
                => page_id.segment_id == segment_id,
            Popped::SegmentCreating(sid) => sid == segment_id,
            Popped::SegmentFreeing(sid, _) => sid == segment_id,
            Popped::VeryUnready(sid, _, _, _) => sid == segment_id,
            Popped::ExtraCount(_) => true,
        }
    }

    pub proof fn unchanged_used_ll(pre: Self, post: Self)
        requires pre.invariant(),
          pre.used_lists == post.used_lists,
          pre.used_dlist_headers == post.used_dlist_headers,
          forall |i: int, j: int|
            #![trigger pre.used_lists.index(i).index(j)]
            0 <= i < pre.used_lists.len()
              && 0 <= j < pre.used_lists[i].len()
              ==> {
                let page_id = pre.used_lists[i][j];
                &&& post.pages.dom().contains(page_id)
                &&& post.pages[page_id] == pre.pages[page_id]
                &&& (post.popped.is_Ready() ==> page_id != post.popped_page_id())
              }
        ensures
          post.ll_inv_valid_used()
    {
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);

        assert forall |i: int|
            #![trigger post.used_dlist_headers.index(i)]
            0 <= i < post.used_lists.len()
        implies
            valid_ll(post.pages, post.used_dlist_headers[i], post.used_lists[i])
        by {
            assert(0 <= i < pre.used_lists.len());
            assert(valid_ll(pre.pages, pre.used_dlist_headers[i], pre.used_lists[i]));
            assert(post.used_lists[i] == pre.used_lists[i]);
            assert(post.used_dlist_headers[i] == pre.used_dlist_headers[i]);
            assert forall |j: int|
                0 <= j < post.used_lists[i].len()
            implies
                valid_ll_i(post.pages, post.used_lists[i], j)
            by {
                let page_id = post.used_lists[i][j];
                assert(page_id == pre.used_lists[i][j]);
                assert(valid_ll_i(pre.pages, pre.used_lists[i], j));
                assert(post.pages.dom().contains(page_id));
                assert(post.pages[page_id] == pre.pages[page_id]);
            };
        };

        assert forall |i: int, j: int|
            0 <= i < post.used_lists.len()
            && 0 <= j < post.used_lists[i].len()
            && #[trigger] post.used_lists.index(i).index(j) == post.used_lists.index(i).index(j)
        implies
            ({
                let page_id = post.used_lists[i][j];
                &&& (valid_bin_idx(i) || i == BIN_FULL)
                &&& post.valid_used_page(page_id, i, j)
                &&& post.pages[page_id].count.is_some()
                &&& post.pages[page_id].full == Some(i == BIN_FULL)
                &&& (post.popped.is_Ready() ==> page_id != post.popped_page_id())
            })
        by {
            let page_id = post.used_lists[i][j];
            assert(page_id == pre.used_lists[i][j]);
            assert(pre.valid_used_page(page_id, i, j));
            assert(post.pages.dom().contains(page_id));
            assert(post.pages[page_id] == pre.pages[page_id]);
            assert(post.valid_used_page(page_id, i, j));
        };
    }

    pub proof fn unchanged_unused_ll(pre: Self, post: Self)
        requires pre.invariant(),
          pre.unused_lists == post.unused_lists,
          pre.unused_dlist_headers == post.unused_dlist_headers,
          forall |i: int, j: int|
            #![trigger pre.unused_lists.index(i).index(j)]
            0 <= i < pre.unused_lists.len()
              && 0 <= j < pre.unused_lists[i].len()
              ==> {
                let page_id = pre.unused_lists[i][j];
                &&& post.pages.dom().contains(page_id)
                &&& post.pages[page_id] == pre.pages[page_id]
              }
        ensures
          post.ll_inv_valid_unused()
    {
        reveal(State::ll_inv_valid_unused);
        reveal(State::valid_unused_page);

        assert forall |i: int|
            #![trigger post.unused_dlist_headers.index(i)]
            0 <= i < post.unused_lists.len()
        implies
            valid_ll(post.pages, post.unused_dlist_headers[i], post.unused_lists[i])
        by {
            assert(0 <= i < pre.unused_lists.len());
            assert(valid_ll(pre.pages, pre.unused_dlist_headers[i], pre.unused_lists[i]));
            assert(post.unused_lists[i] == pre.unused_lists[i]);
            assert(post.unused_dlist_headers[i] == pre.unused_dlist_headers[i]);
            assert forall |j: int|
                0 <= j < post.unused_lists[i].len()
            implies
                valid_ll_i(post.pages, post.unused_lists[i], j)
            by {
                let page_id = post.unused_lists[i][j];
                assert(page_id == pre.unused_lists[i][j]);
                assert(valid_ll_i(pre.pages, pre.unused_lists[i], j));
                assert(post.pages.dom().contains(page_id));
                assert(post.pages[page_id] == pre.pages[page_id]);
            };
        };

        assert forall |i: int, j: int|
            0 <= i < post.unused_lists.len()
            && 0 <= j < post.unused_lists[i].len()
            && #[trigger] post.unused_lists.index(i).index(j) == post.unused_lists.index(i).index(j)
        implies
            ({
                let page_id = post.unused_lists[i][j];
                &&& 0 <= i <= SEGMENT_BIN_MAX
                &&& post.pages.dom().contains(page_id)
                &&& page_id.idx != 0
                &&& post.pages[page_id].is_used == false
                &&& (match post.pages[page_id].count {
                    Some(count) => 1 <= count <= SLICES_PER_SEGMENT,
                    None => false,
                })
                &&& post.pages[page_id].offset == Some(0nat)
                &&& post.pages[page_id].dlist_entry.is_some()
                &&& 0 <= j < post.unused_lists[i].len()
                &&& post.unused_lists[i][j] == page_id
                &&& post.valid_unused_page(page_id, i, j)
                &&& i == smallest_sbin_fitting_size(post.pages[page_id].count.unwrap() as int)
            })
        by {
            let page_id = post.unused_lists[i][j];
            assert(page_id == pre.unused_lists[i][j]);
            assert(pre.valid_unused_page(page_id, i, j));
            assert(post.pages.dom().contains(page_id));
            assert(post.pages[page_id] == pre.pages[page_id]);
            assert(post.valid_unused_page(page_id, i, j));
        };
    }

    pub closed spec fn insert_front(ll: Seq<Seq<PageId>>, i: int, page_id: PageId) -> Seq<Seq<PageId>> {
        ll.update(i, ll[i].insert(0, page_id))
    }

    pub closed spec fn insert_back(ll: Seq<Seq<PageId>>, i: int, page_id: PageId) -> Seq<Seq<PageId>> {
        ll.update(i, ll[i].push(page_id))
    }

    pub proof fn good_range_disjoint_very_unready(&self, page_id: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id) || self.good_range_used(page_id),
        ensures (match self.popped {
            Popped::VeryUnready(sid, idx, count, _) => {
                sid != page_id.segment_id
                  || idx + count <= page_id.idx
                  || idx >= page_id.idx + self.pages[page_id].count.unwrap()
            }
            _ => true,
        })
    {
        reveal(State::popped_basics);
        reveal(State::inv_very_unready);
        reveal(State::attached_ranges);
        reveal(State::attached_ranges_segment);
        reveal(State::attached_rec0);
        reveal(State::popped_for_seg);
        reveal(State::good_range0);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);
        reveal(State::good_range_very_unready);
        reveal(State::count_off0);

        match self.popped {
            Popped::VeryUnready(sid, start, count, _) => {
                let page_count = self.pages[page_id].count.unwrap();
                if sid == page_id.segment_id
                    && !(start + count <= page_id.idx)
                    && !(start >= page_id.idx + page_count)
                {
                    self.very_unready_popped_range_facts();
                    let popped_id = PageId { segment_id: sid, idx: start as nat };
                    assert(self.good_range_very_unready(popped_id));
                    if self.good_range_used(page_id) {
                        if page_id.idx >= start {
                            assert(start <= page_id.idx < start + count);
                            assert(self.pages[page_id].is_used == false);
                            assert(self.pages[page_id].is_used == true);
                            assert(false);
                        } else {
                            assert(page_id.idx < start < page_id.idx + page_count);
                            assert(popped_id.segment_id == page_id.segment_id);
                            assert(page_id.idx <= popped_id.idx < page_id.idx + page_count);
                            assert(self.pages[popped_id].offset == Some((popped_id.idx - page_id.idx) as nat));
                            assert(self.pages[popped_id].offset.is_none());
                            assert(false);
                        }
                    } else {
                        assert(self.good_range_unused(page_id));
                        if page_id.idx >= start {
                            assert(start <= page_id.idx < start + count);
                            assert(self.pages[page_id].offset.is_none());
                            assert(self.pages[page_id].offset == Some(0nat));
                            assert(false);
                        } else {
                            assert(page_id.idx < start < page_id.idx + page_count);
                            assert(self.attached_ranges_segment(page_id.segment_id));
                            assert(self.attached_rec0(page_id.segment_id, true));
                            let first_id = PageId { segment_id: page_id.segment_id, idx: 0 };
                            let first_count = self.pages[first_id].count.unwrap();
                            assert(self.good_range0(page_id.segment_id));
                            assert(self.attached_rec(page_id.segment_id, first_count as int, true));
                            if first_count > page_id.idx {
                                if page_id == first_id {
                                    assert(page_count == first_count);
                                    self.sp_true_implies_le(first_count as int);
                                    assert(first_count <= start);
                                    assert(start < page_id.idx + page_count);
                                    assert(page_id.idx == 0);
                                    assert(start < first_count);
                                    assert(false);
                                } else {
                                    assert(first_id.idx <= page_id.idx < first_id.idx + first_count);
                                    assert(self.pages[page_id].offset == Some((page_id.idx - first_id.idx) as nat));
                                    assert(page_id.idx - first_id.idx > 0);
                                    assert(self.pages[page_id].offset == Some(0nat));
                                    assert(false);
                                }
                            }
                            assert(first_count <= page_id.idx);
                            self.rec_grd(page_id.segment_id, first_count as int, page_id);
                            assert(false);
                        }
                    }
                }
            }
            _ => { }
        }
    }

    pub proof fn rec_grd(&self, segment_id: SegmentId, idx: int, page_id: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id),
            (match self.popped {
                Popped::VeryUnready(sid, idx, count, _) => {
                    sid == page_id.segment_id
                      && !(idx + count <= page_id.idx)
                      && !(idx >= page_id.idx + self.pages[page_id].count.unwrap())
                }
                _ => false,
            }),
            self.attached_rec(segment_id, idx, true),
            0 <= idx <= page_id.idx,
            page_id.segment_id == segment_id,
        ensures
            false
        decreases SLICES_PER_SEGMENT - idx
    {
        reveal(State::attached_rec);
        reveal(State::is_the_popped);
        reveal(State::popped_len);
        reveal(State::page_id_of_popped);
        reveal(State::good_range_unused);
        reveal(State::good_range_used);
        reveal(State::count_off0);

        let page_count = self.pages[page_id].count.unwrap();
        match self.popped {
            Popped::VeryUnready(sid, start, pcount, _) => {
                if idx == SLICES_PER_SEGMENT {
                    assert(page_id.idx == SLICES_PER_SEGMENT);
                    assert(1 <= page_count);
                    assert(page_id.idx + page_count <= SLICES_PER_SEGMENT);
                    assert(false);
                } else if idx > SLICES_PER_SEGMENT {
                    assert(!self.attached_rec(segment_id, idx, true));
                    assert(false);
                } else if Self::is_the_popped(segment_id, idx, self.popped) {
                    self.very_unready_popped_range_facts();
                    assert(idx == start);
                    assert(start <= page_id.idx < start + pcount);
                    assert(self.pages[page_id].offset.is_none());
                    assert(self.pages[page_id].offset == Some(0nat));
                    assert(false);
                } else {
                    let cur = PageId { segment_id, idx: idx as nat };
                    let cur_count = self.pages[cur].count.unwrap();
                    assert(cur_count > 0);
                    assert(idx + cur_count <= SLICES_PER_SEGMENT);
                    assert(self.attached_rec(segment_id, idx + cur_count, true));
                    if idx == page_id.idx {
                        assert(cur == page_id);
                        assert(cur_count == page_count);
                        self.sp_true_implies_le(idx + cur_count);
                        assert(idx + page_count <= start);
                        assert(!(start >= page_id.idx + page_count));
                        assert(false);
                    } else {
                        assert(idx < page_id.idx);
                        if idx + cur_count > page_id.idx {
                            assert(cur.segment_id == page_id.segment_id);
                            assert(cur.idx <= page_id.idx < cur.idx + cur_count);
                            if self.pages[cur].is_used {
                                assert(self.good_range_used(cur));
                                assert(self.pages[page_id].is_used == true);
                                assert(self.pages[page_id].is_used == false);
                                assert(false);
                            } else {
                                assert(self.good_range_unused(cur));
                                let last_id = PageId { segment_id, idx: (idx + cur_count - 1) as nat };
                                if page_id == last_id {
                                    assert(page_id.idx - cur.idx > 0);
                                    assert(self.pages[page_id].offset == Some((page_id.idx - cur.idx) as nat));
                                    assert(self.pages[page_id].offset == Some(0nat));
                                    assert(false);
                                } else {
                                    assert(self.pages[page_id].offset.is_none());
                                    assert(self.pages[page_id].offset == Some(0nat));
                                    assert(false);
                                }
                            }
                        }
                        assert(idx + cur_count <= page_id.idx);
                        self.rec_grd(segment_id, idx + cur_count, page_id);
                    }
                }
            }
            _ => { assert(false); }
        }
    }



    /*pub proof fn good_range_disjoint_two(&self, page_id1: PageId, page_id2: PageId)
        requires self.invariant(),
            self.good_range_unused(page_id1),
            self.good_range_unused(page_id2),
            page_id1 != page_id2,
        ensures 
            page_id1.segment_id != page_id2.segment_id
              || page_id1.idx + self.pages[page_id1].count.unwrap() <= page_id2.idx
              || page_id2.idx + self.pages[page_id2].count.unwrap() <= page_id1.idx
    {
    }*/

    pub proof fn ll_unused_distinct(&self, i1: int, j1: int, i2: int, j2: int)
      requires self.invariant(),
        0 <= i1 < self.unused_lists.len(),
        0 <= j1 < self.unused_lists[i1].len(),
        0 <= i2 < self.unused_lists.len(),
        0 <= j2 < self.unused_lists[i2].len(),
        i1 != i2 || j1 != j2,
      ensures
        self.unused_lists[i1][j1] != self.unused_lists[i2][j2],
      decreases j1
    {
        reveal(State::ll_inv_valid_unused);

        let p1 = self.unused_lists[i1][j1];
        let p2 = self.unused_lists[i2][j2];

        assert(valid_ll(self.pages, self.unused_dlist_headers[i1], self.unused_lists[i1]));
        assert(valid_ll(self.pages, self.unused_dlist_headers[i2], self.unused_lists[i2]));
        assert(self.pages.dom().contains(p1));
        assert(self.pages.dom().contains(p2));
        assert(self.pages[p1].count.is_some());
        assert(self.pages[p2].count.is_some());
        assert(i1 == smallest_sbin_fitting_size(self.pages[p1].count.unwrap() as int));
        assert(i2 == smallest_sbin_fitting_size(self.pages[p2].count.unwrap() as int));

        if i1 == i2 {
            if j1 < j2 {
                valid_ll_distinct(self.pages, self.unused_dlist_headers[i1], self.unused_lists[i1], j1, j2);
            } else {
                assert(j2 < j1);
                valid_ll_distinct(self.pages, self.unused_dlist_headers[i1], self.unused_lists[i1], j2, j1);
            }
        } else {
            if p1 == p2 {
                assert(self.pages[p1].count == self.pages[p2].count);
                assert(i1 == i2);
                assert(false);
            }
        }
    }

    pub proof fn ll_used_distinct(&self, i1: int, j1: int, i2: int, j2: int)
      requires self.invariant(),
        0 <= i1 < self.used_lists.len(),
        0 <= j1 < self.used_lists[i1].len(),
        0 <= i2 < self.used_lists.len(),
        0 <= j2 < self.used_lists[i2].len(),
        i1 != i2 || j1 != j2,
      ensures
        self.used_lists[i1][j1] != self.used_lists[i2][j2],
      decreases j1
    {
        reveal(State::ll_inv_valid_used);
        reveal(State::valid_used_page);

        let p1 = self.used_lists[i1][j1];
        let p2 = self.used_lists[i2][j2];

        assert(valid_ll(self.pages, self.used_dlist_headers[i1], self.used_lists[i1]));
        assert(valid_ll(self.pages, self.used_dlist_headers[i2], self.used_lists[i2]));
        assert(self.valid_used_page(p1, i1, j1));
        assert(self.valid_used_page(p2, i2, j2));
        assert(self.pages[p1].full == Some(i1 == BIN_FULL));
        assert(self.pages[p2].full == Some(i2 == BIN_FULL));

        if i1 == i2 {
            if j1 < j2 {
                valid_ll_distinct(self.pages, self.used_dlist_headers[i1], self.used_lists[i1], j1, j2);
            } else {
                assert(j2 < j1);
                valid_ll_distinct(self.pages, self.used_dlist_headers[i1], self.used_lists[i1], j2, j1);
            }
        } else {
            if p1 == p2 {
                assert(self.pages[p1].full == self.pages[p2].full);
                assert(i1 == BIN_FULL <==> i2 == BIN_FULL);
                if i1 == BIN_FULL {
                    assert(i2 == BIN_FULL);
                    assert(i1 == i2);
                    assert(false);
                } else if i2 == BIN_FULL {
                    assert(i1 == BIN_FULL);
                    assert(false);
                } else {
                    match self.pages[p1].page_header_kind {
                        Some(PageHeaderKind::Normal(bin, _)) => {
                            assert(i1 == bin);
                            assert(i2 == bin);
                            assert(i1 == i2);
                            assert(false);
                        }
                        None => {
                            assert(false);
                        }
                    }
                }
            }
        }
    }

    pub proof fn ll_mono_back(lls1: Seq<Seq<PageId>>, sbin_idx: int, first_page: PageId)
    requires 0 <= sbin_idx < lls1.len()
    ensures ({
        let lls2 = Self::insert_back(lls1, sbin_idx, first_page);
        forall |pid| is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2)
    })
    {
        let lls2 = Self::insert_back(lls1, sbin_idx, first_page);
        let old_ll = lls1[sbin_idx];
        let new_ll = old_ll.push(first_page);
        assert(lls2.len() == lls1.len());
        assert(lls2[sbin_idx] =~~= new_ll);

        assert forall |pid: PageId| is_in_lls(pid, lls1) implies is_in_lls(pid, lls2) by {
            let (i, j): (int, int) = choose |i: int, j: int|
                0 <= i < lls1.len()
                && 0 <= j < lls1[i].len()
                && lls1[i][j] == pid;
            assert(0 <= i < lls1.len());
            assert(0 <= j < lls1[i].len());
            assert(lls1[i][j] == pid);
            assert(0 <= i < lls2.len());
            if i == sbin_idx {
                assert(0 <= j < new_ll.len());
                assert(new_ll[j] == pid);
                assert(0 <= j < lls2[i].len());
                assert(lls2[i][j] == pid);
            } else {
                assert(lls2[i] =~~= lls1[i]);
                assert(0 <= j < lls2[i].len());
                assert(lls2[i][j] == pid);
            }
        }
    }

    pub proof fn ll_mono(lls1: Seq<Seq<PageId>>, sbin_idx: int, first_page: PageId)
    requires 0 <= sbin_idx < lls1.len()
    ensures ({
        let lls2 = Self::insert_front(lls1, sbin_idx, first_page);
        forall |pid| is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2)
    })
    {
        let lls2 = Self::insert_front(lls1, sbin_idx, first_page);
        let old_ll = lls1[sbin_idx];
        let new_ll = old_ll.insert(0, first_page);
        old_ll.insert_ensures(0, first_page);
        assert(lls2.len() == lls1.len());
        assert(lls2[sbin_idx] =~~= new_ll);

        assert forall |pid: PageId| is_in_lls(pid, lls1) implies is_in_lls(pid, lls2) by {
            let (i, j): (int, int) = choose |i: int, j: int|
                0 <= i < lls1.len()
                && 0 <= j < lls1[i].len()
                && lls1[i][j] == pid;
            assert(0 <= i < lls1.len());
            assert(0 <= j < lls1[i].len());
            assert(lls1[i][j] == pid);
            assert(0 <= i < lls2.len());
            if i == sbin_idx {
                let new_j = j + 1;
                assert(0 <= new_j < new_ll.len());
                assert(new_ll[new_j] == pid);
                assert(0 <= new_j < lls2[i].len());
                assert(lls2[i][new_j] == pid);
            } else {
                assert(lls2[i] =~~= lls1[i]);
                assert(0 <= j < lls2[i].len());
                assert(lls2[i][j] == pid);
            }
        }
    }

    pub proof fn ll_remove(lls1: Seq<Seq<PageId>>, lls2: Seq<Seq<PageId>>, sbin_idx: int, list_idx: int)
    requires 0 <= sbin_idx < lls1.len(),
        0 <= list_idx < lls1[sbin_idx].len(),
        lls2 =~~= lls1.update(sbin_idx, lls1[sbin_idx].remove(list_idx)),
    ensures
        forall |pid| pid != lls1[sbin_idx][list_idx] ==>
            #[trigger] is_in_lls(pid, lls1) ==> is_in_lls(pid, lls2),
    {
        let old_ll = lls1[sbin_idx];
        let new_ll = old_ll.remove(list_idx);
        let removed = old_ll[list_idx];
        old_ll.remove_ensures(list_idx);

        assert(lls2.len() == lls1.len());
        assert(lls2[sbin_idx] =~~= new_ll);

        assert forall |pid: PageId|
            pid != removed
            && #[trigger] is_in_lls(pid, lls1)
        implies
            is_in_lls(pid, lls2)
        by {
            let (i, j): (int, int) = choose |i: int, j: int|
                0 <= i < lls1.len()
                && 0 <= j < lls1[i].len()
                && lls1[i][j] == pid;
            assert(0 <= i < lls1.len());
            assert(0 <= j < lls1[i].len());
            assert(lls1[i][j] == pid);

            if i == sbin_idx {
                if j < list_idx {
                    assert(0 <= j < new_ll.len());
                    assert(new_ll[j] == pid);
                    assert(0 <= sbin_idx < lls2.len());
                    assert(0 <= j < lls2[sbin_idx].len());
                    assert(lls2[sbin_idx][j] == pid);
                } else if j == list_idx {
                    assert(pid == removed);
                    assert(false);
                } else {
                    let new_j = j - 1;
                    assert(0 <= new_j < new_ll.len());
                    assert(new_ll[new_j] == pid);
                    assert(0 <= sbin_idx < lls2.len());
                    assert(0 <= new_j < lls2[sbin_idx].len());
                    assert(lls2[sbin_idx][new_j] == pid);
                }
            } else {
                assert(lls2[i] =~~= lls1[i]);
                assert(0 <= i < lls2.len());
                assert(0 <= j < lls2[i].len());
                assert(lls2[i][j] == pid);
            }
        }
    }

    pub proof fn ll_remove_preserves_list_at(
        lls1: Seq<Seq<PageId>>, lls2: Seq<Seq<PageId>>,
        sbin_idx: int, list_idx: int, pid: PageId, i: int
    )
        requires
            0 <= sbin_idx < lls1.len(),
            0 <= list_idx < lls1[sbin_idx].len(),
            lls2 =~~= lls1.update(sbin_idx, lls1[sbin_idx].remove(list_idx)),
            pid != lls1[sbin_idx][list_idx],
            is_in_list_at(pid, lls1, i),
        ensures
            is_in_list_at(pid, lls2, i),
    {
        let old_ll = lls1[sbin_idx];
        let new_ll = old_ll.remove(list_idx);
        let old_j = choose |j: int|
            0 <= j < lls1[i].len()
            && lls1[i][j] == pid;
        old_ll.remove_ensures(list_idx);

        assert(0 <= i < lls1.len());
        assert(0 <= old_j < lls1[i].len());
        assert(lls2.len() == lls1.len());
        assert(0 <= i < lls2.len());

        if i == sbin_idx {
            assert(old_j != list_idx);
            assert(lls2[i] =~~= new_ll);
            if old_j < list_idx {
                assert(0 <= old_j < new_ll.len());
                assert(new_ll[old_j] == pid);
                assert(0 <= old_j < lls2[i].len());
                assert(lls2[i][old_j] == pid);
            } else {
                assert(old_j > list_idx);
                let new_j = old_j - 1;
                assert(0 <= new_j < new_ll.len());
                assert(new_ll[new_j] == pid);
                assert(0 <= new_j < lls2[i].len());
                assert(lls2[i][new_j] == pid);
            }
        } else {
            assert(lls2[i] =~~= lls1[i]);
            assert(0 <= old_j < lls2[i].len());
            assert(lls2[i][old_j] == pid);
        }
    }

    pub proof fn ll_insert_front_preserves_list_at(
        lls1: Seq<Seq<PageId>>, lls2: Seq<Seq<PageId>>,
        bin_idx: int, inserted: PageId, pid: PageId, i: int
    )
        requires
            0 <= bin_idx < lls1.len(),
            lls2 =~~= Self::insert_front(lls1, bin_idx, inserted),
            is_in_list_at(pid, lls1, i),
        ensures
            is_in_list_at(pid, lls2, i),
    {
        let old_ll = lls1[bin_idx];
        let new_ll = old_ll.insert(0, inserted);
        old_ll.insert_ensures(0, inserted);
        let old_j = choose |j: int|
            0 <= j < lls1[i].len()
            && lls1[i][j] == pid;

        assert(0 <= i < lls1.len());
        assert(0 <= old_j < lls1[i].len());
        assert(lls2.len() == lls1.len());
        assert(0 <= i < lls2.len());

        if i == bin_idx {
            let new_j = old_j + 1;
            assert(lls2[i] =~~= new_ll);
            assert(0 <= new_j < new_ll.len());
            assert(new_ll[new_j] == pid);
            assert(0 <= new_j < lls2[i].len());
            assert(lls2[i][new_j] == pid);
        } else {
            assert(lls2[i] =~~= lls1[i]);
            assert(0 <= old_j < lls2[i].len());
            assert(lls2[i][old_j] == pid);
        }
    }

    pub proof fn ll_insert_back_preserves_list_at(
        lls1: Seq<Seq<PageId>>, lls2: Seq<Seq<PageId>>,
        bin_idx: int, inserted: PageId, pid: PageId, i: int
    )
        requires
            0 <= bin_idx < lls1.len(),
            lls2 =~~= Self::insert_back(lls1, bin_idx, inserted),
            is_in_list_at(pid, lls1, i),
        ensures
            is_in_list_at(pid, lls2, i),
    {
        let old_ll = lls1[bin_idx];
        let new_ll = old_ll.push(inserted);
        let old_j = choose |j: int|
            0 <= j < lls1[i].len()
            && lls1[i][j] == pid;

        assert(0 <= i < lls1.len());
        assert(0 <= old_j < lls1[i].len());
        assert(lls2.len() == lls1.len());
        assert(0 <= i < lls2.len());

        if i == bin_idx {
            assert(lls2[i] =~~= new_ll);
            assert(0 <= old_j < new_ll.len());
            assert(new_ll[old_j] == pid);
            assert(0 <= old_j < lls2[i].len());
            assert(lls2[i][old_j] == pid);
        } else {
            assert(lls2[i] =~~= lls1[i]);
            assert(0 <= old_j < lls2[i].len());
            assert(lls2[i][old_j] == pid);
        }
    }
}}

pub open spec fn is_header(pd: PageData) -> bool {
    pd.offset == Some(0nat)
}

pub open spec fn is_unused_header(pd: PageData) -> bool {
    pd.offset == Some(0nat) && !pd.is_used
}

pub open spec fn is_used_header(pd: PageData) -> bool {
    pd.offset == Some(0nat) && pd.is_used
}

pub open spec fn get_next(ll: Seq<PageId>, j: int) -> Option<PageId> {
    if j == ll.len() - 1 {
        None
    } else {
        Some(ll[j + 1])
    }
}

pub open spec fn get_prev(ll: Seq<PageId>, j: int) -> Option<PageId> {
    if j == 0 {
        None
    } else {
        Some(ll[j - 1])
    }
}

pub open spec fn valid_ll_i(pages: Map<PageId, PageData>, ll: Seq<PageId>, j: int) -> bool {
    0 <= j < ll.len()
      && pages.dom().contains(ll[j])
      && pages[ll[j]].dlist_entry.is_some()
      && pages[ll[j]].dlist_entry.unwrap().prev == get_prev(ll, j)
      && pages[ll[j]].dlist_entry.unwrap().next == get_next(ll, j)
}

pub open spec fn valid_ll(pages: Map<PageId, PageData>, header: DlistHeader, ll: Seq<PageId>) -> bool {
    &&& (match header.first {
        Some(first_id) => ll.len() != 0 && ll[0] == first_id,
        None => ll.len() == 0,
    })
    &&& (match header.last {
        Some(last_id) => ll.len() != 0 && ll[ll.len() - 1] == last_id,
        None => ll.len() == 0,
    })
    &&& (forall |j| 0 <= j < ll.len() ==> valid_ll_i(pages, ll, j))
}

pub proof fn valid_ll_distinct(
    pages: Map<PageId, PageData>,
    header: DlistHeader,
    ll: Seq<PageId>,
    j1: int,
    j2: int,
)
    requires
        valid_ll(pages, header, ll),
        0 <= j1 < j2 < ll.len(),
    ensures
        ll[j1] != ll[j2],
    decreases j1
{
    assert(valid_ll_i(pages, ll, j1));
    assert(valid_ll_i(pages, ll, j2));

    if ll[j1] == ll[j2] {
        let page_id = ll[j1];
        assert(pages[page_id].dlist_entry.is_some());
        assert(pages[ll[j2]].dlist_entry.is_some());
        assert(pages[page_id].dlist_entry.unwrap().prev == get_prev(ll, j1));
        assert(pages[page_id].dlist_entry.unwrap().prev == get_prev(ll, j2));

        if j1 == 0 {
            assert(get_prev(ll, j1) == None);
            assert(j2 > 0);
            assert(get_prev(ll, j2) == Some(ll[j2 - 1]));
            assert(false);
        } else {
            assert(get_prev(ll, j1) == Some(ll[j1 - 1]));
            assert(get_prev(ll, j2) == Some(ll[j2 - 1]));
            assert(ll[j1 - 1] == ll[j2 - 1]);
            valid_ll_distinct(pages, header, ll, j1 - 1, j2 - 1);
            assert(false);
        }
    }
}

pub open spec fn is_in_lls(page_id: PageId, s: Seq<Seq<PageId>>) -> bool {
    exists |i: int, j: int| 
        0 <= i < s.len()
        && 0 <= j < s[i].len()
        && s[i][j] == page_id
}

pub open spec fn is_in_list_at(page_id: PageId, s: Seq<Seq<PageId>>, i: int) -> bool {
    0 <= i < s.len()
    && exists |j: int|
        0 <= j < s[i].len()
        && s[i][j] == page_id
}

}
