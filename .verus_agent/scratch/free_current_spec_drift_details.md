baseline=05a6305688419c79fbddd15e7bf901d3af9e9ed6 sources=29 target_fns=['free', 'global_init', 'heap_init', 'heap_malloc']

## verus-mimalloc/alloc_fast.rs::heap_malloc_zero_ex mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- ensures added
  after : final(local).inst() == old(local).inst()
- ensures added
  after : final(local).wf()
- ensures added
  after : ({ let (ptr, points_to_raw, dealloc) = t; points_to_raw@.is_range(ptr as int, size as int) && points_to_raw@.provenance() == ptr@.provenance && ptr == dealloc@.ptr() && dealloc@.inst() == final(local).inst() && dealloc@.size() == size })
- ensures added
  after : forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))

## verus-mimalloc/dealloc_token.rs::valid_block_token mode=spec dep=False removed=False new=False persistent=False impacted_by=[]
- body modified
  before: { &&& block.key().wf() &&& block.instance_id() == instance.id() // TODO factor this stuff into wf predicates // Valid segment &&& is_segment_ptr( block.value().segment_shared_access.points_to.ptr(), block.key().page_id.segment_id) &&& block.value().segment_shared_access.points_to.is_init() &&& block.value().segment_shared_access.points_to.value() .wf(instance, block.key().page_id.segment_id) // Valid slice page &&& is_page_ptr( block.value().page_slice_shared_access.points_to.ptr(), block.key().
  after : { &&& block.key().wf() &&& block.key().slice_idx_is_right() &&& block.instance_id() == instance.id() // TODO factor this stuff into wf predicates // Valid segment &&& is_segment_ptr( block.value().segment_shared_access.points_to.ptr(), block.key().page_id.segment_id) &&& block.value().segment_shared_access.points_to.is_init() &&& block.value().segment_shared_access.points_to.value() .wf(instance, block.key().page_id.segment_id) // Valid slice page &&& is_page_ptr( block.value().page_slice_shared

## verus-mimalloc/free.rs::free_generic mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- requires added
  after : dealloc.mim_instance == old(local).inst()
- requires added
  after : old(local).wf()
- ensures added
  after : final(local).inst() == old(local).inst()
- ensures added
  after : final(local).wf()
- ensures added
  after : forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))

## verus-mimalloc/free.rs::live_block_implies_page_used mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::block_ids_contains_witness mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::entry_token_matches_metadata mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::two_lists_with_live_cardinality_gap mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLSimple::empty mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- ensures added
  after : s.heap_id@ == heap_id
- ensures added
  after : s.wf()
- ensures added
  after : s.instance@ == instance

## verus-mimalloc/linked_list_insert_block.proof.rs::LL::insert_block mode=exec dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_retire mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- requires added
  after : old(local).wf()
- ensures added
  after : final(local).inst() == old(local).inst()
- ensures added
  after : final(local).wf()
- ensures added
  after : forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))

## verus-mimalloc/types.rs::PageInner::wf mode=spec dep=False removed=False new=False persistent=False impacted_by=[]
- body modified
  before: { &&& page_state.block_size == self.xblock_size as nat &&& self.free.wf() &&& self.free.fixed_page() &&& self.free.page_id() == page_id &&& self.free.block_size() == page_state.block_size &&& self.free.instance() == mim_instance &&& self.free.heap_id().is_none() &&& self.local_free.wf() &&& self.local_free.fixed_page() &&& self.local_free.page_id() == page_id &&& self.local_free.block_size() == page_state.block_size &&& self.local_free.instance() == mim_instance &&& self.local_free.heap_id().is_
  after : { &&& page_state.block_size == self.xblock_size as nat &&& self.free.wf() &&& self.free.fixed_page() &&& self.free.page_id() == page_id &&& self.free.block_size() == page_state.block_size &&& self.free.instance() == mim_instance &&& self.free.heap_id().is_none() &&& self.free.idx_bound() == page_state.num_blocks &&& self.local_free.wf() &&& self.local_free.fixed_page() &&& self.local_free.page_id() == page_id &&& self.local_free.block_size() == page_state.block_size &&& self.local_free.instance(

## verus-mimalloc/alloc_fast.rs::heap_malloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_fast.rs::heap_malloc_zero mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::segment_commitx mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::segment_ensure_committed mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/dealloc_token.rs::MimDealloc::into_internal mode=proof dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/init.rs::heap_init mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/init.rs::init_empty_page_ptr mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/init.rs::thread_data_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/layout.rs::SegmentPtr::ptr_segment mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/layout.rs::calculate_page_start mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/layout.rs::segment_page_start_from_slice mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::empty mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::new mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mmap_prot_none mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mmap_prot_read_write mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mprotect_prot_none mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mprotect_prot_read_write mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_reclaim_or_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_slice_split mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_span_free_coalesce mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_span_free_coalesce_before mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segments_page_find_and_allocate mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::span_queue_delete mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_arena_id mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_page_count mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_page_empty mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_page_retired_max mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_page_retired_min mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_pages mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_pages_free_direct mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::get_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::set_page_count mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::set_page_retired_max mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::HeapPtr::set_page_retired_min mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::add_offset mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::add_offset_and_check mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_block_size mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_count mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_index mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_inner_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_inner_ref_maybe_empty mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_next mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_prev mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::get_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::is_gt_0th_slice mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::slice_start mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::PagePtr::sub_offset mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_abandoned mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_allow_decommit mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_commit_mask mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_decommit_expire mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_decommit_mask mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_main2_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_main_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_mem_is_pinned mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_page_after_end mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_page_header_ptr mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_segment_kind mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::get_used mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::is_kind_huge mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::TldPtr::get_mut mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::TldPtr::get_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::TldPtr::get_segments_count mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
