baseline=05a6305688419c79fbddd15e7bf901d3af9e9ed6 sources=29 target_fns=['free', 'global_init', 'heap_init', 'heap_malloc']

## verus-mimalloc/alloc_fast.rs::heap_malloc_zero_ex mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- ensures added
  after : ({ let (ptr, points_to_raw, dealloc) = t; points_to_raw@.is_range(ptr as int, size as int) && points_to_raw@.provenance() == ptr@.provenance && ptr == dealloc@.ptr() && dealloc@.inst() == final(local).inst() && dealloc@.size() == size })
- ensures added
  after : final(local).inst() == old(local).inst()
- ensures added
  after : forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))
- ensures added
  after : final(local).wf()

## verus-mimalloc/commit_segment.rs::lemma_segment_commit_mask_aligned_bytes mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::lemma_segment_ptr_commit_aligned mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::live_block_implies_page_used mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::block_ids_contains_witness mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::block_ids_idx_disjoint_from mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::block_ids_idx_lt_num_blocks mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::block_token_fresh_for_ll mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::empty_fields_wf mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::entry_ptr_nonzero mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::entry_token_matches_metadata mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::make_empty mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- ensures added
  after : final(self).len() == 0
- ensures added
  after : final(self).block_size() == old(self).block_size()
- ensures added
  after : final(self).page_id() == old(self).page_id()
- ensures added
  after : llgstr@.instance == old(self).instance()
- ensures added
  after : final(self).fixed_page() == old(self).fixed_page()
- ensures added
  after : final(self).wf()
- ensures added
  after : llgstr@.page_id == old(self).page_id()
- ensures added
  after : llgstr@.block_size == old(self).block_size()
- ensures added
  after : final(self).heap_id() == old(self).heap_id()
- ensures added
  after : final(self).instance() == old(self).instance()

## verus-mimalloc/linked_list.rs::LL::three_lists_len_bound mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::two_lists_with_live_cardinality_gap mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::wf_first_addr_zero_implies_empty mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::wf_first_zero_implies_empty mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::wf_from_same_repr_addr mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLWithDelayBits::disable mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- ensures added
  after : final(self).wf()
- ensures added
  after : delay@.instance_id() == old(self).instance@.id()
- ensures added
  after : final(self).is_empty()
- ensures added
  after : delay@.key() == old(self).page_id()
- ensures added
  after : final(self).instance == old(self).instance

## verus-mimalloc/linked_list.rs::ThreadLLWithDelayBits::wf_emp_instance_ids mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list_insert_block.proof.rs::LL::insert_block mode=exec dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem_util.rs::Local::mem_chunk_good_preserved_by_commit_update mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem_util.rs::Local::set_range_to_not_used_preserves_mem_chunk_good mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::lemma_mem_chunk_good1_after_metadata_taken mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::AtomicHeapPtr::disable mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
- ensures added
  after : hop@.instance_id() == old(self).instance@.id()
- ensures added
  after : final(self).is_empty()
- ensures added
  after : hop@.key() == old(self).page_id@
- ensures added
  after : final(self).wf(old(self).instance@, old(self).page_id@)

## verus-mimalloc/types.rs::SegmentSharedAccess::wf mode=spec dep=False removed=False new=False persistent=False impacted_by=[]
- body modified
  before: { &&& is_segment_ptr(self.points_to.ptr(), segment_id) &&& (match self.points_to.opt_value() { MemContents::Init(segment_header) => segment_header.wf(mim_instance, segment_id), MemContents::Uninit => false, }) }
  after : { &&& is_segment_ptr(self.points_to.ptr(), segment_id) &&& self.points_to.ptr().addr() != 0 &&& (match self.points_to.opt_value() { MemContents::Init(segment_header) => segment_header.wf(mim_instance, segment_id), MemContents::Uninit => false, }) }

## verus-mimalloc/types.rs::free_fast_live_block_implies_page_used mode=proof dep=False removed=False new=True persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_fast.rs::heap_get_free_small_page mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_fast.rs::heap_malloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_fast.rs::heap_malloc_zero mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_generic.rs::heap_delayed_free_partial mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_generic.rs::page_extend_free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_generic.rs::page_free_collect mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_generic.rs::page_free_list_extend mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/alloc_generic.rs::page_thread_free_collect mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/arena.rs::arena_alloc_aligned mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::segment_commitx mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::segment_delayed_decommit mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::segment_ensure_committed mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/commit_segment.rs::segment_perhaps_decommit mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/dealloc_token.rs::MimDealloc::into_internal mode=proof dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::free_block mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::free_block_mt mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::free_delayed_block mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/free.rs::free_generic mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/init.rs::heap_init mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/init.rs::init_empty_page_ptr mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/init.rs::thread_data_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/layout.rs::SegmentPtr::ptr_segment mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/layout.rs::calculate_page_start mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/layout.rs::segment_page_start_from_slice mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::append mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::ghost_insert_block mode=proof dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::pop_block mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::LL::set_ghost_data mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLSimple::take mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLWithDelayBits::empty mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLWithDelayBits::enable mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLWithDelayBits::take mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/linked_list.rs::ThreadLLWithDelayBits::try_use_delayed_free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_alloc.rs::os_alloc_aligned mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_alloc.rs::os_alloc_aligned_offset mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_alloc.rs::os_mem_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_alloc.rs::os_mem_alloc_aligned mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_alloc.rs::unix_mmap mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_alloc.rs::unix_mmapx mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_commit.rs::os_commit mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_commit.rs::os_commitx mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_commit.rs::os_decommit mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mmap_prot_none mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mmap_prot_read_write mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mprotect_prot_none mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem.rs::mprotect_prot_read_write mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem_util.rs::MemChunk::join mode=proof dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/os_mem_util.rs::MemChunk::split mode=proof dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_init mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_queue_enqueue_from mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_queue_of mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_retire mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_to_full mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_try_use_delayed_free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/page.rs::page_unfull mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/queues.rs::heap_queue_first_update mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/queues.rs::page_queue_push mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/queues.rs::page_queue_push_back mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/queues.rs::page_queue_remove mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_os_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_page_clear mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_page_free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_reclaim_or_alloc mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_slice_split mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_span_allocate mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/segment.rs::segment_span_free mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

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

## verus-mimalloc/types.rs::PagePtr::get_heap mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

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

## verus-mimalloc/types.rs::SegmentPtr::is_abandoned mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::SegmentPtr::is_kind_huge mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::TldPtr::get_mut mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::TldPtr::get_ref mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']

## verus-mimalloc/types.rs::TldPtr::get_segments_count mode=exec dep=False removed=False new=False persistent=False impacted_by=['wf']
