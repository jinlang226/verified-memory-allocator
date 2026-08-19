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
        proof {
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
