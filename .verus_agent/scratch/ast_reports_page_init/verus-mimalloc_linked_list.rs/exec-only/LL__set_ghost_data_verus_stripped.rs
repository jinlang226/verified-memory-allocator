    pub fn set_ghost_data(
        &mut self,
        Ghost(page_id): Ghost<PageId>,
        Ghost(fixed_page): Ghost<bool>,
        Ghost(instance): Ghost<Mim::Instance>,
        Ghost(block_size): Ghost<nat>,
        Ghost(heap_id): Ghost<Option<HeapId>>,
    )
        
    {
        
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
