fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
    
{
    
    
    
    

    

    

    

    let count = page_ptr.get_count(Tracked(&*local));

    let tracked thread_token = local.take_thread_token();
    let tracked (
        Tracked(thread_token),
        Tracked(delay_token),
        Tracked(heap_of_page_token),
    ) = local.instance.create_page_mk_tokens(
            // params
            local.thread_id,
            page_id,
            n_slices as nat,
            block_size as nat,
            new_page_state_map,
            // input ghost state
            thread_token,
        );

    unused_page_get_mut!(page_ptr, local, page => {
        let tracked (Tracked(emp_inst), Tracked(emp_x), Tracked(emp_y)) = BoolAgree::Instance::initialize(false);
        let ghost g = (Ghost(local.instance), Ghost(page_ptr.page_id@), Tracked(emp_x), Tracked(emp_inst));
        page.xheap = AtomicHeapPtr {
            atomic: AtomicPtr::new(Ghost(g), heap_ptr.heap_ptr, Tracked((emp_y, Some(heap_of_page_token)))),
            instance: Ghost(local.instance), page_id: Ghost(page_ptr.page_id@), emp: Tracked(emp_x), emp_inst: Tracked(emp_inst), };
        page.xthread_free.enable(Ghost(block_size as nat), Ghost(page_ptr.page_id@),
            Tracked(local.instance.clone()), Tracked(delay_token));
    });

    
    unused_page_get_mut_inner!(page_ptr, local, inner => {

        inner.xblock_size = block_size as u32;
        let start_offs = calculate_start_offset(block_size);
        proof! {
            assert(count as int == n_slices);
            assert(1 <= n_slices <= SLICES_PER_SEGMENT);
            assert(start_offs as int == start_offset(block_size as int));
            lemma_start_offset_bounds(block_size as int);
            assert(SLICES_PER_SEGMENT as int == 512) by(compute_only);
            assert(SLICE_SIZE as u32 == 65536) by(compute_only);
            assert(MAX_ALIGN_GUARANTEE as int == 128) by(compute_only);
            assert(count <= 512) by(nonlinear_arith)
                requires count as int == n_slices, n_slices <= SLICES_PER_SEGMENT, SLICES_PER_SEGMENT as int == 512;
            assert(count >= 1) by(nonlinear_arith)
                requires count as int == n_slices, 1 <= n_slices;
            assert(count * SLICE_SIZE as u32 <= u32::MAX) by(bit_vector)
                requires count <= 512, SLICE_SIZE as u32 == 65536;
            assert(start_offs <= 384) by(nonlinear_arith)
                requires start_offs as int == start_offset(block_size as int),
                    start_offset(block_size as int) <= 3 * (MAX_ALIGN_GUARANTEE as int),
                    MAX_ALIGN_GUARANTEE as int == 128;
            assert(start_offs <= count * SLICE_SIZE as u32) by(bit_vector)
                requires count >= 1, start_offs <= 384, SLICE_SIZE as u32 == 65536;
        }
        let page_size = count * SLICE_SIZE as u32 - start_offs;
        proof! {
            assert(MEDIUM_OBJ_SIZE_MAX as int == 131072) by(compute_only);
            assert(block_size as int <= 131072);
            assert(131072 <= u32::MAX as int) by(compute_only);
            assert(block_size <= u32::MAX as usize) by(nonlinear_arith)
                requires block_size as int <= 131072, 131072 <= u32::MAX as int;
            assert(block_size as u32 > 0) by(bit_vector)
                requires block_size > 0, block_size <= u32::MAX as usize;
        }
        inner.reserved = (page_size / block_size as u32) as u16;
        proof! {
            reveal(page_init_reserved);
            let ghost total = n_slices * (SLICE_SIZE as int) - start_offset(block_size as int);
            assert(reserved_blocks == total / block_size as int);
            assert((count * SLICE_SIZE as u32) as int == count as int * (SLICE_SIZE as int)) by(bit_vector)
                requires
                    count <= 512,
                    SLICE_SIZE as u32 == 65536;
            assert(page_size as int == (count * SLICE_SIZE as u32) as int - start_offs as int) by(bit_vector)
                requires
                    page_size == count * SLICE_SIZE as u32 - start_offs,
                    start_offs <= count * SLICE_SIZE as u32;
            assert(page_size as int == count as int * (SLICE_SIZE as int) - start_offs as int) by(nonlinear_arith)
                requires
                    page_size as int == (count * SLICE_SIZE as u32) as int - start_offs as int,
                    (count * SLICE_SIZE as u32) as int == count as int * (SLICE_SIZE as int);
            assert(count as int * (SLICE_SIZE as int) == n_slices * (SLICE_SIZE as int)) by(nonlinear_arith)
                requires count as int == n_slices;
            assert(count as int * (SLICE_SIZE as int) - start_offs as int == total) by(nonlinear_arith)
                requires
                    count as int * (SLICE_SIZE as int) == n_slices * (SLICE_SIZE as int),
                    start_offs as int == start_offset(block_size as int),
                    total == n_slices * (SLICE_SIZE as int) - start_offset(block_size as int);
            assert(page_size as int == total);
            assert((block_size as u32) as int == block_size as int) by(bit_vector)
                requires block_size <= u32::MAX as usize;
            assert((page_size / block_size as u32) as int == reserved_blocks) by(nonlinear_arith)
                requires
                    page_size as int == total,
                    (block_size as u32) as int == block_size as int,
                    block_size as u32 > 0,
                    reserved_blocks == total / block_size as int;
            assert((page_size / block_size as u32) as int <= u16::MAX as int) by(nonlinear_arith)
                requires
                    (page_size / block_size as u32) as int == reserved_blocks,
                    reserved_blocks <= u16::MAX as int;
            assert((reserved_blocks as u16) as int == reserved_blocks);
            assert(inner.reserved == reserved_blocks as u16);
            assert(inner.reserved as int == reserved_blocks);
        }

        inner.free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
        inner.local_free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
    });

    

    
    

    
    

    

    
    
    let tracked page_shared_access = local.unused_pages.tracked_remove_keys(range);
    
    let tracked thread_token = local.instance.page_enable(
        local.thread_id,
        page_id,
        n_slices as nat,
        enabled_page_state_map,
        psa_map,
        thread_token,
        page_shared_access,
    );
    

    

    
    
    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local));
    
}
