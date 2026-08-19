fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
{
    let ghost page_id = page_ptr.page_id@;
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost n_blocks = n_slices * SLICE_SIZE / block_size as int;
    let ghost range = page_id.range_from(0, n_slices as int);

    let ghost new_page_state_map = Map::new(
            range,
            |pid: PageId| PageState {
                offset: pid.idx - page_id.idx,
                block_size: block_size as nat,
                num_blocks: 0,
                shared_access: arbitrary(),
                is_enabled: false,
            });

    

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
        //assert(page.xheap.wf(local.instance, page_ptr.page_id@));
    });

    unused_page_get_mut_inner!(page_ptr, local, inner => {

        inner.xblock_size = block_size as u32;
        let start_offs = calculate_start_offset(block_size);
        //proof {
        //    assert(count * SLICE_SIZE as u32 >= start_offs);
        //}
        let page_size = count * SLICE_SIZE as u32 - start_offs;
        inner.reserved = (page_size / block_size as u32) as u16;

        inner.free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));
        inner.local_free.set_ghost_data(
            Ghost(page_id), Ghost(true), Ghost(local.instance), Ghost(block_size as nat), Ghost(None));

        /*assert(inner.capacity == 0);
        assert(inner.free.wf());
        assert(inner.local_free.wf());
        assert(inner.free.block_size() == block_size);
        assert(inner.local_free.block_size() == block_size);
        assert(inner.free.len() == 0);
        assert(inner.local_free.len() == 0);
        assert(inner.free.fixed_page());
        assert(inner.local_free.fixed_page());
        assert(inner.free.page_id() == page_id);
        assert(inner.local_free.page_id() == page_id);
        assert(inner.free.instance() == local.instance);
        assert(inner.local_free.instance() == local.instance);
        assert(inner.used == 0);

        assert(inner.reserved == page_size as int / block_size as int);*/

    });


    //assert(local.is_used_primary(page_ptr.page_id@));
    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local))
}
