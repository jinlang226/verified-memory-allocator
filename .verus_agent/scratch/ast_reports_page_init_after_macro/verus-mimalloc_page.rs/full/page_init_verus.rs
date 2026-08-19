fn page_init(heap_ptr: HeapPtr, page_ptr: PagePtr, block_size: usize, tld_ptr: TldPtr, Tracked(local): Tracked<&mut Local>, Ghost(pq): Ghost<int>)
    requires
        old(local).wf_main_for_page_access(),
        old(local).mem_chunk_good(page_ptr.page_id@.segment_id),
        heap_ptr.wf(),
        heap_ptr.is_in(*old(local)),
        page_ptr.wf(),
        page_ptr.is_in(*old(local)),
        page_ptr.is_in_unused(*old(local)),
        old(local).page_organization.popped == Popped::Ready(page_ptr.page_id@, true),
        valid_bin_idx(pq),
        block_size > 0,
        block_size as int == size_of_bin(pq),
        pq == smallest_bin_fitting_size(block_size as int),
        block_size as int <= MEDIUM_OBJ_SIZE_MAX,
        0 <= page_init_reserved(*old(local), page_ptr.page_id@, block_size),
        page_init_reserved(*old(local), page_ptr.page_id@, block_size) <= u16::MAX as int,
        old(local).segments[page_ptr.page_id@.segment_id].mem.pointsto_has_range(
            block_start_at(page_ptr.page_id@, block_size as int, 0),
            page_init_reserved(*old(local), page_ptr.page_id@, block_size) * block_size as int),
        block_start_at(page_ptr.page_id@, block_size as int,
            page_init_reserved(*old(local), page_ptr.page_id@, block_size))
            <= segment_start(page_ptr.page_id@.segment_id) + SEGMENT_SIZE,
        forall |idx: nat| (idx as int) < page_init_reserved(*old(local), page_ptr.page_id@, block_size) ==>
            page_ptr.page_id@.range_from(0, old(local).page_organization.pages[page_ptr.page_id@].count.unwrap() as int).contains(
                PageId {
                    segment_id: page_ptr.page_id@.segment_id,
                    idx: BlockId::get_slice_idx(page_ptr.page_id@, idx, block_size as nat),
                }),
    ensures
        common_preserves(*old(local), *final(local)),
{
    let ghost page_id = page_ptr.page_id@;
    let ghost n_slices = local.page_organization.pages[page_id].count.unwrap();
    let ghost reserved_blocks = page_init_reserved(*old(local), page_id, block_size);
    let ghost range = page_id.range_from(0, n_slices as int);

    proof! {
        reveal(Local::wf_main_for_page_access);
        reveal(Local::page_organization_valid);
        local.page_organization.ready_popped_range_facts();
        assert(local.unused_pages.dom().contains(page_id));
        assert(local.thread_token.value().segments.dom().contains(page_id.segment_id));
        assert(local.thread_token.value().segments[page_id.segment_id].is_enabled);
        assert(!local.thread_token.value().pages.dom().contains(page_id));
        assert(local.thread_token.value().heap_id == local.heap_id);
    }

    let ghost new_page_state_map = Map::new(
            range,
            |pid: PageId| PageState {
                offset: pid.idx - page_id.idx,
                block_size: block_size as nat,
                num_blocks: 0,
                shared_access: arbitrary(),
                is_enabled: false,
            });

    proof! {
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies pid.segment_id == page_id.segment_id
                && page_id.idx <= pid.idx < page_id.idx + n_slices by {
            assert(range.contains(pid));
        };
        assert forall |pid: PageId| pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + n_slices
            implies #[trigger] new_page_state_map.dom().contains(pid) by {
            assert(range.contains(pid));
        };
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies new_page_state_map[pid].offset + page_id.idx == pid.idx by {
        };
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies !new_page_state_map[pid].is_enabled by {
        };
        assert forall |pid: PageId| #[trigger] new_page_state_map.dom().contains(pid)
            implies new_page_state_map[pid].num_blocks == 0 by {
        };
        assert(new_page_state_map.dom().contains(page_id));
        assert(new_page_state_map[page_id].block_size == block_size as nat);
        assert(new_page_state_map.dom().disjoint(local.thread_token.value().pages.dom())) by {
            assert forall |pid: PageId| new_page_state_map.dom().contains(pid)
                implies !local.thread_token.value().pages.dom().contains(pid) by {
                assert(local.page_organization.pages.dom().contains(pid));
                assert(!local.page_organization.pages[pid].is_used);
                assert(local.unused_pages.dom().contains(pid));
            };
        };
    }

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

    let ghost local_before_inner = *local;
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

    proof! {
        assert(local.pages[page_id].inner.value().capacity == 0);
        assert(local.pages[page_id].inner.value().used == 0);
        assert(local.pages[page_id].inner.value().xblock_size == block_size as u32);
        assert(local.pages[page_id].inner.value().free.wf());
        assert(local.pages[page_id].inner.value().local_free.wf());
        assert(local.pages[page_id].inner.value().free.len() == 0);
        assert(local.pages[page_id].inner.value().local_free.len() == 0);
        assert(local.pages[page_id].inner.value().free.fixed_page());
        assert(local.pages[page_id].inner.value().local_free.fixed_page());
        assert(local.pages[page_id].inner.value().free.page_id() == page_id);
        assert(local.pages[page_id].inner.value().local_free.page_id() == page_id);
        assert(local.pages[page_id].inner.value().free.block_size() == block_size as nat);
        assert(local.pages[page_id].inner.value().local_free.block_size() == block_size as nat);
        assert(local.pages[page_id].inner.value().free.instance() == local.instance);
        assert(local.pages[page_id].inner.value().local_free.instance() == local.instance);
    }

    let ghost page_header_kind = PageHeaderKind::Normal(pq, block_size as int);
    proof! {
        local.page_organization = PageOrg::take_step::set_range_to_used(
            local.page_organization,
            page_header_kind);
    }

    let ghost enabled_page_state_map = Map::new(
        range,
        |pid: PageId| PageState {
            is_enabled: true,
            shared_access: local.unused_pages[pid],
            .. new_page_state_map[pid]
        });
    let ghost psa_map = Map::new(range, |pid: PageId| local.unused_pages[pid]);

    proof! {
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies pid.segment_id == page_id.segment_id
                && page_id.idx <= pid.idx < page_id.idx + n_slices by {
            assert(range.contains(pid));
        };
        assert forall |pid: PageId| pid.segment_id == page_id.segment_id
            && page_id.idx <= pid.idx < page_id.idx + n_slices
            implies #[trigger] enabled_page_state_map.dom().contains(pid) by {
            assert(range.contains(pid));
        };
        assert(enabled_page_state_map.dom() =~= psa_map.dom());
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies psa_map[pid] == enabled_page_state_map[pid].shared_access by {
        };
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies enabled_page_state_map[pid].offset + page_id.idx == pid.idx by {
        };
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies thread_token.value().pages.dom().contains(pid)
                && !thread_token.value().pages[pid].is_enabled by {
            assert(new_page_state_map.dom().contains(pid));
        };
        assert forall |pid: PageId| #[trigger] enabled_page_state_map.dom().contains(pid)
            implies enabled_page_state_map[pid] == PageState {
                is_enabled: true,
                shared_access: psa_map[pid],
                .. thread_token.value().pages[pid]
            } by {
            assert(new_page_state_map.dom().contains(pid));
        };
    }

    let ghost unused_before_enable = local.unused_pages;
    proof! {
        assert(local.unused_pages.dom() == local_before_inner.unused_pages.dom());
        assert(local_before_inner.page_organization.popped == Popped::Ready(page_id, true));
        local_before_inner.page_organization.ready_popped_range_facts();
        assert forall |pid: PageId| #[trigger] range.contains(pid) implies
            local.unused_pages.dom().contains(pid)
        by {
            assert(local_before_inner.page_organization.pages.dom().contains(pid));
            assert(!local_before_inner.page_organization.pages[pid].is_used);
            assert(local_before_inner.unused_pages.dom().contains(pid));
        };
        assert(range.subset_of(local.unused_pages.dom()));
    }
    let tracked page_shared_access = local.unused_pages.tracked_remove_keys(range);
    proof! {
        assert(page_shared_access == unused_before_enable.restrict(range));
        assert(psa_map == unused_before_enable.restrict(range)) by {
            assert(psa_map.dom() =~= range);
            assert forall |pid: PageId| #[trigger] psa_map.dom().contains(pid) implies
                psa_map[pid] == unused_before_enable.restrict(range)[pid]
            by {
                assert(range.contains(pid));
            };
            assert forall |pid: PageId| #[trigger] unused_before_enable.restrict(range).dom().contains(pid) implies
                unused_before_enable.restrict(range)[pid] == psa_map[pid]
            by {
                assert(range.contains(pid));
            };
        };
        assert(page_shared_access == psa_map);
    }
    let tracked thread_token = local.instance.page_enable(
        local.thread_id,
        page_id,
        n_slices as nat,
        enabled_page_state_map,
        psa_map,
        thread_token,
        page_shared_access,
    );
    proof! {
        local.thread_token = thread_token;
        local.psa = local.psa.union_prefer_right(psa_map);
    }

    proof! {
        assert(local.page_organization.popped == Popped::Used(page_id, true));
        assert(local.page_organization.invariant());
        assert(page_organization_queues_match(
            local.page_organization.unused_dlist_headers,
            local.tld.value().segments.span_queue_headers@));
        assert(page_organization_used_queues_match(
            local.page_organization.used_dlist_headers,
            local.heap.pages.value()@));
        assert(page_organization_segments_match(local.page_organization.segments, local.segments));
        assert(page_organization_pages_match(
            local.page_organization.pages,
            local.pages,
            local.psa,
            local.page_organization.popped));
        assert forall |pid: PageId| #[trigger] local.page_organization.pages.dom().contains(pid) implies
            (!local.page_organization.pages[pid].is_used <==> local.unused_pages.dom().contains(pid))
        by {
            if range.contains(pid) {
                assert(!local.unused_pages.dom().contains(pid));
                assert(local.page_organization.pages[pid].is_used);
            }
        };
        assert forall |pid: PageId| (#[trigger] local.unused_pages.dom().contains(pid)) implies
            local.page_organization.pages.dom().contains(pid)
        by { };
        assert forall |pid: PageId| #[trigger] local.unused_pages.dom().contains(pid) implies
            local.unused_pages[pid] == local.psa[pid]
        by { };
        assert forall |pid: PageId| #[trigger] local.thread_token.value().pages.dom().contains(pid) implies
            local.thread_token.value().pages[pid].shared_access == local.psa[pid]
        by {
            if range.contains(pid) {
                assert(psa_map.dom().contains(pid));
                assert(local.thread_token.value().pages[pid].shared_access == psa_map[pid]);
            }
        };
        assert(local.page_organization_valid());
        assert(local.thread_token.value().pages.dom().subset_of(local.pages.dom()));
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.thread_token.value().pages.dom().contains(pid) ==>
                local.pages.index(pid).wf(pid, local.thread_token.value().pages.index(pid), local.instance)
        by {
            if range.contains(pid) {
                if pid == page_id {
                    let page_state = local.thread_token.value().pages[pid];
                    let page_inner = local.pages[pid].inner.value();
                    reveal(PageLocalAccess::wf);
                    reveal(PageInner::wf);
                    reveal(Page::wf);
                    assert(page_state.offset == 0);
                    assert(page_state.block_size == block_size as nat);
                    assert(page_state.num_blocks == 0);
                    assert(page_state.is_enabled);
                    assert(page_state.shared_access == local.psa[pid]);
                    assert(local.psa[pid] == psa_map[pid]);
                    assert(page_inner.capacity == 0);
                    assert(page_inner.used == 0);
                    assert(page_inner.xblock_size == block_size as u32);
                    assert(page_inner.free.wf());
                    assert(page_inner.local_free.wf());
                    assert(page_inner.free.len() == 0);
                    assert(page_inner.local_free.len() == 0);
                    assert(page_inner.free.fixed_page());
                    assert(page_inner.local_free.fixed_page());
                    assert(page_inner.free.page_id() == pid);
                    assert(page_inner.local_free.page_id() == pid);
                    assert(page_inner.free.block_size() == page_state.block_size);
                    assert(page_inner.local_free.block_size() == page_state.block_size);
                    assert(page_inner.free.instance() == local.instance);
                    assert(page_inner.local_free.instance() == local.instance);
                    assert(page_inner.capacity == page_state.num_blocks);
                    assert(page_inner.used + page_inner.free.len() + page_inner.local_free.len() == page_state.num_blocks);
                    assert(page_inner.xblock_size > 0);
                    assert(page_inner.wf(pid, page_state, local.instance));
                    assert(page_state.shared_access.wf(pid, page_state.block_size, local.instance));
                    assert(page_state.shared_access.points_to.value().count.id() == local.pages[pid].count.id());
                    assert(page_state.shared_access.points_to.value().inner.id() == local.pages[pid].inner.id());
                    assert(page_state.shared_access.points_to.value().prev.id() == local.pages[pid].prev.id());
                    assert(page_state.shared_access.points_to.value().next.id() == local.pages[pid].next.id());
                    assert(page_state.shared_access.points_to.is_init());
                    assert(local.page_count(pid) == count as int);
                    assert(page_inner.reserved as int == reserved_blocks);
                    assert(page_state.block_size as int == block_size as int);
                    reveal(page_init_reserved);
                    let ghost total = n_slices * (SLICE_SIZE as int) - start_offset(block_size as int);
                    assert(reserved_blocks == total / block_size as int);
                    lemma_fundamental_div_mod(total, block_size as int);
                    assert(0 <= total % block_size as int);
                    assert(reserved_blocks * block_size as int <= total) by(nonlinear_arith)
                        requires
                            reserved_blocks == total / block_size as int,
                            total == (total / block_size as int) * (block_size as int) + total % block_size as int,
                            0 <= total % block_size as int;
                    assert(wf_reserved(page_state.block_size as int, page_inner.reserved as int, local.page_count(pid))) by(nonlinear_arith)
                        requires
                            page_state.block_size as int == block_size as int,
                            page_inner.reserved as int == reserved_blocks,
                            local.page_count(pid) == n_slices,
                            reserved_blocks * block_size as int <= total,
                            total == n_slices * (SLICE_SIZE as int) - start_offset(block_size as int);
                    assert(local.pages[pid].wf(pid, page_state, local.instance));
                } else {
                    assert(local.pages[pid] == local_before_inner.pages[pid]);
                }
            }
        };
        assert forall |pid: PageId| #[trigger] local.pages.dom().contains(pid) implies
            local.unused_pages.dom().contains(pid) ==>
                local.pages.index(pid).wf_unused(pid, local.unused_pages[pid], local.page_organization.popped, local.instance)
        by {
            assert(local_before_inner.pages[pid] == local.pages[pid] || pid == page_id);
        };
        assert forall |sid: SegmentId| #[trigger] local.segments.dom().contains(sid) implies
            local.segments[sid].wf(sid, local.thread_token.value().segments.index(sid), local.instance)
        by { };
        assert(local.wf_main_for_page_access());
    }

    let ghost local_before_extend = *local;
    proof! {
        assert(common_preserves(*old(local), local_before_extend));
    }
    crate::alloc_generic::page_extend_free(page_ptr, Tracked(&mut *local));
    proof! {
        assert(common_preserves(local_before_extend, *local));
        assert(common_preserves(*old(local), *local));
    }
}
