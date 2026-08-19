fn heap_delayed_free_partial(heap: HeapPtr, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    requires
        old(local).wf(),
        heap.wf(),
        heap.is_in(*old(local)),
    ensures
        final(local).wf(),
        final(local).inst() == old(local).inst(),
        forall |heap0: HeapPtr| heap0.is_in(*old(local)) ==> heap0.is_in(*final(local)),
{
    proof {
        reveal(Local::wf);
        reveal(Local::wf_main);
        assert(local.wf_basic());
        assert(local.thread_token.value().heap.shared_access.points_to.value().thread_delayed_free.wf());
        assert(local.thread_token.value().heap.shared_access.points_to.value().thread_delayed_free.instance@.id() == local.instance.id());
        assert(local.thread_token.value().heap.shared_access.points_to.value().thread_delayed_free.heap_id == local.heap_id);
    }
    let mut ll = heap.get_ref(Tracked(&*local)).thread_delayed_free.take();
    let mut all_freed = true;
    while !ll.is_empty()
        invariant
            local.wf(),
            heap.wf(), heap.is_in(*local),
            ll.wf(), ll.no_duplicate_keys(),
            local.inst() == old(local).inst(),
            forall |heap0: HeapPtr| heap0.is_in(*old(local)) ==> heap0.is_in(*local),
            ll.instance().id() == local.instance.id(),
            ll.heap_id() == Some(heap.heap_id@)
    {
        let (ptr, Tracked(perm), Tracked(block)) = ll.pop_block();
        let tracked dealloc_inner = MimDeallocInner {
            mim_instance: local.instance.clone(),
            mim_block: block,
            ptr: ptr,
        };
        proof {
            reveal(MimDeallocInner::wf);
            reveal(valid_block_token);
            assert(dealloc_inner.mim_instance == local.instance);
            assert(dealloc_inner.mim_block.instance_id() == local.instance.id());
            assert(dealloc_inner.mim_block.value().heap_id == Some(local.heap_id));
            assert(dealloc_inner.ptr == ptr);
            assert(is_block_ptr(ptr, dealloc_inner.block_id()));
            local.instance.block_in_heap_has_valid_page(
                local.thread_id,
                dealloc_inner.block_id(),
                &local.thread_token,
                &dealloc_inner.mim_block,
            );
            local.instance.get_block_properties(
                local.thread_id,
                dealloc_inner.block_id(),
                &local.thread_token,
                &dealloc_inner.mim_block,
            );
            assert(local.thread_token.value().pages.dom().contains(dealloc_inner.block_id().page_id));
            assert(local.pages.dom().contains(dealloc_inner.block_id().page_id));
            assert(local.thread_token.value().segments.dom().contains(dealloc_inner.block_id().page_id.segment_id));
            assert(local.segments.dom().contains(dealloc_inner.block_id().page_id.segment_id));
            assert(local.pages[dealloc_inner.block_id().page_id].wf(
                dealloc_inner.block_id().page_id,
                local.thread_token.value().pages[dealloc_inner.block_id().page_id],
                local.instance));
            assert(local.segments[dealloc_inner.block_id().page_id.segment_id].wf(
                dealloc_inner.block_id().page_id.segment_id,
                local.thread_token.value().segments[dealloc_inner.block_id().page_id.segment_id],
                local.instance));
            assert(valid_block_token(dealloc_inner.mim_block, dealloc_inner.mim_instance));
            assert(dealloc_inner.wf());
        }
        let (success, Tracked(p_opt), Tracked(d_opt)) =
                crate::free::free_delayed_block(ptr, Tracked(perm),
                    Tracked(dealloc_inner), Tracked(&mut *local));
        if !success {
            all_freed = false;
            let tracked perm = p_opt.tracked_unwrap();
            let tracked dealloc = d_opt.tracked_unwrap();
            let tracked block = dealloc.mim_block;

            heap.get_ref(Tracked(&*local)).thread_delayed_free
                .atomic_insert_block(ptr as *mut Node, Tracked(perm), Tracked(block));
        }
    }
    return all_freed;
}
