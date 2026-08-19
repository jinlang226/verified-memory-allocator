fn heap_delayed_free_partial(heap: HeapPtr, Tracked(local): Tracked<&mut Local>) -> (b: bool)
    
{
    
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
