## free (exec-only): MISMATCH

--- source
+++ verus
@@ -1,17 +1,7 @@
 pub fn free(ptr: *mut u8, Tracked(user_perm): Tracked<PointsToRaw>, Tracked(user_dealloc): Tracked<Option<MimDealloc>>, Tracked(local): Tracked<&mut Local>)
     // According to the Linux man pages, `ptr` is allowed to be NULL,
     // in which case no operation is performed.
-    requires
-        old(local).wf(),
-        ptr.addr() != 0 ==> user_dealloc.is_some(),
-        ptr.addr() != 0 ==> user_perm.is_range(ptr as int, user_dealloc.unwrap().size()),
-        ptr.addr() != 0 ==> user_perm.provenance() == ptr@.provenance,
-        ptr.addr() != 0 ==> ptr == user_dealloc.unwrap().ptr(),
-        ptr.addr() != 0 ==> old(local).inst() == user_dealloc.unwrap().inst()
-    ensures
-        final(local).wf(),
-        final(local).inst() == old(local).inst(),
-        forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local)),
+    
 {
     if ptr.addr() == 0 {
         return;
@@ -36,10 +26,18 @@
 
     // Determine if this operation is thread local or not
 
+    
+    
+    
+    
+    
+    
+
     let segment_thread_id_u64 = atomic_with_ghost!(
         &segment.thread_id => load();
         returning thread_id_u64;
         ghost g => {
+            loaded_segment_thread_id = g.value();
             if g.value() == local.thread_id {
                 local.instance.block_on_the_local_thread(
                     local.thread_token.key(),
@@ -48,12 +46,21 @@
                     &dealloc.mim_block,
                     &g,
                     );
+                assert(local.thread_token.value().pages.dom().contains(dealloc.block_id().page_id));
+                assert(local.thread_token.value().pages[dealloc.block_id().page_id].offset == 0);
+                assert(local.thread_token.value().pages[dealloc.block_id().page_id].block_size == dealloc.block_id().block_size);
+                assert(dealloc.block_id().idx < local.thread_token.value().pages[dealloc.block_id().page_id].num_blocks);
+                loaded_page_is_in_local = true;
+                loaded_page_is_primary = true;
+                loaded_page_block_size_matches = true;
+                loaded_block_idx_lt_num_blocks = true;
             }
         }
     );
 
     let (thread_id, Tracked(is_thread)) = crate::thread::thread_id();
     let is_local = thread_id.thread_id == segment_thread_id_u64;
+    
 
     // Calculate the pointer to the PageHeader for the *slice* that this block is in.
     // Remember this might not be the "main" PageHeader for this Page.
@@ -91,39 +98,310 @@
     let page: &Page = page_ptr.borrow(Tracked(&page_shared_access.points_to));
     */
 
-    let ghost page_id = dealloc.block_id().page_id;
     let page = PagePtr {
         page_ptr,
         page_id: Ghost(page_id),
     };
 
-
     // Case based on whether this is thread local or not
 
     if likely(is_local) {
-        //assert(local.pages.dom().contains(page_id));
-        //assert(page.is_in(*local));
-        //assert(page.wf());
-        //assert(local.is_used_primary(page_id));
-
+        
         if likely(page.get_inner_ref(Tracked(&*local)).not_full_nor_aligned()) {
+            
+            
             let used;
             page_get_mut_inner!(page, local, page_inner => {
-                let tracked mim_block = dealloc.mim_block;
-
-                //proof {
-                    //assert(mim_block.key().page_id == page_inner.free.page_id());
-                    //assert(mim_block.key().block_size == page_inner.free.block_size());
-                //}
+                let tracked MimDeallocInner { mim_instance: dealloc_mim_instance, mim_block: mut live_block, ptr: dealloc_ptr } = dealloc;
+                let ghost dealloc_block_id = live_block.key();
+                proof {
+                    reveal(PageInner::wf);
+                    assert(valid_block_token(live_block, dealloc_mim_instance));
+
+                    assert(local_before_inner.wf());
+                    assert(page_state_before == local_before_inner.thread_token.value().pages[page_id]);
+                    assert(local_before_inner.page_inner(page_id).used == page_inner.used);
+                    assert(local_before_inner.page_inner(page_id).free.len() == page_inner.free.len());
+                    assert(local_before_inner.page_inner(page_id).local_free.len() == page_inner.local_free.len());
+                    assert(page_inner.wf(page_id, page_state_before, local.instance));
+                    assert(page_inner.free.wf());
+                    assert(page_inner.local_free.wf());
+
+                    assert(dealloc_block_id.page_id == page_id);
+                    assert(dealloc_block_id.idx < page_state_before.num_blocks);
+                    assert(live_block.instance_id() == local.instance.id());
+
+                    if exists |block_id: BlockId| page_inner.free.block_ids().contains(block_id)
+                        && !(block_id.idx < page_state_before.num_blocks) {
+                        let bad_id = choose |block_id: BlockId| page_inner.free.block_ids().contains(block_id)
+                            && !(block_id.idx < page_state_before.num_blocks);
+                        page_inner.free.block_ids_contains_witness(bad_id);
+                        let i = choose |i: nat| i < page_inner.free.len()
+                            && page_inner.free.perms@.dom().contains(i)
+                            && page_inner.free.perms@[i].2.key() == bad_id;
+                        page_inner.free.entry_token_matches_metadata(i);
+                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
+                            page_inner.free.perms.borrow_mut().tracked_remove(i);
+                        assert(entry_block.key() == bad_id);
+                        assert(entry_block.instance_id() == local.instance.id());
+                        block_token_idx_lt_num_blocks(
+                            &local.instance,
+                            &local.thread_token,
+                            local.thread_id,
+                            &entry_block,
+                            page_state_before.num_blocks,
+                        );
+                        page_inner.free.perms.borrow_mut().tracked_insert(i, (
+                            entry_node,
+                            entry_raw,
+                            entry_block,
+                            entry_exposed,
+                        ));
+                        assert(false);
+                    }
+                    assert forall |block_id: BlockId| #[trigger] page_inner.free.block_ids().contains(block_id) implies
+                        block_id.idx < page_state_before.num_blocks by {
+                        if !(block_id.idx < page_state_before.num_blocks) {
+                            assert(exists |bad_id: BlockId| page_inner.free.block_ids().contains(bad_id)
+                                && !(bad_id.idx < page_state_before.num_blocks));
+                            assert(false);
+                        }
+                    };
+                    if exists |block_id: BlockId| page_inner.local_free.block_ids().contains(block_id)
+                        && !(block_id.idx < page_state_before.num_blocks) {
+                        let bad_id = choose |block_id: BlockId| page_inner.local_free.block_ids().contains(block_id)
+                            && !(block_id.idx < page_state_before.num_blocks);
+                        page_inner.local_free.block_ids_contains_witness(bad_id);
+                        let i = choose |i: nat| i < page_inner.local_free.len()
+                            && page_inner.local_free.perms@.dom().contains(i)
+                            && page_inner.local_free.perms@[i].2.key() == bad_id;
+                        page_inner.local_free.entry_token_matches_metadata(i);
+                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
+                            page_inner.local_free.perms.borrow_mut().tracked_remove(i);
+                        assert(entry_block.key() == bad_id);
+                        assert(entry_block.instance_id() == local.instance.id());
+                        block_token_idx_lt_num_blocks(
+                            &local.instance,
+                            &local.thread_token,
+                            local.thread_id,
+                            &entry_block,
+                            page_state_before.num_blocks,
+                        );
+                        page_inner.local_free.perms.borrow_mut().tracked_insert(i, (
+                            entry_node,
+                            entry_raw,
+                            entry_block,
+                            entry_exposed,
+                        ));
+                        assert(false);
+                    }
+                    assert forall |block_id: BlockId| #[trigger] page_inner.local_free.block_ids().contains(block_id) implies
+                        block_id.idx < page_state_before.num_blocks by {
+                        if !(block_id.idx < page_state_before.num_blocks) {
+                            assert(exists |bad_id: BlockId| page_inner.local_free.block_ids().contains(bad_id)
+                                && !(bad_id.idx < page_state_before.num_blocks));
+                            assert(false);
+                        }
+                    };
+
+                    if exists |block_id: BlockId| page_inner.free.block_ids().contains(block_id)
+                        && block_id.idx == dealloc_block_id.idx {
+                        let collision_id = choose |block_id: BlockId| page_inner.free.block_ids().contains(block_id)
+                            && block_id.idx == dealloc_block_id.idx;
+                        page_inner.free.block_ids_contains_witness(collision_id);
+                        let i = choose |i: nat| i < page_inner.free.len()
+                            && page_inner.free.perms@.dom().contains(i)
+                            && page_inner.free.perms@[i].2.key() == collision_id;
+                        page_inner.free.entry_token_matches_metadata(i);
+                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
+                            page_inner.free.perms.borrow_mut().tracked_remove(i);
+                        assert(entry_block.key() == collision_id);
+                        assert(entry_block.key().page_id == dealloc_block_id.page_id);
+                        assert(entry_block.key().idx == dealloc_block_id.idx);
+                        assert(entry_block.instance_id() == local.instance.id());
+                        let tracked (Tracked(entry_block), Tracked(returned_live_block)) =
+                            LL::owned_block_tokens_same_page_idx_impossible_retain(&local.instance, entry_block, live_block);
+                        page_inner.free.perms.borrow_mut().tracked_insert(i, (
+                            entry_node,
+                            entry_raw,
+                            entry_block,
+                            entry_exposed,
+                        ));
+                        live_block = returned_live_block;
+                        assert(false);
+                    }
+                    assert forall |block_id: BlockId| #[trigger] page_inner.free.block_ids().contains(block_id) implies
+                        block_id.idx != dealloc_block_id.idx by {
+                        if block_id.idx == dealloc_block_id.idx {
+                            assert(exists |collision_id: BlockId| page_inner.free.block_ids().contains(collision_id)
+                                && collision_id.idx == dealloc_block_id.idx);
+                            assert(false);
+                        }
+                    };
+                    assert(!page_inner.free.block_ids().contains(dealloc_block_id));
+
+                    if exists |block_id: BlockId| page_inner.local_free.block_ids().contains(block_id)
+                        && block_id.idx == dealloc_block_id.idx {
+                        let collision_id = choose |block_id: BlockId| page_inner.local_free.block_ids().contains(block_id)
+                            && block_id.idx == dealloc_block_id.idx;
+                        page_inner.local_free.block_ids_contains_witness(collision_id);
+                        let i = choose |i: nat| i < page_inner.local_free.len()
+                            && page_inner.local_free.perms@.dom().contains(i)
+                            && page_inner.local_free.perms@[i].2.key() == collision_id;
+                        page_inner.local_free.entry_token_matches_metadata(i);
+                        let tracked (entry_node, entry_raw, entry_block, entry_exposed) =
+                            page_inner.local_free.perms.borrow_mut().tracked_remove(i);
+                        assert(entry_block.key() == collision_id);
+                        assert(entry_block.key().page_id == dealloc_block_id.page_id);
+                        assert(entry_block.key().idx == dealloc_block_id.idx);
+                        assert(entry_block.instance_id() == local.instance.id());
+                        let tracked (Tracked(entry_block), Tracked(returned_live_block)) =
+                            LL::owned_block_tokens_same_page_idx_impossible_retain(&local.instance, entry_block, live_block);
+                        page_inner.local_free.perms.borrow_mut().tracked_insert(i, (
+                            entry_node,
+                            entry_raw,
+                            entry_block,
+                            entry_exposed,
+                        ));
+                        live_block = returned_live_block;
+                        assert(false);
+                    }
+                    assert forall |block_id: BlockId| #[trigger] page_inner.local_free.block_ids().contains(block_id) implies
+                        block_id.idx != dealloc_block_id.idx by {
+                        if block_id.idx == dealloc_block_id.idx {
+                            assert(exists |collision_id: BlockId| page_inner.local_free.block_ids().contains(collision_id)
+                                && collision_id.idx == dealloc_block_id.idx);
+                            assert(false);
+                        }
+                    };
+                    assert(!page_inner.local_free.block_ids().contains(dealloc_block_id));
+
+                    if exists |free_id: BlockId, local_id: BlockId|
+                        #[trigger] page_inner.free.block_ids().contains(free_id)
+                            && #[trigger] page_inner.local_free.block_ids().contains(local_id)
+                            && free_id.idx == local_id.idx {
+                        let free_id = choose |free_id: BlockId| exists |local_id: BlockId|
+                            #[trigger] page_inner.free.block_ids().contains(free_id)
+                                && #[trigger] page_inner.local_free.block_ids().contains(local_id)
+                                && free_id.idx == local_id.idx;
+                        let local_id = choose |local_id: BlockId|
+                            page_inner.free.block_ids().contains(free_id)
+                                && page_inner.local_free.block_ids().contains(local_id)
+                                && free_id.idx == local_id.idx;
+                        page_inner.free.block_ids_contains_witness(free_id);
+                        let i = choose |i: nat| i < page_inner.free.len()
+                            && page_inner.free.perms@.dom().contains(i)
+                            && page_inner.free.perms@[i].2.key() == free_id;
+                        page_inner.free.entry_token_matches_metadata(i);
+                        page_inner.local_free.block_ids_contains_witness(local_id);
+                        let j = choose |j: nat| j < page_inner.local_free.len()
+                            && page_inner.local_free.perms@.dom().contains(j)
+                            && page_inner.local_free.perms@[j].2.key() == local_id;
+                        page_inner.local_free.entry_token_matches_metadata(j);
+                        let tracked (free_node, free_raw, free_block, free_exposed) =
+                            page_inner.free.perms.borrow_mut().tracked_remove(i);
+                        let tracked (local_node, local_raw, local_block, local_exposed) =
+                            page_inner.local_free.perms.borrow_mut().tracked_remove(j);
+                        assert(free_block.key() == free_id);
+                        assert(local_block.key() == local_id);
+                        assert(free_block.key().page_id == local_block.key().page_id);
+                        assert(free_block.key().idx == local_block.key().idx);
+                        assert(free_block.instance_id() == local.instance.id());
+                        assert(local_block.instance_id() == local.instance.id());
+                        let tracked (Tracked(free_block), Tracked(local_block)) =
+                            LL::owned_block_tokens_same_page_idx_impossible_retain(&local.instance, free_block, local_block);
+                        page_inner.free.perms.borrow_mut().tracked_insert(i, (
+                            free_node,
+                            free_raw,
+                            free_block,
+                            free_exposed,
+                        ));
+                        page_inner.local_free.perms.borrow_mut().tracked_insert(j, (
+                            local_node,
+                            local_raw,
+                            local_block,
+                            local_exposed,
+                        ));
+                        assert(false);
+                    }
+                    assert forall |free_id: BlockId, local_id: BlockId|
+                        #[trigger] page_inner.free.block_ids().contains(free_id)
+                            && #[trigger] page_inner.local_free.block_ids().contains(local_id)
+                            && free_id.idx == local_id.idx implies false by {
+                        assert(exists |free_id0: BlockId, local_id0: BlockId|
+                            page_inner.free.block_ids().contains(free_id0)
+                                && page_inner.local_free.block_ids().contains(local_id0)
+                                && free_id0.idx == local_id0.idx);
+                        assert(false);
+                    };
+                    assert(page_inner.free.block_ids().disjoint(page_inner.local_free.block_ids())) by {
+                        if !page_inner.free.block_ids().disjoint(page_inner.local_free.block_ids()) {
+                            let block_id = choose |block_id: BlockId|
+                                page_inner.free.block_ids().contains(block_id)
+                                    && page_inner.local_free.block_ids().contains(block_id);
+                            assert(false);
+                        }
+                    };
+
+                    LL::two_lists_with_live_cardinality_gap(
+                        &page_inner.free,
+                        &page_inner.local_free,
+                        dealloc_block_id,
+                        page_state_before.num_blocks,
+                    );
+                    assert(local_before_inner.page_inner(page_id).free.len()
+                        + local_before_inner.page_inner(page_id).local_free.len()
+                        < page_state_before.num_blocks);
+                    live_block_implies_page_used(&live_block, local_before_inner);
+                    assert(page_inner.used >= 1);
+                }
+                let ghost used_before_free = page_inner.used;
+                let ghost free_len_before = page_inner.free.len();
+                let ghost local_free_len_before = page_inner.local_free.len();
+                let ghost local_free_block_ids_before = page_inner.local_free.block_ids();
+                let ghost freed_block_id = dealloc_block_id;
+                let tracked mim_block = live_block;
 
                 page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));
-
-                //assert(page_inner.used >= 1);
 
                 used = page_inner.used - 1;
                 page_inner.used = used;
+
+                proof {
+                    reveal(PageInner::wf);
+                    assert(page_inner.used == used_before_free - 1);
+                    assert(page_inner.free.len() == free_len_before + 1);
+                    assert(page_inner.local_free.len() == local_free_len_before);
+                    assert(page_inner.local_free.block_ids() == local_free_block_ids_before);
+                    assert(page_inner.free.block_ids().disjoint(page_inner.local_free.block_ids())) by {
+                        if !page_inner.free.block_ids().disjoint(page_inner.local_free.block_ids()) {
+                            let block_id = choose |block_id: BlockId|
+                                page_inner.free.block_ids().contains(block_id)
+                                    && page_inner.local_free.block_ids().contains(block_id);
+                            if block_id == freed_block_id {
+                                assert(!page_inner.local_free.block_ids().contains(freed_block_id));
+                            } else {
+                                assert(local_before_inner.page_inner(page_id).free.block_ids().contains(block_id));
+                                assert(local_before_inner.page_inner(page_id).local_free.block_ids().contains(block_id));
+                                assert(false);
+                            }
+                        }
+                    };
+                    assert(page_inner.used + page_inner.free.len() + page_inner.local_free.len()
+                        == page_state_before.num_blocks) by(nonlinear_arith)
+                        requires
+                            page_inner.used == used_before_free - 1,
+                            page_inner.free.len() == free_len_before + 1,
+                            page_inner.local_free.len() == local_free_len_before,
+                            used_before_free + free_len_before + local_free_len_before
+                                == page_state_before.num_blocks,
+                            used_before_free >= 1;
+                    assert(page_inner.wf(page_id, page_state_before, local.instance));
+                }
+
             });
 
+            
 
             if unlikely(used == 0) {
                 crate::page::page_retire(page, Tracked(&mut *local));
