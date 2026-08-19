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
@@ -36,10 +26,17 @@
 
     // Determine if this operation is thread local or not
 
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
@@ -48,11 +45,20 @@
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
+    
     let is_local = thread_id.thread_id == segment_thread_id_u64;
 
     // Calculate the pointer to the PageHeader for the *slice* that this block is in.
@@ -91,39 +97,61 @@
     let page: &Page = page_ptr.borrow(Tracked(&page_shared_access.points_to));
     */
 
-    let ghost page_id = dealloc.block_id().page_id;
+    
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
+        
+
+        
+        
+        
+        
 
         if likely(page.get_inner_ref(Tracked(&*local)).not_full_nor_aligned()) {
+            
+            
             let used;
             page_get_mut_inner!(page, local, page_inner => {
                 let tracked mim_block = dealloc.mim_block;
 
-                //proof {
-                    //assert(mim_block.key().page_id == page_inner.free.page_id());
-                    //assert(mim_block.key().block_size == page_inner.free.block_size());
-                //}
+                proof {
+                    assert(page_inner.used == used_before_free);
+                    assert(mim_block.key() == dealloc.block_id());
+                    assert(mim_block.key().page_id == page_inner.free.page_id());
+                    assert(mim_block.key().block_size == page_inner.free.block_size());
+                    assert(mim_block.instance_id() == page_inner.free.instance().id());
+                }
 
                 page_inner.free.insert_block(ptr, Tracked(perm), Tracked(mim_block));
 
-                //assert(page_inner.used >= 1);
+                assert(page_inner.used >= 1);
 
                 used = page_inner.used - 1;
                 page_inner.used = used;
+
+                proof {
+                    assert(page_inner.used == used_before_free - 1);
+                    assert(page_inner.free.len() == free_len_before + 1);
+                    assert(page_inner.local_free.len() == local_free_len_before);
+                    assert(used_before_free + free_len_before + local_free_len_before == page_state_before.num_blocks);
+                    assert(page_inner.used + page_inner.free.len() + page_inner.local_free.len() == page_state_before.num_blocks) by(nonlinear_arith)
+                        requires
+                            page_inner.used == used_before_free - 1,
+                            page_inner.free.len() == free_len_before + 1,
+                            page_inner.local_free.len() == local_free_len_before,
+                            used_before_free + free_len_before + local_free_len_before == page_state_before.num_blocks,
+                            used_before_free >= 1;
+                    assert(page_inner.wf(page_id, page_state_before, local.instance));
+                }
             });
 
+            
 
             if unlikely(used == 0) {
                 crate::page::page_retire(page, Tracked(&mut *local));
