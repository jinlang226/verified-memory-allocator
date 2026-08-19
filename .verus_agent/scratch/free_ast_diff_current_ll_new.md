## LL::new (exec-only): MISMATCH

--- source
+++ verus
@@ -4,11 +4,13 @@
         Ghost(block_size): Ghost<nat>,
         Ghost(heap_id): Ghost<Option<HeapId>>,
     ) -> (ll: LL)
+        
     {
+        
         LL {
             first: core::ptr::null_mut(),
             data: Ghost(LLData {
-                fixed_page, block_size, page_id, instance, len: 0, heap_id,
+                fixed_page, block_size, page_id, instance, len: 0, heap_id, block_ids: Set::empty(), idx_bound: 0,
             }),
             perms: Tracked(Map::tracked_empty()),
         }
