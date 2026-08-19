## ThreadLLSimple::empty (exec-only): MISMATCH

--- source
+++ verus
@@ -1,9 +1,10 @@
     pub fn empty(Ghost(instance): Ghost<Mim::Instance>, Ghost(heap_id): Ghost<HeapId>) -> (s: Self)
+        
     {
         let p: *mut Node = core::ptr::null_mut();
         Self {
             instance: Ghost(instance),
             heap_id: Ghost(heap_id),
-            atomic: AtomicPtr::new(Ghost((Ghost(instance), Ghost(heap_id))), core::ptr::null_mut(), Tracked(Tracked(LL { first: p, data: Ghost(LLData { fixed_page: false, block_size: arbitrary(), page_id: arbitrary(), instance, len: 0, heap_id: Some(heap_id), }), perms: Tracked(Map::tracked_empty()), })),),
+            atomic: AtomicPtr::new(Ghost((Ghost(instance), Ghost(heap_id))), core::ptr::null_mut(), Tracked(Tracked(LL { first: p, data: Ghost(LLData { fixed_page: false, block_size: arbitrary(), page_id: arbitrary(), instance, len: 0, heap_id: Some(heap_id), block_ids: Set::empty(), idx_bound: 0, }), perms: Tracked(Map::tracked_empty()), })),),
         }
     }
