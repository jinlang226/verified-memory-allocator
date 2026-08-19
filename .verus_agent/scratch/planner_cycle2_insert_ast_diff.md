## LL::insert_block (exec-only): MISMATCH

--- source
+++ verus
@@ -1,11 +1,25 @@
     pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
+        
     {
-        let Tracked(mut mem1) = Tracked::<PointsTo<Node>>::assume_new();
+        
+        
+        
+
+        
+
+        let tracked (points_to_node_raw, points_to_padding) =
+            points_to_raw.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));
+
+        
+
         vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$
 
         let ptr = ptr as *mut Node;
-        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
+        
+        let tracked mut points_to_node = points_to_node_raw.into_typed::<Node>(ptr.addr());
+        ptr_mut_write(ptr, Tracked(&mut points_to_node), Node { ptr: self.first });
         self.first = ptr;
         let Tracked(is_exposed) = expose_provenance(ptr);
 
+        
     }
