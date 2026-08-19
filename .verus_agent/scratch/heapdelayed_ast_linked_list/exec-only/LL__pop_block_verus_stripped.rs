    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
        
    {
        
        
        
        
        let tracked (mut points_to_node, points_to_raw, block, is_exposed) = self.perms.borrow_mut().tracked_remove(pop_idx);

        let ptr: *mut Node = with_exposed_provenance(self.first.addr(), Tracked(is_exposed));
        
        let node = ptr_mut_read(ptr, Tracked(&mut points_to_node));
        
        self.first = node.ptr;

        
        let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
        let ptru = ptr as *mut u8;

        

        return (ptru, Tracked(points_to_raw), Tracked(block))
    }
