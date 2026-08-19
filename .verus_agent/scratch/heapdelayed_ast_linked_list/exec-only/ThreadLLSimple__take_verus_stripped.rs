    pub fn take(&self) -> (ll: LL)
        
    {
        let res = self.atomic.load();
        if res.addr() == 0 {
            
            return LL::new(Ghost(arbitrary()), Ghost(false),
                Ghost(self.instance@), Ghost(arbitrary()), Ghost(Some(self.heap_id@)));
        }

        let tracked ll: LL;
        let p = core::ptr::null_mut::<Node>();
        let res = atomic_with_ghost!(
            &self.atomic => swap(core::ptr::null_mut());
            ghost g => {
                ll = g.get();
                let mut data = ll.data@;
                data.len = 0;
                data.block_ids = Set::empty();
                data.idx_bound = 0;
                let tracked new_ll = LL {
                    first: p,
                    data: Ghost(data),
                    perms: Tracked(Map::tracked_empty()),
                };
                new_ll.empty_fields_wf();
                g = Tracked(new_ll);
            }
        );
        let new_ll = LL {
            first: res,
            data: Ghost(ll.data@),
            perms: Tracked(ll.perms.get()),
        };
        

        new_ll
    }
