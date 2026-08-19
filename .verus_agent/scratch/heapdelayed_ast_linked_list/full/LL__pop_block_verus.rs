    pub fn pop_block(&mut self) -> (x: (*mut u8, Tracked<PointsToRaw>, Tracked<Mim::block>))
        requires
            old(self).wf(),
            old(self).no_duplicate_keys(),
            old(self).first_addr() != 0,
        ensures
            final(self).wf(),
            final(self).no_duplicate_keys(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            x.1@.is_range(x.0 as int, x.2@.key().block_size as int),
            x.1@.provenance() == x.0@.provenance,
            x.2@.instance_id() == old(self).instance().id(),
            match old(self).heap_id() {
                Some(heap_id) => x.2@.value().heap_id == Some(heap_id),
                None => true,
            },
            is_block_ptr(x.0, x.2@.key()),
    {
        let ghost old_data = self.data@;
        let ghost old_len = self.data@.len;
        let ghost pop_idx = (old_len - 1) as nat;
        proof {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::block_ids);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(LL::first_addr);
            reveal(LL::no_duplicate_keys);
            if old_len == 0 {
                assert(self.next_ptr(self.data@.len) == core::ptr::null_mut::<Node>());
                assert(self.first.addr() == 0);
                assert(false);
            }
            assert(0 <= pop_idx < old_len);
            assert(self.valid_node(pop_idx, self.next_ptr(pop_idx)));
            assert(self.perms@.dom().contains(pop_idx));
            assert(self.perms@[pop_idx].0.ptr().addr() == self.first.addr());
            assert(self.perms@[pop_idx].0.is_init());
            assert(self.data@.block_ids.contains(self.perms@[pop_idx].2.key()));
        }
        let tracked (mut points_to_node, points_to_raw, block, is_exposed) = self.perms.borrow_mut().tracked_remove(pop_idx);

        let ptr: *mut Node = with_exposed_provenance(self.first.addr(), Tracked(is_exposed));
        proof {
            assert(block.key() == old(self).perms@[pop_idx].2.key());
            assert(points_to_node.ptr().addr() == old(self).first.addr());
            assert(points_to_node.is_init());
            assert(points_to_raw.is_range(
                points_to_node.ptr().addr() + size_of::<Node>(),
                block.key().block_size - size_of::<Node>()));
            assert(points_to_raw.provenance() == points_to_node.ptr()@.provenance);
            assert(is_exposed.provenance() == points_to_raw.provenance());
            assert(ptr.addr() == points_to_node.ptr().addr());
            assert(ptr@.provenance == points_to_node.ptr()@.provenance);
            assert(ptr == points_to_node.ptr());
        }
        let node = ptr_mut_read(ptr, Tracked(&mut points_to_node));
        proof {
            assert(node.ptr.addr() == old(self).next_ptr(pop_idx).addr());
        }
        self.first = node.ptr;

        proof {
            assert(points_to_node.ptr() == ptr);
        }
        let tracked points_to_raw = points_to_node.into_raw().join(points_to_raw);
        let ptru = ptr as *mut u8;

        proof {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::block_ids);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(LL::first_addr);
            reveal(LL::no_duplicate_keys);
            let ghost block_id = block.key();
            self.data = Ghost(LLData {
                fixed_page: old_data.fixed_page,
                block_size: old_data.block_size,
                page_id: old_data.page_id,
                heap_id: old_data.heap_id,
                instance: old_data.instance,
                len: pop_idx,
                block_ids: old_data.block_ids.remove(block_id),
                idx_bound: old_data.idx_bound,
            });
            assert(self.perms@.dom() =~= old(self).perms@.dom().remove(pop_idx));
            assert(self.next_ptr(self.data@.len).addr() == self.first.addr());
            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len by {
                assert(old(self).perms@.dom().contains(i));
                assert(i != pop_idx);
                assert(0 <= i < old_len);
                assert(i < pop_idx);
            }
            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
                if 0 <= i < self.data@.len {
                    assert(old(self).valid_node(i, old(self).next_ptr(i)));
                    assert(self.perms@[i] == old(self).perms@[i]);
                    assert(self.next_ptr(i) == old(self).next_ptr(i));
                    assert(self.valid_node(i, self.next_ptr(i)));
                }
            }
            assert(old_data.block_ids.contains(block_id));
            assert(self.data@.block_ids.len() == self.data@.len) by {
                vstd::set::lemma_set_remove_len(old_data.block_ids, block_id);
            }
            assert forall |i: nat| 0 <= i < self.data@.len implies
                self.data@.block_ids.contains(#[trigger] self.perms@[i].2.key()) by {
                assert(old(self).data@.block_ids.contains(old(self).perms@[i].2.key()));
                assert(self.perms@[i] == old(self).perms@[i]);
                assert(self.perms@[i].2.key() != block_id) by {
                    if self.perms@[i].2.key() == block_id {
                        assert(old(self).perms@[i].2.key() == old(self).perms@[pop_idx].2.key());
                        assert(i != pop_idx);
                        assert(old(self).no_duplicate_keys());
                        assert(false);
                    }
                }
            }
            assert forall |bid: BlockId| #[trigger] self.data@.block_ids.contains(bid) implies
                exists |i: nat| 0 <= i < self.data@.len && self.perms@[i].2.key() == bid by {
                assert(old_data.block_ids.contains(bid));
                assert(bid != block_id);
                let i = choose |i: nat| 0 <= i < old_len && old(self).perms@[i].2.key() == bid;
                assert(i != pop_idx) by {
                    if i == pop_idx {
                        assert(bid == block_id);
                        assert(false);
                    }
                }
                assert(i < pop_idx);
                assert(self.perms@[i] == old(self).perms@[i]);
            }
            assert forall |bid: BlockId| #[trigger] self.data@.block_ids.contains(bid) implies
                bid.page_id == self.data@.page_id && bid.block_size == self.data@.block_size by {
                assert(old_data.block_ids.contains(bid));
            }
            assert forall |bid1: BlockId, bid2: BlockId|
                #[trigger] self.data@.block_ids.contains(bid1)
                    && #[trigger] self.data@.block_ids.contains(bid2)
                    && bid1.page_id == bid2.page_id
                    && bid1.idx == bid2.idx implies bid1 == bid2 by {
                assert(old_data.block_ids.contains(bid1));
                assert(old_data.block_ids.contains(bid2));
            }
            assert forall |i: nat, j: nat|
                0 <= i < self.data@.len && 0 <= j < self.data@.len && i != j implies
                    self.perms@[i].2.key() != self.perms@[j].2.key() by {
                assert(old(self).no_duplicate_keys());
                assert(self.perms@[i] == old(self).perms@[i]);
                assert(self.perms@[j] == old(self).perms@[j]);
            }
            assert(self.no_duplicate_keys());
            assert(self.wf());
            assert(points_to_raw.is_range(ptru as int, block.key().block_size as int));
            assert(points_to_raw.provenance() == ptru@.provenance);
            assert(block.instance_id() == old(self).instance().id());
            match old(self).heap_id() {
                Some(heap_id) => assert(block.value().heap_id == Some(heap_id)),
                None => { },
            }
            assert(is_block_ptr(ptru, block.key()));
        }

        return (ptru, Tracked(points_to_raw), Tracked(block))
    }
