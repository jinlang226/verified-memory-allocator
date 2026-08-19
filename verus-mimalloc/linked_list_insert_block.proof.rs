verus!{
impl LL {
    #[inline(always)]
    #[verus_verify]
    pub fn insert_block(&mut self, ptr: *mut u8, Tracked(points_to_raw): Tracked<PointsToRaw>, Tracked(block_token): Tracked<Mim::block>)
        requires
            old(self).wf(),
            old(self).fixed_page(),
            block_token.instance_id() == old(self).instance().id(),
            block_token.key().page_id == old(self).page_id(),
            block_token.key().block_size == old(self).block_size(),
            match old(self).heap_id() {
                Some(heap_id) => block_token.value().heap_id == Some(heap_id),
                None => true,
            },
            is_block_ptr(ptr, block_token.key()),
            points_to_raw.is_range(ptr as int, block_token.key().block_size as int),
            points_to_raw.provenance() == ptr@.provenance,
        ensures
            final(self).wf(),
            final(self).fixed_page() == old(self).fixed_page(),
            final(self).page_id() == old(self).page_id(),
            final(self).block_size() == old(self).block_size(),
            final(self).instance() == old(self).instance(),
            final(self).heap_id() == old(self).heap_id(),
            final(self).len() == old(self).len() + 1,
    {
        let ghost old_len = self.data@.len;
        let ghost old_first = self.first;
        let ghost old_data = self.data@;

        proof {
            reveal(LL::wf);
            reveal(LL::next_ptr);
            reveal(LL::valid_node);
            reveal(LL::len);
            reveal(LL::fixed_page);
            reveal(LL::page_id);
            reveal(LL::block_size);
            reveal(LL::instance);
            reveal(LL::heap_id);
            reveal(is_block_ptr1);
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            lemma_is_block_ptr_aligned_to_node(ptr, block_token.key());
            assert(block_token.key().block_size >= size_of::<Node>());
        }

        proof_decl! {
            let tracked (points_to_node_raw, points_to_padding) =
                points_to_raw.split(set_int_range(ptr as int, ptr as int + size_of::<Node>()));
        }

        proof {
            assert(points_to_padding.provenance() == ptr@.provenance);
            assert(points_to_padding.is_range(
                ptr as int + size_of::<Node>(),
                block_token.key().block_size as int - size_of::<Node>() as int));
        }

        vstd::layout::layout_for_type_is_valid::<Node>(); // $line_count$Proof$

        let ptr = ptr as *mut Node;
        proof {
            vstd::set_lib::lemma_int_range(ptr as int, ptr as int + size_of::<Node>());
            assert(points_to_node_raw.is_range(ptr as int, size_of::<Node>() as int));
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            assert(ptr.addr() as int == ptr as int);
            assert(size_of::<Node>() == 8);
            assert(align_of::<Node>() == 8);
            lemma_is_block_ptr_aligned_to_node(ptr as *mut u8, block_token.key());
            assert(ptr.addr() as int % align_of::<Node>() as int == 0);
        }
        proof_decl! {
            let tracked mut mem1 = points_to_node_raw.into_typed::<Node>(ptr.addr());
        }
        ptr_mut_write(ptr, Tracked(&mut mem1), Node { ptr: self.first });
        self.first = ptr;
        let Tracked(is_exposed) = expose_provenance(ptr);

        proof {
            self.perms.borrow_mut().tracked_insert(old_len, (
                mem1,
                points_to_padding,
                block_token,
                is_exposed,
            ));
            self.data = Ghost(LLData {
                fixed_page: old_data.fixed_page,
                block_size: old_data.block_size,
                page_id: old_data.page_id,
                heap_id: old_data.heap_id,
                instance: old_data.instance,
                len: old_len + 1,
                block_ids: old_data.block_ids.insert(block_token.key()),
                idx_bound: old_data.idx_bound,
            });

            assert(self.data@.len == old_len + 1);
            assert(self.perms@.dom() =~= old(self).perms@.dom().insert(old_len));
            assert forall |i: nat| self.perms@.dom().contains(i) implies 0 <= i < self.data@.len by {
                if i == old_len {
                } else {
                    assert(old(self).perms@.dom().contains(i));
                    assert(0 <= i < old_len);
                }
            }
            assert(self.next_ptr(self.data@.len).addr() == self.first.addr());
            assert forall |i: nat| #[trigger] self.valid_node(i, self.next_ptr(i)) by {
                if 0 <= i < self.data@.len {
                    if i == old_len {
                        assert(self.perms@.dom().contains(i));
                        assert(self.perms@[i].0.ptr() == self.first);
                        assert(self.perms@[i].0.is_init());
                        assert(self.perms@[i].0.value().ptr.addr() == old_first.addr());
                        assert(self.next_ptr(i).addr() == old_first.addr());
                        assert(self.perms@[i].0.value().ptr.addr() == self.next_ptr(i).addr());
                        assert(self.perms@[i].2.key().block_size - size_of::<Node>() >= 0);
                        assert(self.perms@[i].1.is_range(
                            self.perms@[i].0.ptr().addr() + size_of::<Node>(),
                            self.perms@[i].2.key().block_size - size_of::<Node>()));
                        assert(self.perms@[i].1.provenance() == self.perms@[i].0.ptr()@.provenance);
                        assert(self.perms@[i].3.provenance() == self.perms@[i].1.provenance());
                        assert(self.perms@[i].2.instance_id() == self.data@.instance.id());
                        assert(is_block_ptr(self.perms@[i].0.ptr() as *mut u8, self.perms@[i].2.key()));
                        assert(self.perms@[i].2.key().page_id == self.data@.page_id);
                        assert(self.perms@[i].2.key().block_size == self.data@.block_size);
                        assert(self.data@.heap_id.is_None() || self.perms@[i].2.value().heap_id == self.data@.heap_id);
                        assert(self.valid_node(i, self.next_ptr(i)));
                    } else {
                        assert(old(self).valid_node(i, old(self).next_ptr(i)));
                        assert(self.perms@[i] == old(self).perms@[i]);
                        assert(self.next_ptr(i) == old(self).next_ptr(i));
                        assert(self.data@.fixed_page == old(self).data@.fixed_page);
                        assert(self.data@.block_size == old(self).data@.block_size);
                        assert(self.data@.page_id == old(self).data@.page_id);
                        assert(self.data@.heap_id == old(self).data@.heap_id);
                        assert(self.data@.instance == old(self).data@.instance);
                        assert(self.valid_node(i, self.next_ptr(i)));
                    }
                }
            }
            assert(self.wf());
        }
    }
}
}
