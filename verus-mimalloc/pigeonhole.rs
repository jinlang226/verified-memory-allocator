#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;

use crate::tokens::{BlockId, PageId};

verus!{

pub proof fn block_id_set_len_bound(blocks: Set<BlockId>, page_id: PageId, len: nat)
    requires
        forall |block_id: BlockId| #[trigger] blocks.contains(block_id) ==>
            block_id.page_id == page_id && block_id.idx < len,
        forall |block_id1: BlockId, block_id2: BlockId|
            #[trigger] blocks.contains(block_id1) && #[trigger] blocks.contains(block_id2)
            && block_id1.page_id == block_id2.page_id
            && block_id1.idx == block_id2.idx ==> block_id1 == block_id2,
    ensures
        blocks.len() <= len,
    decreases len,
{
    if len == 0 {
        if blocks.len() != 0 {
            lemma_set_empty_equivalency_len(blocks);
            let block_id = blocks.choose();
            assert(blocks.contains(block_id));
            assert(block_id.idx < len);
            assert(false);
        }
    } else {
        let last = (len - 1) as nat;
        if exists |block_id: BlockId| blocks.contains(block_id) && block_id.page_id == page_id && block_id.idx == last {
            let last_block = choose |block_id: BlockId| blocks.contains(block_id)
                && block_id.page_id == page_id && block_id.idx == last;
            let blocks0 = blocks.remove(last_block);

            assert(blocks0.len() == blocks.len() - 1) by {
                vstd::set::lemma_set_remove_len(blocks, last_block);
            }

            assert forall |block_id: BlockId| #[trigger] blocks0.contains(block_id) implies
                block_id.page_id == page_id && block_id.idx < last
            by {
                assert(blocks.contains(block_id));
                assert(block_id != last_block);
                assert(block_id.page_id == page_id);
                assert(block_id.idx < len);
                if !(block_id.idx < last) {
                    assert(block_id.idx == last) by(nonlinear_arith)
                        requires
                            block_id.idx < len,
                            last == len - 1,
                            !(block_id.idx < last);
                    assert(last_block.page_id == page_id);
                    assert(last_block.idx == last);
                    assert(block_id == last_block);
                    assert(false);
                }
            };

            assert forall |block_id1: BlockId, block_id2: BlockId|
                #[trigger] blocks0.contains(block_id1) && #[trigger] blocks0.contains(block_id2)
                && block_id1.page_id == block_id2.page_id
                && block_id1.idx == block_id2.idx implies block_id1 == block_id2
            by {
                assert(blocks.contains(block_id1));
                assert(blocks.contains(block_id2));
            };

            block_id_set_len_bound(blocks0, page_id, last);
            assert(blocks.len() <= len) by(nonlinear_arith)
                requires
                    blocks0.len() <= last,
                    blocks0.len() == blocks.len() - 1,
                    last == len - 1;
        } else {
            assert forall |block_id: BlockId| #[trigger] blocks.contains(block_id) implies
                block_id.page_id == page_id && block_id.idx < last
            by {
                assert(block_id.page_id == page_id);
                assert(block_id.idx < len);
                if !(block_id.idx < last) {
                    assert(block_id.idx == last) by(nonlinear_arith)
                        requires
                            block_id.idx < len,
                            last == len - 1,
                            !(block_id.idx < last);
                    assert(exists |bid: BlockId| blocks.contains(bid) && bid.page_id == page_id && bid.idx == last);
                    assert(false);
                }
            };

            block_id_set_len_bound(blocks, page_id, last);
            assert(blocks.len() <= len) by(nonlinear_arith)
                requires
                    blocks.len() <= last,
                    last == len - 1;
        }
    }
}

}
