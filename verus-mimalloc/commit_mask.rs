use vstd::prelude::*;
use crate::config::*;
use crate::tokens::*;
use crate::layout::*;
use crate::types::*;
use vstd::contrib::set_build;
use vstd::set_lib::set_int_range;
use vstd::arithmetic::div_mod::{
    group_mod_properties, lemma_div_is_ordered, lemma_div_multiples_vanish,
    lemma_fundamental_div_mod, lemma_indistinguishable_quotients, lemma_mod_multiples_basic,
};

verus!{

// used for triggering
spec fn mod64(x: usize) -> usize { x % 64 }
spec fn div64(x: usize) -> usize { x / 64 }

#[verifier::opaque]
spec fn is_bit_set(a: usize, b: usize) -> bool {
    a & (1usize << b) == (1usize << b)
}

#[allow(unused_macros)]
macro_rules! is_bit_set {
    ($a:expr, $b:expr) => {
        $a & (1u64 << $b) == (1u64 << $b)
    }
}

#[verifier::rlimit(200)]
proof fn lemma_commit_mask_constants()
    ensures
        COMMIT_MASK_BITS as usize == 512,
        COMMIT_MASK_FIELD_COUNT as usize == 8,
        usize::BITS as usize == 64,
{
    assert(COMMIT_MASK_BITS == 512) by(compute_only);
    assert(COMMIT_MASK_FIELD_COUNT == 8) by(compute_only);
}

#[verifier::rlimit(200)]
proof fn lemma_shift_zero(word: usize)
    ensures
        word >> 0usize == word,
{
    assert(word >> 0usize == word) by(bit_vector) { }
}

#[verifier::rlimit(200)]
proof fn lemma_shifted_even_nonzero_ofs_lt_63(word: usize, ofs: usize)
    requires
        ofs < 64,
        word >> ofs != 0,
        (word >> ofs) & 1usize == 0,
    ensures
        ofs < 63,
{
    if 63usize <= ofs {
        assert(ofs == 63usize);
        let shifted = word >> ofs;
        assert(shifted == word >> 63usize);
        assert((word >> 63usize) <= 1usize) by(bit_vector);
        assert(shifted <= 1usize);
        assert(shifted == 1usize) by(nonlinear_arith)
            requires
                shifted != 0usize,
                shifted <= 1usize;
        assert(1usize & 1usize == 1usize) by(bit_vector);
        assert(shifted & 1usize == 1usize);
        assert(false);
    }
}

#[verifier::rlimit(200)]
proof fn lemma_shifted_next_one_ofs_lt_63(word: usize, ofs: usize)
    requires
        ofs < 64,
        ((word >> ofs) >> 1usize) & 1usize == 1usize,
    ensures
        ofs < 63,
{
    if 63usize <= ofs {
        assert(ofs == 63usize);
        let shifted = word >> ofs;
        assert(shifted == word >> 63usize);
        assert((word >> 63usize) >> 1usize == 0usize) by(bit_vector);
        assert(shifted >> 1usize == 0usize);
        assert((word >> ofs) >> 1usize == shifted >> 1usize);
        assert(((word >> ofs) >> 1usize) == 0usize);
        assert(0usize & 1usize == 0usize) by(bit_vector);
        assert(((word >> ofs) >> 1usize) & 1usize == 0usize);
        assert(false);
    }
}

#[verifier::rlimit(200)]
proof fn lemma_even_nonzero_shift(mask: usize, ofs: usize)
    requires
        ofs < 63,
        mask != 0,
        mask & 1usize == 0,
    ensures
        ofs + 1 < 64,
        mask >> 1usize != 0,
{
    assert(mask >> 1usize != 0usize) by(bit_vector)
        requires
            mask != 0usize,
            mask & 1usize == 0usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_shift_compose_one(word: usize, ofs: usize)
    requires
        ofs < 63,
    ensures
        (word >> ofs) >> 1usize == word >> add(ofs, 1usize),
{
    assert((word >> ofs) >> 1usize == word >> add(ofs, 1usize)) by(bit_vector)
        requires
            ofs < 63usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_low_one_shift(mask: usize, ofs: usize)
    requires
        ofs < 63,
        (mask >> 1usize) & 1usize == 1usize,
    ensures
        ofs + 1 < 64,
{
}

#[verifier::rlimit(200)]
proof fn lemma_zero_bit(bit: usize)
    requires
        bit < 64,
    ensures
        !is_bit_set(0usize, bit),
{
    reveal(is_bit_set);
    assert(0usize & (1usize << bit) == 0usize) by(bit_vector)
        requires
            bit < 64usize
    { }
    assert((1usize << bit) != 0usize) by(bit_vector)
        requires
            bit < 64usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_full_word_bit(bit: usize)
    requires
        bit < 64,
    ensures
        is_bit_set(!0usize, bit),
{
    reveal(is_bit_set);
    assert(!0usize & (1usize << bit) == (1usize << bit)) by(bit_vector)
        requires
            bit < 64usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_low_bit_either(mask: usize)
    ensures
        mask & 1usize == 0usize || mask & 1usize == 1usize,
{
    assert(mask & 1usize == 0usize || mask & 1usize == 1usize) by(bit_vector) { }
}

#[verifier::rlimit(200)]
proof fn lemma_shift_low_bit_is_bit_set(word: usize, ofs: usize)
    requires
        ofs < 64,
        (word >> ofs) & 1usize == 1usize,
    ensures
        is_bit_set(word, ofs),
{
    reveal(is_bit_set);
    assert((word >> ofs) & 1usize == 1usize);
    assert(word & (1usize << ofs) == (1usize << ofs)) by(bit_vector)
        requires
            ofs < 64usize,
            (word >> ofs) & 1usize == 1usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_clear_word_bit(word: usize, other: usize, bit: usize)
    requires
        bit < 64,
    ensures
        is_bit_set(word & !other, bit) <==> is_bit_set(word, bit) && !is_bit_set(other, bit),
{
    reveal(is_bit_set);
    assert(((word & !other) & (1usize << bit) == (1usize << bit))
        <==> ((word & (1usize << bit) == (1usize << bit))
            && !(other & (1usize << bit) == (1usize << bit)))) by(bit_vector)
        requires
            bit < 64usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_intersect_word_bit(word: usize, other: usize, bit: usize)
    requires
        bit < 64,
    ensures
        is_bit_set(word & other, bit) <==> is_bit_set(word, bit) && is_bit_set(other, bit),
{
    reveal(is_bit_set);
    assert(((word & other) & (1usize << bit) == (1usize << bit))
        <==> ((word & (1usize << bit) == (1usize << bit))
            && (other & (1usize << bit) == (1usize << bit)))) by(bit_vector)
        requires
            bit < 64usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_set_word_bit(word: usize, other: usize, bit: usize)
    requires
        bit < 64,
    ensures
        is_bit_set(word | other, bit) <==> is_bit_set(word, bit) || is_bit_set(other, bit),
{
    reveal(is_bit_set);
    assert(((word | other) & (1usize << bit) == (1usize << bit))
        <==> ((word & (1usize << bit) == (1usize << bit))
            || (other & (1usize << bit) == (1usize << bit)))) by(bit_vector)
        requires
            bit < 64usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_create_word_mask_bit(mask: usize, ofs: usize, c: usize, bit: usize)
    requires
        ofs < 64,
        c <= 64 - ofs,
        bit < 64,
        mask == if c >= 64 { !0usize } else { sub(1usize << c, 1usize) << ofs },
    ensures
        is_bit_set(mask, bit) <==> ofs <= bit < ofs + c,
{
    reveal(is_bit_set);
    if c >= 64 {
        assert(c == 64 && ofs == 0) by(nonlinear_arith)
            requires
                ofs < 64,
                c <= 64 - ofs,
                c >= 64;
        assert(mask == !0usize);
        assert(!0usize & (1usize << bit) == (1usize << bit)) by(bit_vector)
            requires
                bit < 64usize
        { }
    } else {
        assert(c < 64);
        assert(((sub(1usize << c, 1usize) << ofs) & (1usize << bit) == (1usize << bit)) <==> ofs <= bit < ofs + c) by(bit_vector)
            requires
                ofs < 64usize,
                c < 64usize,
                c <= 64usize - ofs,
                bit < 64usize
        { }
    }
}

#[verifier::rlimit(200)]
proof fn lemma_mod64_lt(x: usize)
    ensures
        mod64(x) < 64,
{
    assert(x % 64usize < 64usize) by(nonlinear_arith);
}

#[verifier::rlimit(200)]
proof fn lemma_div64_range(x: usize, q: usize)
    requires
        x / 64usize == q,
    ensures
        64usize * q <= x,
        x < 64usize * (q + 1usize),
{
    assert(64usize * q <= x) by(nonlinear_arith)
        requires
            x / 64usize == q;
    assert(x < 64usize * (q + 1usize)) by(nonlinear_arith)
        requires
            x / 64usize == q;
}

#[verifier::rlimit(200)]
proof fn lemma_div64_bound_512(x: usize, i: usize)
    requires
        x / 64usize == i,
        i < 8,
    ensures
        x < 512,
{
    assert(x < (i + 1usize) * 64usize) by(nonlinear_arith)
        requires
            x / 64usize == i;
    assert((i + 1usize) * 64usize <= 512usize) by(nonlinear_arith)
        requires
            i < 8usize;
}

#[verifier::rlimit(200)]
proof fn lemma_div64_after_inc(x: usize, i: usize)
    requires
        x < 512,
        x / 64usize == i,
    ensures
        add(x, 1usize) / 64 == if mod64(add(x, 1usize)) == 0 { add(i, 1usize) as int } else { i as int },
{
    assert(add(x, 1usize) / 64 == if add(x, 1usize) % 64 == 0usize { add(i, 1usize) as int } else { i as int }) by(nonlinear_arith)
        requires
            x < 512usize,
            x / 64usize == i
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_div64_inc_same(x: usize, i: usize)
    requires
        x < 512,
        x / 64usize == i,
        mod64(x) < 63,
    ensures
        mod64(add(x, 1usize)) == add(mod64(x), 1usize),
        add(x, 1usize) / 64 == i,
{
    assert(add(x, 1usize) % 64 == add(x % 64usize, 1usize)) by(nonlinear_arith)
        requires
            x < 512usize,
            x % 64usize < 63usize
    { }
    assert(add(x, 1usize) / 64 == i) by(nonlinear_arith)
        requires
            x < 512usize,
            x / 64usize == i,
            x % 64usize < 63usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_div64_mod64_zero_value(x: usize, q: usize)
    requires
        x / 64usize == q,
        mod64(x) == 0,
    ensures
        x == 64usize * q,
{
    assert(x == 64usize * q) by(nonlinear_arith)
        requires
            x / 64usize == q,
            x % 64usize == 0usize
    { }
}

#[verifier::rlimit(200)]
proof fn lemma_empty_range(lo: int)
    ensures
        Set::<int>::range(lo, lo) =~= Set::empty(),
{
    assert forall|x: int| #[trigger] Set::<int>::range(lo, lo).contains(x) == Set::<int>::empty().contains(x) by {
        if Set::<int>::range(lo, lo).contains(x) {
            assert(false);
        }
    }
}

// I don't think there's a good reason that some of these would need `j < 64` and others don't but
// for some the bitvector assertions without it succeeds and for others it doesn't.

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

// {(x, y) | 0 <= x < 8 && y < 64}
spec fn set_8_64() -> Set<(int, usize)> {
    set_build!{ (x, y): (int, usize) | x: int in 0..8, y: usize in 0..64 }
}

impl CommitMask {
    pub closed spec fn concrete_empty(&self) -> bool {
        self.mask[0] == 0 && self.mask[1] == 0 && self.mask[2] == 0 && self.mask[3] == 0
            && self.mask[4] == 0 && self.mask[5] == 0 && self.mask[6] == 0 && self.mask[7] == 0
    }

    pub closed spec fn view(&self) -> Set<int> {
        Set::range(0, 512).filter(|bit: int|
            (0 <= bit < 64 && is_bit_set(self.mask[0], bit as usize))
            || (64 <= bit < 128 && is_bit_set(self.mask[1], (bit - 64) as usize))
            || (128 <= bit < 192 && is_bit_set(self.mask[2], (bit - 128) as usize))
            || (192 <= bit < 256 && is_bit_set(self.mask[3], (bit - 192) as usize))
            || (256 <= bit < 320 && is_bit_set(self.mask[4], (bit - 256) as usize))
            || (320 <= bit < 384 && is_bit_set(self.mask[5], (bit - 320) as usize))
            || (384 <= bit < 448 && is_bit_set(self.mask[6], (bit - 384) as usize))
            || (448 <= bit < 512 && is_bit_set(self.mask[7], (bit - 448) as usize))
        )
    }

    #[verifier::rlimit(200)]
    proof fn lemma_concrete_empty_view(&self)
        requires
            self.concrete_empty(),
        ensures
            self@ =~= Set::empty(),
    {
        assert forall|bit: int| #[trigger] self@.contains(bit) == Set::<int>::empty().contains(bit) by {
            if self@.contains(bit) {
                assert(0 <= bit < 512);
                if 0 <= bit < 64 {
                    lemma_zero_bit(bit as usize);
                } else if 64 <= bit < 128 {
                    lemma_zero_bit((bit - 64) as usize);
                } else if 128 <= bit < 192 {
                    lemma_zero_bit((bit - 128) as usize);
                } else if 192 <= bit < 256 {
                    lemma_zero_bit((bit - 192) as usize);
                } else if 256 <= bit < 320 {
                    lemma_zero_bit((bit - 256) as usize);
                } else if 320 <= bit < 384 {
                    lemma_zero_bit((bit - 320) as usize);
                } else if 384 <= bit < 448 {
                    lemma_zero_bit((bit - 384) as usize);
                } else {
                    assert(448 <= bit < 512);
                    lemma_zero_bit((bit - 448) as usize);
                }
                assert(false);
            }
        }
    }

    #[verifier::opaque]
    pub open spec fn bytes(&self, segment_id: SegmentId) -> Set<int> {
        // {addr | self@.contains((addr - segment_start(segment_id)) / COMMIT_SIZE)}
        let start = segment_start(segment_id);
        self@.map_flatten_by(
            |i: int| Set::range(start + i * COMMIT_SIZE, start + (i + 1) * COMMIT_SIZE),
            |addr: int| (addr - start) / COMMIT_SIZE as int,
        )
    }

    #[verus_verify]
    pub fn empty() -> (cm: CommitMask)
        ensures
            true,
            cm.concrete_empty(),
            cm@ =~= Set::empty(),
    {
        let res = CommitMask { mask: [ 0, 0, 0, 0, 0, 0, 0, 0 ] };
        proof { res.lemma_concrete_empty_view(); }
        res
    }

    #[verus_verify]
    pub fn all_set(&self, other: &CommitMask) -> (res: bool)
        ensures
            res ==> other@ <= self@,
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] & other.mask[j] == other.mask[j]
        {
            if self.mask[i] & other.mask[i] != other.mask[i] {
                return false;
            }
            i = i + 1;
        }
        proof {
            assert forall |bit: int| #[trigger] other@.contains(bit) implies self@.contains(bit) by {
                assert(0 <= bit < 512);
                if 0 <= bit < 64 {
                    assert(self.mask[0] & other.mask[0] == other.mask[0]);
                    lemma_intersect_word_bit(self.mask[0], other.mask[0], bit as usize);
                } else if 64 <= bit < 128 {
                    assert(self.mask[1] & other.mask[1] == other.mask[1]);
                    lemma_intersect_word_bit(self.mask[1], other.mask[1], (bit - 64) as usize);
                } else if 128 <= bit < 192 {
                    assert(self.mask[2] & other.mask[2] == other.mask[2]);
                    lemma_intersect_word_bit(self.mask[2], other.mask[2], (bit - 128) as usize);
                } else if 192 <= bit < 256 {
                    assert(self.mask[3] & other.mask[3] == other.mask[3]);
                    lemma_intersect_word_bit(self.mask[3], other.mask[3], (bit - 192) as usize);
                } else if 256 <= bit < 320 {
                    assert(self.mask[4] & other.mask[4] == other.mask[4]);
                    lemma_intersect_word_bit(self.mask[4], other.mask[4], (bit - 256) as usize);
                } else if 320 <= bit < 384 {
                    assert(self.mask[5] & other.mask[5] == other.mask[5]);
                    lemma_intersect_word_bit(self.mask[5], other.mask[5], (bit - 320) as usize);
                } else if 384 <= bit < 448 {
                    assert(self.mask[6] & other.mask[6] == other.mask[6]);
                    lemma_intersect_word_bit(self.mask[6], other.mask[6], (bit - 384) as usize);
                } else {
                    assert(448 <= bit < 512);
                    assert(self.mask[7] & other.mask[7] == other.mask[7]);
                    lemma_intersect_word_bit(self.mask[7], other.mask[7], (bit - 448) as usize);
                }
            }
        }
        return true;
    }

    #[verus_verify]
    pub fn any_set(&self, other: &CommitMask) -> (res: bool)
        ensures
            true,
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] & other.mask[j] == 0
        {
            if self.mask[i] & other.mask[i] != 0 {
                return true;
            }
            i += 1;
        }
        return false;
    }

    #[verus_verify]
    pub fn create_intersect(&self, other: &CommitMask, res: &mut CommitMask)
        ensures
            final(res)@ =~= self@.intersect(other@),
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] res.mask[j] == self.mask[j] & other.mask[j],
        {
            res.mask[i] = self.mask[i] & other.mask[i];
            i += 1;
        }
        proof {
            assert forall|bit: int| #[trigger] res@.contains(bit) == self@.intersect(other@).contains(bit) by {
                if 0 <= bit < 512 {
                    if 0 <= bit < 64 {
                        lemma_intersect_word_bit(self.mask[0], other.mask[0], bit as usize);
                    } else if 64 <= bit < 128 {
                        lemma_intersect_word_bit(self.mask[1], other.mask[1], (bit - 64) as usize);
                    } else if 128 <= bit < 192 {
                        lemma_intersect_word_bit(self.mask[2], other.mask[2], (bit - 128) as usize);
                    } else if 192 <= bit < 256 {
                        lemma_intersect_word_bit(self.mask[3], other.mask[3], (bit - 192) as usize);
                    } else if 256 <= bit < 320 {
                        lemma_intersect_word_bit(self.mask[4], other.mask[4], (bit - 256) as usize);
                    } else if 320 <= bit < 384 {
                        lemma_intersect_word_bit(self.mask[5], other.mask[5], (bit - 320) as usize);
                    } else if 384 <= bit < 448 {
                        lemma_intersect_word_bit(self.mask[6], other.mask[6], (bit - 384) as usize);
                    } else {
                        assert(448 <= bit < 512);
                        lemma_intersect_word_bit(self.mask[7], other.mask[7], (bit - 448) as usize);
                    }
                } else {
                    assert(!res@.contains(bit));
                    assert(!self@.contains(bit));
                    assert(!self@.intersect(other@).contains(bit));
                }
            }
        }
    }

    pub fn clear(&mut self, other: &CommitMask)
        ensures
            final(self)@ =~= old(self)@ - other@,
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] self.mask[j] == old(self).mask[j] & !other.mask[j],
                forall|j: int| i <= j < 8 ==> #[trigger] self.mask[j] == old(self).mask[j]
        {
            let m = self.mask[i];
            self.mask[i] = m & !other.mask[i];
            i += 1;
        }
        proof {
            assert forall|bit: int| #[trigger] self@.contains(bit) == (old(self)@ - other@).contains(bit) by {
                if 0 <= bit < 512 {
                    if 0 <= bit < 64 {
                        lemma_clear_word_bit(old(self).mask[0], other.mask[0], bit as usize);
                    } else if 64 <= bit < 128 {
                        lemma_clear_word_bit(old(self).mask[1], other.mask[1], (bit - 64) as usize);
                    } else if 128 <= bit < 192 {
                        lemma_clear_word_bit(old(self).mask[2], other.mask[2], (bit - 128) as usize);
                    } else if 192 <= bit < 256 {
                        lemma_clear_word_bit(old(self).mask[3], other.mask[3], (bit - 192) as usize);
                    } else if 256 <= bit < 320 {
                        lemma_clear_word_bit(old(self).mask[4], other.mask[4], (bit - 256) as usize);
                    } else if 320 <= bit < 384 {
                        lemma_clear_word_bit(old(self).mask[5], other.mask[5], (bit - 320) as usize);
                    } else if 384 <= bit < 448 {
                        lemma_clear_word_bit(old(self).mask[6], other.mask[6], (bit - 384) as usize);
                    } else {
                        assert(448 <= bit < 512);
                        lemma_clear_word_bit(old(self).mask[7], other.mask[7], (bit - 448) as usize);
                    }
                } else {
                    assert(!self@.contains(bit));
                    assert(!old(self)@.contains(bit));
                    assert(!(old(self)@ - other@).contains(bit));
                }
            }
        }
    }

    #[verus_verify]
    pub fn set(&mut self, other: &CommitMask)
        ensures
            final(self)@ =~= old(self)@ + other@,
    {
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] self.mask[j] == old(self).mask[j] | other.mask[j],
                forall|j: int| i <= j < 8 ==> #[trigger] self.mask[j] == old(self).mask[j]
        {
            let m = self.mask[i];
            self.mask[i] = m | other.mask[i];
            i += 1;
        }
        proof {
            assert forall|bit: int| #[trigger] self@.contains(bit) == (old(self)@ + other@).contains(bit) by {
                if 0 <= bit < 512 {
                    if 0 <= bit < 64 {
                        lemma_set_word_bit(old(self).mask[0], other.mask[0], bit as usize);
                    } else if 64 <= bit < 128 {
                        lemma_set_word_bit(old(self).mask[1], other.mask[1], (bit - 64) as usize);
                    } else if 128 <= bit < 192 {
                        lemma_set_word_bit(old(self).mask[2], other.mask[2], (bit - 128) as usize);
                    } else if 192 <= bit < 256 {
                        lemma_set_word_bit(old(self).mask[3], other.mask[3], (bit - 192) as usize);
                    } else if 256 <= bit < 320 {
                        lemma_set_word_bit(old(self).mask[4], other.mask[4], (bit - 256) as usize);
                    } else if 320 <= bit < 384 {
                        lemma_set_word_bit(old(self).mask[5], other.mask[5], (bit - 320) as usize);
                    } else if 384 <= bit < 448 {
                        lemma_set_word_bit(old(self).mask[6], other.mask[6], (bit - 384) as usize);
                    } else {
                        assert(448 <= bit < 512);
                        lemma_set_word_bit(old(self).mask[7], other.mask[7], (bit - 448) as usize);
                    }
                } else {
                    assert(!self@.contains(bit));
                    assert(!old(self)@.contains(bit));
                    assert(!(old(self)@ + other@).contains(bit));
                }
            }
        }
    }

    #[verus_verify]
    pub fn create(&mut self, idx: usize, count: usize)
        requires
            self.concrete_empty(),
            count <= COMMIT_MASK_BITS as usize,
            count < COMMIT_MASK_BITS as usize ==> idx as int + count as int <= 512,
        ensures
            count == COMMIT_MASK_BITS as usize ==> final(self)@ =~= Set::range(0, COMMIT_MASK_BITS as int),
            count < COMMIT_MASK_BITS as usize ==> final(self)@ =~= Set::range(idx as int, idx as int + count as int),
    {
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
            proof {
                self.lemma_concrete_empty_view();
                lemma_empty_range(idx as int);
                assert(self@ =~= Set::range(idx as int, idx as int + count as int));
            }
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;
            proof {
                self.lemma_concrete_empty_view();
                lemma_empty_range(idx as int);
                assert(self@ == Set::range(idx as int, idx as int));
                assert forall|j: int| i <= j < 8 implies self.mask[j] == 0 by {
                    assert(self.concrete_empty());
                }
                assert(count < COMMIT_MASK_BITS as usize) by(nonlinear_arith)
                    requires
                        count <= COMMIT_MASK_BITS as usize,
                        count != COMMIT_MASK_BITS as usize;
                assert(i < 8) by(nonlinear_arith)
                    requires
                        count > 0,
                        idx as int + count as int <= 512,
                        i == idx / 64,
                        usize::BITS as usize == 64;
                assert(64 * i + ofs + bitcount <= 512) by(nonlinear_arith)
                    requires
                        idx as int + count as int <= 512,
                        i == idx / 64,
                        ofs == idx % 64,
                        bitcount == count,
                        usize::BITS as usize == 64;
            }

            while bitcount > 0
                invariant
                    self@ == Set::range(idx as int, idx + (count - bitcount)),
                    ofs == if count == bitcount { idx % 64 } else { 0 },
                    bitcount > 0 ==> 64 * i + ofs == idx + (count - bitcount),
                    idx + count <= 512,
                    forall|j: int| i <= j < 8 ==> self.mask[j] == 0,
                    bitcount <= count,
            {

                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                proof {
                    assert(c <= bitcount);
                    assert(c <= avail);
                    assert(c <= 64) by(nonlinear_arith)
                        requires
                            c <= avail,
                            avail == 64 - ofs,
                            ofs < 64,
                            usize::BITS as usize == 64;
                }
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    proof {
                        assert(c < 64);
                        assert((1usize << c) >= 1usize) by(bit_vector)
                            requires c < 64;
                    }

                    ((1usize << c) - 1) << ofs
                };
                let old_self = Ghost(*self);
                self.mask[i] = mask;
                let oi = Ghost(i);
                let obc = Ghost(bitcount);
                let oofs = Ghost(ofs);
                proof {
                    assert(obc@ > c ==> c == avail);
                }
                bitcount -= c;
                ofs = 0;
                i += 1;
                proof {
                    assert(oofs@ < 64) by(nonlinear_arith)
                        requires
                            oofs@ == if count == obc@ { idx % 64 } else { 0 };
                    assert(avail == 64 - oofs@) by(nonlinear_arith)
                        requires
                            avail == 64 - oofs@,
                            usize::BITS as usize == 64;
                    assert(avail > 0) by(nonlinear_arith)
                        requires
                            avail == 64 - oofs@,
                            oofs@ < 64;
                    assert(c > 0) by(nonlinear_arith)
                        requires
                            c == if obc@ > avail { avail } else { obc@ },
                            obc@ > 0,
                            avail > 0;
                    assert(c <= 64 - oofs@) by(nonlinear_arith)
                        requires
                            c <= avail,
                            avail == 64 - oofs@;
                    assert(mask == if c >= 64 { !0usize } else { sub(1usize << c, 1usize) << oofs@ });
                    assert(idx + (count - bitcount) == idx + (count - obc@) + c) by(nonlinear_arith)
                        requires
                            bitcount == obc@ - c,
                            c <= obc@,
                            obc@ <= count;
                    assert(64 * oi@ + oofs@ == idx + (count - obc@)) by(nonlinear_arith)
                        requires
                            obc@ > 0,
                            64 * oi@ + oofs@ == idx + (count - obc@);
                    assert forall|bit: int| #[trigger] self@.contains(bit) == Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit) by {
                        if 0 <= bit < 512 {
                            if 64 * oi@ <= bit < 64 * oi@ + 64 {
                                let bit_in_word = (bit - 64 * oi@) as usize;
                                assert(bit_in_word < 64) by(nonlinear_arith)
                                    requires
                                        64 * oi@ <= bit < 64 * oi@ + 64,
                                        bit_in_word == bit - 64 * oi@;
                                lemma_create_word_mask_bit(mask, oofs@, c, bit_in_word);
                                assert(bit == 64 * oi@ + bit_in_word) by(nonlinear_arith)
                                    requires
                                        bit_in_word == bit - 64 * oi@;
                                assert(idx + (count - bitcount) == 64 * oi@ + oofs@ + c) by(nonlinear_arith)
                                    requires
                                        64 * oi@ + oofs@ == idx + (count - obc@),
                                        idx + (count - bitcount) == idx + (count - obc@) + c,
                                        bit_in_word == bit - 64 * oi@;
                                if Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit) {
                                    if count == obc@ {
                                        assert(idx + (count - obc@) == idx) by(nonlinear_arith)
                                            requires
                                                count == obc@;
                                        assert(64 * oi@ + oofs@ == idx);
                                    } else {
                                        assert(oofs@ == 0);
                                        assert(64 * oi@ == idx + (count - obc@)) by(nonlinear_arith)
                                            requires
                                                64 * oi@ + oofs@ == idx + (count - obc@),
                                                oofs@ == 0;
                                    }
                                    assert(bit >= idx + (count - obc@)) by(nonlinear_arith)
                                        requires
                                            Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit),
                                            bit == 64 * oi@ + bit_in_word,
                                            64 * oi@ + oofs@ == idx + (count - obc@),
                                            64 * oi@ <= bit < 64 * oi@ + 64,
                                            oofs@ == if count == obc@ { idx % 64 } else { 0 };
                                    assert(oofs@ <= bit_in_word < oofs@ + c) by(nonlinear_arith)
                                        requires
                                            Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit),
                                            bit == 64 * oi@ + bit_in_word,
                                            idx + (count - bitcount) == 64 * oi@ + oofs@ + c,
                                            64 * oi@ + oofs@ == idx + (count - obc@),
                                            bit >= idx + (count - obc@),
                                            64 * oi@ <= bit < 64 * oi@ + 64;
                                }
                                if oofs@ <= bit_in_word < oofs@ + c {
                                    assert(bit >= idx + (count - obc@)) by(nonlinear_arith)
                                        requires
                                            oofs@ <= bit_in_word,
                                            bit == 64 * oi@ + bit_in_word,
                                            64 * oi@ + oofs@ == idx + (count - obc@);
                                    assert(idx as int <= idx + (count - obc@)) by(nonlinear_arith)
                                        requires
                                            obc@ <= count;
                                    assert(idx as int <= bit) by(nonlinear_arith)
                                        requires
                                            idx as int <= idx + (count - obc@),
                                            bit >= idx + (count - obc@);
                                    assert(bit < idx + (count - bitcount)) by(nonlinear_arith)
                                        requires
                                            oofs@ <= bit_in_word < oofs@ + c,
                                            bit == 64 * oi@ + bit_in_word,
                                            idx + (count - bitcount) == 64 * oi@ + oofs@ + c;
                                    assert(Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit)) by(nonlinear_arith)
                                        requires
                                            oofs@ <= bit_in_word < oofs@ + c,
                                            bit >= idx + (count - obc@),
                                            idx as int <= bit,
                                            bit < idx + (count - bitcount),
                                            bit == 64 * oi@ + bit_in_word,
                                            idx + (count - bitcount) == 64 * oi@ + oofs@ + c,
                                            64 * oi@ + oofs@ == idx + (count - obc@);
                                }
                            } else {
                                assert(self@.contains(bit) == old_self@@.contains(bit));
                                assert(old_self@@.contains(bit) == Set::<int>::range(idx as int, idx + (count - obc@)).contains(bit));
                                assert(Set::<int>::range(idx as int, idx + (count - obc@)).contains(bit) == Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit)) by(nonlinear_arith)
                                    requires
                                        64 * oi@ + oofs@ == idx + (count - obc@),
                                        idx + (count - bitcount) == idx + (count - obc@) + c,
                                        c <= 64 - oofs@,
                                        !(64 * oi@ <= bit < 64 * oi@ + 64);
                            }
                        } else {
                            assert(!self@.contains(bit));
                            assert(!Set::<int>::range(idx as int, idx + (count - bitcount)).contains(bit)) by(nonlinear_arith)
                                requires
                                    idx + (count - bitcount) <= 512,
                                    !(0 <= bit < 512);
                        }
                    }
                    assert(self@ == Set::range(idx as int, idx + (count - bitcount)));
                    assert forall|j: int| i <= j < 8 implies self.mask[j] == 0 by {
                        assert(i == oi@ + 1);
                        assert(old_self@.mask[j] == 0);
                    }
                    if bitcount > 0 {
                        assert(obc@ > c);
                        assert(c == avail);
                        assert(c == 64 - oofs@) by(nonlinear_arith)
                            requires
                                c == avail,
                                avail == 64 - oofs@,
                                usize::BITS as usize == 64;
                        assert(64 * i + ofs + bitcount <= 512) by(nonlinear_arith)
                            requires
                                64 * oi@ + oofs@ + obc@ <= 512,
                                c == 64 - oofs@,
                                bitcount == obc@ - c,
                                i == oi@ + 1,
                                ofs == 0;
                        assert(i < 8) by(nonlinear_arith)
                            requires
                                64 * i + ofs + bitcount <= 512,
                                bitcount > 0,
                                ofs == 0;
                    }
                }

            }
            proof {
                assert(bitcount == 0);
                assert(count - bitcount == count);
                assert(idx + (count - bitcount) == idx + count);
                assert(self@ =~= Set::range(idx as int, idx as int + count as int));
            }
        }
    }

    #[verus_verify]
    pub fn create_empty(&mut self)
        ensures
            final(self).concrete_empty(),
            final(self)@ =~= Set::empty(),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == 0
        {
            self.mask[i] = 0;
            i += 1;
        }
        proof {
            self.lemma_concrete_empty_view();
        }
    }

    #[verus_verify]
    pub fn create_full(&mut self)
        ensures
            final(self)@ =~= Set::range(0, COMMIT_MASK_BITS as int),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == !0usize
        {
            self.mask[i] = !0usize;
            i += 1;
        }
        proof {
            lemma_commit_mask_constants();
            assert forall|bit: int| #[trigger] self@.contains(bit) == Set::<int>::range(0, COMMIT_MASK_BITS as int).contains(bit) by {
                if 0 <= bit < 512 {
                    if 0 <= bit < 64 {
                        lemma_full_word_bit(bit as usize);
                    } else if 64 <= bit < 128 {
                        lemma_full_word_bit((bit - 64) as usize);
                    } else if 128 <= bit < 192 {
                        lemma_full_word_bit((bit - 128) as usize);
                    } else if 192 <= bit < 256 {
                        lemma_full_word_bit((bit - 192) as usize);
                    } else if 256 <= bit < 320 {
                        lemma_full_word_bit((bit - 256) as usize);
                    } else if 320 <= bit < 384 {
                        lemma_full_word_bit((bit - 320) as usize);
                    } else if 384 <= bit < 448 {
                        lemma_full_word_bit((bit - 384) as usize);
                    } else {
                        assert(448 <= bit < 512);
                        lemma_full_word_bit((bit - 448) as usize);
                    }
                } else {
                    assert(!self@.contains(bit));
                    assert(!Set::<int>::range(0, COMMIT_MASK_BITS as int).contains(bit));
                }
            }
        }
    }

#[verifier::external_body]
    pub fn committed_size(&self, total: usize) -> usize
    {
        todo(); loop { }
    }

    #[verus_verify]
    pub fn next_run(&self, idx: usize) -> (res: (usize, usize))
        ensures
            res.0 <= COMMIT_MASK_BITS as usize,
            res.1 <= COMMIT_MASK_BITS as usize,
            res.0 as int + res.1 as int <= COMMIT_MASK_BITS as int,
            forall|j: int| res.0 as int <= j < res.0 as int + res.1 as int ==> self@.contains(j),
    {
        // Starting at idx, scan to find the first bit.

        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        // Changed loop condition to use 8 rather than COMMIT_MASK_FIELD_COUNT due to
        // https://github.com/verus-lang/verus/issues/925
        while i < 8
            invariant
                ofs < 64,
            ensures
                i < 8 ==> mask == self.mask[i as int] >> ofs,
                i < 8 ==> ofs < 64,
                i < 8 ==> mask & 1 == 1
        {
            mask = self.mask[i] >> ofs;
            if mask != 0 {
                while mask & 1 == 0
                    invariant
                        i < 8,
                        ofs < 64,
                        mask == self.mask[i as int] >> ofs,
                        mask != 0,
                {
                    let ghost old_ofs = ofs;
                    let ghost old_mask = mask;
                    proof {
                        lemma_shifted_even_nonzero_ofs_lt_63(self.mask[i as int], ofs);
                        lemma_even_nonzero_shift(mask, ofs);
                        lemma_shift_compose_one(self.mask[i as int], ofs);
                    }

                    mask = mask >> 1usize;
                    ofs += 1;
                    proof {
                        assert(ofs == add(old_ofs, 1usize));
                        assert(mask == old_mask >> 1usize);
                    }
                }

                proof {
                    assert(mask & 1usize == 1usize) by(bit_vector)
                        requires
                            mask & 1usize != 0usize
                    { }
                }
                break;
            }
            i += 1;
            ofs = 0;
        }

        if i >= COMMIT_MASK_FIELD_COUNT as usize {
            proof {
                lemma_commit_mask_constants();
                assert(COMMIT_MASK_BITS as usize <= COMMIT_MASK_BITS as usize);
                assert(0usize <= COMMIT_MASK_BITS as usize);
                assert(COMMIT_MASK_BITS as int + 0 as int <= COMMIT_MASK_BITS as int);
            }
            (COMMIT_MASK_BITS as usize, 0)
        } else {
            proof {
                lemma_commit_mask_constants();
                assert(i < 8);
            }
            // Count 1 bits in this run
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            let ghost mut cur_ofs: usize = ofs;
            proof {
                assert(next_idx == i * 64 + cur_ofs);
                assert(next_idx < 512) by(nonlinear_arith)
                    requires
                        i < 8,
                        cur_ofs < 64,
                        next_idx == i * 64 + cur_ofs;
            }

            loop
                invariant_except_break
                    mask & 1 == 1,
                    i < 8,
                    mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                    (next_idx + count) / 64 == i,
                invariant
                    forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                ensures
                    next_idx + count <= 512
            {
                loop
                    invariant_except_break
                        mask & 1 == 1,
                        i < 8,
                        mask == self.mask[i as int] >> mod64((next_idx + count) as usize),
                        (next_idx + count) / 64 == i,
                    invariant
                        forall|j: usize| next_idx <= j < next_idx + count ==> #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)),
                    ensures
                        mask & 1 == 0,
                        (next_idx + count) / 64 == if mod64((next_idx + count) as usize) == 0 { i + 1 } else { i as int }
                {
                    let ghost old_count = count;
                    let ghost old_pos: usize = add(next_idx, count);
                    let ghost old_mod: usize = mod64(old_pos);
                    let ghost old_mask = mask;
                    count += 1;
                    mask = mask >> 1usize;
                    proof {
                        assert(old_pos == add(next_idx, old_count));
                        assert(count == add(old_count, 1usize));
                        assert(old_pos == next_idx + old_count);
                        assert(count == old_count + 1);
                        assert(add(next_idx, count) == next_idx + count);
                        assert(add(old_pos, 1usize) == old_pos + 1);
                        assert(mask == old_mask >> 1usize);
                        assert(old_pos / 64usize == i);
                        lemma_mod64_lt(old_pos);
                        lemma_div64_bound_512(old_pos, i);
                        lemma_shift_low_bit_is_bit_set(self.mask[i as int], old_mod);
                        assert(div64(old_pos) == i);
                        assert forall|j: usize| next_idx <= j < next_idx + count implies #[trigger] is_bit_set(self.mask[div64(j) as int], mod64(j)) by {
                            if j < next_idx + old_count {
                                assert(is_bit_set(self.mask[div64(j) as int], mod64(j)));
                            } else {
                                assert(j == old_pos) by(nonlinear_arith)
                                    requires
                                        old_pos == next_idx + old_count,
                                        count == old_count + 1,
                                        next_idx <= j < next_idx + count,
                                        !(j < next_idx + old_count);
                                assert(div64(j) == i);
                                assert(mod64(j) == old_mod);
                            }
                        }
                        assert(add(next_idx, count) == add(old_pos, 1usize));
                        assert((next_idx + count) as usize == add(old_pos, 1usize));
                        lemma_div64_after_inc(old_pos, i);
                    }

                    if (mask & 1) != 1 {
                        proof {
                            lemma_low_bit_either(mask);
                            assert(mask & 1usize == 0usize);
                            assert((next_idx + count) / 64 == if mod64((next_idx + count) as usize) == 0 { i + 1 } else { i as int });
                        }

                        break;
                    }
                    proof {
                        assert(mask & 1usize == 1usize);
                        assert(((self.mask[i as int] >> old_mod) >> 1usize) & 1usize == 1usize);
                        lemma_shifted_next_one_ofs_lt_63(self.mask[i as int], old_mod);
                        lemma_shift_compose_one(self.mask[i as int], old_mod);
                        lemma_div64_inc_same(old_pos, i);
                        assert(mod64((next_idx + count) as usize) == add(old_mod, 1usize));
                        assert(mask == self.mask[i as int] >> mod64((next_idx + count) as usize));
                        assert((next_idx + count) / 64 == i);
                        assert(next_idx + count < 512) by(nonlinear_arith)
                            requires
                                i < 8,
                                (next_idx + count) / 64 == i;
                    }
                }

                if ((next_idx + count) % usize::BITS as usize) == 0 {
                    let ghost old_i = i;
                    i += 1;
                    if i >= COMMIT_MASK_FIELD_COUNT as usize {
                        proof {
                            let pos: usize = (next_idx + count) as usize;
                            assert(pos == next_idx + count);
                            lemma_commit_mask_constants();
                            assert(mod64(pos) == 0);
                            assert((next_idx + count) / 64 == i);
                            assert(i == 8) by(nonlinear_arith)
                                requires
                                    old_i < 8,
                                    i == old_i + 1,
                                    i >= 8;
                            lemma_div64_mod64_zero_value(pos, i);
                            assert(pos == 64 * i);
                            assert(next_idx + count == 64 * i);
                            assert(next_idx + count <= 512) by(nonlinear_arith)
                                requires
                                    next_idx + count == 64 * i,
                                    i == 8;
                        }
                        break;
                    }
                    proof {
                        lemma_commit_mask_constants();
                        assert(i < 8);
                        assert(mod64((next_idx + count) as usize) == 0);
                        assert((next_idx + count) / 64 == i);
                    }
                    mask = self.mask[i];

                    ofs = 0;
                    proof {
                        cur_ofs = 0;
                        lemma_shift_zero(self.mask[i as int]);
                        assert(mask == self.mask[i as int] >> mod64((next_idx + count) as usize));
                        assert((next_idx + count) / 64 == i);
                        assert(next_idx + count < 512) by(nonlinear_arith)
                            requires
                                i < 8,
                                (next_idx + count) / 64 == i;
                    }
                }

                if (mask & 1) != 1 {
                    proof {
                        let pos: usize = (next_idx + count) as usize;
                        assert(pos == next_idx + count);
                        if ((next_idx + count) % 64) == 0 {
                            assert(mod64(pos) == 0);
                            lemma_div64_mod64_zero_value(pos, i);
                            assert(pos == 64 * i);
                            assert(next_idx + count == 64 * i);
                            assert(next_idx + count <= 512) by(nonlinear_arith)
                                requires
                                    next_idx + count == 64 * i,
                                    i < 8;
                        } else {
                            assert(mod64(pos) != 0);
                            assert((next_idx + count) / 64 == i);
                            lemma_div64_bound_512(pos, i);
                            assert(next_idx + count < 512);
                        }
                    }
                    break;
                }
                proof {
                    if ((next_idx + count) % 64) != 0 {
                        assert(false);
                    }
                }
            }

            proof {
                lemma_commit_mask_constants();
                assert(next_idx + count <= 512);
                assert(next_idx as int + count as int <= COMMIT_MASK_BITS as int);
                assert(next_idx <= COMMIT_MASK_BITS as usize) by(nonlinear_arith)
                    requires
                        next_idx as int + count as int <= COMMIT_MASK_BITS as int;
                assert(count <= COMMIT_MASK_BITS as usize) by(nonlinear_arith)
                    requires
                        next_idx as int + count as int <= COMMIT_MASK_BITS as int;
                assert forall|j: int| next_idx as int <= j < next_idx as int + count as int implies self@.contains(j) by {
                    assert(0 <= j < 512) by(nonlinear_arith)
                        requires
                            next_idx as int <= j,
                            j < next_idx as int + count as int,
                            next_idx + count <= 512;
                    let uj = j as usize;
                    assert(uj as int == j);
                    assert(uj < 512);
                    assert(uj / 64usize < 8) by(nonlinear_arith)
                        requires
                            uj < 512;
                    assert(next_idx <= uj < next_idx + count);
                    assert(is_bit_set(self.mask[div64(uj) as int], mod64(uj)));
                    if div64(uj) == 0 {
                        lemma_div64_range(uj, 0usize);
                        assert(0 <= j < 64) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 0usize <= uj,
                                uj < 64usize * (0usize + 1usize);
                    } else if div64(uj) == 1 {
                        lemma_div64_range(uj, 1usize);
                        assert(64 <= j < 128) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 1usize <= uj,
                                uj < 64usize * (1usize + 1usize);
                    } else if div64(uj) == 2 {
                        lemma_div64_range(uj, 2usize);
                        assert(128 <= j < 192) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 2usize <= uj,
                                uj < 64usize * (2usize + 1usize);
                    } else if div64(uj) == 3 {
                        lemma_div64_range(uj, 3usize);
                        assert(192 <= j < 256) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 3usize <= uj,
                                uj < 64usize * (3usize + 1usize);
                    } else if div64(uj) == 4 {
                        lemma_div64_range(uj, 4usize);
                        assert(256 <= j < 320) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 4usize <= uj,
                                uj < 64usize * (4usize + 1usize);
                    } else if div64(uj) == 5 {
                        lemma_div64_range(uj, 5usize);
                        assert(320 <= j < 384) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 5usize <= uj,
                                uj < 64usize * (5usize + 1usize);
                    } else if div64(uj) == 6 {
                        lemma_div64_range(uj, 6usize);
                        assert(384 <= j < 448) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 6usize <= uj,
                                uj < 64usize * (6usize + 1usize);
                    } else {
                        assert(div64(uj) == 7) by(nonlinear_arith)
                            requires
                                uj / 64usize < 8,
                                uj / 64usize != 0,
                                uj / 64usize != 1,
                                uj / 64usize != 2,
                                uj / 64usize != 3,
                                uj / 64usize != 4,
                                uj / 64usize != 5,
                                uj / 64usize != 6;
                        lemma_div64_range(uj, 7usize);
                        assert(448 <= j < 512) by(nonlinear_arith)
                            requires
                                uj as int == j,
                                64usize * 7usize <= uj,
                                uj < 64usize * (7usize + 1usize);
                    }
                }
            }
            (next_idx, count)
        }
    }

    #[verus_verify]
    pub fn is_empty(&self) -> (b: bool)
        ensures
            b ==> self@ =~= Set::empty(),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == 0
        {
            if self.mask[i] != 0 {
                return false;
            }
            i += 1;
        }
        proof {
            assert(self.concrete_empty());
            self.lemma_concrete_empty_view();
        }
        return true;
    }

    #[verus_verify]
    pub fn is_full(&self) -> (b: bool)
        ensures
            b ==> self@ =~= Set::range(0, COMMIT_MASK_BITS as int),
    {
        let mut i = 0;
        while i < 8
            invariant forall|j: int| #![auto] 0 <= j < i ==> self.mask[j] == !0usize
        {
            if self.mask[i] != (!0usize) {
                return false;
            }
            i = i + 1;
        }
        proof {
            lemma_commit_mask_constants();
            assert forall|bit: int| #[trigger] self@.contains(bit) == Set::<int>::range(0, COMMIT_MASK_BITS as int).contains(bit) by {
                if 0 <= bit < 512 {
                    if 0 <= bit < 64 {
                        lemma_full_word_bit(bit as usize);
                    } else if 64 <= bit < 128 {
                        lemma_full_word_bit((bit - 64) as usize);
                    } else if 128 <= bit < 192 {
                        lemma_full_word_bit((bit - 128) as usize);
                    } else if 192 <= bit < 256 {
                        lemma_full_word_bit((bit - 192) as usize);
                    } else if 256 <= bit < 320 {
                        lemma_full_word_bit((bit - 256) as usize);
                    } else if 320 <= bit < 384 {
                        lemma_full_word_bit((bit - 320) as usize);
                    } else if 384 <= bit < 448 {
                        lemma_full_word_bit((bit - 384) as usize);
                    } else {
                        assert(448 <= bit < 512);
                        lemma_full_word_bit((bit - 448) as usize);
                    }
                } else {
                    assert(!self@.contains(bit));
                    assert(!Set::<int>::range(0, COMMIT_MASK_BITS as int).contains(bit));
                }
            }
        }
        return true;
    }
}

}
