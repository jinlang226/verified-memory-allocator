use vstd::prelude::*;
use crate::config::*;
use crate::tokens::*;
use crate::layout::*;
use crate::types::*;
use vstd::contrib::set_build;
use vstd::set_lib::set_int_range;

verus!{

#[verifier::external_body]
proof fn lemma_map_distribute<S,T>(s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T)
    ensures s1.union(s2).map(f) == s1.map(f).union(s2.map(f))
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_map_distribute_auto<S,T>()
    ensures forall|s1: Set<S>, s2: Set<S>, f: spec_fn(S) -> T| s1.union(s2).map(f) == #[trigger] s1.map(f).union(s2.map(f))
{
    unimplemented!();
}

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

#[verifier::external_body]
proof fn lemma_bitmask_to_is_bit_set(n: usize, o: usize)
    requires
        n < 64,
        o <= 64 - n,
    ensures ({
        let m = sub(1usize << n, 1) << o;
        &&& forall|j: usize| j < o           ==> !is_bit_set(m, j)
        &&& forall|j: usize| o <= j < o + n  ==> is_bit_set(m, j)
        &&& forall|j: usize| o + n <= j < 64 ==> !is_bit_set(m, j)
    })
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_3_aux(a: u64, b: u64, hi: u64) -> (i: u64)
    requires
        a & b != b,
        hi <= 64,
        a >> hi == 0,
        b >> hi == 0,
    ensures
        i < hi,
        !is_bit_set!(a, i),
        is_bit_set!(b, i),
    decreases hi
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_3(a: usize, b: usize) -> (i: usize)
    requires a & b != b
    ensures
        i < 64,
        !is_bit_set(a, i),
        is_bit_set(b, i),
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_2(a: usize) -> (b: usize)
    requires a != !0usize
    ensures
        b < 64,
        !is_bit_set(a, b)
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_1_aux(a: u64, hi: u64) -> (i: u64)
    requires
        a != 0,
        hi <= 64,
        a >> hi == 0,
    ensures
        i < hi,
        is_bit_set!(a, i),
    decreases hi
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_obtain_bit_index_1(a: usize) -> (b: usize)
    requires a != 0
    ensures
        b < 64,
        is_bit_set(a, b)
{
    unimplemented!();
}

// I don't think there's a good reason that some of these would need `j < 64` and others don't but
// for some the bitvector assertions without it succeeds and for others it doesn't.
#[verifier::external_body]
proof fn lemma_is_bit_set()
    ensures
        forall|j: usize| j < 64 ==> !(#[trigger] is_bit_set(0, j)),
        forall|j: usize| is_bit_set(!0usize, j),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a | b, j)  <==> is_bit_set(a, j) || is_bit_set(b, j),
        forall|a: usize, b: usize, j: usize| j < 64 ==> (#[trigger] is_bit_set(a & !b, j) <==> is_bit_set(a, j) && !is_bit_set(b, j)),
        forall|a: usize, b: usize, j: usize| #[trigger] is_bit_set(a & b, j)  <==> is_bit_set(a, j) && is_bit_set(b, j),
        // Implied by previous properties, possibly too aggressive trigger
        forall|a: usize, b: usize, j: usize| j < 64 ==> (a & b == 0) ==> !(#[trigger] is_bit_set(a, j) && #[trigger] is_bit_set(b, j)),
{
    unimplemented!();
}

pub struct CommitMask {
    mask: [usize; 8],     // size = COMMIT_MASK_FIELD_COUNT
}

// {(x, y) | 0 <= x < 8 && y < 64}
spec fn set_8_64() -> Set<(int, usize)> {
    set_build!{ (x, y): (int, usize) | x: int in 0..8, y: usize in 0..64 }
}

impl CommitMask {
    pub closed spec fn view(&self) -> Set<int> {
        set_8_64()
            .filter(|t: (int, usize)| is_bit_set(self.mask[t.0], t.1))
            .map(|t: (int, usize)| t.0 * 64 + t.1)
    }

    #[verifier::external_body]
    proof fn lemma_view(&self)
        ensures
        // forall|i: int| self@.contains(i) ==> i < 512,
        // TODO: this isn't currently used but probably will need it (-> check later)
        (forall|i: int| self@.contains(i) ==> {
            let a = i / usize::BITS as int;
            let b = (i % usize::BITS as int) as usize;
            &&& a * 64 + b == i
            &&& is_bit_set(self.mask[a], b)
        }),
        forall|a: int, b: usize| 0 <= a < 8 && b < 64 && is_bit_set(self.mask[a], b)
            ==> #[trigger] self@.contains(a * 64 + b),
    {
        unimplemented!();
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

#[verifier::external_body]
    pub fn empty() -> (cm: CommitMask)
{
        let res = CommitMask { mask: [ 0, 0, 0, 0, 0, 0, 0, 0 ] };
        res
    }

#[verifier::external_body]
    pub fn all_set(&self, other: &CommitMask) -> (res: bool)
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
        return true;
    }

#[verifier::external_body]
    pub fn any_set(&self, other: &CommitMask) -> (res: bool)
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

#[verifier::external_body]
    pub fn create_intersect(&self, other: &CommitMask, res: &mut CommitMask)
{
        let mut i = 0;
        while i < 8
            invariant
                forall|j: int| 0 <= j < i ==> #[trigger] res.mask[j] == self.mask[j] & other.mask[j],
        {
            res.mask[i] = self.mask[i] & other.mask[i];
            i += 1;
        }
    }

#[verifier::external_body]
    pub fn clear(&mut self, other: &CommitMask)
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
    }

#[verifier::external_body]
    pub fn set(&mut self, other: &CommitMask)
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
    }

    #[verifier::external_body]
    proof fn lemma_change_one_entry(&self, other: &Self, i: int)
        requires
            0 <= i < 8,
            self.mask[i] == 0,
            forall|j: int| 0 <= j < i ==> other.mask[j] == self.mask[j],
            forall|j: int| i < j < 8 ==> other.mask[j] == self.mask[j],
        ensures
            other@ == self@.union(Set::range(0, 64).filter(|b: usize| is_bit_set(other.mask[i], b)).map(|b: usize| 64 * i + b)),
    {
        unimplemented!();
    }

#[verifier::external_body]
    pub fn create(&mut self, idx: usize, count: usize)
{
        if count == COMMIT_MASK_BITS as usize {
            self.create_full();
        } else if count == 0 {
            assert(self@ =~= Set::range(idx as int, idx + count));
        } else {
            let mut i = idx / usize::BITS as usize;
            let mut ofs: usize = idx % usize::BITS as usize;
            let mut bitcount = count;
            assert(Set::range(idx as int, idx + (count - bitcount)) =~= Set::empty());
            while bitcount > 0
                invariant
                    self@ == Set::range(idx as int, idx + (count - bitcount)),
                    ofs == if count == bitcount { idx % 64 } else { 0 },
                    bitcount > 0 ==> 64 * i + ofs == idx + (count - bitcount),
                    idx + count <= 512,
                    forall|j: int| i <= j < 8 ==> self.mask[j] == 0,
                    bitcount <= count,
            {
                assert(i < 8) by (nonlinear_arith)
                    requires
                        idx + (count - bitcount) < 512,
                        i == (idx + (count - bitcount)) / 64;
                let avail = usize::BITS as usize - ofs;
                let c = if bitcount > avail { avail } else { bitcount };
                let mask = if c >= usize::BITS as usize {
                    !0usize
                } else {
                    assert((1usize << c) > 0usize) by (bit_vector) requires c < 64usize;
                    ((1usize << c) - 1) << ofs
                };
                let old_self = Ghost(*self);
                self.mask[i] = mask;
                let oi = Ghost(i);
                let obc = Ghost(bitcount);
                let oofs = Ghost(ofs);
                bitcount -= c;
                ofs = 0;
                i += 1;
                assert(self@ =~= Set::range(idx as int, idx + (count - bitcount)));
            }
        }
    }

#[verifier::external_body]
    pub fn create_empty(&mut self)
{
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == 0
        {
            self.mask[i] = 0;
            i += 1;
        }
    }

#[verifier::external_body]
    pub fn create_full(&mut self)
{
        let mut i = 0;
        while i < 8
            invariant forall|j: int| 0 <= j < i ==> self.mask[j] == !0usize
        {
            self.mask[i] = !0usize;
            i += 1;
        }
    }

#[verifier::external_body]
    pub fn committed_size(&self, total: usize) -> usize
    {
        todo(); loop { }
    }

#[verifier::external_body]
    pub fn next_run(&self, idx: usize) -> (res: (usize, usize))
{
        // Starting at idx, scan to find the first bit.

        let mut i: usize = idx / usize::BITS as usize;
        let mut ofs: usize = idx % usize::BITS as usize;
        let mut mask: usize = 0;

        assert(ofs < 64) by (nonlinear_arith)
            requires ofs == idx % usize::BITS as usize;
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
                    assert((mask >> 1usize) != 0usize) by (bit_vector)
                        requires mask != 0usize, mask & 1 == 0usize;
                    assert(forall|m:u64,n:u64| #![auto] n < 64 ==> (m >> n) >> 1u64 == m >> add(n, 1u64)) by (bit_vector);
                    assert(forall|m: u64| #![auto] (m >> 63u64) >> 1u64 == 0u64) by (bit_vector);
                    mask = mask >> 1usize;
                    ofs += 1;
                }
                assert(mask & 1 == 1usize) by (bit_vector) requires mask & 1 != 0usize;
                break;
            }
            i += 1;
            ofs = 0;
        }

        if i >= COMMIT_MASK_FIELD_COUNT as usize {
            (COMMIT_MASK_BITS as usize, 0)
        } else {
            // Count 1 bits in this run
            let mut count: usize = 0;
            let next_idx = i * usize::BITS as usize + ofs;
            assert((i * 64 + ofs) % 64 == ofs) by (nonlinear_arith)
                requires ofs < 64;
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
                    count += 1;
                    mask = mask >> 1usize;

                    if (mask & 1) != 1 {
                        assert(mask & 1 == 0usize) by (bit_vector) requires mask & 1 != 1usize;
                        break;
                    }
                }

                if ((next_idx + count) % usize::BITS as usize) == 0 {
                    i += 1;
                    if i >= COMMIT_MASK_FIELD_COUNT as usize {
                        break;
                    }
                    mask = self.mask[i];
                    assert(forall|m: u64| m >> 0u64 == m) by (bit_vector);
                    ofs = 0;
                }

                if (mask & 1) != 1 {
                    break;
                }
            }

            assert forall |j: usize| next_idx <= j < next_idx + count implies self@.contains(j as int) by {
                self.lemma_view();
                assert(self@.contains(div64(j) * 64 + mod64(j)));
            };

            (next_idx, count)
        }
    }

#[verifier::external_body]
    pub fn is_empty(&self) -> (b: bool)
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
        return true;
    }

#[verifier::external_body]
    pub fn is_full(&self) -> (b: bool)
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
        return true;
    }
}

#[verifier::external_body]
pub proof fn set_int_range_commit_size(sid: SegmentId, mask: CommitMask)
    requires mask@.contains(0)
    ensures set_int_range(segment_start(sid), segment_start(sid) + COMMIT_SIZE) <= mask.bytes(sid)
{
    unimplemented!();
}


}
