#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::assert_by_contradiction;

verus!{

#[verifier::external_body]
// TODO: This belongs in set_lib
proof fn singleton_set_unique_elt<T>(s: Set<T>, a:T, b:T)
    requires
        s.len() == 1,
        s.contains(a),
        s.contains(b),
    ensures
        a == b
{
    unimplemented!()
}

#[verifier::external_body]
proof fn set_mismatch(s1:Set<nat>, s2:Set<nat>, missing:nat)
    requires
        s1.len() == s2.len(),
        forall |elt| s2.contains(elt) ==> s1.contains(elt),
        s1.contains(missing),
        !s2.contains(missing),
    ensures
        false
{
    unimplemented!()
}

/* TODO: These next two should be derived from the set_int_range and lemma_int_range in 
 *       set_lib.rs, but it's surprisingly painful to do so */

/// Creates a finite set of nats in the range [lo, hi).
pub open spec fn set_nat_range(lo: nat, hi: nat) -> Set<nat> {
    Set::range(lo, hi)
}

#[verifier::external_body]
/// If a set solely contains nats in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_nat_range(lo: nat, hi: nat)
    requires
        lo <= hi,
    ensures
        set_nat_range(lo, hi).len() == hi - lo
{
    unimplemented!()
}


#[verifier::external_body]
proof fn nat_set_size(s:Set<nat>, bound:nat)
    requires
        forall |i: nat| (0 <= i < bound <==> s.contains(i)),
    ensures
        s.len() == bound
{
    unimplemented!()
}

        

#[verifier::external_body]
pub proof fn pigeonhole_missing_idx_implies_double_helper(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
    prev_vals: Set<nat>,
    k: nat,
) -> (dup2: nat)
    requires
        len >= 2,
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
        0 <= k < len,
        prev_vals.len() == k,
        //forall |j| 0 <= j < k ==> #[trigger] prev_vals.contains(m[j]),
        forall |elt| #[trigger] prev_vals.contains(elt) ==> exists |j| 0 <= j < k && m[j] == elt,
    ensures 
        m.dom().contains(dup2),
        exists |dup1| #![auto] dup1 != dup2 && m.dom().contains(dup1) && 0 <= dup1 < len && m[dup1] == m[dup2]
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn pigeonhole_missing_idx_implies_double(
    m: Map<nat, nat>,
    missing: nat,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len <==> m.dom().contains(i)),
        forall |i: nat| (#[trigger] m.dom().contains(i) ==> (
            0 <= m[i] < len && m[i] != missing
        )),
        0 <= missing < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    unimplemented!()
}

#[verifier::external_body]
pub proof fn pigeonhole_too_many_elements_implies_double(
    m: Map<nat, nat>,
    len: nat,
) -> (r: (nat, nat))
    requires
        forall |i: nat| (0 <= i < len + 1 <==> m.dom().contains(i)),
        forall |i: nat| #[trigger] m.dom().contains(i) ==> 0 <= m[i] < len,
    ensures ({ let (i, j) = r;
        i != j
          && m.dom().contains(i)
          && m.dom().contains(j)
          && m[i] == m[j]
    })
{
    unimplemented!()
}

}
