#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::modes::*;
use vstd::*;
use vstd::cell::*;

use crate::types::*;

verus!{

pub closed spec fn flags0_is_reset(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags0_is_committed(u: u8) -> bool { u & 2 != 0 }
pub closed spec fn flags0_is_zero_init(u: u8) -> bool { u & 4 != 0 }

pub closed spec fn flags1_in_full(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags1_has_aligned(u: u8) -> bool { u & 2 != 0 }

pub closed spec fn flags2_is_zero(u: u8) -> bool { u & 1 != 0 }
pub closed spec fn flags2_retire_expire(u: u8) -> int { (u >> 1u8) as int }

impl PageInner {
    pub open spec fn is_reset(&self) -> bool { flags0_is_reset(self.flags0) }
    pub open spec fn is_committed(&self) -> bool { flags0_is_committed(self.flags0) }
    pub open spec fn is_zero_init(&self) -> bool { flags0_is_zero_init(self.flags0) }

    pub open spec fn in_full(&self) -> bool { flags1_in_full(self.flags1) }
    pub open spec fn has_aligned(&self) -> bool { flags1_has_aligned(self.flags1) }

    pub open spec fn is_zero(&self) -> bool { flags2_is_zero(self.flags2) }
    pub open spec fn retire_expire(&self) -> int { flags2_retire_expire(self.flags2) }

    // getters

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_is_reset(&self) -> (b: bool)
        ensures b == self.is_reset()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_is_committed(&self) -> (b: bool)
        ensures b == self.is_committed()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_is_zero_init(&self) -> (b: bool)
        ensures b == self.is_zero_init()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_in_full(&self) -> (b: bool)
        ensures b == self.in_full()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_has_aligned(&self) -> (b: bool)
        ensures b == self.has_aligned()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_is_zero(&self) -> (b: bool)
        ensures b == self.is_zero()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn get_retire_expire(&self) -> (u: u8)
        ensures u == self.retire_expire(),
            u <= 127
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn not_full_nor_aligned(&self) -> (b: bool)
        ensures b ==> (!self.in_full() && !self.has_aligned())
    {
        unimplemented!()
    }

    // setters

    #[verifier::external_body]
    #[inline(always)]
    pub fn set_retire_expire(&mut self, u: u8)
        requires u <= 127,
        ensures 
            *final(self) == (PageInner { flags2: final(self).flags2, .. *old(self) }),
            final(self).is_zero() == old(self).is_zero(),
            final(self).retire_expire() == u
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn set_is_reset(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags0: final(self).flags0, .. *old(self) }),
            final(self).is_reset() == b,
            final(self).is_committed() == old(self).is_committed(),
            final(self).is_zero_init() == old(self).is_zero_init()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn set_is_committed(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags0: final(self).flags0, .. *old(self) }),
            final(self).is_reset() == old(self).is_reset(),
            final(self).is_committed() == b,
            final(self).is_zero_init() == old(self).is_zero_init()
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn set_is_zero_init(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags0: final(self).flags0, .. *old(self) }),
            final(self).is_reset() == old(self).is_reset(),
            final(self).is_committed() == old(self).is_committed(),
            final(self).is_zero_init() == b
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn set_in_full(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags1: final(self).flags1, .. *old(self) }),
            final(self).has_aligned() == old(self).has_aligned(),
            final(self).in_full() == b
    {
        unimplemented!()
    }

    #[verifier::external_body]
    #[inline(always)]
    pub fn set_has_aligned(&mut self, b: bool)
        ensures *final(self) == (PageInner { flags1: final(self).flags1, .. *old(self) }),
            final(self).has_aligned() == b,
            final(self).in_full() == old(self).in_full()
    {
        unimplemented!()
    }

}

}
