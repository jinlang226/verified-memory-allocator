#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::modes::*;
use vstd::*;
use vstd::cell::*;

use crate::types::*;

verus!{

pub closed spec fn flags0_is_reset(u: u8) -> bool { (u & 1u8) != 0 }
pub closed spec fn flags0_is_committed(u: u8) -> bool { (u & 2u8) != 0 }
pub closed spec fn flags0_is_zero_init(u: u8) -> bool { (u & 4u8) != 0 }

pub closed spec fn flags1_in_full(u: u8) -> bool { (u & 1u8) != 0 }
pub closed spec fn flags1_has_aligned(u: u8) -> bool { (u & 2u8) != 0 }

pub closed spec fn flags2_is_zero(u: u8) -> bool { (u & 1u8) != 0 }
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

    #[inline(always)]
    #[verus_verify]
    pub fn get_is_reset(&self) -> (b: bool)
        ensures b == self.is_reset(),
    {
        (self.flags0 & 1) != 0
    }

    #[inline(always)]
    pub fn get_is_committed(&self) -> (b: bool)
        ensures b == self.is_committed(),
    {
        (self.flags0 & 2) != 0
    }

    #[inline(always)]
    pub fn get_is_zero_init(&self) -> (b: bool)
        ensures b == self.is_zero_init(),
    {
        (self.flags0 & 4) != 0
    }

    #[inline(always)]
    #[verus_verify]
    pub fn get_in_full(&self) -> (b: bool)
        ensures b == self.in_full(),
    {
        (self.flags1 & 1) != 0
    }

    #[inline(always)]
    pub fn get_has_aligned(&self) -> (b: bool)
        ensures b == self.has_aligned(),
    {
        (self.flags1 & 2) != 0
    }

    #[inline(always)]
    pub fn get_is_zero(&self) -> (b: bool)
        ensures b == self.is_zero(),
    {
        (self.flags2 & 1) != 0
    }

    #[inline(always)]
    pub fn get_retire_expire(&self) -> (u: u8)
        ensures u as int == self.retire_expire(),
    {
        let x = self.flags2 >> 1u8;
        x
    }

    #[inline(always)]
    #[verus_verify]
    pub fn not_full_nor_aligned(&self) -> (b: bool)
        ensures
            b == (self.flags1 == 0),
            b ==> !self.in_full() && !self.has_aligned(),
    {
        proof {
            let f = self.flags1;
            if f == 0u8 {
                assert((f & 1u8) == 0u8) by(bit_vector)
                    requires f == 0u8;
                assert((f & 2u8) == 0u8) by(bit_vector)
                    requires f == 0u8;
            }
        }
        self.flags1 == 0
    }

    // setters

    #[inline(always)]
    pub fn set_retire_expire(&mut self, u: u8)
        ensures
            final(self).flags0 == old(self).flags0,
            final(self).flags1 == old(self).flags1,
            final(self).flags2 == ((old(self).flags2 & 1u8) | (u << 1u8)),
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).free == old(self).free,
            final(self).used == old(self).used,
            final(self).xblock_size == old(self).xblock_size,
            final(self).local_free == old(self).local_free,
            final(self).is_zero() == old(self).is_zero(),
    {
        let ghost old_flags2 = self.flags2;
        let ghost new_flags2 = (old_flags2 & 1u8) | (u << 1u8);
        proof {
            assert(((new_flags2 & 1u8) != 0) == ((old_flags2 & 1u8) != 0)) by(bit_vector)
                requires new_flags2 == ((old_flags2 & 1u8) | (u << 1u8));
        }
        self.flags2 = (self.flags2 & 1) | (u << 1u8);
    }

    #[inline(always)]
    pub fn set_is_reset(&mut self, b: bool)
        ensures
            final(self).flags0 == ((old(self).flags0 & !1u8) | if b { 1u8 } else { 0u8 }),
            final(self).flags1 == old(self).flags1,
            final(self).flags2 == old(self).flags2,
            final(self).is_reset() == b,
            final(self).is_committed() == old(self).is_committed(),
            final(self).is_zero_init() == old(self).is_zero_init(),
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).free == old(self).free,
            final(self).used == old(self).used,
            final(self).xblock_size == old(self).xblock_size,
            final(self).local_free == old(self).local_free,
    {
        let ghost old_flags0 = self.flags0;
        let ghost new_flags0 = (old_flags0 & !1u8) | if b { 1u8 } else { 0u8 };
        proof {
            if b {
                assert((new_flags0 & 1u8) != 0) by(bit_vector)
                    requires new_flags0 == ((old_flags0 & !1u8) | 1u8);
            } else {
                assert((new_flags0 & 1u8) == 0u8) by(bit_vector)
                    requires new_flags0 == ((old_flags0 & !1u8) | 0u8);
            }
            assert(((new_flags0 & 2u8) != 0) == ((old_flags0 & 2u8) != 0)) by(bit_vector)
                requires new_flags0 == ((old_flags0 & !1u8) | if b { 1u8 } else { 0u8 });
            assert(((new_flags0 & 4u8) != 0) == ((old_flags0 & 4u8) != 0)) by(bit_vector)
                requires new_flags0 == ((old_flags0 & !1u8) | if b { 1u8 } else { 0u8 });
        }
        self.flags0 = (self.flags0 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
    pub fn set_is_committed(&mut self, b: bool)
        ensures
            final(self).flags0 == ((old(self).flags0 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8)),
            final(self).flags1 == old(self).flags1,
            final(self).flags2 == old(self).flags2,
            final(self).is_reset() == old(self).is_reset(),
            final(self).is_committed() == b,
            final(self).is_zero_init() == old(self).is_zero_init(),
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).free == old(self).free,
            final(self).used == old(self).used,
            final(self).xblock_size == old(self).xblock_size,
            final(self).local_free == old(self).local_free,
    {
        let ghost old_flags0 = self.flags0;
        let ghost new_flags0 = (old_flags0 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8);
        proof {
            assert(((new_flags0 & 1u8) != 0) == ((old_flags0 & 1u8) != 0)) by(bit_vector)
                requires new_flags0 == ((old_flags0 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8));
            if b {
                assert((new_flags0 & 2u8) != 0) by(bit_vector)
                    requires new_flags0 == ((old_flags0 & !2u8) | (1u8 << 1u8));
            } else {
                assert((new_flags0 & 2u8) == 0u8) by(bit_vector)
                    requires new_flags0 == ((old_flags0 & !2u8) | (0u8 << 1u8));
            }
            assert(((new_flags0 & 4u8) != 0) == ((old_flags0 & 4u8) != 0)) by(bit_vector)
                requires new_flags0 == ((old_flags0 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8));
        }
        self.flags0 = (self.flags0 & !2) | ((if b { 1 } else { 0 }) << 1u8)

    }

    #[inline(always)]
    pub fn set_is_zero_init(&mut self, b: bool)
        ensures
            final(self).flags0 == ((old(self).flags0 & !4u8) | ((if b { 1u8 } else { 0u8 }) << 2u8)),
            final(self).flags1 == old(self).flags1,
            final(self).flags2 == old(self).flags2,
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).free == old(self).free,
            final(self).used == old(self).used,
            final(self).xblock_size == old(self).xblock_size,
            final(self).local_free == old(self).local_free,
            final(self).is_reset() == old(self).is_reset(),
            final(self).is_committed() == old(self).is_committed(),
            final(self).is_zero_init() == b,
    {
        let ghost old_flags0 = self.flags0;
        let ghost new_flags0 = (old_flags0 & !4u8) | ((if b { 1u8 } else { 0u8 }) << 2u8);
        proof {
            assert(((new_flags0 & 1u8) != 0) == ((old_flags0 & 1u8) != 0)) by(bit_vector)
                requires new_flags0 == ((old_flags0 & !4u8) | ((if b { 1u8 } else { 0u8 }) << 2u8));
            assert(((new_flags0 & 2u8) != 0) == ((old_flags0 & 2u8) != 0)) by(bit_vector)
                requires new_flags0 == ((old_flags0 & !4u8) | ((if b { 1u8 } else { 0u8 }) << 2u8));
            if b {
                assert((new_flags0 & 4u8) != 0) by(bit_vector)
                    requires new_flags0 == ((old_flags0 & !4u8) | (1u8 << 2u8));
            } else {
                assert((new_flags0 & 4u8) == 0u8) by(bit_vector)
                    requires new_flags0 == ((old_flags0 & !4u8) | (0u8 << 2u8));
            }
        }
        self.flags0 = (self.flags0 & !4) | ((if b { 1 } else { 0 }) << 2u8)

    }

    #[inline(always)]
    pub fn set_in_full(&mut self, b: bool)
        ensures
            final(self).flags0 == old(self).flags0,
            final(self).flags1 == ((old(self).flags1 & !1u8) | if b { 1u8 } else { 0u8 }),
            final(self).flags2 == old(self).flags2,
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).free == old(self).free,
            final(self).used == old(self).used,
            final(self).xblock_size == old(self).xblock_size,
            final(self).local_free == old(self).local_free,
            final(self).in_full() == b,
            final(self).has_aligned() == old(self).has_aligned(),
    {
        let ghost old_flags1 = self.flags1;
        let ghost new_flags1 = (old_flags1 & !1u8) | if b { 1u8 } else { 0u8 };
        proof {
            if b {
                assert((new_flags1 & 1u8) != 0) by(bit_vector)
                    requires new_flags1 == ((old_flags1 & !1u8) | 1u8);
            } else {
                assert((new_flags1 & 1u8) == 0u8) by(bit_vector)
                    requires new_flags1 == ((old_flags1 & !1u8) | 0u8);
            }
            assert(((new_flags1 & 2u8) != 0) == ((old_flags1 & 2u8) != 0)) by(bit_vector)
                requires new_flags1 == ((old_flags1 & !1u8) | if b { 1u8 } else { 0u8 });
        }
        self.flags1 = (self.flags1 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
    pub fn set_has_aligned(&mut self, b: bool)
        ensures
            final(self).flags0 == old(self).flags0,
            final(self).flags1 == ((old(self).flags1 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8)),
            final(self).flags2 == old(self).flags2,
            final(self).capacity == old(self).capacity,
            final(self).reserved == old(self).reserved,
            final(self).free == old(self).free,
            final(self).used == old(self).used,
            final(self).xblock_size == old(self).xblock_size,
            final(self).local_free == old(self).local_free,
            final(self).in_full() == old(self).in_full(),
            final(self).has_aligned() == b,
    {
        let ghost old_flags1 = self.flags1;
        let ghost new_flags1 = (old_flags1 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8);
        proof {
            assert(((new_flags1 & 1u8) != 0) == ((old_flags1 & 1u8) != 0)) by(bit_vector)
                requires new_flags1 == ((old_flags1 & !2u8) | ((if b { 1u8 } else { 0u8 }) << 1u8));
            if b {
                assert((new_flags1 & 2u8) != 0) by(bit_vector)
                    requires new_flags1 == ((old_flags1 & !2u8) | (1u8 << 1u8));
            } else {
                assert((new_flags1 & 2u8) == 0u8) by(bit_vector)
                    requires new_flags1 == ((old_flags1 & !2u8) | (0u8 << 1u8));
            }
        }
        self.flags1 = (self.flags1 & !2) | ((if b { 1 } else { 0 }) << 1u8);
    }

}

}
