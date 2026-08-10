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

    #[inline(always)]
#[verifier::external_body]
    pub fn get_is_reset(&self) -> (b: bool)
{
        (self.flags0 & 1) != 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn get_is_committed(&self) -> (b: bool)
{
        (self.flags0 & 2) != 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn get_is_zero_init(&self) -> (b: bool)
{
        (self.flags0 & 4) != 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn get_in_full(&self) -> (b: bool)
{
        (self.flags1 & 1) != 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn get_has_aligned(&self) -> (b: bool)
{
        (self.flags1 & 2) != 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn get_is_zero(&self) -> (b: bool)
{
        (self.flags2 & 1) != 0
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn get_retire_expire(&self) -> (u: u8)
{
        let x = self.flags2 >> 1u8;
        x
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn not_full_nor_aligned(&self) -> (b: bool)
{
        self.flags1 == 0
    }

    // setters

    #[inline(always)]
#[verifier::external_body]
    pub fn set_retire_expire(&mut self, u: u8)
{
        self.flags2 = (self.flags2 & 1) | (u << 1u8);
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn set_is_reset(&mut self, b: bool)
{
        self.flags0 = (self.flags0 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn set_is_committed(&mut self, b: bool)
{
        self.flags0 = (self.flags0 & !2) | ((if b { 1 } else { 0 }) << 1u8)

    }

    #[inline(always)]
#[verifier::external_body]
    pub fn set_is_zero_init(&mut self, b: bool)
{
        self.flags0 = (self.flags0 & !4) | ((if b { 1 } else { 0 }) << 2u8)

    }

    #[inline(always)]
#[verifier::external_body]
    pub fn set_in_full(&mut self, b: bool)
{
        self.flags1 = (self.flags1 & !1) | (if b { 1 } else { 0 })
    }

    #[inline(always)]
#[verifier::external_body]
    pub fn set_has_aligned(&mut self, b: bool)
{
        self.flags1 = (self.flags1 & !2) | ((if b { 1 } else { 0 }) << 1u8);
    }

}

}
