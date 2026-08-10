use vstd::prelude::*;
use vstd::assert_by_contradiction;
use vstd::calc;
use vstd::std_specs::bits::u64_leading_zeros;
use crate::config::*;

//fn main() {}

// BLOCK SIZE BINS
//
// For a given allocation size, what bin does it fit in?
// Based off of logic in mi_bin
//
// First  compute wsize = ceil(size / (word size))
//
// Now, each wsize up to 8 gets its own bin.
// After that, each number is rounded up to a number such that
// all its 1s in the binary representation are of the 3 most significant
//
//
// wsize      bin size                        bin #
//
// 0, 1       1                               1
// 2          2                               2
// 3          3                               3
// 4          4                               4
// 5          5                               5
// 6          6                               6
// 7          7                               7
// 8          8                               8
//
// 9, 10      10      (10 = 1010)             9
// 11, 12     12      (12 = 1100)             10
// 13, 14     14      (14 = 1010)             11
// 15, 16     16      (16 = 10000)            12
//
// 17-20      20      (20 = 10100)            13
// 21-24      24      (24 = 11000)            14
// 25-28      28      (28 = 11100)            15
// 29-32      32      (32 = 100000)           16
//
// ...
//
// This goes up to MEDIUM_OBJ_WSIZE_MAX, and after that, everything goes in the "huge bin"
// which has bin # BIN_HUGE.
//
// The bin # should fit in a u8.
//
// -----------------------------------------------------------------------------------
//
// SLICE BINS (SBINS)
//
// When we allocate a page spanning a given # of slices, the '# of slices' also goes
// into a bin. To keep things straight, I'm going to call this binning method
// "sbins", while the above is just normal "bins".
//
// The algorithm here is a similar, though for some reason size 8 is lumped in with
// the bin [9, 10], and everything from that point is shifted down an index.
//
// slices     bin size                        bin #
//
// 0          0                               0         (unused)
// 1          1                               1
// 2          2                               2
// 3          3                               3
// 4          4                               4
// 5          5                               5
// 6          6                               6
// 7          7                               7

// 8, 9, 10   10      (10 = 1010)             8

// 11, 12     12      (12 = 1100)             9
// 13, 14     14      (14 = 1010)             10
// 15, 16     16      (16 = 10000)            11
//
// 17-20      20      (20 = 10100)            11
// 21-24      24      (24 = 11000)            13
// 25-28      28      (28 = 11100)            14
// 29-32      32      (32 = 100000)           15
//
// ...
//
// 449-512    512                             31
//
// The max # of slices is SLICES_PER_SEGMENT (512) which goes in bin 31.

verus!{


// TODO: Pulled in constants to make this a standalone file
/*
global size_of usize == 8;

// Log of the (pointer-size in bytes) // TODO make configurable
pub const INTPTR_SHIFT: u64 = 3;
pub const INTPTR_SIZE: u64 = 8;

// Log of the size of a 'slice'
pub const SLICE_SHIFT: u64 = 13 + INTPTR_SHIFT;

// Size of a slice
pub const SLICE_SIZE: u64 = 65536; //(1 << SLICE_SHIFT);

// Log of the size of a 'segment'
pub const SEGMENT_SHIFT: u64 = 9 + SLICE_SHIFT;

// Log of the size of a 'segment'
pub const SEGMENT_SIZE: u64 = (1 << SEGMENT_SHIFT);

// Log of the size of a 'segment'
pub const SEGMENT_ALIGN: u64 = SEGMENT_SIZE;

// Size of a 'segment'
pub const SLICES_PER_SEGMENT: u64 = (SEGMENT_SIZE / SLICE_SIZE);

pub const BIN_HUGE: u64 = 73;

pub const PAGES_DIRECT: usize = SMALL_WSIZE_MAX + 1;
pub const SMALL_SIZE_MAX: usize = SMALL_WSIZE_MAX * INTPTR_SIZE as usize;
pub const SMALL_WSIZE_MAX: usize = 128;

pub const SEGMENT_BIN_MAX: usize = 31;

// maximum alloc size the user is allowed to request
// note: mimalloc use ptrdiff_t max here
pub const MAX_ALLOC_SIZE: usize = isize::MAX as usize;
*/

pub open spec fn valid_bin_idx(bin_idx: int) -> bool {
    1 <= bin_idx <= BIN_HUGE
}

#[verifier::opaque]
pub open spec fn size_of_bin(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if 1 <= bin_idx <= 8 {
       (usize::BITS / 8) as nat * (bin_idx as nat)
    } else if bin_idx == BIN_HUGE {
        // the "real" upper bound on this bucket is infinite
        // the lemmas on bin sizes assume each bin has a lower bound and upper bound
        // so we pretend this is the upper bound

        8 * (524288 + 1)
        //8 * (MEDIUM_OBJ_WSIZE_MAX as nat + 1)
    } else {
        let group = (bin_idx - 9) / 4;
        let inner = (bin_idx - 9) % 4;

        ((usize::BITS / 8) * (inner + 5) * pow2(group + 1)) as nat
    }
}

#[verifier::external_body]
proof fn mod8(x:int, y:int) by (nonlinear_arith)
    requires x == 8 * y,
    ensures  x % 8 == 0,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn size_of_bin_mult_word_size(bin_idx: int)
    ensures size_of_bin(bin_idx) % 8 == 0
{
    unimplemented!();
}

// spec equivalent of bin
pub open spec fn smallest_bin_fitting_size(size: int) -> int {
    let bytes_per_word = (usize::BITS / 8) as int;
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize
    } else if wsize > 524288 {
        BIN_HUGE as int
    } else {
        let w = (wsize - 1) as u64;
        //let lz = w.leading_zeros();
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let shifted = (w >> (b - 2) as u64) as u8;
        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;
        bin_idx
    }
}

pub open spec fn pfd_lower(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    if bin_idx == 1 {
        0
    } else {
        size_of_bin(bin_idx - 1) / INTPTR_SIZE as nat + 1
    }
}

pub open spec fn pfd_upper(bin_idx: int) -> nat
    recommends valid_bin_idx(bin_idx)
{
    size_of_bin(bin_idx) / INTPTR_SIZE as nat
}

// TODO: The assertions in this lemma are duplicated in init.rs
#[verifier::external_body]
pub proof fn lemma_bin_sizes_constants()
    ensures
        size_of_bin(1) == 8, size_of_bin(1) / 8 == 1,
        size_of_bin(2) == 16, size_of_bin(2) / 8 == 2,
        size_of_bin(3) == 24, size_of_bin(3) / 8 == 3,
        size_of_bin(4) == 32, size_of_bin(4) / 8 == 4,
        size_of_bin(5) == 40, size_of_bin(5) / 8 == 5,
        size_of_bin(6) == 48, size_of_bin(6) / 8 == 6,
        size_of_bin(7) == 56, size_of_bin(7) / 8 == 7,
        size_of_bin(8) == 64, size_of_bin(8) / 8 == 8,
        size_of_bin(9) == 80, size_of_bin(9) / 8 == 10,
        size_of_bin(10) == 96, size_of_bin(10) / 8 == 12,
        size_of_bin(11) == 112, size_of_bin(11) / 8 == 14,
        size_of_bin(12) == 128, size_of_bin(12) / 8 == 16,
        size_of_bin(13) == 160, size_of_bin(13) / 8 == 20,
        size_of_bin(14) == 192, size_of_bin(14) / 8 == 24,
        size_of_bin(15) == 224, size_of_bin(15) / 8 == 28,
        size_of_bin(16) == 256, size_of_bin(16) / 8 == 32,
        size_of_bin(17) == 320, size_of_bin(17) / 8 == 40,
        size_of_bin(18) == 384, size_of_bin(18) / 8 == 48,
        size_of_bin(19) == 448, size_of_bin(19) / 8 == 56,
        size_of_bin(20) == 512, size_of_bin(20) / 8 == 64,
        size_of_bin(21) == 640, size_of_bin(21) / 8 == 80,
        size_of_bin(22) == 768, size_of_bin(22) / 8 == 96,
        size_of_bin(23) == 896, size_of_bin(23) / 8 == 112,
        size_of_bin(24) == 1024, size_of_bin(24) / 8 == 128,
        size_of_bin(25) == 1280, size_of_bin(25) / 8 == 160,
        size_of_bin(26) == 1536, size_of_bin(26) / 8 == 192,
        size_of_bin(27) == 1792, size_of_bin(27) / 8 == 224,
        size_of_bin(28) == 2048, size_of_bin(28) / 8 == 256,
        size_of_bin(29) == 2560, size_of_bin(29) / 8 == 320,
        size_of_bin(30) == 3072, size_of_bin(30) / 8 == 384,
        size_of_bin(31) == 3584, size_of_bin(31) / 8 == 448,
        size_of_bin(32) == 4096, size_of_bin(32) / 8 == 512,
        size_of_bin(33) == 5120, size_of_bin(33) / 8 == 640,
        size_of_bin(34) == 6144, size_of_bin(34) / 8 == 768,
        size_of_bin(35) == 7168, size_of_bin(35) / 8 == 896,
        size_of_bin(36) == 8192, size_of_bin(36) / 8 == 1024,
        size_of_bin(37) == 10240, size_of_bin(37) / 8 == 1280,
        size_of_bin(38) == 12288, size_of_bin(38) / 8 == 1536,
        size_of_bin(39) == 14336, size_of_bin(39) / 8 == 1792,
        size_of_bin(40) == 16384, size_of_bin(40) / 8 == 2048,
        size_of_bin(41) == 20480, size_of_bin(41) / 8 == 2560,
        size_of_bin(42) == 24576, size_of_bin(42) / 8 == 3072,
        size_of_bin(43) == 28672, size_of_bin(43) / 8 == 3584,
        size_of_bin(44) == 32768, size_of_bin(44) / 8 == 4096,
        size_of_bin(45) == 40960, size_of_bin(45) / 8 == 5120,
        size_of_bin(46) == 49152, size_of_bin(46) / 8 == 6144,
        size_of_bin(47) == 57344, size_of_bin(47) / 8 == 7168,
        size_of_bin(48) == 65536, size_of_bin(48) / 8 == 8192,
        size_of_bin(49) == 81920, size_of_bin(49) / 8 == 10240,
        size_of_bin(50) == 98304, size_of_bin(50) / 8 == 12288,
        size_of_bin(51) == 114688, size_of_bin(51) / 8 == 14336,
        size_of_bin(52) == 131072, size_of_bin(52) / 8 == 16384,
        size_of_bin(53) == 163840, size_of_bin(53) / 8 == 20480,
        size_of_bin(54) == 196608, size_of_bin(54) / 8 == 24576,
        size_of_bin(55) == 229376, size_of_bin(55) / 8 == 28672,
        size_of_bin(56) == 262144, size_of_bin(56) / 8 == 32768,
        size_of_bin(57) == 327680, size_of_bin(57) / 8 == 40960,
        size_of_bin(58) == 393216, size_of_bin(58) / 8 == 49152,
        size_of_bin(59) == 458752, size_of_bin(59) / 8 == 57344,
        size_of_bin(60) == 524288, size_of_bin(60) / 8 == 65536,
        size_of_bin(61) == 655360, size_of_bin(61) / 8 == 81920,
        size_of_bin(62) == 786432, size_of_bin(62) / 8 == 98304,
        size_of_bin(63) == 917504, size_of_bin(63) / 8 == 114688,
        size_of_bin(64) == 1048576, size_of_bin(64) / 8 == 131072,
        size_of_bin(65) == 1310720, size_of_bin(65) / 8 == 163840,
        size_of_bin(66) == 1572864, size_of_bin(66) / 8 == 196608,
        size_of_bin(67) == 1835008, size_of_bin(67) / 8 == 229376,
        size_of_bin(68) == 2097152, size_of_bin(68) / 8 == 262144,
        size_of_bin(69) == 2621440, size_of_bin(69) / 8 == 327680,
        size_of_bin(70) == 3145728, size_of_bin(70) / 8 == 393216,
        size_of_bin(71) == 3670016, size_of_bin(71) / 8 == 458752,
        size_of_bin(72) == 4194304, size_of_bin(72) / 8 == 524288,
        size_of_bin(73) == 4194312, size_of_bin(73) / 8 == 524289,
{
    unimplemented!();
}


/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize:int) -> bool
{
    valid_bin_idx(bin_idx) &&
    !(pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)) &&
    0 <= wsize <= 128
    ==>
    smallest_bin_fitting_size(wsize * INTPTR_SIZE) != bin_idx
}

spec fn check_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize_start:int, wsize_end:int) -> bool
    decreases wsize_end - wsize_start,
{
   if wsize_start >= wsize_end {
       true
   } else {
          property_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start)
       && check_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start + 1, wsize_end)
   }
}

#[verifier::external_body]
proof fn result_idx_out_of_range_has_different_bin_size(bin_idx: int, wsize_start:int, wsize_end:int)
    ensures
        check_idx_out_of_range_has_different_bin_size(bin_idx, wsize_start, wsize_end) ==>
            (forall |wsize| wsize_start <= wsize < wsize_end ==>
                 property_idx_out_of_range_has_different_bin_size(bin_idx, wsize)),
    decreases wsize_end - wsize_start,
{
    unimplemented!();
}

spec fn check2_idx_out_of_range_has_different_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
    if bin_idx_start >= bin_idx_end {
        true
    } else {
        check_idx_out_of_range_has_different_bin_size(bin_idx_start, wsize_start, wsize_end)
        && check2_idx_out_of_range_has_different_bin_size(bin_idx_start + 1, bin_idx_end, wsize_start, wsize_end)
    }
}

#[verifier::external_body]
proof fn result2_idx_out_of_range_has_different_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int)
    ensures
        check2_idx_out_of_range_has_different_bin_size(bin_idx_start, bin_idx_end, wsize_start, wsize_end) ==>
            (forall |bin_idx,wsize| bin_idx_start <= bin_idx < bin_idx_end && wsize_start <= wsize < wsize_end ==>
                     property_idx_out_of_range_has_different_bin_size(bin_idx, wsize)),
    decreases bin_idx_end - bin_idx_start,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn different_bin_size(bin_idx1: int, bin_idx2: int)
    requires
        valid_bin_idx(bin_idx1),
        valid_bin_idx(bin_idx2),
        bin_idx1 != bin_idx2,
    ensures
        size_of_bin(bin_idx1) != size_of_bin(bin_idx2)
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn idx_out_of_range_has_different_bin_size(bin_idx: int, wsize: int)
    requires
        valid_bin_idx(bin_idx),
        !(pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)),
        0 <= wsize <= 128,
    ensures
        smallest_bin_fitting_size(wsize * INTPTR_SIZE) != bin_idx
{
    unimplemented!();
}

/********************************************************
 * TODO: All of these should be standard library proofs
 ********************************************************/

#[verifier::external_body]
proof fn div2(x: u64, y:int) by (nonlinear_arith)
    requires y > 0,
    ensures x as int / (y * 2) == (x as int / y) / 2,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn lemma_div_is_ordered(x: int, y: int, z: int) by (nonlinear_arith)
    requires
        x <= y,
        0 < z,
    ensures x / z <= y / z
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn lemma_div_by_multiple(b: int, d: int) by (nonlinear_arith)
    requires
        0 <= b,
        0 < d,
    ensures
        (b * d) / d == b
{
    unimplemented!();
}

#[verifier::external_body]
proof fn mul_assoc(x: nat, y: nat, z: nat) by (nonlinear_arith)
    ensures (x * y) * z == y * (x * z)
{
    unimplemented!();
}

#[verifier::external_body]
proof fn mul_ordering(x: nat, y: nat, z: nat) by (nonlinear_arith)
    requires
        0 < x && 1 < y && 0 < z,
        x * y == z,
    ensures
        x < z,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn pow2_positive(e:int)
    ensures pow2(e) > 0,
    decreases e,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn pow2_adds(e1:nat, e2:nat)
    ensures
        pow2(e1 as int) * pow2(e2 as int) == pow2((e1 + e2) as int),
    decreases e1,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn pow2_subtracts(e1:nat, e2:nat)
    requires e1 <= e2,
    ensures
        pow2(e2 as int) / pow2(e1 as int) == pow2((e2 - e1) as int),
{
    unimplemented!();
}

#[verifier::external_body]
proof fn pow2_properties()
    ensures
        forall |e:int| pow2(e) > 0,
        forall |e:int| e > 0 ==> #[trigger] pow2(e) / 2 == pow2(e - 1),
        forall |e1, e2| 0 <= e1 < e2 ==> pow2(e1) < pow2(e2),
        forall |e1, e2| 0 <= e1 && 0 <= e2 ==> pow2(e1) * pow2(e2) == #[trigger] pow2(e1 + e2),
        forall |e1, e2| 0 <= e1 <= e2 ==> pow2(e2) / pow2(e1) == #[trigger] pow2(e2 - e1),
{
    unimplemented!();
}

#[verifier::external_body]
proof fn shift_is_div(x:u64, shift:u64)
    requires 0 <= shift < 64,
    ensures x >> shift == x as nat / pow2(shift as int),
    decreases shift,
{
    unimplemented!();
}

/********************************************************
 * END: All of these should be standard library proofs
 ********************************************************/

#[verifier::external_body]
proof fn leading_zeros_powers_of_2(i: u64, exp: nat)
    requires
        i == pow2(exp as int),
        exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
    decreases i,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn leading_zeros_between_powers_of_2(i: u64, exp: nat)
    requires
        pow2(exp as int) <= i < pow2((exp + 1) as int),
        1 <= exp < 64
    ensures
        u64_leading_zeros(i) == 64 - exp - 1,
    decreases exp,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn log2(i:u64) -> (e:nat)
    requires i >= 1,
    ensures pow2(e as int) <= i < pow2((e+1) as int),
    decreases i,
{
    unimplemented!();
}


/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_idx_in_range_has_bin_size(bin_idx: int, wsize:int) -> bool
{
    valid_bin_idx(bin_idx) &&
    (pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx))
    ==>
    smallest_bin_fitting_size(wsize * INTPTR_SIZE) == bin_idx
}

spec fn check_idx_in_range_has_bin_size(bin_idx: int, wsize_start:int, wsize_end:int) -> bool
    decreases wsize_end - wsize_start,
{
   if wsize_start >= wsize_end {
       true
   } else {
          property_idx_in_range_has_bin_size(bin_idx, wsize_start)
       && check_idx_in_range_has_bin_size(bin_idx, wsize_start + 1, wsize_end)
   }
}

#[verifier::external_body]
proof fn result_idx_in_range_has_bin_size(bin_idx: int, wsize_start:int, wsize_end:int)
    ensures
        check_idx_in_range_has_bin_size(bin_idx, wsize_start, wsize_end) ==>
            (forall |wsize| wsize_start <= wsize < wsize_end ==>
                 property_idx_in_range_has_bin_size(bin_idx, wsize)),
    decreases wsize_end - wsize_start,
{
    unimplemented!();
}

spec fn check2_idx_in_range_has_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
    if bin_idx_start >= bin_idx_end {
        true
    } else {
        check_idx_in_range_has_bin_size(bin_idx_start, wsize_start, wsize_end)
        && check2_idx_in_range_has_bin_size(bin_idx_start + 1, bin_idx_end, wsize_start, wsize_end)
    }
}

#[verifier::external_body]
proof fn result2_idx_in_range_has_bin_size(bin_idx_start: int, bin_idx_end: int, wsize_start:int, wsize_end:int)
    ensures
        check2_idx_in_range_has_bin_size(bin_idx_start, bin_idx_end, wsize_start, wsize_end) ==>
            (forall |bin_idx,wsize| bin_idx_start <= bin_idx < bin_idx_end && wsize_start <= wsize < wsize_end ==>
                     property_idx_in_range_has_bin_size(bin_idx, wsize)),
    decreases bin_idx_end - bin_idx_start,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn idx_in_range_has_bin_size(bin_idx: int, wsize: int)
    requires
        valid_bin_idx(bin_idx),
        (pfd_lower(bin_idx) <= wsize <= pfd_upper(bin_idx)),
        wsize <= 128,
    ensures
        smallest_bin_fitting_size(wsize * INTPTR_SIZE) == bin_idx
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn pfd_lower_le_upper(bin_idx: int)
    requires valid_bin_idx(bin_idx),
    ensures pfd_lower(bin_idx) <= pfd_upper(bin_idx)
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn size_of_bin_bounds(b: int)
    requires valid_bin_idx(b),
    ensures size_of_bin(b) >= INTPTR_SIZE,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn size_of_bin_bounds_not_huge(b: int)
    requires valid_bin_idx(b), b != BIN_HUGE,
    ensures 8 <= size_of_bin(b) <= 4194304
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn out_of_small_range(bin_idx: int)
    requires valid_bin_idx(bin_idx),
        size_of_bin(bin_idx) > SMALL_SIZE_MAX,
    ensures
        pfd_lower(bin_idx) >= PAGES_DIRECT,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn size_le_8_implies_idx_eq_1(bin_idx: int)
    requires valid_bin_idx(bin_idx), size_of_bin(bin_idx) / 8 <= 1,
    ensures bin_idx == 1,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn size_gt_8_implies_idx_gt_1(bin_idx: int)
    requires valid_bin_idx(bin_idx), size_of_bin(bin_idx) / 8 > 1,
    ensures bin_idx > 1,
{
    unimplemented!();
}


pub open spec fn pow2(i: int) -> nat
    decreases i
{
    if i <= 0 {
        1
    } else {
        pow2(i - 1) * 2
    }
}

/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_bounds_for_smallest_bitting_size(size:int) -> bool
{
    valid_bin_idx(smallest_bin_fitting_size(size)) &&
    size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bounds_for_smallest_bitting_size(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_bounds_for_smallest_bitting_size(size_start)
       && check_bounds_for_smallest_bitting_size(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_bounds_for_smallest_bitting_size(size_start:int, size_end:int)
    ensures
        check_bounds_for_smallest_bitting_size(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_bounds_for_smallest_bitting_size(size)),
    decreases size_end - size_start,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn bounds_for_smallest_bin_fitting_size(size: int)
    requires 0 <= size <= 128 * 8,
    ensures
        valid_bin_idx(smallest_bin_fitting_size(size)),
        size_of_bin(smallest_bin_fitting_size(size)) >= size,
{
    unimplemented!();
}

/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_smallest_bin_fitting_size_size_of_bin(bin_idx:int) -> bool
{
    smallest_bin_fitting_size(size_of_bin(bin_idx) as int) == bin_idx
}

spec fn check_smallest_bin_fitting_size_size_of_bin(bin_idx_start:int, bin_idx_end:int) -> bool
    decreases bin_idx_end - bin_idx_start,
{
   if bin_idx_start >= bin_idx_end {
       true
   } else {
          property_smallest_bin_fitting_size_size_of_bin(bin_idx_start)
       && check_smallest_bin_fitting_size_size_of_bin(bin_idx_start + 1, bin_idx_end)
   }
}

#[verifier::external_body]
proof fn result_smallest_bin_fitting_size_size_of_bin(bin_idx_start:int, bin_idx_end:int)
    ensures
        check_smallest_bin_fitting_size_size_of_bin(bin_idx_start, bin_idx_end) ==>
            (forall |bin_idx| bin_idx_start <= bin_idx < bin_idx_end ==>
                 property_smallest_bin_fitting_size_size_of_bin(bin_idx)),
    decreases bin_idx_end - bin_idx_start,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn smallest_bin_fitting_size_size_of_bin(bin_idx: int)
    requires valid_bin_idx(bin_idx),
    ensures smallest_bin_fitting_size(size_of_bin(bin_idx) as int) == bin_idx,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn leading_zeros_monotonic(w:u64)
    ensures
       forall |x:u64| x < w ==> u64_leading_zeros(w) <= u64_leading_zeros(x),
    decreases w,
{
    unimplemented!();
}

#[verifier::external_body]
proof fn leading_zeros_between(lo:u64, mid:u64, hi:u64)
    requires lo <= mid < hi,
    ensures u64_leading_zeros(lo) >= u64_leading_zeros(mid) >= u64_leading_zeros(hi),
{
    unimplemented!();
}

/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_bin(size:int) -> bool
{
    131072 >= size_of_bin(smallest_bin_fitting_size(size)) >= size
}

spec fn check_bin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start + 8,
{
   if size_start >= size_end {
       true
   } else {
          property_bin(size_start)
       && check_bin(size_start + 8, size_end)
   }
}

spec fn id(i:int) -> bool { true }

#[verifier::external_body]
proof fn result_bin(size_start:int, size_end:int)
    requires size_start % 8 == 0,
    ensures
        check_bin(size_start, size_end) ==>
            (forall |size: int| size_start <= size < size_end && size % 8 == 0 ==>
                 #[trigger] id(size) && property_bin(size)),
    decreases size_end - size_start + 8,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn bin_size_result(size: usize)
    requires
        size <= 131072, //  == MEDIUM_OBJ_SIZE_MAX
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    ensures
        131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
    decreases 8 - ((size + 7) % 8)
{
    unimplemented!();
}

// The "proof" is below is broken into chunks,
// so (a) we don't exceed the interpreter's stack limit,
// and (b) because the interpreter time seems to scale
// non-linearly with recursion depth
#[verifier::external_body]
pub proof fn bin_size_result_mul8(size: usize)
    requires
        size % 8 == 0,
        size <= 131072, //  == MEDIUM_OBJ_SIZE_MAX
        valid_bin_idx(smallest_bin_fitting_size(size as int)),
    ensures
        131072 >= size_of_bin(smallest_bin_fitting_size(size as int) as int) >= size,
{
    unimplemented!();
}

// Used to compute a bin for a given size
#[verifier::external_body]
pub fn bin(size: usize) -> (bin_idx: u8)
{
    let bytes_per_word = usize::BITS as usize / 8;
    assert(usize::BITS / 8 == 8) by (nonlinear_arith);
    let wsize = (size + bytes_per_word - 1) / bytes_per_word;
    assert(((wsize * 8) + 8 - 1) / 8 == wsize) by (nonlinear_arith);

    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize as u8
    } else {
        assert(9 <= wsize < 131073);
        let w: u64 = (wsize - 1) as u64;
        assert(8 <= w < 131072);
        let lz: u32 = w.leading_zeros();
        assert(46 <= lz <= 60) by {
            assert(u64_leading_zeros(8) == 60) by (compute_only);
            assert(u64_leading_zeros(131072) == 46) by (compute_only);
            leading_zeros_between(8, w, 131072);
        }
        let ghost log2_w = log2(w);

        let b = (usize::BITS - 1 - lz) as u8;
        assert(b == log2_w);
        assert(3 <= b <= 17);

//        assert(w > 255 ==> u64_leading_zeros(w) <= 52) by {
//            if w > 255 {
//                assert(u64_leading_zeros(256) == 55) by (compute_only);
//                leading_zeros_between(256, w, 131072);
//            }
//        }
        // This isn't true with this limited context, b/c we need to know how w and b scale relative to each other
//        assert((w >> sub(b as u64, 2)) < 256) by (bit_vector)
//            requires 8 <= w < 131072 && 3 <= b <= 17;
        assert(w >> ((b as u64 - 2) as u64) <= 8) by {
            assert(w < pow2((log2_w + 1) as int));
            assert(pow2((log2_w - 2) as int) > 0) by { pow2_properties(); }
            assert(w as nat / pow2((log2_w - 2) as int) <=
                    pow2((log2_w + 1) as int) / pow2((log2_w - 2) as int)) by {
                lemma_div_is_ordered(w as int,
                                     pow2((log2_w + 1) as int) as int,
                                     pow2((log2_w - 2) as int) as int);
            }
            assert(pow2((log2_w + 1) as int) / pow2((log2_w - 2) as int) == pow2(3)) by {
                pow2_subtracts((log2_w - 2) as nat, log2_w + 1);
            }
            assert(pow2(3) == 8) by (compute_only);
            shift_is_div(w, ((b as u64 - 2) as u64));
        }
        assert((w >> sub(b as u64, 2)) < 256);

        let shifted = (w >> (b as u64 - 2)) as u8;

        assert((w >> sub(sub(63, lz as u64), 2)) & 0x03 < 4) by (bit_vector)
            requires 8 <= w < 131073 && 46 <= lz <= 60;
        //assert(((w >> sub(63 - lz as u64), 2)) & 0x03 < 4);
        //assert((w >> ((63 - lz as u64) - 2)) & 0x03 < 4);

        assert(shifted & 0x03 < 4) by (bit_vector);
        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;

        assert(valid_bin_idx(bin_idx as int));
        assert(bin_idx == smallest_bin_fitting_size(size as int));
        assert(size_of_bin(bin_idx as int) >= size) by { bin_size_result(size); };
        //assert(size_of_bin(bin_idx as int) >= size)
            // Can't call this because the precondition restricts it to small sizes
            // by { bounds_for_smallest_bin_fitting_size(size as int); }

        bin_idx
    }
}

//////// Segment bins

pub open spec fn valid_sbin_idx(sbin_idx: int) -> bool {
    0 <= sbin_idx <= SEGMENT_BIN_MAX
}

pub closed spec fn size_of_sbin(sbin_idx: int) -> nat
    recommends valid_sbin_idx(sbin_idx)
{
    if 0 <= sbin_idx <= 7 {
        sbin_idx as nat
    } else if sbin_idx == 8 {
        10
    } else {
        let group = (sbin_idx - 8) / 4;
        let inner = (sbin_idx - 8) % 4;

        ((inner + 5) * pow2(group + 1)) as nat
    }
}

pub open spec fn smallest_sbin_fitting_size(i: int) -> int
{
    if i <= 8 {
        i
    } else {
        let w = (i - 1) as u64;
        //let lz = w.leading_zeros();
        let lz = u64_leading_zeros(w);
        let b = (usize::BITS - 1 - lz) as u8;
        let sbin_idx = ((b << 2u8) as u64 | ((w >> (b as u64 - 2) as u64) & 0x03)) - 4;
        sbin_idx
    }
}

/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_sbin_idx_smallest_sbin_fitting_size(size:int) -> bool
{
    valid_sbin_idx(smallest_sbin_fitting_size(size))
}

spec fn check_sbin_idx_smallest_sbin_fitting_size(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin_idx_smallest_sbin_fitting_size(size_start)
       && check_sbin_idx_smallest_sbin_fitting_size(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin_idx_smallest_sbin_fitting_size(size_start:int, size_end:int)
    ensures
        check_sbin_idx_smallest_sbin_fitting_size(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin_idx_smallest_sbin_fitting_size(size)),
    decreases size_end - size_start,
{
    unimplemented!();
}

#[verifier::external_body]
pub proof fn valid_sbin_idx_smallest_sbin_fitting_size(i: int)
    requires 0 <= i <= SLICES_PER_SEGMENT
    ensures valid_sbin_idx(smallest_sbin_fitting_size(i)),
{
    unimplemented!();
}

/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_sbin_bounds(size:int) -> bool
{
    let lz = u64_leading_zeros(size as u64);
    let b = (63 - lz) as u8;
    // Satisfy various type requirements
    (b  >= 2) &&
    (((b << 2u8) as u64 | ((size as u64 >> (b as u64 - 2) as u64) & 0x03)) >= 4)
}

spec fn check_sbin_bounds(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin_bounds(size_start)
       && check_sbin_bounds(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin_bounds(size_start:int, size_end:int)
    ensures
        check_sbin_bounds(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin_bounds(size)),
    decreases size_end - size_start,
{
    unimplemented!();
}

/** Put our desired property into a proof-by-compute-friendly form **/
spec fn property_sbin(slice_count:int) -> bool
{
    let sbin_idx = smallest_sbin_fitting_size(slice_count as int);
    valid_sbin_idx(sbin_idx as int) &&
    size_of_sbin(sbin_idx as int) >= slice_count
}

spec fn check_sbin(size_start:int, size_end:int) -> bool
    decreases size_end - size_start,
{
   if size_start >= size_end {
       true
   } else {
          property_sbin(size_start)
       && check_sbin(size_start + 1, size_end)
   }
}

#[verifier::external_body]
proof fn result_sbin(size_start:int, size_end:int)
    ensures
        check_sbin(size_start, size_end) ==>
            (forall |size| size_start <= size < size_end ==>
                 property_sbin(size)),
    decreases size_end - size_start,
{
    unimplemented!();
}

#[verifier::external_body]
pub fn slice_bin(slice_count: usize) -> (sbin_idx: usize)
{
    // Based on mi_slice_bin8
    if slice_count <= 8 {
        slice_count
    } else {
        let w = (slice_count - 1) as u64;
        assert(SLICES_PER_SEGMENT == 512) by (compute_only);
        assert(9 <= slice_count <= 512);
        assert(8 <= w <= 511);
        let lz = w.leading_zeros();
        let b = (usize::BITS - 1 - lz) as u8;
        let sbin_idx = ((b << 2u8) as u64 | ((w >> (b as u64 - 2)) & 0x03)) - 4;
        assert(sbin_idx == smallest_sbin_fitting_size(slice_count as int));
        sbin_idx as usize
    }
}
}
