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

/********************************************************
 * TODO: All of these should be standard library proofs
 ********************************************************/

/********************************************************
 * END: All of these should be standard library proofs
 ********************************************************/

proof fn log2(i:u64) -> (e:nat)
{ arbitrary() }

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

// The "proof" is below is broken into chunks,
// so (a) we don't exceed the interpreter's stack limit,
// and (b) because the interpreter time seems to scale
// non-linearly with recursion depth

// Used to compute a bin for a given size
#[verifier::external_body]
pub fn bin(size: usize) -> (bin_idx: u8)
{
    let bytes_per_word = usize::BITS as usize / 8;

    let wsize = (size + bytes_per_word - 1) / bytes_per_word;

    if wsize <= 1 {
        1
    } else if wsize <= 8 {
        wsize as u8
    } else {

        let w: u64 = (wsize - 1) as u64;

        let lz: u32 = w.leading_zeros();

        let ghost log2_w = log2(w);

        let b = (usize::BITS - 1 - lz) as u8;

        

//        assert(w > 255 ==> u64_leading_zeros(w) <= 52) by {
//            if w > 255 {
//                assert(u64_leading_zeros(256) == 55) by (compute_only);
//                leading_zeros_between(256, w, 131072);
//            }
//        }
        // This isn't true with this limited context, b/c we need to know how w and b scale relative to each other
//        assert((w >> sub(b as u64, 2)) < 256) by (bit_vector)
//            requires 8 <= w < 131072 && 3 <= b <= 17;

        

        let shifted = (w >> (b as u64 - 2)) as u8;

        //assert(((w >> sub(63 - lz as u64), 2)) & 0x03 < 4);
        //assert((w >> ((63 - lz as u64) - 2)) & 0x03 < 4);

        let bin_idx = ((b * 4) + (shifted & 0x03)) - 3;

        

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
{ arbitrary() }

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
pub fn slice_bin(slice_count: usize) -> (sbin_idx: usize)
{
    // Based on mi_slice_bin8
    if slice_count <= 8 {
        slice_count
    } else {
        let w = (slice_count - 1) as u64;

        

        let lz = w.leading_zeros();
        let b = (usize::BITS - 1 - lz) as u8;
        let sbin_idx = ((b << 2u8) as u64 | ((w >> (b as u64 - 2)) & 0x03)) - 4;

        sbin_idx as usize
    }
}
}
