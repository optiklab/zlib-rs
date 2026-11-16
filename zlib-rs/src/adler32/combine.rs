#[cfg(verus_keep_ghost)]
use crate::{proofs, specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires specs::canonical(adler1), specs::canonical(adler2),
    ensures result as int == specs::combine(adler1, adler2, len2 as int),
        specs::canonical(result),
))]
pub fn adler32_combine(adler1: u32, adler2: u32, len2: u64) -> u32 {
    const BASE: u64 = super::constants::BASE as u64;

    let rem = len2 % BASE;

    #[cfg(verus_keep_ghost)]
    proof! {
        proofs::split(adler1);
        proofs::split(adler2);
        assert(BASE << 1 == 131042u64) by (bit_vector);
    }
    let adler1 = adler1 as u64;
    let adler2 = adler2 as u64;

    let mut sum1 = adler1 & 0xffff;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(rem as int * sum1 as int <= 65520int * 65520int) by (nonlinear_arith)
            requires rem < 65521, sum1 < 65521;
    }
    let mut sum2 = rem * sum1;
    sum2 %= BASE;
    sum1 += (adler2 & 0xffff) + BASE - 1;
    sum2 += ((adler1 >> 16) & 0xffff) + ((adler2 >> 16) & 0xffff) + BASE - rem;

    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost unreduced_a = sum1;
        let ghost unreduced_b = sum2;
    }

    if sum1 >= BASE {
        sum1 -= BASE;
    }
    if sum1 >= BASE {
        sum1 -= BASE;
    }
    if sum2 >= (BASE << 1) {
        sum2 -= BASE << 1;
    }
    if sum2 >= BASE {
        sum2 -= BASE;
    }

    #[cfg(verus_keep_ghost)]
    proof! {
        proofs::combine_reductions(unreduced_a as int, unreduced_b as int, sum1, sum2);
        proofs::combine_formula(adler1 as u32, adler2 as u32, len2, rem, sum1, sum2);
        assert(sum1 | (sum2 << 16) == sum1 + sum2 * 65536) by (bit_vector)
            requires sum1 < 65521, sum2 < 65521;
        assert((((sum1 | (sum2 << 16)) as u32) & 0xffff) as u64 == sum1)
            by (bit_vector) requires sum1 < 65521, sum2 < 65521;
        assert(((((sum1 | (sum2 << 16)) as u32) >> 16) & 0xffff) as u64 == sum2)
            by (bit_vector) requires sum1 < 65521, sum2 < 65521;
    }
    (sum1 | (sum2 << 16)) as u32
}
