use super::constants::BASE;

#[cfg(verus_keep_ghost)]
use crate::{proofs, specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        buf.len() == 1,
        adler as int + buf@[0] as int <= u32::MAX,
        sum2 as int + (adler as int + buf@[0] as int) % (specs::MODULUS as int) <= u32::MAX,
    ensures result as int == specs::update(adler as int, sum2 as int, buf@),
))]
pub(crate) fn adler32_len_1(mut adler: u32, buf: &[u8], mut sum2: u32) -> u32 {
    #[cfg(verus_keep_ghost)]
    proof! {
        proofs::single_byte(buf@);
        proofs::mod_add(sum2 as int, adler as int + buf@[0] as int);
    }
    adler += buf[0] as u32;
    adler %= BASE;
    sum2 += adler;
    sum2 %= BASE;
    #[cfg(verus_keep_ghost)]
    proof! { proofs::pack(adler, sum2); }
    adler | (sum2 << 16)
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        adler as int + specs::byte_sum(buf@) <= u32::MAX,
        sum2 as int + buf.len() as int * adler as int
            + specs::weighted_sum(buf@) <= u32::MAX,
    ensures result as int == specs::update(adler as int, sum2 as int, buf@),
))]
pub(crate) fn adler32_len_16(mut adler: u32, buf: &[u8], mut sum2: u32) -> u32 {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_a = adler as int;
        let ghost initial_b = sum2 as int;
    }
    #[cfg(verus_keep_ghost)]
    proof! { proofs::prefix_bounds(buf@, 0); }

    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= i <= buf.len(),
            adler as int == initial_a + specs::byte_sum(buf@.take(i as int)),
            sum2 as int == initial_b + i as int * initial_a
                + specs::weighted_sum(buf@.take(i as int)),
        decreases buf.len() - i,
    ))]
    while i < buf.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            proofs::prefix_step(buf@, i as int);
            proofs::prefix_bounds(buf@, i as int + 1);
            assert((i as int + 1) * initial_a == i as int * initial_a + initial_a)
                by (nonlinear_arith);
            assert((i as int + 1) * initial_a <= buf.len() as int * initial_a)
                by (nonlinear_arith)
                requires 0 <= initial_a, i < buf.len();
        }
        adler += buf[i] as u32;
        sum2 += adler;
        i += 1;
    }

    #[cfg(verus_keep_ghost)]
    proof! { assert(buf@.take(buf.len() as int) == buf@); }
    adler %= BASE;
    sum2 %= BASE;
    #[cfg(verus_keep_ghost)]
    proof! { proofs::pack(adler, sum2); }
    adler | (sum2 << 16)
}
