pub(crate) use super::short::{adler32_len_1, adler32_len_16};
use super::NMAX;

#[cfg(verus_keep_ghost)]
use crate::{proofs, specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// macros for loop unrolling
macro_rules! do1 {
    ($sum1:expr, $sum2:expr, $chunk:expr, $i:expr) => {
        #[cfg(verus_keep_ghost)]
        proof! {
            proofs::prefix_step($chunk@, $i as int);
            proofs::prefix_bounds($chunk@, $i as int + 1);
        }
        // SAFETY: the eight-byte kernel bounds every unrolled index.
        $sum1 += unsafe { *$chunk.get_unchecked($i) } as u32;
        $sum2 += $sum1;
    };
}

macro_rules! do2 {
    ($sum1:expr, $sum2:expr, $chunk:expr, $i:expr) => {
        do1!($sum1, $sum2, $chunk, $i);
        do1!($sum1, $sum2, $chunk, $i + 1);
    };
}

macro_rules! do4 {
    ($sum1:expr, $sum2:expr, $chunk:expr, $i:expr) => {
        do2!($sum1, $sum2, $chunk, $i);
        do2!($sum1, $sum2, $chunk, $i + 2);
    };
}

macro_rules! do8 {
    ($sum1:expr, $sum2:expr, $chunk:expr, $i:expr) => {
        do4!($sum1, $sum2, $chunk, $i);
        do4!($sum1, $sum2, $chunk, $i + 4);
    };
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result as int == specs::scalar_update(adler, buf@),
))]
pub fn adler32_rust(mut adler: u32, buf: &[u8]) -> u32 {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = adler;
        let ghost initial_a = specs::low(adler);
        let ghost initial_b = specs::high(adler);
    }
    /* split Adler-32 into component sums */
    let mut sum2 = (adler >> 16) & 0xffff;
    adler &= 0xffff;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(adler <= 65535) by (bit_vector) requires adler == initial & 0xffff;
        assert(sum2 <= 65535) by (bit_vector)
            requires sum2 == (initial >> 16) & 0xffff;
        assert(adler | (sum2 << 16) == initial) by (bit_vector)
            requires adler == initial & 0xffff, sum2 == (initial >> 16) & 0xffff;
    }

    /* in case user likes doing a byte at a time, keep it fast */
    if buf.len() == 1 {
        return adler32_len_1(adler, buf, sum2);
    }

    /* initial Adler-32 value (deferred check for len == 1 speed) */
    if buf.is_empty() {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((adler | (sum2 << 16)) as int
                == specs::scalar_update(adler | (sum2 << 16), buf@));
        }
        return adler | (sum2 << 16);
    }

    /* in case short lengths are provided, keep it somewhat fast */
    if buf.len() < 16 {
        #[cfg(verus_keep_ghost)]
        proof! { proofs::delayed_bounds(adler as int, sum2 as int, buf@); }
        return adler32_len_16(adler, buf, sum2);
    }

    let mut offset = 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(buf@.subrange(0, buf.len() as int) == buf@);
        assert(adler as int == initial_a);
        assert(sum2 as int == initial_b);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= offset <= buf.len(),
            adler <= 65535, sum2 <= 65535,
            specs::update(adler as int, sum2 as int,
                buf@.subrange(offset as int, buf.len() as int))
                == specs::update(initial_a, initial_b, buf@),
        decreases buf.len() - offset,
    ))]
    while buf.len() - offset >= NMAX as usize {
        let end = offset + NMAX as usize;
        let chunk = &buf[offset..end];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(chunk@ + buf@.subrange(end as int, buf.len() as int)
                == buf@.subrange(offset as int, buf.len() as int));
            proofs::update_concatenation(adler as int, sum2 as int, chunk@,
                buf@.subrange(end as int, buf.len() as int));
            proofs::update_components(adler as int, sum2 as int, chunk@);
        }
        let checksum = adler32_len_64(adler, chunk, sum2);
        adler = checksum & 0xffff;
        sum2 = (checksum >> 16) & 0xffff;
        offset = end;
    }

    /* do remaining bytes (less than NMAX, still just one modulo) */
    adler32_len_64(adler, &buf[offset..], sum2)
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        chunk.len() == 16,
        adler as int + specs::byte_sum(chunk@) <= u32::MAX,
        sum2 as int + 16 * adler as int + specs::weighted_sum(chunk@) <= u32::MAX,
    ensures
        result.0 as int == adler as int + specs::byte_sum(chunk@),
        result.1 as int == sum2 as int + 16 * adler as int + specs::weighted_sum(chunk@),
))]
#[inline(always)]
fn adler32_chunk(mut adler: u32, chunk: &[u8], mut sum2: u32) -> (u32, u32) {
    #[cfg(verus_keep_ghost)]
    proof! {
        proofs::prefix_chunk(chunk@, 8, 8);
        proofs::prefix_bounds(chunk@, 8);
        assert(chunk@.subrange(8, 16) == chunk@.skip(8));
        assert(chunk@.take(16) == chunk@);
    }
    let first = adler32_chunk8(adler, &chunk[..8], sum2);
    adler = first.0;
    sum2 = first.1;
    adler32_chunk8(adler, &chunk[8..], sum2)
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        chunk.len() == 8,
        adler as int + specs::byte_sum(chunk@) <= u32::MAX,
        sum2 as int + 8 * adler as int + specs::weighted_sum(chunk@) <= u32::MAX,
    ensures
        result.0 as int == adler as int + specs::byte_sum(chunk@),
        result.1 as int == sum2 as int + 8 * adler as int + specs::weighted_sum(chunk@),
))]
#[inline(always)]
fn adler32_chunk8(mut adler: u32, chunk: &[u8], mut sum2: u32) -> (u32, u32) {
    #[cfg(verus_keep_ghost)]
    proof! { proofs::prefix_bounds(chunk@, 0); }
    do8!(adler, sum2, chunk, 0);
    #[cfg(verus_keep_ghost)]
    proof! { assert(chunk@.take(8) == chunk@); }
    (adler, sum2)
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires adler <= 65535, sum2 <= 65535, buf.len() <= NMAX,
    ensures result as int == specs::update(adler as int, sum2 as int, buf@),
))]
pub(crate) fn adler32_len_64(mut adler: u32, buf: &[u8], mut sum2: u32) -> u32 {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_a = adler as int;
        let ghost initial_b = sum2 as int;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        proofs::delayed_bounds(initial_a, initial_b, buf@);
        proofs::prefix_bounds(buf@, 0);
    }
    let mut offset = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= offset <= buf.len(),
            adler as int == initial_a + specs::byte_sum(buf@.take(offset as int)),
            sum2 as int == initial_b + offset as int * initial_a
                + specs::weighted_sum(buf@.take(offset as int)),
        decreases buf.len() - offset,
    ))]
    while buf.len() - offset >= 16 {
        let end = offset + 16;
        let chunk = &buf[offset..end];
        #[cfg(verus_keep_ghost)]
        proof! {
            proofs::prefix_chunk(buf@, offset as int, 16);
            proofs::prefix_bounds(buf@, end as int);
            assert(end as int * initial_a == offset as int * initial_a + 16 * initial_a)
                by (nonlinear_arith) requires end == offset + 16;
            assert(end as int * initial_a <= buf.len() as int * initial_a)
                by (nonlinear_arith) requires 0 <= initial_a, end <= buf.len();
        }
        let sums = adler32_chunk(adler, chunk, sum2);
        adler = sums.0;
        sum2 = sums.1;
        offset = end;
    }

    /* Process tail (len < 16).  */
    let tail = &buf[offset..];
    #[cfg(verus_keep_ghost)]
    proof! {
        proofs::prefix_chunk(buf@, offset as int, tail.len() as int);
        assert(buf@.take(buf.len() as int) == buf@);
        assert(tail.len() as int * (initial_a
            + specs::byte_sum(buf@.take(offset as int)))
            == tail.len() as int * initial_a
                + tail.len() as int * specs::byte_sum(buf@.take(offset as int)))
            by (nonlinear_arith);
        assert(buf.len() as int * initial_a
            == offset as int * initial_a + tail.len() as int * initial_a)
            by (nonlinear_arith) requires buf.len() == offset + tail.len();
    }
    adler32_len_16(adler, tail, sum2)
}
