#[cfg(verus_keep_ghost)]
use crate::{bit_proofs, bit_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *old(count) <= 32,
    ensures
        result.1 == *old(count) as int / 8,
        result.0@.take(result.1 as int) == bit_specs::sync_bytes(*old(word), *old(count)),
        *final(count) == 0,
        *final(word) == *old(word) >> *old(count),
))]
pub(super) fn drain_sync_buffer(word: &mut u64, count: &mut u8) -> ([u8; 4], usize) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_word = *word;
        let ghost initial_count = *count;
    }
    #[cfg(verus_keep_ghost)]
    proof! { bit_proofs::alignment(*count); }
    let mut bytes = [0u8; 4];
    let skip = *count & 7;
    *word >>= skip;
    *count -= skip;

    let mut len = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            len <= 4,
            *count as int + 8 * len as int == initial_count as int - skip as int,
            *word == initial_word >> ((skip as int + 8 * len as int) as u64),
            forall|index: int| 0 <= index < len ==>
                bytes@[index] == (initial_word >> ((skip as int + 8 * index) as u64)) as u8,
        decreases *count,
    ))]
    while *count >= 8 {
        #[cfg(verus_keep_ghost)]
        proof! {
            bit_proofs::shift_compose(initial_word,
                (skip as int + 8 * len as int) as u64, 8);
        }
        bytes[len] = *word as u8;
        len += 1;
        *word >>= 8;
        *count -= 8;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bytes@.take(len as int) =~= bit_specs::sync_bytes(initial_word, initial_count));
    }
    (bytes, len)
}
