#![forbid(unsafe_code)]

use super::HeaderOutcome;
use crate::Code;
#[cfg(verus_keep_ghost)]
use crate::{bit_specs, header_loop_specs as lengths};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 257 <= nlen <= 286, 1 <= ndist <= 30,
        nlen + ndist <= lens.len(), *old(have) <= nlen + ndist,
        crate::dynamic_header_specs::decoded_prefix(old(lens)@, *old(have) as nat),
        1 <= root <= 7, table.len() >= crate::huffman_specs::capacity(root as nat),
        forall|index: int| 0 <= index < crate::huffman_specs::capacity(root as nat)
            ==> 1 <= (#[trigger] table@[index]).bits <= root,
        *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(), *final(count) <= 64,
        *final(count) as int <= *old(count) as int + 8 * result.0 as int,
        *old(have) <= *final(have) <= nlen + ndist <= 316,
        crate::dynamic_header_specs::decoded_prefix(final(lens)@, *final(have) as nat),
        final(lens)@.len() == old(lens)@.len(),
        forall|index: int| 0 <= index < old(lens)@.len()
            && (index < *old(have) || *final(have) <= index)
                ==> #[trigger] final(lens)@[index] == old(lens)@[index],
        (result.1 == HeaderOutcome::Complete || result.1 == HeaderOutcome::MissingEob)
            <==> *final(have) == nlen + ndist,
        (result.1 == HeaderOutcome::Complete)
            <==> *final(have) == nlen + ndist && final(lens)@[256] != 0,
        (result.1 == HeaderOutcome::MissingEob)
            <==> *final(have) == nlen + ndist && final(lens)@[256] == 0,
        result.1 == HeaderOutcome::Complete ==>
            crate::dynamic_header_specs::decoded_prefix(final(lens)@, (nlen + ndist) as nat)
                && final(lens)@[256] != 0,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        forall|alphabet: Seq<u16>|
            #[trigger] crate::huffman_specs::header_decoding_table(alphabet, table@, root) ==>
                lengths::header_result(alphabet,
                    bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
                    bit_specs::input_bits(input@), (nlen + ndist) as nat, input.len() as nat,
                    lengths::state(old(lens)@, *old(have) as nat, *old(word), *old(count), 0, 0),
                    lengths::state(final(lens)@, *final(have) as nat, *final(word), *final(count),
                        result.0 as nat,
                        (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat),
                    result.1),
))]
pub(crate) fn resume_dynamic_header(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    table: &[Code],
    root: usize,
    lens: &mut [u16],
    have: &mut usize,
    nlen: usize,
    ndist: usize,
) -> (usize, HeaderOutcome) {
    let total = nlen + ndist;
    super::read_length_header(word, count, input, table, root, lens, have, total)
}
