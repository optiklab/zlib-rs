#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= length <= 15,
    ensures result as int ==
        (cursor as int + huffman_specs::capacity((32 - length) as nat)) % 4294967296,
        huffman_specs::aligned_cursor(cursor, length as u32) ==>
            huffman_specs::aligned_cursor(result, length as u32),
))]
pub(super) fn advance_reversed_code(cursor: u32, length: usize) -> u32 {
    #[cfg(verus_keep_ghost)]
    proof! { huffman_proofs::normalized_code_step(length); }
    let step = 0x80000000u32 >> (length - 1);
    let result = cursor.wrapping_add(step);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(step as int == huffman_specs::capacity((32 - length) as nat));
        if huffman_specs::aligned_cursor(cursor, length as u32) {
            assert(result & (u32::MAX >> (length as u32)) == 0) by (bit_vector)
                requires 1 <= length <= 15,
                    cursor & (u32::MAX >> (length as u32)) == 0,
                    step == 0x80000000u32 >> ((length - 1) as u32),
                    result as u64 ==
                        ((cursor as u64 + step as u64) as u64) % 0x1_0000_0000u64;
        }
    }
    result
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures huffman_specs::is_reversal(word, result),
        forall|length: u32| 1 <= length <= 15
            && #[trigger] huffman_specs::aligned_cursor(word, length) ==>
                result < huffman_specs::capacity(length as nat),
))]
pub(super) fn reverse_word(word: u32) -> u32 {
    let pairs = ((word & 0x55555555) << 1) | ((word & 0xaaaaaaaa) >> 1);
    let quads = ((pairs & 0x33333333) << 2) | ((pairs & 0xcccccccc) >> 2);
    let nibbles = ((quads & 0x0f0f0f0f) << 4) | ((quads & 0xf0f0f0f0) >> 4);
    let bytes = ((nibbles & 0x00ff00ff) << 8) | ((nibbles & 0xff00ff00) >> 8);
    let halves = ((bytes & 0x0000ffff) << 16) | ((bytes & 0xffff0000) >> 16);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|index: u32| index < 32 implies
            #[trigger] huffman_specs::word_bit(halves, index)
                == huffman_specs::word_bit(word, (31 - index) as u32) by {
            assert((halves >> index) & 1 == (word >> ((31 - index) as u32)) & 1)
                by (bit_vector)
                requires index < 32,
                    pairs == ((word & 0x55555555) << 1) | ((word & 0xaaaaaaaa) >> 1),
                    quads == ((pairs & 0x33333333) << 2) | ((pairs & 0xcccccccc) >> 2),
                    nibbles == ((quads & 0x0f0f0f0f) << 4) | ((quads & 0xf0f0f0f0) >> 4),
                    bytes == ((nibbles & 0x00ff00ff) << 8) | ((nibbles & 0xff00ff00) >> 8),
                    halves == ((bytes & 0x0000ffff) << 16) | ((bytes & 0xffff0000) >> 16);
        }
        assert forall|length: u32| 1 <= length <= 15
            && #[trigger] huffman_specs::aligned_cursor(word, length)
            implies halves < huffman_specs::capacity(length as nat) by {
            huffman_proofs::u32_shift_capacity(length);
            assert(halves < 1u32 << length) by (bit_vector)
                requires 1 <= length <= 15, word & (u32::MAX >> length) == 0,
                    pairs == ((word & 0x55555555) << 1) | ((word & 0xaaaaaaaa) >> 1),
                    quads == ((pairs & 0x33333333) << 2) | ((pairs & 0xcccccccc) >> 2),
                    nibbles == ((quads & 0x0f0f0f0f) << 4) | ((quads & 0xf0f0f0f0) >> 4),
                    bytes == ((nibbles & 0x00ff00ff) << 8) | ((nibbles & 0xff00ff00) >> 8),
                    halves == ((bytes & 0x0000ffff) << 16) | ((bytes & 0xffff0000) >> 16);
        }
    }
    halves
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= length <= 15,
    ensures result.0 as int ==
        (cursor as int + huffman_specs::capacity((32 - length) as nat)) % 4294967296,
        huffman_specs::is_reversal(result.0, result.1),
        huffman_specs::aligned_cursor(cursor, length as u32) ==>
            huffman_specs::aligned_cursor(result.0, length as u32)
                && result.1 < huffman_specs::capacity(length as nat),
))]
pub(super) fn next_code(cursor: u32, length: usize) -> (u32, u32) {
    let next = advance_reversed_code(cursor, length);
    let huff = reverse_word(next);
    (next, huff)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn reverses_code_words() {
        for (word, expected) in [
            (0, 0),
            (u32::MAX, u32::MAX),
            (0x80000000, 1),
            (1, 0x80000000),
            (0x12345678, 0x1e6a2c48),
        ] {
            assert_eq!(reverse_word(word), expected);
        }
    }

    #[test]
    fn successor_wraps_complete_code_space() {
        assert_eq!(advance_reversed_code(0, 1), 0x80000000);
        assert_eq!(advance_reversed_code(0x80000000, 1), 0);
        assert_eq!(advance_reversed_code(0xfffe0000, 15), 0);
    }
}
