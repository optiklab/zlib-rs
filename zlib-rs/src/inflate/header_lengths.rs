#![forbid(unsafe_code)]

#[cfg(not(verus_keep_ghost))]
use super::bitreader::buffer;
#[cfg(verus_keep_ghost)]
use crate::{
    bit_proofs, bit_specs, buffer, dynamic_header_proofs, dynamic_header_specs, reader_state_proofs,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
const ORDER: [u8; 19] = [
    16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
];

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub(super) enum RepeatExtra {
    NeedInput,
    MissingPrevious,
    Value(u16),
}

#[inline]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= code_bits <= 7, 16 <= symbol <= 18, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        result.0 == if bit_specs::needed_bytes(*old(count),
                (code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)) as usize)
                    <= input.len() {
            bit_specs::needed_bytes(*old(count),
                (code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)) as usize)
        } else { input.len() as nat },
        matches!(result.1, RepeatExtra::NeedInput) == (
            (*old(count) as nat + 8 * input.len() as nat)
                < code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)),
        matches!(result.1, RepeatExtra::MissingPrevious) == (
            *old(count) as nat + 8 * input.len() as nat
                >= code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)
            && symbol == 16 && have == 0),
        matches!(result.1, RepeatExtra::Value(_)) == (
            *old(count) as nat + 8 * input.len() as nat
                >= code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)
            && (symbol != 16 || have != 0)),
        *final(count) <= 64,
        *final(count) as int == *old(count) as int + 8 * result.0 as int
            - dynamic_header_specs::repeat_consumed_bits(
                *old(count) as nat + 8 * input.len() as nat, code_bits as nat, symbol as nat, have as nat),
        match result.1 {
            RepeatExtra::Value(extra) => extra as nat == dynamic_header_specs::repeat_extra_value(
                bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
                code_bits as nat, symbol as nat)
                && extra < dynamic_header_specs::repeat_extra_limit(symbol as nat),
            _ => true,
        },
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(dynamic_header_specs::repeat_consumed_bits(
                        *old(count) as nat + 8 * input.len() as nat,
                        code_bits as nat, symbol as nat, have as nat) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == loaded >> (dynamic_header_specs::repeat_consumed_bits(
                *old(count) as nat + 8 * input.len() as nat,
                code_bits as nat, symbol as nat, have as nat) as u8),
))]
pub(super) fn read_repeat_extra(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    code_bits: u8,
    symbol: u16,
    have: usize,
) -> (usize, RepeatExtra) {
    let extra_bits = if symbol == 16 {
        2usize
    } else if symbol == 17 {
        3usize
    } else {
        7usize
    };
    let target = usize::from(code_bits) + extra_bits;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(extra_bits == dynamic_header_specs::repeat_extra_width(symbol as nat));
        bit_proofs::header_fill_bounds(*count, target);
    }
    let (consumed, complete) = buffer::fill_from_slice(word, count, input, target);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost loaded = *word;
        let ghost pending = bit_specs::input_bits(input@).skip(8 * consumed as int);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source);
        if !complete {
            assert(source.skip(0) =~= source);
            assert(loaded >> 0u8 == loaded) by (bit_vector);
            assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
                bit_specs::input_bits(input@).take(8 * consumed as int)) && *word == value >> 0u8);
        }
    }
    if !complete {
        return (consumed, RepeatExtra::NeedInput);
    }
    buffer::consume_bits(word, count, code_bits);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source.skip(code_bits as int));
        if symbol == 16 && have == 0 {
            assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
                bit_specs::input_bits(input@).take(8 * consumed as int)) && *word == value >> code_bits);
        }
    }
    if symbol == 16 && have == 0 {
        return (consumed, RepeatExtra::MissingPrevious);
    }
    let extra = buffer::peek_bits(*word, extra_bits) as u16;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(extra as nat == dynamic_header_specs::repeat_extra_value(
            source, code_bits as nat, symbol as nat)
            && extra < dynamic_header_specs::repeat_extra_limit(symbol as nat)) by {
            bit_proofs::numeric_field(*word, *count, extra_bits as u8,
                source.skip(code_bits as int), pending);
            assert(source.skip(code_bits as int).take(extra_bits as int)
                =~= source.subrange(code_bits as int, code_bits as int + extra_bits as int));
            dynamic_header_proofs::repeat_extra_bounds(source, code_bits as nat, symbol as nat);
            reveal(dynamic_header_specs::repeat_extra_value);
        }
    }
    buffer::consume_bits(word, count, extra_bits as u8);
    let result = (consumed, RepeatExtra::Value(extra));
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(result.0 == if bit_specs::needed_bytes(original_count, target) <= input.len() {
            bit_specs::needed_bytes(original_count, target)
        } else { input.len() as nat });
        bit_proofs::shift_compose(loaded, code_bits as u64, extra_bits as u64);
        assert(1u64 << 2u8 == 4 && 1u64 << 3u8 == 8 && 1u64 << 7u8 == 128) by (bit_vector);
        assert(bit_specs::buffered_bits(*word, *count)
            + bit_specs::input_bits(input@).skip(8 * result.0 as int) =~= source.skip(target as int));
        assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
            bit_specs::input_bits(input@).take(8 * result.0 as int)) && *word == value >> target);
    }
    result
}

#[inline]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) < total <= lengths.len(), total <= 320,
        1 <= bits <= 7, symbol <= 18, bits <= *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        *final(count) as int <= *old(count) as int + 8 * result.0 as int <= 64,
        *old(count) as int + 8 * result.0 as int - *final(count) as int <= 14,
        *old(have) <= *final(have) <= total,
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        result.1 == Some(true) ==> *old(have) < *final(have),
        result.1 != Some(true) ==> final(lengths)@ == old(lengths)@
            && *final(have) == *old(have),
        forall|index: int| 0 <= index < old(lengths)@.len()
            && (index < *old(have) || *final(have) <= index)
                ==> #[trigger] final(lengths)@[index] == old(lengths)@[index],
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == loaded
                >> ((*old(count) as int + 8 * result.0 as int - *final(count) as int) as u8),
        dynamic_header_specs::symbol_input_effect(old(lengths)@, final(lengths)@,
            *old(have) as nat, *final(have) as nat, total as nat,
            bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
            *old(count), input.len() as nat, bits as nat, symbol as nat,
            result.0 as nat,
            (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat, result.1),
))]
pub(super) fn read_selected_length_symbol(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    bits: u8,
    symbol: u16,
    lengths: &mut [u16],
    have: &mut usize,
    total: usize,
) -> (usize, Option<bool>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost original_lengths = lengths@;
        let ghost original_have = *have;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    if symbol < 16 {
        buffer::consume_bits(word, count, bits);
        #[cfg(verus_keep_ghost)]
        proof! { assert(*count as int == original_count as int - bits as int); }
        push_decoded_length(lengths, have, symbol);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bit_specs::input_bits(input@).skip(0) =~= bit_specs::input_bits(input@));
            assert(bit_specs::filled_word(original_word, original_count, original_word,
                bit_specs::input_bits(input@).take(0)));
            assert(exists|loaded: u64| #[trigger] bit_specs::filled_word(original_word, original_count,
                    loaded, bit_specs::input_bits(input@).take(0))
                && *word == loaded >> bits);
            assert(bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@)
                =~= source.skip(bits as int));
            reveal(dynamic_header_specs::symbol_input_effect);
        }
        (0, Some(true))
    } else {
        let result = read_repeat_lengths(word, count, input, bits, symbol, lengths, have, total);
        #[cfg(verus_keep_ghost)]
        proof! {
            let target = (bits as nat
                + dynamic_header_specs::repeat_extra_width(symbol as nat)) as usize;
            bit_proofs::header_fill_bounds(original_count, target);
            crate::dynamic_header_proofs::repeat_input_frames(original_lengths, lengths@,
                original_have as nat, *have as nat, total as nat, source,
                bits as nat, symbol as nat, result.1);
            reveal(dynamic_header_specs::symbol_input_effect);
        }
        result
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) <= total <= lengths.len(), total <= 320,
        1 <= code_bits <= 7, 16 <= symbol <= 18, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        result.0 == if bit_specs::needed_bytes(*old(count),
                (code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)) as usize)
                    <= input.len() {
            bit_specs::needed_bytes(*old(count),
                (code_bits as nat + dynamic_header_specs::repeat_extra_width(symbol as nat)) as usize)
        } else { input.len() as nat },
        dynamic_header_specs::repeat_input_transition(old(lengths)@, final(lengths)@,
            *old(have) as nat, *final(have) as nat, total as nat,
            bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
            code_bits as nat, symbol as nat, result.1),
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        *final(have) <= total,
        *final(count) <= 64,
        *final(count) as int == *old(count) as int + 8 * result.0 as int
            - dynamic_header_specs::repeat_consumed_bits(
                *old(count) as nat + 8 * input.len() as nat, code_bits as nat, symbol as nat,
                *old(have) as nat),
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(dynamic_header_specs::repeat_consumed_bits(
                        *old(count) as nat + 8 * input.len() as nat,
                        code_bits as nat, symbol as nat, *old(have) as nat) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == loaded >> (dynamic_header_specs::repeat_consumed_bits(
                *old(count) as nat + 8 * input.len() as nat,
                code_bits as nat, symbol as nat, *old(have) as nat) as u8),
))]
pub(super) fn read_repeat_lengths(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    code_bits: u8,
    symbol: u16,
    lengths: &mut [u16],
    have: &mut usize,
    total: usize,
) -> (usize, Option<bool>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original_count = *count; }
    let (consumed, outcome) = read_repeat_extra(word, count, input, code_bits, symbol, *have);
    #[cfg(verus_keep_ghost)]
    proof! {
        let target = (code_bits as nat
            + dynamic_header_specs::repeat_extra_width(symbol as nat)) as usize;
        assert(consumed == if bit_specs::needed_bytes(original_count, target) <= input.len() {
            bit_specs::needed_bytes(original_count, target)
        } else { input.len() as nat });
    }
    match outcome {
        RepeatExtra::NeedInput => (consumed, None),
        RepeatExtra::MissingPrevious => (consumed, Some(false)),
        RepeatExtra::Value(extra) => (
            consumed,
            Some(repeat_decoded_length(lengths, have, total, symbol, extra)),
        ),
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        result.0 == if bit_specs::needed_bytes(*old(count), 14) <= input.len() {
            bit_specs::needed_bytes(*old(count), 14)
        } else { input.len() as nat },
        result.1.is_some() == (*old(count) as int + 8 * input.len() as int >= 14),
        result.1.is_none() ==> result.0 == input.len() && *final(count) < 14,
        *final(count) <= 64,
        forall|next_pending: Seq<bool>|
            bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            #[trigger] bit_specs::cached_suffix(*final(word), *final(count), next_pending),
        *final(count) as int == *old(count) as int + 8 * result.0 as int
            - if result.1.is_some() { 14int } else { 0int },
        match result.1 {
            Some(values) =>
                (values.0 as nat, values.1 as nat, values.2 as nat)
                    == dynamic_header_specs::header_counts(
                        bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                && 257 <= values.0 <= 288 && 1 <= values.1 <= 32 && 4 <= values.2 <= 19,
            None => true,
        },
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
            == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                .skip(if result.1.is_some() { 14int } else { 0int }),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == if result.1.is_some() { loaded >> 14u8 } else { loaded },
))]
pub(super) fn read_counts(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
) -> (usize, Option<(usize, usize, usize)>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    #[cfg(verus_keep_ghost)]
    proof! { bit_proofs::header_fill_bounds(*count, 14); }
    let (consumed, complete) = buffer::fill_from_slice(word, count, input, 14);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost loaded = *word;
        let ghost pending = bit_specs::input_bits(input@).skip(8 * consumed as int);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source);
        if !complete {
            assert(source.skip(0) =~= source);
            assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
                bit_specs::input_bits(input@).take(8 * consumed as int)) && *word == value);
        }
    }
    if !complete {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|next_pending: Seq<bool>|
                bit_specs::cached_suffix(original_word, original_count, Seq::empty()) implies
                #[trigger] bit_specs::cached_suffix(*word, *count, next_pending) by {
                reader_state_proofs::clean_cache_retarget(*word, *count, next_pending);
            }
        }
        return (consumed, None);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(1u64 << 5u8 == 32 && 1u64 << 4u8 == 16) by (bit_vector);
        bit_proofs::numeric_field(*word, *count, 5, source, pending);
    }
    let nlen = buffer::peek_bits(*word, 5) as usize + 257;
    buffer::consume_bits(word, count, 5);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source.skip(5));
        bit_proofs::numeric_field(*word, *count, 5, source.skip(5), pending);
    }
    let ndist = buffer::peek_bits(*word, 5) as usize + 1;
    buffer::consume_bits(word, count, 5);
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::shift_compose(loaded, 5, 5);
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source.skip(10));
        bit_proofs::numeric_field(*word, *count, 4, source.skip(10), pending);
    }
    let ncode = buffer::peek_bits(*word, 4) as usize + 4;
    buffer::consume_bits(word, count, 4);
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::shift_compose(loaded, 10, 4);
        assert(source.skip(5).take(5) =~= source.subrange(5, 10));
        assert(source.skip(10).take(4) =~= source.subrange(10, 14));
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source.skip(14));
        dynamic_header_proofs::header_counts_bounds(source);
        assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
            bit_specs::input_bits(input@).take(8 * consumed as int)) && *word == value >> 14u8);
        assert forall|next_pending: Seq<bool>|
            bit_specs::cached_suffix(original_word, original_count, Seq::empty()) implies
            #[trigger] bit_specs::cached_suffix(*word, *count, next_pending) by {
            reader_state_proofs::clean_cache_retarget(*word, *count, next_pending);
        }
    }
    (consumed, Some((nlen, ndist, ncode)))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::prefix_fits(old(lengths)@, *old(have) as nat),
        *old(have) < 19, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 == if *old(count) >= 3 || input.len() == 0 { 0int } else { 1int },
        result.1 == (*old(count) as int + 8 * input.len() as int >= 3),
        *final(count) == *old(count) as int + 8 * result.0 as int
            - if result.1 { 3int } else { 0int },
        *final(count) <= 64,
        *final(have) == *old(have) as int + if result.1 { 1int } else { 0int },
        dynamic_header_specs::prefix_fits(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        forall|index: int| 0 <= index < old(lengths)@.len() ==>
            #[trigger] final(lengths)@[index]
                == if result.1 && index == dynamic_header_specs::wire_symbol(*old(have) as nat) {
                    bit_specs::three_bit_value(
                        bit_specs::buffered_bits(*old(word), *old(count))
                            + bit_specs::input_bits(input@))
                } else { old(lengths)@[index] },
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
            == (bit_specs::buffered_bits(*old(word), *old(count))
                + bit_specs::input_bits(input@)).skip(if result.1 { 3int } else { 0int }),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        result.0 == 0 ==> *final(word)
            == if result.1 { *old(word) >> 3u8 } else { *old(word) },
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == if result.1 { loaded >> 3u8 } else { loaded },
))]
pub(super) fn read_length(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lengths: &mut [u16],
    have: &mut usize,
) -> (usize, bool) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(dynamic_header_specs::prefix_fits);
        bit_proofs::needed_bytes_bounds(*count, 3);
        assert(bit_specs::needed_bytes(*count, 3) == if *count >= 3 { 0nat } else { 1nat });
    }
    let (consumed, complete) = buffer::fill_from_slice(word, count, input, 3);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost loaded = *word;
        let ghost loaded_bits = bit_specs::buffered_bits(*word, *count);
        let ghost pending = bit_specs::input_bits(input@).skip(8 * consumed as int);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if consumed == 0 {
            assert(bit_specs::input_bits(input@).take(0) =~= Seq::empty());
            bit_proofs::filled_word_empty(original_word, original_count, loaded);
        }
        assert(loaded_bits + pending =~= source);
        if !complete {
            assert(source.len() < 3);
            assert(source.skip(0) =~= source);
            assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
                    bit_specs::input_bits(input@).take(8 * consumed as int)) && *word == value);
        }
    }
    if !complete {
        return (consumed, false);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::three_bit_word(*word, *count);
        assert(1u64 << 3u64 == 8u64) by (bit_vector);
        assert(loaded_bits.take(3) =~= source.take(3));
        assert(bit_specs::three_bit_value(loaded_bits) == bit_specs::three_bit_value(source));
    }
    let value = buffer::peek_bits(*word, 3) as u16;
    write_length(lengths, *have, value);
    *have += 1;
    buffer::consume_bits(word, count, 3);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count) + pending =~= source.skip(3));
        assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count, value,
                bit_specs::input_bits(input@).take(8 * consumed as int)) && *word == value >> 3u8);
    }
    (consumed, true)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::prefix_fits(old(lengths)@, *old(have) as nat),
        *old(have) <= target <= 19, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        result.0 == if bit_specs::needed_bytes(*old(count), (3 * (target - *old(have))) as usize) <= input.len() {
            bit_specs::needed_bytes(*old(count), (3 * (target - *old(have))) as usize)
        } else { input.len() as nat },
        result.1 == (*final(have) == target),
        result.1 == (*old(count) as int + 8 * input.len() as int
            >= 3 * (target as int - *old(have) as int)),
        *old(have) <= *final(have) <= target,
        !result.1 ==> result.0 == input.len() && *final(count) < 3,
        *final(count) as int == *old(count) as int + 8 * result.0 as int
            - 3 * (*final(have) as int - *old(have) as int),
        *final(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        dynamic_header_specs::prefix_fits(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        forall|position: nat| position < 19 ==>
            #[trigger] final(lengths)@[dynamic_header_specs::wire_symbol(position) as int]
                == if *old(have) <= position < *final(have) {
                    bit_specs::three_bit_value(
                        (bit_specs::buffered_bits(*old(word), *old(count))
                            + bit_specs::input_bits(input@))
                            .skip(3 * (position as int - *old(have) as int)))
                } else { old(lengths)@[dynamic_header_specs::wire_symbol(position) as int] },
        forall|index: int| 19 <= index < old(lengths)@.len() ==>
            #[trigger] final(lengths)@[index] == old(lengths)@[index],
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
            == (bit_specs::buffered_bits(*old(word), *old(count))
                + bit_specs::input_bits(input@))
                    .skip(3 * (*final(have) as int - *old(have) as int)),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == loaded >> ((3 * (*final(have) as int - *old(have) as int)) as u64),
))]
pub(super) fn read_lengths(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lengths: &mut [u16],
    have: &mut usize,
    target: usize,
) -> (usize, bool) {
    let start = *have;
    let needed = 3 * (target - start);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost original_lengths = lengths@;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(dynamic_header_specs::prefix_fits);
        bit_proofs::header_fill_bounds(*count, needed);
    }
    let (consumed, _enough) = buffer::fill_from_slice(word, count, input, needed);
    let pending = &input[consumed..];
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost loaded = *word;
        let ghost loaded_count = *count;
        let ghost unread = bit_specs::input_bits(pending@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::input_suffix(input@, consumed as int);
        assert(pending@ =~= input@.skip(consumed as int));
        assert(bit_specs::buffered_bits(*word, *count) + unread =~= source);
        assert(loaded >> 0u64 == loaded) by (bit_vector);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start == *old(have),
            start <= *have <= target <= 19,
            needed == 3 * (target - start),
            original_word == *old(word), original_count == *old(count),
            original_count <= 64,
            original_lengths == old(lengths)@,
            lengths.len() == original_lengths.len(),
            original_lengths.len() >= 19,
            consumed <= input.len(),
            consumed == if bit_specs::needed_bytes(original_count, needed) <= input.len() {
                bit_specs::needed_bytes(original_count, needed)
            } else { input.len() as nat },
            loaded_count as int == original_count as int + 8 * consumed as int,
            loaded_count <= 64,
            *count as int == loaded_count as int - 3 * (*have as int - start as int),
            *count <= 64,
            _enough == (original_count as int + 8 * input.len() as int >= needed),
            _enough ==> *count as int >= 3 * (target as int - *have as int),
            !_enough ==> consumed == input.len(),
            pending@ == input@.skip(consumed as int),
            unread == bit_specs::input_bits(pending@),
            unread == bit_specs::input_bits(input@).skip(8 * consumed as int),
            source == bit_specs::buffered_bits(original_word, original_count)
                + bit_specs::input_bits(input@),
            bit_specs::buffered_bits(*word, *count) + unread
                == source.skip(3 * (*have as int - start as int)),
            bit_specs::cached_suffix(*word, *count, unread),
            bit_specs::filled_word(original_word, original_count, loaded,
                bit_specs::input_bits(input@).take(8 * consumed as int)),
            *word == loaded >> ((3 * (*have as int - start as int)) as u64),
            dynamic_header_specs::prefix_fits(lengths@, *have as nat),
            forall|position: nat| position < 19 ==>
                #[trigger] lengths@[dynamic_header_specs::wire_symbol(position) as int]
                    == if start <= position < *have {
                        bit_specs::three_bit_value(source.skip(3 * (position as int - start as int)))
                    } else { original_lengths[dynamic_header_specs::wire_symbol(position) as int] },
            forall|index: int| 19 <= index < original_lengths.len() ==>
                #[trigger] lengths@[index] == original_lengths[index],
        decreases target - *have,
    ))]
    while *have < target {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(dynamic_header_specs::prefix_fits); }
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost position = *have;
            let ghost previous_stream = bit_specs::buffered_bits(*word, *count) + unread;
        }
        let (_advanced, complete) = read_length(word, count, pending, lengths, have);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(_advanced == 0);
            assert(unread.skip(0) =~= unread);
        }
        if !complete {
            #[cfg(verus_keep_ghost)]
            proof! {
                if bit_specs::cached_suffix(original_word, original_count, Seq::empty()) {
                    reader_state_proofs::bounded_read_clean(original_word, original_count,
                        *word, *count, bit_specs::input_bits(input@).take(8 * consumed as int),
                        (3 * (*have as int - start as int)) as u8);
                }
            }
            return (consumed, complete);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            bit_proofs::shift_compose(loaded, (3 * (position as int - start as int)) as u64, 3);
            assert(previous_stream.skip(3) =~= source.skip(3 * (*have as int - start as int)));
            assert forall|earlier: nat| earlier < 19 implies
                #[trigger] lengths@[dynamic_header_specs::wire_symbol(earlier) as int]
                    == if start <= earlier < *have {
                        bit_specs::three_bit_value(source.skip(3 * (earlier as int - start as int)))
                    } else { original_lengths[dynamic_header_specs::wire_symbol(earlier) as int] } by {
                dynamic_header_proofs::wire_roundtrip(earlier);
                if earlier != position {
                    if dynamic_header_specs::wire_symbol(earlier)
                        == dynamic_header_specs::wire_symbol(position as nat) {
                        dynamic_header_proofs::wire_injective(earlier, position as nat);
                    }
                }
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if bit_specs::cached_suffix(original_word, original_count, Seq::empty()) {
            reader_state_proofs::bounded_read_clean(original_word, original_count,
                *word, *count, bit_specs::input_bits(input@).take(8 * consumed as int),
                (3 * (*have as int - start as int)) as u8);
        }
    }
    (consumed, true)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires lengths.len() >= 19, position < 19, value <= 7,
    ensures final(lengths)@.len() == old(lengths)@.len(),
        forall|index: int| 0 <= index < old(lengths)@.len() ==>
            #[trigger] final(lengths)@[index]
                == if index == dynamic_header_specs::wire_symbol(position as nat) {
                    value
                } else { old(lengths)@[index] },
        dynamic_header_specs::prefix_fits(old(lengths)@, position as nat) ==>
            dynamic_header_specs::prefix_fits(final(lengths)@, position as nat + 1),
))]
pub(super) fn write_length(lengths: &mut [u16], position: usize, value: u16) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost previous = lengths@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(dynamic_header_specs::prefix_fits);
        dynamic_header_proofs::wire_roundtrip(position as nat);
        assert(ORDER@[position as int] == dynamic_header_specs::wire_symbol(position as nat));
    }
    lengths[usize::from(ORDER[position])] = value;
    #[cfg(verus_keep_ghost)]
    proof! {
        if dynamic_header_specs::prefix_fits(previous, position as nat) {
            assert forall|earlier: nat| earlier < position + 1 implies
                #[trigger] lengths@[dynamic_header_specs::wire_symbol(earlier) as int] <= 7 by {
                dynamic_header_proofs::wire_roundtrip(earlier);
                if earlier != position {
                    if dynamic_header_specs::wire_symbol(earlier)
                        == dynamic_header_specs::wire_symbol(position as nat) {
                        dynamic_header_proofs::wire_injective(earlier, position as nat);
                    }
                }
            }
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    requires dynamic_header_specs::prefix_fits(old(lengths)@, *old(have) as nat),
    ensures *final(have) == 19,
        dynamic_header_specs::padded_header(old(lengths)@, final(lengths)@, *old(have) as nat),
        forall|symbol: int| 0 <= symbol < 19 ==> #[trigger] final(lengths)@[symbol] <= 7,
))]
pub(super) fn finish_length_header(lengths: &mut [u16], have: &mut usize) {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(dynamic_header_specs::prefix_fits); }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial_have = *have;
        let ghost original = lengths@;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant initial_have <= *have <= 19,
            lengths.len() == original.len(),
            original.len() >= 19,
            dynamic_header_specs::prefix_fits(lengths@, *have as nat),
            forall|position: nat| position < 19 ==>
                #[trigger] lengths@[dynamic_header_specs::wire_symbol(position) as int]
                    == if initial_have <= position < *have { 0 }
                        else { original[dynamic_header_specs::wire_symbol(position) as int] },
            forall|index: int| 19 <= index < original.len() ==>
                #[trigger] lengths@[index] == original[index],
        decreases 19 - *have,
    ))]
    while *have < 19 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(dynamic_header_specs::prefix_fits); }
        let position = *have;
        write_length(lengths, position, 0);
        *have += 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|earlier: nat| earlier < 19 implies
                #[trigger] lengths@[dynamic_header_specs::wire_symbol(earlier) as int]
                    == if initial_have <= earlier < *have { 0 }
                        else { original[dynamic_header_specs::wire_symbol(earlier) as int] } by {
                dynamic_header_proofs::wire_roundtrip(earlier);
                if earlier != position {
                    if dynamic_header_specs::wire_symbol(earlier)
                        == dynamic_header_specs::wire_symbol(position as nat) {
                        dynamic_header_proofs::wire_injective(earlier, position as nat);
                    }
                }
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { dynamic_header_proofs::complete_prefix_bounded(lengths@); }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) < lengths.len(), value <= 15,
    ensures *final(have) == *old(have) + 1,
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        forall|index: int| 0 <= index < old(lengths)@.len() ==>
            #[trigger] final(lengths)@[index] == if index == *old(have) { value }
                else { old(lengths)@[index] },
))]
pub(super) fn push_decoded_length(lengths: &mut [u16], have: &mut usize, value: u16) {
    lengths[*have] = value;
    *have += 1;
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) <= total <= lengths.len(), total <= 320,
        16 <= symbol <= 18,
        extra < dynamic_header_specs::repeat_extra_limit(symbol as nat),
    ensures dynamic_header_specs::repeat_transition(old(lengths)@, final(lengths)@,
        *old(have) as nat, *final(have) as nat, total as nat, symbol as nat, extra as nat, result),
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        *final(have) <= total,
))]
pub(super) fn repeat_decoded_length(
    lengths: &mut [u16],
    have: &mut usize,
    total: usize,
    symbol: u16,
    extra: u16,
) -> bool {
    if symbol == 16 && *have == 0 {
        return false;
    }
    let count = usize::from(extra) + if symbol == 18 { 11 } else { 3 };
    if *have + count > total {
        return false;
    }
    let value = if symbol == 16 { lengths[*have - 1] } else { 0 };
    let mut remaining = count;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = lengths@;
        let ghost start = *have;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 0 <= remaining <= count,
            *have == start + count - remaining,
            *have <= start + count <= total <= lengths.len(),
            lengths.len() == original.len(),
            dynamic_header_specs::decoded_prefix(lengths@, *have as nat),
            value <= 15,
            forall|index: int| 0 <= index < original.len() ==>
                #[trigger] lengths@[index] == if start <= index < *have { value }
                    else { original[index] },
        decreases remaining,
    ))]
    while remaining != 0 {
        push_decoded_length(lengths, have, value);
        remaining -= 1;
    }
    true
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::inflate::inftrees::{finish_code_length_table, lookup_code_length, InflateTable};
    use crate::Code;

    #[test]
    fn repeat_instructions_cover_every_extra_value_and_previous_zero() {
        for (symbol, limit, base) in [(16, 4, 3), (17, 8, 3), (18, 128, 11)] {
            for extra in 0..limit {
                for previous in [0, 15] {
                    let mut lengths = [u16::MAX; 320];
                    lengths[..5].fill(previous);
                    let mut have = 5;
                    assert!(repeat_decoded_length(
                        &mut lengths,
                        &mut have,
                        320,
                        symbol,
                        extra
                    ));
                    let count = base + usize::from(extra);
                    let value = if symbol == 16 { previous } else { 0 };
                    assert_eq!(have, 5 + count);
                    assert_eq!(&lengths[..5], &[previous; 5]);
                    assert!(lengths[5..have].iter().all(|length| *length == value));
                    assert!(lengths[have..].iter().all(|length| *length == u16::MAX));
                }
            }
        }
    }

    #[test]
    fn invalid_repeats_leave_all_storage_and_progress_unchanged() {
        let original = [u16::MAX; 320];
        let mut lengths = original;
        let mut have = 0;
        assert!(!repeat_decoded_length(&mut lengths, &mut have, 320, 16, 0));
        assert_eq!((have, lengths), (0, original));

        for (symbol, extra, count) in [(16, 3, 6), (17, 7, 10), (18, 127, 138)] {
            lengths[..5].fill(7);
            let before = lengths;
            have = 5;
            assert!(!repeat_decoded_length(
                &mut lengths,
                &mut have,
                5 + count - 1,
                symbol,
                extra
            ));
            assert_eq!((have, lengths), (5, before));
            assert!(repeat_decoded_length(
                &mut lengths,
                &mut have,
                5 + count,
                symbol,
                extra
            ));
            assert_eq!(have, 5 + count);
        }
    }

    #[test]
    fn literal_and_repeat_may_cross_the_literal_distance_alphabet_boundary() {
        let mut lengths = [u16::MAX; 320];
        lengths[..255].fill(13);
        let mut have = 255;
        push_decoded_length(&mut lengths, &mut have, 4);
        assert!(repeat_decoded_length(&mut lengths, &mut have, 260, 16, 1));
        assert_eq!(have, 260);
        assert_eq!(&lengths[..255], &[13; 255]);
        assert_eq!(&lengths[255..260], &[4; 5]);
        assert_eq!(&lengths[260..], &[u16::MAX; 60]);
    }

    #[test]
    fn wire_order_header_builds_the_rfc_table_and_preserves_unwritten_storage() {
        let wire_lengths = [0, 0, 0, 3, 0, 4, 0, 4, 0, 2, 0, 3, 0, 3, 0, 3, 0, 3];
        let mut lengths = [u16::MAX; 32];
        let mut have = 0;
        for value in wire_lengths {
            write_length(&mut lengths, have, value);
            have += 1;
        }
        let sentinel = Code {
            op: 64,
            bits: 7,
            val: 123,
        };
        let mut table = [sentinel; 128];
        let mut work = [42; 19];
        assert_eq!(
            finish_code_length_table(&mut lengths, &mut have, &mut table, &mut work),
            InflateTable::Success { root: 4, used: 16 }
        );
        assert_eq!(have, 19);
        assert_eq!(&lengths[..8], &[3, 3, 3, 3, 3, 2, 4, 4]);
        assert_eq!(&lengths[8..19], &[0; 11]);
        assert_eq!(&lengths[19..], &[u16::MAX; 13]);
        assert_eq!(&work[..8], &[5, 0, 1, 2, 3, 4, 6, 7]);
        assert_eq!(&work[8..], &[42; 11]);
        let symbols = [5, 2, 0, 4, 5, 3, 1, 6, 5, 2, 0, 4, 5, 3, 1, 7];
        let bits = [2, 3, 3, 3, 2, 3, 3, 4, 2, 3, 3, 3, 2, 3, 3, 4];
        for (index, code) in table[..16].iter().enumerate() {
            assert_eq!(
                (code.op, code.bits, code.val),
                (0, bits[index], symbols[index])
            );
            let word = (u64::MAX << 4) | index as u64;
            let selected = lookup_code_length(&table, 4, word);
            assert_eq!(
                (selected.op, selected.bits, selected.val),
                (0, bits[index], symbols[index])
            );
        }
        assert_eq!(&table[16..], &[sentinel; 112]);
    }

    #[test]
    fn full_wire_header_preserves_the_final_alphabet_member() {
        let mut lengths = [0; 19];
        for position in 0..19 {
            write_length(
                &mut lengths,
                position,
                u16::from(position == 3 || position == 18),
            );
        }
        let mut have = 19;
        let mut table = [Code {
            op: 0,
            bits: 0,
            val: 0,
        }; 128];
        let mut work = [42; 19];
        assert_eq!(
            finish_code_length_table(&mut lengths, &mut have, &mut table, &mut work),
            InflateTable::Success { root: 1, used: 2 }
        );
        assert_eq!((table[0].val, table[1].val), (0, 15));
        assert_eq!((table[0].bits, table[1].bits), (1, 1));
        assert_eq!(&work[..2], &[0, 15]);
        assert_eq!(&work[2..], &[42; 17]);
    }

    #[test]
    fn empty_and_invalid_headers_preserve_constructor_frames() {
        let sentinel = Code {
            op: 64,
            bits: 7,
            val: 123,
        };
        for invalid in [false, true] {
            let mut lengths = [u16::MAX; 32];
            let mut have = 0;
            if invalid {
                for position in 0..4 {
                    write_length(&mut lengths, position, 1);
                    have += 1;
                }
            }
            let mut table = [sentinel; 128];
            let mut work = [42; 19];
            let result = finish_code_length_table(&mut lengths, &mut have, &mut table, &mut work);
            assert_eq!(have, 19);
            let mut expected = [0; 19];
            if invalid {
                for symbol in [0, 16, 17, 18] {
                    expected[symbol] = 1;
                }
                assert_eq!(result, InflateTable::InvalidCode);
                assert_eq!(table, [sentinel; 128]);
            } else {
                assert_eq!(result, InflateTable::Success { root: 1, used: 2 });
                assert_eq!(
                    &table[..2],
                    &[Code {
                        op: 64,
                        bits: 1,
                        val: 0
                    }; 2]
                );
                assert_eq!(&table[2..], &[sentinel; 126]);
            }
            assert_eq!(&lengths[..19], &expected);
            assert_eq!(&lengths[19..], &[u16::MAX; 13]);
            assert_eq!(work, [42; 19]);
        }
    }
}
