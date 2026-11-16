#![forbid(unsafe_code)]

#[cfg(verus_keep_ghost)]
use crate::{bit_proofs, bit_specs, reader_state_proofs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(word) == 0, *final(count) == 0,
        bit_specs::buffered_bits(*final(word), *final(count)) == Seq::<bool>::empty(),
        forall|pending: Seq<bool>|
            #[trigger] bit_specs::cached_suffix(*final(word), *final(count), pending),
))]
pub(super) fn reset_bits(word: &mut u64, count: &mut u8) {
    *word = 0;
    *count = 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count) =~= Seq::<bool>::empty());
        assert forall|pending: Seq<bool>| #[trigger] bit_specs::cached_suffix(0, 0, pending) by {
            reveal(bit_specs::cached_suffix);
            assert forall|index: nat| index < 64 implies
                !(#[trigger] bit_specs::word_bit(0, index)) by {
                let position = index as u64;
                assert((0u64 >> position) & 1 == 0) by (bit_vector);
            }
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires *old(count) < 64, bits < 64, *old(count) as int + bits as int <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()),
    ensures *final(count) as int == *old(count) as int + bits as int,
        *final(word) as int == *old(word) as int
            + ((value & (((1u64 << bits) - 1) as u64)) << *old(count)) as int,
        bit_specs::buffered_bits(*final(word), *final(count))
            == bit_specs::buffered_bits(*old(word), *old(count))
                + bit_specs::buffered_bits(value, bits),
        bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
))]
pub(super) fn prime_bits(word: &mut u64, count: &mut u8, bits: u8, value: u64) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost supplied_value = value;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        reader_state_proofs::clean_cache_bound(*word, *count, *count);
        assert(1u64 << bits > 0) by (bit_vector) requires bits < 64;
    }
    let value = value & ((1 << bits) - 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(value & (((1u64 << bits) - 1) as u64) == value) by (bit_vector)
            requires bits < 64, value == supplied_value & (((1u64 << bits) - 1) as u64);
        let shifted = value << *count;
        assert(*word & shifted == 0) by (bit_vector)
            requires *count < 64, *word < (1u64 << *count),
                shifted == value << *count;
        assert(*word as u128 + shifted as u128 == (*word | shifted) as u128)
            by (bit_vector) requires *word & shifted == 0;
        assert(*word as int + shifted as int <= u64::MAX as int);
        assert(bit_specs::append_compatible(*word, *count, value, bits)) by {
            reveal(bit_specs::cached_suffix);
        }
        bit_proofs::appended_buffer(*word, *count, value, bits);
    }
    *word += value << *count;
    *count += bits;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(*word == original_word | (value << original_count));
        assert(bit_specs::buffered_bits(value, bits)
            =~= bit_specs::buffered_bits(supplied_value, bits)) by {
            assert forall|index: int| 0 <= index < bits implies
                #[trigger] bit_specs::word_bit(value, index as nat)
                    == bit_specs::word_bit(supplied_value, index as nat) by {
                let position = index as u64;
                assert(((value >> position) & 1) == ((supplied_value >> position) & 1))
                    by (bit_vector) requires position < bits < 64,
                        value == supplied_value & (((1u64 << bits) - 1) as u64);
            }
        }
        assert forall|index: nat| *count <= index < 64 implies
            !(#[trigger] bit_specs::word_bit(*word, index)) by {
            reveal(bit_specs::cached_suffix);
            let position = index as u64;
            assert(!bit_specs::word_bit(original_word, index));
            assert(((*word >> position) & 1) == 0) by (bit_vector)
                requires position < 64, original_count < 64, bits < 64,
                    position as int >= original_count as int + bits as int,
                    (original_word >> position) & 1 != 1,
                    *word == original_word | (value << original_count),
                    value & (((1u64 << bits) - 1) as u64) == value;
        }
        reveal(bit_specs::cached_suffix);
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires n < 64,
    ensures result == word & (((1u64 << n) - 1) as u64),
        forall|index: nat| index < 64 ==>
        #[trigger] bit_specs::word_bit(result, index)
            == (index < n && bit_specs::word_bit(word, index)),
        result < (1u64 << n),
))]
pub(crate) fn peek_bits(word: u64, n: usize) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        let width = n as u64;
        assert(1u64 << width > 0) by (bit_vector) requires width < 64;
    }
    let mask = (1u64 << n) - 1;
    let result = word & mask;
    #[cfg(verus_keep_ghost)]
    proof! {
        let width = n as u64;
        assert(result < (1u64 << width)) by (bit_vector)
            requires width < 64, mask == ((1u64 << width) - 1) as u64,
                result == word & mask;
        assert forall|index: nat| index < 64 implies
            #[trigger] bit_specs::word_bit(result, index)
                == (index < n && bit_specs::word_bit(word, index)) by {
            let position = index as u64;
            assert(((result >> position) & 1 == 1)
                == (position < width && ((word >> position) & 1 == 1))) by (bit_vector)
                requires width < 64, position < 64,
                    mask == ((1u64 << width) - 1) as u64, result == word & mask;
        }
    }
    result
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires *old(count) <= 64, n <= *old(count), n < 64,
    ensures *final(count) == *old(count) - n,
        *final(word) == *old(word) >> n,
        bit_specs::buffered_bits(*final(word), *final(count))
            == bit_specs::buffered_bits(*old(word), *old(count))
                .subrange(n as int, *old(count) as int),
        forall|pending: Seq<bool>| bit_specs::cached_suffix(*old(word), *old(count), pending) ==>
            #[trigger] bit_specs::cached_suffix(*final(word), *final(count), pending),
))]
pub(crate) fn consume_bits(word: &mut u64, count: &mut u8, n: u8) {
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::shifted_buffer(*word, *count, n);
        assert forall|pending: Seq<bool>| bit_specs::cached_suffix(*word, *count, pending) implies
            #[trigger] bit_specs::cached_suffix(*word >> n, (*count - n) as u8, pending) by {
            bit_proofs::cached_consume(*word, *count, n, pending);
        }
    }
    *word >>= n;
    *count -= n;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires *old(count) <= 64,
    ensures *final(count) == *old(count) as int - *old(count) as int % 8,
        *final(word) == *old(word) >> ((*old(count) as int % 8) as u8),
        bit_specs::buffered_bits(*final(word), *final(count))
            == bit_specs::buffered_bits(*old(word), *old(count))
                .subrange(*old(count) as int % 8, *old(count) as int),
        *final(count) % 8 == 0,
        forall|pending: Seq<bool>| bit_specs::cached_suffix(*old(word), *old(count), pending) ==>
            #[trigger] bit_specs::cached_suffix(*final(word), *final(count), pending),
))]
pub(super) fn align_to_byte(word: &mut u64, count: &mut u8) {
    #[cfg(verus_keep_ghost)]
    proof! { bit_proofs::alignment(*count); }
    let skip = *count & 7;
    consume_bits(word, count, skip);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires *old(count) <= 56,
    ensures *final(count) == *old(count) + 8,
        *final(word) == *old(word) | ((byte as u64) << *old(count)),
        bit_specs::append_compatible(*old(word), *old(count), byte as u64, 8) ==>
            bit_specs::buffered_bits(*final(word), *final(count))
                == bit_specs::buffered_bits(*old(word), *old(count))
                    + bit_specs::buffered_bits(byte as u64, 8),
        forall|pending: Seq<bool>| pending.len() >= 8
            && #[trigger] bit_specs::cached_suffix(*old(word), *old(count), pending)
            && bit_specs::buffered_bits(byte as u64, 8) == pending.take(8) ==>
            bit_specs::cached_suffix(*final(word), *final(count), pending.skip(8))
                && bit_specs::buffered_bits(*final(word), *final(count))
                    == bit_specs::buffered_bits(*old(word), *old(count)) + pending.take(8),
))]
pub(super) fn append_byte(word: &mut u64, count: &mut u8, byte: u8) {
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::appended_buffer(*word, *count, byte as u64, 8);
        assert forall|pending: Seq<bool>| pending.len() >= 8
            && #[trigger] bit_specs::cached_suffix(*word, *count, pending)
            && bit_specs::buffered_bits(byte as u64, 8) == pending.take(8) implies
            bit_specs::cached_suffix(*word | ((byte as u64) << *count),
                (*count + 8) as u8, pending.skip(8))
                && bit_specs::buffered_bits(*word | ((byte as u64) << *count), (*count + 8) as u8)
                    == bit_specs::buffered_bits(*word, *count) + pending.take(8) by {
            bit_proofs::byte_read_agrees(byte, pending);
            bit_proofs::cached_append(*word, *count, byte as u64, 8, pending);
        }
    }
    *word |= (byte as u64) << *count;
    *count += 8;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *old(count) < 64,
    ensures result == (63 - *old(count) as int) / 8, result <= 7,
        *final(count) == *old(count) as int + 8 * result as int,
        56 <= *final(count) <= 63,
        *final(word) == *old(word) | (read << *old(count)),
        bit_specs::append_compatible(*old(word), *old(count), read, (8 * result) as u8) ==>
            bit_specs::buffered_bits(*final(word), *final(count))
                == bit_specs::buffered_bits(*old(word), *old(count))
                    + bit_specs::buffered_bits(read, (8 * result) as u8),
        forall|pending: Seq<bool>| pending.len() >= 64
            && #[trigger] bit_specs::cached_suffix(*old(word), *old(count), pending)
            && bit_specs::buffered_bits(read, 64) == pending.take(64) ==>
            bit_specs::cached_suffix(*final(word), *final(count),
                pending.skip(8 * result as int))
                && bit_specs::buffered_bits(*final(word), *final(count))
                    == bit_specs::buffered_bits(*old(word), *old(count))
                        + pending.take(8 * result as int),
))]
pub(super) fn refill_bits(word: &mut u64, count: &mut u8, read: u64) -> u8 {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::refill_accounting(*count);
        let added = (8 * (((63u8 ^ *count) >> 3) as nat)) as u8;
        bit_proofs::appended_buffer(*word, *count, read, added);
    }
    *word |= read << *count;
    // XOR equals subtraction for counts in 0..63 and preserves the original hot path.
    let increment = (63 ^ *count) >> 3;
    *count |= 56;
    #[cfg(verus_keep_ghost)]
    proof! {
        let added = (8 * increment) as u8;
        assert(*count == (original_count + added) as u8);
        assert forall|pending: Seq<bool>| pending.len() >= 64
            && #[trigger] bit_specs::cached_suffix(original_word, original_count, pending)
            && bit_specs::buffered_bits(read, 64) == pending.take(64) implies
            bit_specs::cached_suffix(*word, *count, pending.skip(8 * increment as int))
                && bit_specs::buffered_bits(*word, *count)
                    == bit_specs::buffered_bits(original_word, original_count)
                        + pending.take(8 * increment as int) by {
            bit_proofs::full_read_agrees(read, pending, added);
            bit_proofs::cached_append(original_word, original_count, read, added, pending);
        }
    }
    increment
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *old(count) <= 64,
    ensures result == *old(count) as int / 8,
        *final(count) == *old(count) as int % 8,
        *final(count) <= 7,
        *final(word) == *old(word) & (((1u64 << *final(count)) - 1) as u64),
        bit_specs::buffered_bits(*final(word), *final(count))
            == bit_specs::buffered_bits(*old(word), *old(count)).take(*final(count) as int),
        forall|pending: Seq<bool>|
            #[trigger] bit_specs::cached_suffix(*final(word), *final(count), pending),
))]
pub(super) fn return_unused_bits(word: &mut u64, count: &mut u8) -> u8 {
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::alignment(*count);
        assert(*count >> 3 == *count / 8
            && ((*count >> 3) << 3) as int == *count as int - (*count & 7) as int)
            by (bit_vector);
    }
    let bytes = *count >> 3;
    *count -= bytes << 3;
    *word = peek_bits(*word, *count as usize);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(bit_specs::cached_suffix);
        assert forall|pending: Seq<bool>|
            #[trigger] bit_specs::cached_suffix(*word, *count, pending) by {
            assert forall|index: nat| *count <= index < 64 implies
                #[trigger] bit_specs::word_bit(*word, index) == false by {}
        }
    }
    bytes
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *old(count) <= 64, target <= 64,
        *old(count) as int + 8 * bit_specs::needed_bytes(*old(count), target) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 == if input.len() < bit_specs::needed_bytes(*old(count), target) {
            input.len() as int
        } else { bit_specs::needed_bytes(*old(count), target) as int },
        result.1 == (input.len() >= bit_specs::needed_bytes(*old(count), target)),
        result.1 == (*final(count) >= target),
        *final(count) == *old(count) as int + 8 * result.0 as int,
        *final(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        bit_specs::filled_word(*old(word), *old(count), *final(word),
            bit_specs::input_bits(input@).take(8 * result.0 as int)),
        bit_specs::buffered_bits(*final(word), *final(count))
            == bit_specs::buffered_bits(*old(word), *old(count))
                + bit_specs::input_bits(input@).take(8 * result.0 as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
))]
pub(crate) fn fill_from_slice(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    target: usize,
) -> (usize, bool) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost wanted = bit_specs::needed_bytes(*count, target);
        let ghost stream = bit_specs::input_bits(input@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::needed_bytes_bounds(*count, target);
        assert(bit_specs::buffered_bits(*word, *count)
            =~= bit_specs::buffered_bits(original_word, original_count) + stream.take(0));
        assert(stream.skip(0) =~= stream);
        assert(bit_specs::filled_word(original_word, original_count, *word, stream.take(0)));
    }
    let mut consumed = 0usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant consumed <= input.len(),
            consumed <= wanted <= 8,
            original_count <= 64,
            original_count == *old(count),
            original_word == *old(word),
            *count as int == original_count as int + 8 * consumed as int,
            original_count as int + 8 * wanted <= 64,
            *count <= 64,
            target <= 64,
            wanted == bit_specs::needed_bytes(original_count, target),
            original_count as int + 8 * wanted >= target,
            wanted > 0 ==> original_count as int + 8 * (wanted - 1) < target,
            bit_specs::buffered_bits(*word, *count)
                == bit_specs::buffered_bits(original_word, original_count)
                    + stream.take(8 * consumed as int),
            bit_specs::cached_suffix(*word, *count, stream.skip(8 * consumed as int)),
            bit_specs::filled_word(original_word, original_count, *word,
                stream.take(8 * consumed as int)),
            stream == bit_specs::input_bits(input@),
        decreases wanted - consumed,
    ))]
    while (*count as usize) < target {
        if consumed == input.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                if bit_specs::cached_suffix(original_word, original_count, Seq::empty()) {
                    reader_state_proofs::exact_fill_clean(original_word, original_count,
                        *word, stream.take(8 * consumed as int));
                }
            }
            return (consumed, false);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(consumed < wanted);
            assert(*count <= 56);
            bit_proofs::input_byte_step(input@, consumed as int);
            bit_proofs::filled_word_step(original_word, original_count, *word, *count,
                stream.take(8 * consumed as int), input@[consumed as int]);
        }
        append_byte(word, count, input[consumed]);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((bit_specs::buffered_bits(original_word, original_count)
                + stream.take(8 * consumed as int))
                + bit_specs::buffered_bits(input@[consumed as int] as u64, 8)
                =~= bit_specs::buffered_bits(original_word, original_count)
                    + (stream.take(8 * consumed as int)
                        + bit_specs::buffered_bits(input@[consumed as int] as u64, 8)));
            assert(bit_specs::buffered_bits(*word, *count)
                == bit_specs::buffered_bits(original_word, original_count)
                    + stream.take(8 * (consumed as int + 1)));
        }
        consumed += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if bit_specs::cached_suffix(original_word, original_count, Seq::empty()) {
            reader_state_proofs::exact_fill_clean(original_word, original_count,
                *word, stream.take(8 * consumed as int));
        }
    }
    (consumed, true)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires input.len() >= 8,
    ensures bit_specs::buffered_bits(result, 64) == bit_specs::input_bits(input@).take(64),
))]
fn read_word(input: &[u8]) -> u64 {
    let result = u64::from(input[0])
        | (u64::from(input[1]) << 8)
        | (u64::from(input[2]) << 16)
        | (u64::from(input[3]) << 24)
        | (u64::from(input[4]) << 32)
        | (u64::from(input[5]) << 40)
        | (u64::from(input[6]) << 48)
        | (u64::from(input[7]) << 56);
    #[cfg(verus_keep_ghost)]
    proof! {
        let a = input@[0] as u64;
        let b = input@[1] as u64;
        let c = input@[2] as u64;
        let d = input@[3] as u64;
        let e = input@[4] as u64;
        let f = input@[5] as u64;
        let g = input@[6] as u64;
        let h = input@[7] as u64;
        let bits = bit_specs::buffered_bits(result, 64);
        let expected = bit_specs::input_bits(input@).take(64);
        assert forall|index: int| 0 <= index < 64 implies
            #[trigger] bits[index] == expected[index] by {
            let position = index as u64;
            let octet = input@[index / 8] as u64;
            assert(octet == if position < 8 { a } else if position < 16 { b }
                else if position < 24 { c } else if position < 32 { d }
                else if position < 40 { e } else if position < 48 { f }
                else if position < 56 { g } else { h });
            assert(((result >> position) & 1) == ((octet >> (position % 8)) & 1))
                by (bit_vector) requires position < 64,
                    a <= 255, b <= 255, c <= 255, d <= 255,
                    e <= 255, f <= 255, g <= 255, h <= 255,
                    result == a | (b << 8u64) | (c << 16u64) | (d << 24u64)
                        | (e << 32u64) | (f << 40u64) | (g << 48u64) | (h << 56u64),
                    octet == if position < 8 { a } else if position < 16 { b }
                        else if position < 24 { c } else if position < 32 { d }
                        else if position < 40 { e } else if position < 48 { f }
                        else if position < 56 { g } else { h };
        }
        assert(bits =~= expected);
    }
    result
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *old(count) < 64, input.len() >= 8,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result == (63 - *old(count) as int) / 8,
        result <= 7,
        *final(count) == *old(count) as int + 8 * result as int,
        56 <= *final(count) <= 63,
        bit_specs::buffered_bits(*final(word), *final(count))
            == bit_specs::buffered_bits(*old(word), *old(count))
                + bit_specs::input_bits(input@).take(8 * result as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result as int)),
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result as int)
            == bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
        exists|read: u64| #[trigger] bit_specs::buffered_bits(read, 64)
                == bit_specs::input_bits(input@).take(64)
            && *final(word) == *old(word) | (read << *old(count)),
))]
pub(super) fn refill_from_slice(word: &mut u64, count: &mut u8, input: &[u8]) -> u8 {
    let read = read_word(input);
    refill_bits(word, count, read)
}
