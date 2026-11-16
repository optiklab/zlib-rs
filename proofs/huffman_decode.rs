use crate::canonical_intervals as intervals;
use crate::huffman_proofs as facts;
use crate::huffman_specs as model;
use crate::Code;
use vstd::prelude::*;

verus! {

pub proof fn reversal_prefix(word: u32, width: u32) -> (result: u32)
    requires width <= 32,
    ensures
        forall|index: u32| index < width ==> #[trigger] model::word_bit(result, index)
            == model::word_bit(word, (31 - index) as u32),
        forall|index: u32| width <= index < 32 ==>
            #[trigger] model::word_bit(result, index) == 0,
    decreases width,
{
    if width == 0 {
        assert forall|index: u32| index < 32 implies
            #[trigger] model::word_bit(0, index) == 0 by {
            assert((0u32 >> index) & 1 == 0) by (bit_vector);
        }
        0
    } else {
        let position = (width - 1) as u32;
        let previous = reversal_prefix(word, position);
        let bit = (word >> ((31 - position) as u32)) & 1;
        assert(bit <= 1) by (bit_vector)
            requires bit == (word >> ((31 - position) as u32)) & 1;
        let result = previous | (bit << position);
        assert forall|index: u32| index < width implies
            #[trigger] model::word_bit(result, index)
                == model::word_bit(word, (31 - index) as u32) by {
            if index < position {
                assert(model::word_bit(previous, index)
                    == model::word_bit(word, (31 - index) as u32));
                assert((result >> index) & 1 == (previous >> index) & 1)
                    by (bit_vector) requires index < position < 32,
                        result == previous | (bit << position), bit <= 1;
            } else {
                assert(index == position);
                assert(model::word_bit(previous, position) == 0);
                assert((result >> position) & 1 == bit)
                    by (bit_vector) requires position < 32,
                        result == previous | (bit << position),
                        (previous >> position) & 1 == 0, bit <= 1;
            }
        }
        assert forall|index: u32| width <= index < 32 implies
            #[trigger] model::word_bit(result, index) == 0 by {
            assert(model::word_bit(previous, index) == 0);
            assert((result >> index) & 1 == 0) by (bit_vector)
                requires position < index < 32, result == previous | (bit << position),
                    (previous >> index) & 1 == 0, bit <= 1;
        }
        result
    }
}

pub proof fn reversal_total(word: u32)
    ensures model::is_reversal(word, model::reversed_word(word)),
{
    let witness = reversal_prefix(word, 32);
    facts::reversal_matches_model(word, witness);
}

pub proof fn reversal_symmetric(word: u32, reversed: u32)
    requires model::is_reversal(word, reversed),
    ensures model::is_reversal(reversed, word),
{
    assert forall|index: u32| index < 32 implies
        #[trigger] model::word_bit(word, index)
            == model::word_bit(reversed, (31 - index) as u32) by {
        let opposite = (31 - index) as u32;
        assert(opposite < 32 && (31 - opposite) as u32 == index) by (bit_vector)
            requires index < 32, opposite == (31 - index) as u32;
        assert(model::word_bit(reversed, opposite) == model::word_bit(word, index));
    }
}

pub proof fn reversal_low_prefix(word: u32, normalized: u32, length: u32)
    requires 1 <= length <= 15, model::is_reversal(word, normalized),
    ensures model::is_reversal(normalized & !(u32::MAX >> length),
        word & (u32::MAX >> ((32 - length) as u32))),
{
    let low = word & (u32::MAX >> ((32 - length) as u32));
    let high = normalized & !(u32::MAX >> length);
    assert forall|index: u32| index < 32 implies
        #[trigger] model::word_bit(low, index)
            == model::word_bit(high, (31 - index) as u32) by {
        let opposite = (31 - index) as u32;
        assert(opposite < 32 && (31 - opposite) as u32 == index) by (bit_vector)
            requires index < 32, opposite == (31 - index) as u32;
        assert(model::word_bit(normalized, opposite) == model::word_bit(word, index));
        assert((low >> index) & 1 == (high >> opposite) & 1) by (bit_vector)
            requires index < 32, opposite == (31 - index) as u32, 1 <= length <= 15,
                low == word & (u32::MAX >> ((32 - length) as u32)),
                high == normalized & !(u32::MAX >> length),
                (normalized >> opposite) & 1 == (word >> index) & 1;
    }
}

pub proof fn low_prefix_interval(word: u32, normalized: u32, cursor: u32,
    prefix: u32, length: u32)
    requires 1 <= length <= 15, model::is_reversal(word, normalized),
        model::is_reversal(cursor, prefix), model::aligned_cursor(cursor, length),
    ensures (word & (u32::MAX >> ((32 - length) as u32)) == prefix)
        <==> ((cursor as int) <= (normalized as int)
            < (cursor as int) + model::capacity((32 - length) as nat)),
{
    let low = word & (u32::MAX >> ((32 - length) as u32));
    let high = normalized & !(u32::MAX >> length);
    reversal_low_prefix(word, normalized, length);
    if low == prefix {
        reversal_symmetric(high, low);
        reversal_symmetric(cursor, prefix);
        facts::reversal_unique(prefix, high, cursor);
    }
    if high == cursor {
        facts::reversal_unique(cursor, low, prefix);
    }
    let step = 0x80000000u32 >> ((length - 1) as u32);
    facts::normalized_code_step(length as usize);
    assert((high == cursor) <==>
        (cursor as u64 <= normalized as u64
            && (normalized as u64) < cursor as u64 + step as u64)) by (bit_vector)
        requires 1 <= length <= 15, high == normalized & !(u32::MAX >> length),
            cursor & (u32::MAX >> length) == 0,
            step == 0x80000000u32 >> ((length - 1) as u32);
}

pub proof fn low_mask_remainder(word: u32, length: u32)
    requires 1 <= length <= 15,
    ensures (word & (u32::MAX >> ((32 - length) as u32))) as int
        == (word as int) % model::capacity(length as nat),
{
    facts::capacity_is_power(length as nat);
    facts::u32_shift_capacity(length);
    facts::capacity_positive(length as nat);
    facts::depth_capacity(length as nat);
    vstd::bits::lemma_u32_low_bits_mask_is_mod(word, length as nat);
    assert(vstd::bits::low_bits_mask(length as nat) == model::capacity(length as nat) - 1);
    let mask = vstd::bits::low_bits_mask(length as nat) as u32;
    assert(mask == ((1u32 << length) - 1) as u32);
    assert(mask == u32::MAX >> ((32 - length) as u32)) by (bit_vector)
        requires 1 <= length <= 15, mask == ((1u32 << length) - 1) as u32;
}

pub proof fn canonical_word(lengths: Seq<u16>, counts: Seq<u16>, symbol: int)
    requires model::valid_histogram(lengths, counts),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
        model::valid_prefix(counts, lengths[symbol] as nat),
    ensures {
        let length = lengths[symbol] as u32;
        let value = model::canonical_code(lengths, symbol)
            * model::capacity((32 - length) as nat);
        let cursor = value as u32;
        value == cursor as int && model::aligned_cursor(cursor, length)
            && model::is_reversal(cursor, model::canonical_prefix(lengths, symbol))
    },
{
    let length = lengths[symbol] as u32;
    let shift = (32 - length) as u32;
    let code = model::canonical_code(lengths, symbol);
    let value = code * model::capacity(shift as nat);
    intervals::canonical_interval_bound(lengths, counts, symbol);
    facts::canonical_code_bound(lengths, counts, symbol);
    facts::depth_capacity(length as nat);
    facts::capacity_positive(shift as nat);
    facts::capacity_is_power(shift as nat);
    vstd::bits::lemma_u32_shl_is_mul(code as u32, shift);
    let cursor = value as u32;
    let code_word = code as u32;
    assert(model::aligned_cursor(cursor, length)) by (bit_vector)
        requires 1 <= length <= 15, shift == (32 - length) as u32,
            cursor == code_word << shift;
    reversal_total(cursor);
}

pub proof fn prefix_matches_interval(lengths: Seq<u16>, counts: Seq<u16>,
    symbol: int, word: u32)
    requires model::valid_histogram(lengths, counts),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
        model::valid_prefix(counts, lengths[symbol] as nat),
    ensures model::code_prefix_matches(lengths, symbol, word)
        <==> model::canonical_interval_contains(lengths, symbol,
            model::reversed_word(word) as int),
{
    canonical_word(lengths, counts, symbol);
    reversal_total(word);
    low_mask_remainder(word, lengths[symbol] as u32);
    let cursor = (model::canonical_code(lengths, symbol)
        * model::capacity((32 - lengths[symbol]) as nat)) as u32;
    low_prefix_interval(word, model::reversed_word(word), cursor,
        model::canonical_prefix(lengths, symbol), lengths[symbol] as u32);
    let code = model::canonical_code(lengths, symbol);
    let width = model::capacity((32 - lengths[symbol]) as nat);
    assert(code * width + width == (code + 1) * width) by (nonlinear_arith);
}

pub proof fn matching_symbol_unique(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int, word: u32)
    requires model::valid_histogram(lengths, counts), model::valid_prefix(counts, 15),
        model::code_prefix_matches(lengths, first, word),
        model::code_prefix_matches(lengths, second, word),
    ensures first == second,
{
    prefix_matches_interval(lengths, counts, first, word);
    prefix_matches_interval(lengths, counts, second, word);
    if first != second {
        intervals::canonical_intervals_disjoint(lengths, counts, first, second);
    }
}

pub proof fn matching_symbol_exists(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, word: u32)
    requires model::valid_histogram(lengths, counts), model::valid_prefix(counts, 15),
        model::bucket_ordered(lengths, counts, work), model::slots(counts, 15) == 0,
    ensures exists|symbol: int| #[trigger] model::code_prefix_matches(lengths, symbol, word),
{
    reversal_total(word);
    let normalized = model::reversed_word(word) as int;
    intervals::canonical_intervals_partition(lengths, counts, work, normalized);
    let selected = choose|symbol: int|
        #[trigger] model::canonical_interval_contains(lengths, symbol, normalized)
        && (forall|other: int| #[trigger] model::canonical_interval_contains(lengths, other, normalized)
            ==> other == symbol);
    prefix_matches_interval(lengths, counts, selected, word);
    assert(model::code_prefix_matches(lengths, selected, word));
}

pub(crate) proof fn root_written_symbol(lengths: Seq<u16>, work: Seq<u16>,
    processed: nat, index: int, target: u16, position: nat, original: Code)
    requires forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= 7,
        1 <= model::maximum_length(lengths) <= 7,
        model::valid_histogram(lengths, model::histogram(lengths)),
        model::valid_prefix(model::histogram(lengths), 15),
        model::bucket_ordered(lengths, model::histogram(lengths), work),
        position < processed <= model::before(model::histogram(lengths), 16),
        position < work.len(), work[position as int] == target,
        0 <= index < model::capacity(model::maximum_length(lengths) as nat),
        model::code_prefix_matches(lengths, target as int, index as u32),
    ensures model::root_codes_after(lengths, work, processed, index, original)
        == (Code { op: 0, bits: lengths[target as int] as u8, val: target }),
    decreases processed,
{
    let counts = model::histogram(lengths);
    let previous = (processed - 1) as nat;
    facts::ordered_symbol_at(lengths, counts, work, previous as int);
    let last = work[previous as int] as int;
    facts::depth_capacity(model::maximum_length(lengths) as nat);
    assert(index as u32 as int == index);
    facts::root_codes_step(lengths, work, previous, index, original);
    if model::code_prefix_matches(lengths, last, index as u32) {
        matching_symbol_unique(lengths, counts, target as int, last, index as u32);
    } else {
        assert(position < previous);
        root_written_symbol(lengths, work, previous, index, target, position, original);
    }
}

pub(crate) proof fn root_table_decodes(lengths: Seq<u16>, work: Seq<u16>,
    table: Seq<Code>, original: Seq<Code>)
    requires lengths.len() <= 19,
        forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= 7,
        1 <= model::maximum_length(lengths) <= 7,
        model::valid_histogram(lengths, model::histogram(lengths)),
        model::valid_prefix(model::histogram(lengths), 15),
        model::slots(model::histogram(lengths), 15) == 0,
        model::capacity(model::maximum_length(lengths) as nat) <= table.len(),
        model::root_codes_table(lengths, work,
            model::before(model::histogram(lengths), 16), table, original),
    ensures model::root_decoding_table(lengths, table),
{
    let counts = model::histogram(lengths);
    let total = model::before(counts, 16);
    facts::depth_capacity(model::maximum_length(lengths) as nat);
    assert forall|index: int| 0 <= index < model::capacity(model::maximum_length(lengths) as nat)
        implies #[trigger] model::root_entry_decodes(lengths, table[index], index as u32) by {
        matching_symbol_exists(lengths, counts, work, index as u32);
        let selected = choose|symbol: int|
            #[trigger] model::code_prefix_matches(lengths, symbol, index as u32);
        facts::sorted_symbol_position(lengths, counts, work, selected);
        let position = (model::before(counts, lengths[selected] as nat)
            + model::occurrences(lengths.take(selected), lengths[selected])) as nat;
        root_written_symbol(lengths, work, total, index, selected as u16, position, original[index]);
        assert(table[index] == Code {
            op: 0, bits: lengths[selected] as u8, val: selected as u16,
        });
        assert forall|other: int| #[trigger] model::code_prefix_matches(lengths, other, index as u32)
            implies other == selected by {
            matching_symbol_unique(lengths, counts, selected, other, index as u32);
        }
        assert(model::root_entry_decodes(lengths, table[index], index as u32));
    }
}

pub proof fn maximum_symbol_bound(lengths: Seq<u16>, symbol: int)
    requires 0 <= symbol < lengths.len(),
    ensures lengths[symbol] <= model::maximum_length(lengths),
    decreases lengths.len(),
{
    if symbol < lengths.len() - 1 {
        maximum_symbol_bound(lengths.drop_last(), symbol);
        assert(lengths.drop_last()[symbol] == lengths[symbol]);
    } else {
        assert(lengths[symbol] == lengths.last());
    }
}

pub proof fn prefix_root_projection(lengths: Seq<u16>, symbol: int, word: u32, root: nat)
    requires 0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= root <= 15,
    ensures model::code_prefix_matches(lengths, symbol, word)
        <==> model::code_prefix_matches(lengths, symbol,
            ((word as int) % model::capacity(root)) as u32),
{
    let length = lengths[symbol] as nat;
    let stride = model::capacity(length);
    let repeats = model::capacity((root - length) as nat);
    facts::capacity_product(length, (root - length) as nat);
    facts::capacity_positive(length);
    facts::capacity_positive((root - length) as nat);
    facts::depth_capacity(root);
    vstd::arithmetic::div_mod::lemma_mod_mod(word as int, stride, repeats);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as int, model::capacity(root));
}

pub(crate) proof fn root_word_decodes(lengths: Seq<u16>, table: Seq<Code>, word: u32)
    requires model::root_decoding_table(lengths, table),
    ensures model::root_entry_decodes(lengths,
        table[(word as int) % model::capacity(model::maximum_length(lengths) as nat)], word),
{
    let root = model::maximum_length(lengths) as nat;
    let index = (word as int) % model::capacity(root);
    facts::capacity_positive(root);
    facts::depth_capacity(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as int, model::capacity(root));
    assert(model::root_entry_decodes(lengths, table[index], index as u32));
    let selected = choose|symbol: int|
        #[trigger] model::code_prefix_matches(lengths, symbol, index as u32)
        && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
        && table[index] == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 }
        && (forall|other: int| #[trigger] model::code_prefix_matches(lengths, other, index as u32)
            ==> other == symbol);
    maximum_symbol_bound(lengths, selected);
    prefix_root_projection(lengths, selected, word, root);
    assert(model::code_prefix_matches(lengths, selected, word));
    assert forall|other: int| #[trigger] model::code_prefix_matches(lengths, other, word)
        implies other == selected by {
        maximum_symbol_bound(lengths, other);
        prefix_root_projection(lengths, other, word, root);
    }
    assert(model::root_entry_decodes(lengths, table[index], word));
}

}
