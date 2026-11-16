use crate::dynamic_header_specs as model;
use crate::huffman_specs as huffman;
use vstd::prelude::*;

verus! {

pub proof fn symbol_transition_from_effect(alphabet: Seq<u16>,
    before: Seq<u16>, after: Seq<u16>, processed: nat, final_processed: nat,
    total: nat, source: Seq<bool>, count: u8, available: nat,
    code_bits: nat, symbol: nat, reported: nat, dropped: nat, outcome: Option<bool>)
    requires (huffman::maximum_length(alphabet) == 0 && source.len() > 0
            && code_bits == 1 && symbol == 0)
        || (huffman::maximum_length(alphabet) > 0
            && huffman::code_length_source_prefix(alphabet, symbol as int, source)
            && code_bits == alphabet[symbol as int]),
        model::symbol_input_effect(before, after, processed, final_processed,
            total, source, count, available, code_bits, symbol, reported, dropped, outcome),
    ensures model::symbol_input_transition(alphabet, before, after, processed, final_processed,
        total, source, count, available, reported, dropped, outcome),
{
    reveal(model::symbol_input_transition);
    if huffman::maximum_length(alphabet) > 0 {
        assert(exists|selected: int| #[trigger] huffman::code_length_source_prefix(alphabet, selected, source)
            && model::symbol_input_effect(before, after, processed, final_processed,
                total, source, count, available, alphabet[selected] as nat, selected as nat,
                reported, dropped, outcome));
    }
}

pub proof fn symbol_transition_without_code(alphabet: Seq<u16>, before: Seq<u16>,
    processed: nat, total: nat, source: Seq<bool>, count: u8, available: nat)
    requires huffman::maximum_length(alphabet) == 0 ==> source.len() == 0,
        huffman::maximum_length(alphabet) > 0 ==>
            !(exists|symbol: int| huffman::code_length_source_prefix(alphabet, symbol, source)),
    ensures model::symbol_input_transition(alphabet, before, before, processed, processed,
        total, source, count, available, 0, 0, None),
{
    reveal(model::symbol_input_transition);
}

pub proof fn symbol_effect_after_prefix(before: Seq<u16>, after: Seq<u16>,
    processed: nat, final_processed: nat, total: nat, source: Seq<bool>,
    count: u8, available: nat, code_bits: nat, symbol: nat,
    first: nat, second: nat, dropped: nat, outcome: Option<bool>)
    requires count <= 64, 1 <= code_bits <= 7, symbol <= 18,
        count as nat + 8 * first <= 64, first <= available,
        first <= crate::bit_specs::needed_bytes(count, code_bits as usize),
        model::symbol_input_effect(before, after, processed, final_processed, total,
            source, (count as nat + 8 * first) as u8, (available - first) as nat,
            code_bits, symbol, second, dropped, outcome),
    ensures model::symbol_input_effect(before, after, processed, final_processed, total,
        source, count, available, code_bits, symbol, first + second, dropped, outcome),
{
    reveal(model::symbol_input_effect);
    let target = if symbol < 16 { code_bits }
        else { code_bits + model::repeat_extra_width(symbol) };
    crate::bit_proofs::needed_bytes_bounds(count, code_bits as usize);
    crate::bit_proofs::needed_bytes_bounds(count, target as usize);
    assert(first <= crate::bit_specs::needed_bytes(count, target as usize));
    crate::bit_proofs::capped_fill_after_prefix(count, target as usize, first, available);
}

pub proof fn repeat_input_frames(before: Seq<u16>, after: Seq<u16>,
    processed: nat, final_processed: nat, total: nat, source: Seq<bool>,
    code_bits: nat, symbol: nat, outcome: Option<bool>)
    requires model::repeat_input_transition(before, after, processed, final_processed,
        total, source, code_bits, symbol, outcome),
    ensures after.len() == before.len(), processed <= final_processed,
        outcome == Some(true) ==> processed < final_processed,
        outcome != Some(true) ==> after == before && final_processed == processed,
        forall|index: int| 0 <= index < before.len()
            && (index < processed || final_processed <= index)
                ==> #[trigger] after[index] == before[index],
{
    if source.len() >= code_bits + model::repeat_extra_width(symbol) {
        if outcome != Some(true) {
            assert(after =~= before);
        }
    }
}

pub proof fn two_symbol_header_codes()
    ensures huffman::maximum_length(seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0]) == 1,
        huffman::canonical_prefix(seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], 0) == 0,
        huffman::canonical_prefix(seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0], 16) == 1,
{
    let alphabet = seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0];
    maximum_bounded(alphabet, 1);
    crate::huffman_decode::maximum_symbol_bound(alphabet, 0);
    assert(huffman::canonical_code(alphabet, 0) == 0
        && huffman::canonical_code(alphabet, 16) == 1) by {
        reveal_with_fuel(huffman::occurrences, 20);
    }
    assert(huffman::capacity(31) == 2147483648) by (compute);
    assert forall|index: u32| index < 32 implies
        #[trigger] huffman::word_bit(0, index) == huffman::word_bit(0, (31 - index) as u32) by {
        assert((0u32 >> index) & 1 == (0u32 >> ((31 - index) as u32)) & 1)
            by (bit_vector) requires index < 32;
    }
    crate::huffman_proofs::reversal_matches_model(0, 0);
    assert forall|index: u32| index < 32 implies
        #[trigger] huffman::word_bit(1, index)
            == huffman::word_bit(0x80000000, (31 - index) as u32) by {
        assert((1u32 >> index) & 1 == (0x80000000u32 >> ((31 - index) as u32)) & 1)
            by (bit_vector) requires index < 32;
    }
    crate::huffman_proofs::reversal_matches_model(0x80000000, 1);
}

pub proof fn symbol_input_fixture()
    ensures model::symbol_input_transition(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![7u16,9,9,9,9], seq![7u16,0,9,9,9], 1, 2, 5,
            seq![false], 1, 0, 0, 1, Some(true)),
        model::symbol_input_transition(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![7u16,9,9,9,9], seq![7u16,7,7,7,9], 1, 4, 5,
            seq![true,false,false,true,false,true,false,true], 0, 1, 1, 3, Some(true)),
        model::symbol_input_transition(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![7u16,9,9,9,9], seq![7u16,9,9,9,9], 0, 0, 5,
            seq![true,false,false], 3, 0, 0, 1, Some(false)),
        model::symbol_input_transition(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![7u16,9,9,9,9], seq![7u16,9,9,9,9], 1, 1, 3,
            seq![true,false,false], 3, 0, 0, 3, Some(false)),
        model::symbol_input_transition(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![7u16,9,9,9,9], seq![7u16,9,9,9,9], 0, 0, 5,
            seq![true,false], 2, 0, 0, 0, None),
        model::symbol_input_transition(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![7u16,9,9,9,9], seq![7u16,9,9,9,9], 1, 1, 5,
            Seq::empty(), 0, 0, 0, 0, None),
{
    let alphabet = seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0];
    two_symbol_header_codes();
    reveal(model::symbol_input_effect);
    reveal(model::symbol_input_transition);
    reveal(model::repeat_extra_value);
    reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    assert(huffman::code_length_source_prefix(alphabet, 0, seq![false]));
    assert(huffman::code_length_source_prefix(alphabet, 16,
        seq![true,false,false,true,false,true,false,true]));
    assert(huffman::code_length_source_prefix(alphabet, 16, seq![true,false,false]));
    assert(huffman::code_length_source_prefix(alphabet, 16, seq![true,false]));
}

pub proof fn empty_symbol_input_fixture()
    ensures model::symbol_input_transition(Seq::new(19, |index: int| 0u16),
            seq![9u16,9], seq![0u16,9], 0, 1, 2,
            seq![true,false,false,false,false,false,false,false], 0, 1, 1, 1, Some(true)),
        model::symbol_input_transition(Seq::new(19, |index: int| 0u16),
            seq![9u16,9], seq![9u16,9], 0, 0, 2,
            Seq::empty(), 0, 0, 0, 0, None),
{
    maximum_bounded(Seq::new(19, |index: int| 0u16), 0);
    reveal(model::symbol_input_effect);
    reveal(model::symbol_input_transition);
}

pub proof fn wire_roundtrip(position: nat)
    requires position < 19,
    ensures model::wire_symbol(position) < 19,
        model::wire_position(model::wire_symbol(position)) == position,
{
    if position < 3 {
    } else if position == 3 {
    } else if position % 2 == 0 {
        assert(position == 2 * (position / 2));
    } else {
        assert(position % 2 == 1);
        assert(19 - position == 2 * ((19 - position) / 2));
    }
}

pub proof fn wire_inverse(symbol: nat)
    requires symbol < 19,
    ensures model::wire_position(symbol) < 19,
        model::wire_symbol(model::wire_position(symbol)) == symbol,
{
    if symbol >= 16 {
    } else if symbol == 0 {
    } else if symbol <= 7 {
        assert((19 - 2 * symbol) % 2 == 1);
    } else {
        assert((2 * (symbol - 6)) % 2 == 0);
    }
}

pub proof fn wire_injective(first: nat, second: nat)
    requires first < 19, second < 19, model::wire_symbol(first) == model::wire_symbol(second),
    ensures first == second,
{
    wire_roundtrip(first);
    wire_roundtrip(second);
}

pub proof fn rfc_wire_order()
    ensures Seq::new(19, |index: int| model::wire_symbol(index as nat))
        == seq![16nat, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15],
{
    let order = seq![16nat, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
    assert forall|index: int| 0 <= index < 19 implies
        #[trigger] model::wire_symbol(index as nat) == order[index] by {
        assert(index == 0 || index == 1 || index == 2 || index == 3 || index == 4
            || index == 5 || index == 6 || index == 7 || index == 8 || index == 9
            || index == 10 || index == 11 || index == 12 || index == 13 || index == 14
            || index == 15 || index == 16 || index == 17 || index == 18);
    }
    assert(Seq::new(19, |index: int| model::wire_symbol(index as nat)) =~= order);
}

pub proof fn header_counts_bounds(source: Seq<bool>)
    requires source.len() >= 14,
    ensures 257 <= model::header_counts(source).0 <= 288,
        1 <= model::header_counts(source).1 <= 32,
        4 <= model::header_counts(source).2 <= 19,
{
    reveal_with_fuel(crate::bit_specs::low_first_value, 6);
}

pub proof fn header_counts_fixture()
    ensures model::header_counts(
        seq![false, true, true, false, true, true, false, true,
            true, false, true, true, true, false]) == (279nat, 14nat, 11nat),
{
    reveal_with_fuel(crate::bit_specs::low_first_value, 6);
}

pub proof fn header_from_wire(before: Seq<u16>, after: Seq<u16>, start: nat, end: nat,
    source: Seq<bool>)
    requires before.len() >= 19, after.len() == before.len(), start <= end <= 19,
        3 * (end - start) <= source.len(),
        forall|position: nat| position < 19 ==>
            #[trigger] after[model::wire_symbol(position) as int]
                == if start <= position < end {
                    crate::bit_specs::three_bit_value(source.skip(3 * (position as int - start as int)))
                } else { before[model::wire_symbol(position) as int] },
        forall|index: int| 19 <= index < before.len() ==> #[trigger] after[index] == before[index],
    ensures after == model::length_header(before, start, end, source, false),
{
    let expected = model::length_header(before, start, end, source, false);
    assert forall|index: int| 0 <= index < before.len() implies
        #[trigger] after[index] == expected[index] by {
        if index < 19 {
            wire_inverse(index as nat);
            assert(after[model::wire_symbol(model::wire_position(index as nat)) as int]
                == expected[index]);
        }
    }
    assert(after =~= expected);
}

pub proof fn pad_read_header(before: Seq<u16>, after: Seq<u16>, start: nat, end: nat,
    source: Seq<bool>)
    requires before.len() >= 19, start <= end <= 19, 3 * (end - start) <= source.len(),
        model::padded_header(model::length_header(before, start, end, source, false), after, end),
    ensures after == model::length_header(before, start, end, source, true),
{
    let expected = model::length_header(before, start, end, source, true);
    assert forall|index: int| 0 <= index < before.len() implies
        #[trigger] after[index] == expected[index] by {
        if index < 19 {
            wire_inverse(index as nat);
            assert(after[model::wire_symbol(model::wire_position(index as nat)) as int]
                == expected[index]);
        }
    }
    assert(after =~= expected);
}

pub proof fn complete_prefix_bounded(lengths: Seq<u16>)
    requires model::prefix_fits(lengths, 19),
    ensures forall|symbol: int| 0 <= symbol < 19 ==> #[trigger] lengths[symbol] <= 7,
{
    reveal(model::prefix_fits);
    assert forall|symbol: int| 0 <= symbol < 19 implies #[trigger] lengths[symbol] <= 7 by {
        wire_inverse(symbol as nat);
        let position = model::wire_position(symbol as nat);
        assert(lengths[model::wire_symbol(position) as int] <= 7);
    }
}

pub proof fn maximum_bounded(lengths: Seq<u16>, limit: nat)
    requires forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= limit,
    ensures huffman::maximum_length(lengths) <= limit,
    decreases lengths.len(),
{
    if lengths.len() > 0 {
        assert forall|symbol: int| 0 <= symbol < lengths.drop_last().len()
            implies lengths.drop_last()[symbol] <= limit by {
            assert(lengths.drop_last()[symbol] == lengths[symbol]);
        }
        maximum_bounded(lengths.drop_last(), limit);
        assert(lengths.last() <= limit);
    }
}

pub proof fn repeat_count_bounds(symbol: nat, extra: nat)
    requires 16 <= symbol <= 18, extra < model::repeat_extra_limit(symbol),
    ensures symbol == 16 ==> 3 <= model::repeat_count(symbol, extra) <= 6,
        symbol == 17 ==> 3 <= model::repeat_count(symbol, extra) <= 10,
        symbol == 18 ==> 11 <= model::repeat_count(symbol, extra) <= 138,
{
}

pub proof fn repeat_extra_bounds(source: Seq<bool>, code_bits: nat, symbol: nat)
    requires 16 <= symbol <= 18,
        source.len() >= code_bits + model::repeat_extra_width(symbol),
    ensures model::repeat_extra_value(source, code_bits, symbol) < model::repeat_extra_limit(symbol),
{
    reveal(model::repeat_extra_value);
    reveal_with_fuel(crate::bit_specs::low_first_value, 8);
}

pub proof fn repeat_input_fixture()
    ensures model::repeat_input_transition(
            seq![7u16, 4, 9, 9, 9, 9], seq![7u16, 4, 4, 4, 4, 4],
            2, 6, 6, seq![true, false, true, true, false, true, false, false, true, true],
            3, 16, Some(true)),
        model::repeat_input_transition(
            seq![7u16, 4, 9, 9, 9, 9], seq![7u16, 4, 9, 9, 9, 9],
            2, 2, 5, seq![true, false, true, true, false, true, false, false, true, true],
            3, 16, Some(false)),
        model::repeat_input_transition(
            seq![9u16, 9, 9, 9], seq![9u16, 9, 9, 9],
            0, 0, 4, seq![true, false, true, true, false, true, false, false, true, true],
            3, 16, Some(false)),
        !model::repeat_input_transition(
            seq![9u16, 9, 9, 9], seq![9u16, 9, 9, 9],
            0, 0, 4, seq![true, false, true, true, false, true, false, false, true, true],
            3, 16, None),
        model::repeat_input_transition(
            seq![9u16, 9, 9, 9], seq![9u16, 9, 9, 9],
            0, 0, 4, seq![true, false, true, true], 3, 16, None),
        !model::repeat_input_transition(
            seq![9u16, 9, 9, 9], seq![9u16, 9, 9, 9],
            0, 0, 4, seq![true, false, true, true], 3, 16, Some(false)),
{
    reveal(model::repeat_extra_value);
    reveal_with_fuel(crate::bit_specs::low_first_value, 8);
}

pub proof fn repeat_extra_fixture()
    ensures model::repeat_extra_value(
            seq![true, false, true, true, false, true, false, false, true, true], 3, 16) == 1,
        model::repeat_extra_value(
            seq![true, false, true, true, false, true, false, false, true, true], 3, 17) == 5,
        model::repeat_extra_value(
            seq![true, false, true, true, false, true, false, false, true, true], 3, 18) == 101,
        model::repeat_consumed_bits(4, 3, 16, 0) == 0,
        model::repeat_consumed_bits(5, 3, 16, 0) == 3,
        model::repeat_consumed_bits(5, 3, 16, 1) == 5,
        model::repeat_consumed_bits(5, 3, 17, 0) == 0,
        model::repeat_consumed_bits(6, 3, 17, 0) == 6,
        model::repeat_consumed_bits(10, 3, 18, 0) == 10,
{
    reveal(model::repeat_extra_value);
    reveal_with_fuel(crate::bit_specs::low_first_value, 8);
}

}
