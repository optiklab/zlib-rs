use crate::huffman_decode as decode;
use crate::huffman_proofs as facts;
use crate::huffman_specs as model;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) proof fn masked_subtable_index(word: u64, root: u8, width: u8, masked: u64)
    requires 1 <= root, 1 <= width, root as int + width as int <= 15,
        masked == word & (((1u64 << (root as u64 + width as u64)) - 1) as u64),
    ensures (masked >> root) as int
        == ((word as int) / model::capacity(root as nat)) % model::capacity(width as nat),
{
    let r = root as u64;
    let w = width as u64;
    let shifted = word >> r;
    let mask = ((1u64 << w) - 1) as u64;
    assert(masked >> r == shifted & mask) by (bit_vector)
        requires 1 <= r, 1 <= w, r + w <= 15,
            shifted == word >> r, mask == ((1u64 << w) - 1) as u64,
            masked == word & (((1u64 << (r + w)) - 1) as u64);
    facts::capacity_is_power(root as nat);
    facts::capacity_is_power(width as nat);
    facts::capacity_positive(root as nat);
    facts::capacity_positive(width as nat);
    vstd::bits::lemma_u64_pow2_no_overflow(width as nat);
    vstd::bits::lemma_u64_shl_is_mul(1, w);
    vstd::bits::lemma_u64_shr_is_div(word, r);
    vstd::bits::lemma_u64_low_bits_mask_is_mod(shifted, width as nat);
    assert(mask as nat == vstd::bits::low_bits_mask(width as nat));
}

pub proof fn common_low_prefix(first: u32, second: u32, length: nat, available: nat)
    requires length <= available,
        (first as int) % model::capacity(available)
            == (second as int) % model::capacity(available),
    ensures (first as int) % model::capacity(length)
        == (second as int) % model::capacity(length),
{
    facts::capacity_positive(length);
    facts::capacity_positive((available - length) as nat);
    facts::capacity_product(length, (available - length) as nat);
    vstd::arithmetic::div_mod::lemma_mod_mod(first as int,
        model::capacity(length), model::capacity((available - length) as nat));
    vstd::arithmetic::div_mod::lemma_mod_mod(second as int,
        model::capacity(length), model::capacity((available - length) as nat));
}

pub(crate) proof fn root_lookahead_stable(lengths: Seq<u16>, table: Seq<Code>,
    first: u32, second: u32, available: nat)
    requires model::root_decoding_table(lengths, table),
        available <= 32,
        (first as int) % model::capacity(available)
            == (second as int) % model::capacity(available),
        table[(first as int) % model::capacity(model::maximum_length(lengths) as nat)].bits
            <= available,
    ensures table[(first as int) % model::capacity(model::maximum_length(lengths) as nat)]
        == table[(second as int) % model::capacity(model::maximum_length(lengths) as nat)],
{
    let root = model::maximum_length(lengths) as nat;
    let first_entry = table[(first as int) % model::capacity(root)];
    let second_entry = table[(second as int) % model::capacity(root)];
    decode::root_word_decodes(lengths, table, first);
    decode::root_word_decodes(lengths, table, second);
    let selected = choose|symbol: int|
        #[trigger] model::code_prefix_matches(lengths, symbol, first)
        && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
        && first_entry == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 }
        && (forall|other: int| #[trigger] model::code_prefix_matches(lengths, other, first)
            ==> other == symbol);
    decode::maximum_symbol_bound(lengths, selected);
    common_low_prefix(first, second, lengths[selected] as nat, available);
    assert(model::code_prefix_matches(lengths, selected, second));
    let target = choose|symbol: int|
        #[trigger] model::code_prefix_matches(lengths, symbol, second)
        && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
        && second_entry == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 }
        && (forall|other: int| #[trigger] model::code_prefix_matches(lengths, other, second)
            ==> other == symbol);
    assert(selected == target);
}

pub(crate) proof fn root_entry_bounds(lengths: Seq<u16>, table: Seq<Code>)
    requires model::root_decoding_table(lengths, table),
    ensures forall|index: int| 0 <= index < model::capacity(model::maximum_length(lengths) as nat)
        ==> 1 <= (#[trigger] table[index]).bits <= model::maximum_length(lengths),
{
    facts::capacity_monotone(model::maximum_length(lengths) as nat, 7);
    assert(model::capacity(7) == 128) by (compute);
    assert forall|index: int| 0 <= index < model::capacity(model::maximum_length(lengths) as nat)
        implies 1 <= (#[trigger] table[index]).bits <= model::maximum_length(lengths) by {
        assert(model::root_entry_decodes(lengths, table[index], index as u32));
        let selected = choose|symbol: int|
            #[trigger] model::code_prefix_matches(lengths, symbol, index as u32)
                && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
                && table[index] == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 };
        decode::maximum_symbol_bound(lengths, selected);
    }
}

pub(crate) proof fn root_entry_symbol(lengths: Seq<u16>, entry: Code, word: u32)
    requires model::root_entry_decodes(lengths, entry, word),
        model::maximum_length(lengths) <= 7,
    ensures entry.val <= 18, entry.val < lengths.len(),
        entry.bits == lengths[entry.val as int], 1 <= entry.bits <= 7,
{
    let selected = choose|symbol: int|
        #[trigger] model::code_prefix_matches(lengths, symbol, word)
            && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
            && entry == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 };
    decode::maximum_symbol_bound(lengths, selected);
}

pub(crate) proof fn constructed_header_table(lengths: Seq<u16>, before_table: Seq<Code>,
    table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>, root: usize, used: usize)
    requires lengths.len() == 19, table.len() >= 2,
        model::code_length_result(lengths, before_table, table, before_work, work,
            crate::huffman::InflateTable::Success { root, used }),
    ensures model::header_decoding_table(lengths, table, root),
{
    reveal(model::header_decoding_table);
}

pub(crate) proof fn header_entry_symbol(lengths: Seq<u16>, table: Seq<Code>,
    root: usize, entry: Code, word: u32)
    requires model::header_decoding_table(lengths, table, root),
        entry == table[(word as int) % model::capacity(root as nat)],
    ensures entry.val <= 18, entry.val < lengths.len(), 1 <= entry.bits <= 7,
        model::maximum_length(lengths) == 0 ==> entry.bits == 1 && entry.val == 0,
        model::maximum_length(lengths) > 0 ==> entry.bits == lengths[entry.val as int],
{
    reveal(model::header_decoding_table);
    if model::maximum_length(lengths) == 0 {
        assert(model::capacity(1) == 2) by (compute);
        assert(0 <= (word as int) % 2 < 2);
    } else {
        decode::root_word_decodes(lengths, table, word);
        root_entry_symbol(lengths, entry, word);
    }
}

pub(crate) proof fn constructed_root_bounds(lengths: Seq<u16>, before_table: Seq<Code>,
    table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>, root: usize, used: usize)
    requires table.len() >= 2,
        model::code_length_result(lengths, before_table, table, before_work, work,
            crate::huffman::InflateTable::Success { root, used }),
    ensures 1 <= root <= 7, model::capacity(root as nat) <= table.len(),
        forall|index: int| 0 <= index < model::capacity(root as nat)
            ==> 1 <= (#[trigger] table[index]).bits <= root,
{
    if model::maximum_length(lengths) == 0 {
        assert(model::capacity(1) == 2) by (compute);
    } else {
        root_entry_bounds(lengths, table);
    }
}

pub proof fn peek_root_index(word: u64, root: u32, value: u64)
    requires 1 <= root <= 15,
        value == word & (((1u64 << root) - 1) as u64),
    ensures value as int == (word as u32 as int) % model::capacity(root as nat),
        value < model::capacity(root as nat),
{
    let low = word as u32;
    let mask = u32::MAX >> ((32 - root) as u32);
    assert(value == (low & mask) as u64) by (bit_vector)
        requires 1 <= root <= 15, low == word as u32,
            mask == u32::MAX >> ((32 - root) as u32),
            value == word & (((1u64 << root) - 1) as u64);
    decode::low_mask_remainder(low, root);
    facts::capacity_positive(root as nat);
    vstd::arithmetic::div_mod::lemma_mod_bound(low as int, model::capacity(root as nat));
}

pub proof fn available_source_prefix(lengths: Seq<u16>, symbol: int,
    word: u64, count: u8, source: Seq<bool>, pending: Seq<bool>)
    requires 0 <= symbol < lengths.len(), symbol <= 18, 1 <= lengths[symbol] <= 7,
        lengths[symbol] <= count <= 64,
        crate::bit_specs::buffered_bits(word, count) + pending == source,
    ensures model::code_length_source_prefix(lengths, symbol, source)
        == model::code_prefix_matches(lengths, symbol, word as u32),
{
    let width = lengths[symbol] as u8;
    let value = word & (((1u64 << width) - 1) as u64);
    crate::bit_proofs::numeric_field(word, count, width, source, pending);
    peek_root_index(word, width as u32, value);
}

pub proof fn filled_u32_prefix(before: u64, after: u64, available: u8, added: Seq<bool>)
    requires available <= 7,
        crate::bit_specs::filled_word(before, available, after, added),
    ensures (before as u32 as int) % model::capacity(available as nat)
        == (after as u32 as int) % model::capacity(available as nat),
{
    if available == 0 {
        assert(model::capacity(0) == 1) by (compute);
    } else {
        let source = crate::bit_specs::buffered_bits(before, available);
        let preserved = crate::bit_specs::buffered_bits(after, available);
        assert forall|index: int| 0 <= index < available implies
            #[trigger] preserved[index] == source[index] by {
            assert(crate::bit_specs::word_bit(before, index as nat)
                == crate::bit_specs::word_bit(after, index as nat));
        }
        assert(preserved =~= source);
        assert(source + Seq::empty() =~= source);
        crate::bit_proofs::numeric_field(before, available, available, source, Seq::empty());
        crate::bit_proofs::numeric_field(after, available, available, source, Seq::empty());
        peek_root_index(before, available as u32, before & (((1u64 << available) - 1) as u64));
        peek_root_index(after, available as u32, after & (((1u64 << available) - 1) as u64));
    }
}

pub(crate) proof fn root_entry_source(lengths: Seq<u16>, entry: Code,
    word: u64, count: u8, source: Seq<bool>, pending: Seq<bool>)
    requires model::root_entry_decodes(lengths, entry, word as u32),
        1 <= entry.bits <= 7, entry.bits <= count <= 64,
        crate::bit_specs::buffered_bits(word, count) + pending == source,
    ensures model::code_length_source_prefix(lengths, entry.val as int, source),
{
    let selected = choose|symbol: int|
        #[trigger] model::code_prefix_matches(lengths, symbol, word as u32)
        && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
        && entry == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 };
    assert(selected == entry.val as int);
    available_source_prefix(lengths, selected, word, count, source, pending);
}

pub(crate) proof fn root_source_ready(lengths: Seq<u16>, entry: Code, word: u64, count: u8)
    requires model::root_entry_decodes(lengths, entry, word as u32),
        1 <= entry.bits <= 7, count <= 64,
    ensures (exists|symbol: int| model::code_length_source_prefix(lengths, symbol,
            crate::bit_specs::buffered_bits(word, count))) == (entry.bits <= count),
{
    let source = crate::bit_specs::buffered_bits(word, count);
    assert(source + Seq::empty() =~= source);
    if entry.bits <= count {
        root_entry_source(lengths, entry, word, count, source, Seq::empty());
    } else {
        let selected = choose|symbol: int|
            #[trigger] model::code_prefix_matches(lengths, symbol, word as u32)
            && model::symbol_domain(model::Alphabet::CodeLengths, symbol as nat)
            && entry == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 }
            && (forall|other: int| #[trigger] model::code_prefix_matches(lengths, other, word as u32)
                ==> other == symbol);
        assert forall|symbol: int| !model::code_length_source_prefix(lengths, symbol, source) by {
            if model::code_length_source_prefix(lengths, symbol, source) {
                available_source_prefix(lengths, symbol, word, count, source, Seq::empty());
                assert(symbol == selected);
            }
        }
    }
}

// RFC 1951 3.2.2's ABCDEFGH example; B's nonpalindromic wire code is 011.
pub proof fn rfc_canonical_example()
    ensures model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 0) == 2,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 1) == 3,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 2) == 4,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 3) == 5,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 4) == 6,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 5) == 0,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 6) == 14,
        model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 7) == 15,
        model::code_length_source_prefix(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 1,
            seq![false, true, true]),
        !model::code_length_source_prefix(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 1,
            seq![false, true]),
{
    let lengths = seq![3u16, 3, 3, 3, 3, 2, 4, 4];
    assert(model::canonical_code(lengths, 0) == 2
        && model::canonical_code(lengths, 1) == 3
        && model::canonical_code(lengths, 2) == 4
        && model::canonical_code(lengths, 3) == 5
        && model::canonical_code(lengths, 4) == 6
        && model::canonical_code(lengths, 5) == 0
        && model::canonical_code(lengths, 6) == 14
        && model::canonical_code(lengths, 7) == 15) by {
        reveal_with_fuel(model::occurrences, 9);
        reveal_with_fuel(model::canonical_start, 5);
    }
    assert(model::capacity(29) == 536870912) by (compute);
    assert forall|index: u32| index < 32 implies
        #[trigger] model::word_bit(6, index)
            == model::word_bit(0x60000000, (31 - index) as u32) by {
        assert((6u32 >> index) & 1 == (0x60000000u32 >> ((31 - index) as u32)) & 1)
            by (bit_vector) requires index < 32;
    }
    facts::reversal_matches_model(0x60000000, 6);
    assert(model::canonical_code(lengths, 1)
        * model::capacity((32 - lengths[1]) as nat) == 0x60000000);
    assert(model::canonical_prefix(lengths, 1) == 6);
    let source = seq![false, true, true];
    assert(crate::bit_specs::low_first_value(source.take(3)) == 6) by {
        reveal_with_fuel(crate::bit_specs::low_first_value, 4);
    }
}

}
