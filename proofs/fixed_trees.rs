use crate::fixed_tree_specs as model;
use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn range_population(prefix: int, lower: int, upper: int) -> nat {
    if prefix <= lower { 0 }
    else if prefix < upper { (prefix - lower) as nat }
    else { (upper - lower) as nat }
}

pub(crate) open spec fn literal_population(prefix: int, length: u16) -> nat {
    if length == 7 { range_population(prefix, 256, 280) }
    else if length == 8 {
        range_population(prefix, 0, 144) + range_population(prefix, 280, 288)
    } else if length == 9 { range_population(prefix, 144, 256) }
    else { 0 }
}

pub(crate) proof fn literal_prefix_population(prefix: int, length: u16)
    requires 0 <= prefix <= 288,
    ensures h::occurrences(model::literal_lengths().take(prefix), length)
        == literal_population(prefix, length),
    decreases prefix,
{
    let lengths = model::literal_lengths();
    if prefix == 0 {
        assert(lengths.take(0) =~= Seq::<u16>::empty());
    } else {
        literal_prefix_population(prefix - 1, length);
        facts::histogram_prefix_step(lengths, prefix - 1, length);
        assert(lengths[prefix - 1] == model::literal_length(prefix - 1));
    }
}

pub(crate) proof fn distance_prefix_population(prefix: int, length: u16)
    requires 0 <= prefix <= 32,
    ensures h::occurrences(model::distance_lengths().take(prefix), length)
        == if length == 5 { prefix as nat } else { 0nat },
    decreases prefix,
{
    let lengths = model::distance_lengths();
    if prefix == 0 {
        assert(lengths.take(0) =~= Seq::<u16>::empty());
    } else {
        distance_prefix_population(prefix - 1, length);
        facts::histogram_prefix_step(lengths, prefix - 1, length);
    }
}

pub(crate) proof fn literal_start(depth: nat)
    requires 1 <= depth <= 9,
    ensures h::canonical_start(model::literal_lengths(), depth)
        == if depth <= 7 { 0nat } else if depth == 8 { 48nat } else { 400nat },
    decreases depth,
{
    if depth > 1 {
        literal_start((depth - 1) as nat);
        literal_prefix_population(288, (depth - 1) as u16);
        assert(model::literal_lengths().take(288) =~= model::literal_lengths());
    }
}

pub(crate) proof fn distance_start(depth: nat)
    requires 1 <= depth <= 5,
    ensures h::canonical_start(model::distance_lengths(), depth) == 0,
    decreases depth,
{
    if depth > 1 {
        distance_start((depth - 1) as nat);
        distance_prefix_population(32, (depth - 1) as u16);
        assert(model::distance_lengths().take(32) =~= model::distance_lengths());
    }
}

pub(crate) proof fn literal_assignment(symbol: int)
    requires 0 <= symbol < 288,
    ensures h::canonical_code(model::literal_lengths(), symbol) == model::literal_code(symbol),
        7 <= model::literal_lengths()[symbol] <= 9,
{
    let lengths = model::literal_lengths();
    assert(lengths[symbol] == model::literal_length(symbol));
    literal_prefix_population(symbol, lengths[symbol]);
    literal_start(lengths[symbol] as nat);
}

pub(crate) proof fn distance_assignment(symbol: int)
    requires 0 <= symbol < 32,
    ensures h::canonical_code(model::distance_lengths(), symbol) == symbol,
        model::distance_lengths()[symbol] == 5,
{
    distance_prefix_population(symbol, 5);
    distance_start(5);
}

pub(crate) proof fn five_bit_reversal(word: u32)
    requires word < 32,
    ensures model::reverse_five(word) < 32,
        model::reverse_five(model::reverse_five(word)) == word,
        h::is_reversal(word << 27, model::reverse_five(word)),
{
    let reversed = model::reverse_five(word);
    assert(reversed < 32) by (bit_vector)
        requires reversed == ((word & 1) << 4) | ((word & 2) << 2) | (word & 4)
            | ((word & 8) >> 2) | ((word & 16) >> 4);
    assert(model::reverse_five(reversed) == word) by (bit_vector)
        requires word < 32,
            reversed == ((word & 1) << 4) | ((word & 2) << 2) | (word & 4)
                | ((word & 8) >> 2) | ((word & 16) >> 4),
            model::reverse_five(reversed) == ((reversed & 1) << 4) | ((reversed & 2) << 2)
                | (reversed & 4) | ((reversed & 8) >> 2) | ((reversed & 16) >> 4);
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(reversed, bit)
            == h::word_bit(word << 27, (31 - bit) as u32) by {
        assert(((reversed >> bit) & 1) == (((word << 27) >> ((31 - bit) as u32)) & 1))
            by (bit_vector) requires bit < 32, word < 32,
                reversed == ((word & 1) << 4) | ((word & 2) << 2) | (word & 4)
                    | ((word & 8) >> 2) | ((word & 16) >> 4);
    }
}

pub(crate) proof fn distance_prefix(symbol: u32)
    requires symbol < 32,
    ensures h::canonical_prefix(model::distance_lengths(), symbol as int)
        == model::reverse_five(symbol),
{
    distance_assignment(symbol as int);
    five_bit_reversal(symbol);
    assert(h::capacity(27) == 134217728) by (compute);
    facts::capacity_is_power(27);
    vstd::bits::lemma_u32_shl_is_mul(symbol, 27);
    facts::reversal_matches_model(symbol << 27, model::reverse_five(symbol));
}

pub(crate) proof fn distance_table(codes: Seq<crate::Code>)
    requires codes.len() >= 32,
        forall|index: int| 0 <= index < 32 ==>
            #[trigger] codes[index] == model::distance_entry(index),
    ensures crate::root_table_specs::table(h::Alphabet::Distances,
        model::distance_lengths(), 5, codes),
{
    complete_fixed_distributions();
    assert(h::capacity(5) == 32) by (compute);
    reveal(crate::root_table_specs::table);
    assert forall|index: int| 0 <= index < 32 implies
        #[trigger] crate::root_table_specs::entry(h::Alphabet::Distances,
            model::distance_lengths(), codes[index], index as u32) by {
        five_bit_reversal(index as u32);
        let symbol = model::reverse_five(index as u32);
        distance_prefix(symbol);
        assert((index as u32 as int) % 32 == index);
        assert(h::code_prefix_matches(model::distance_lengths(), symbol as int, index as u32));
        if symbol <= 29 {
            assert(h::distance_extra(symbol as nat) <= 13);
            facts::capacity_monotone(h::distance_extra(symbol as nat), 13);
            facts::capacity_monotone(h::distance_extra(symbol as nat) + 1, 14);
            facts::capacity_positive(h::distance_extra(symbol as nat));
            facts::capacity_positive(h::distance_extra(symbol as nat) + 1);
            assert(h::capacity(13) == 8192 && h::capacity(14) == 16384) by (compute);
            assert((symbol as int) % 2 <= 1);
            assert(0 <= h::distance_base(symbol as nat) <= 24577) by (nonlinear_arith)
                requires 0 <= h::capacity(h::distance_extra(symbol as nat)) <= 8192,
                    0 <= h::capacity(h::distance_extra(symbol as nat) + 1) <= 16384,
                    h::distance_base(symbol as nat) == if symbol <= 3 {
                        symbol as int + 1
                    } else {
                        1 + h::capacity(h::distance_extra(symbol as nat) + 1)
                            + ((symbol as int) % 2) * h::capacity(h::distance_extra(symbol as nat))
                    }, 0 <= (symbol as int) % 2 <= 1, symbol <= 29;
        } else {
            assert(h::invalid_operation(64)) by (compute);
        }
        assert(crate::table_emission_specs::leaf(h::Alphabet::Distances,
            symbol as nat, 5, codes[index]));
        assert forall|other: int|
            #[trigger] h::code_prefix_matches(model::distance_lengths(), other, index as u32)
                implies other == symbol by {
            distance_prefix(other as u32);
            five_bit_reversal(other as u32);
        }
    }
}

pub(crate) proof fn independent_distance_cells()
    ensures model::distance_entry(0) == (crate::Code { op: 16, bits: 5, val: 1 }),
        model::distance_entry(1) == (crate::Code { op: 23, bits: 5, val: 257 }),
        model::distance_entry(15) == (crate::Code { op: 64, bits: 5, val: 0 }),
        model::distance_entry(23) == (crate::Code { op: 29, bits: 5, val: 24577 }),
        model::distance_entry(31) == (crate::Code { op: 64, bits: 5, val: 0 }),
{
    let first = crate::Code { op: 16, bits: 5, val: 1 };
    let next = crate::Code { op: 23, bits: 5, val: 257 };
    let reserved = crate::Code { op: 64, bits: 5, val: 0 };
    let largest = crate::Code { op: 29, bits: 5, val: 24577 };
    assert(model::distance_entry(0) == first) by (compute);
    assert(model::distance_entry(1) == next) by (compute);
    assert(model::distance_entry(15) == reserved) by (compute);
    assert(model::distance_entry(23) == largest) by (compute);
    assert(model::distance_entry(31) == reserved) by (compute);
}

pub(crate) proof fn nine_bit_prefix(index: u32, width: u32)
    requires index < 512, 7 <= width <= 9,
    ensures model::reverse_nine(index) < 512,
        h::is_reversal((model::reverse_nine(index) >> ((9 - width) as u32)) << ((32 - width) as u32),
            index % (1u32 << width)),
{
    let reversed = model::reverse_nine(index);
    assert(reversed < 512) by (bit_vector)
        requires reversed == ((index & 1) << 8) | ((index & 2) << 6) | ((index & 4) << 4)
            | ((index & 8) << 2) | (index & 16) | ((index & 32) >> 2)
            | ((index & 64) >> 4) | ((index & 128) >> 6) | ((index & 256) >> 8);
    let normalized = (reversed >> ((9 - width) as u32)) << ((32 - width) as u32);
    let prefix = index % (1u32 << width);
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(prefix, bit)
            == h::word_bit(normalized, (31 - bit) as u32) by {
        assert(((prefix >> bit) & 1) == ((normalized >> ((31 - bit) as u32)) & 1))
            by (bit_vector) requires bit < 32, index < 512, 7 <= width <= 9,
                normalized == (reversed >> ((9 - width) as u32)) << ((32 - width) as u32),
                prefix == index % (1u32 << width),
                reversed == ((index & 1) << 8) | ((index & 2) << 6) | ((index & 4) << 4)
                    | ((index & 8) << 2) | (index & 16) | ((index & 32) >> 2)
                    | ((index & 64) >> 4) | ((index & 128) >> 6) | ((index & 256) >> 8);
    }
}

pub(crate) proof fn literal_selected_prefix(index: u32)
    requires index < 512,
    ensures 0 <= model::literal_symbol(index) < 288,
        h::code_prefix_matches(model::literal_lengths(), model::literal_symbol(index), index),
{
    let reversed = model::reverse_nine(index);
    nine_bit_prefix(index, 9);
    let symbol = model::literal_symbol(index);
    assert(0 <= symbol < 288);
    literal_assignment(symbol);
    let width = model::literal_length(symbol) as u32;
    assert(7 <= width <= 9);
    nine_bit_prefix(index, width);
    assert((reversed >> 2) == reversed / 4) by (bit_vector);
    assert((reversed >> 1) == reversed / 2) by (bit_vector);
    assert(h::capacity(7) == 128 && h::capacity(8) == 256 && h::capacity(9) == 512)
        by (compute);
    assert(h::capacity(23) == 8388608 && h::capacity(24) == 16777216
        && h::capacity(25) == 33554432) by (compute);
    if reversed < 96 {
        assert(width == 7 && model::literal_code(symbol) == (reversed as int) / 4);
    } else if reversed < 384 {
        assert(width == 8 && model::literal_code(symbol) == (reversed as int) / 2);
    } else if reversed < 400 {
        assert(width == 8 && model::literal_code(symbol) == (reversed as int) / 2);
    } else {
        assert(width == 9 && model::literal_code(symbol) == reversed);
        assert(reversed >> 0 == reversed) by (bit_vector);
    }
    assert(h::canonical_code(model::literal_lengths(), symbol)
        == (reversed >> ((9 - width) as u32)) as nat);
    facts::capacity_is_power(width as nat);
    vstd::bits::lemma_u32_pow2_no_overflow(width as nat);
    vstd::bits::lemma_u32_shl_is_mul(1, width);
    facts::capacity_is_power((32 - width) as nat);
    vstd::bits::lemma_u32_shl_is_mul(reversed >> ((9 - width) as u32), (32 - width) as u32);
    facts::reversal_matches_model((reversed >> ((9 - width) as u32)) << ((32 - width) as u32),
        index % (1u32 << width));
}

pub(crate) proof fn literal_table(codes: Seq<crate::Code>)
    requires codes.len() >= 512,
        forall|index: int| 0 <= index < 512 ==>
            #[trigger] codes[index] == model::literal_entry(index),
    ensures crate::root_table_specs::table(h::Alphabet::LiteralLengths,
        model::literal_lengths(), 9, codes),
{
    complete_fixed_distributions();
    let lengths = model::literal_lengths();
    let counts = h::histogram(lengths);
    assert forall|level: int| 1 <= level <= 15 implies
        counts[level] == h::occurrences(lengths, level as u16) by {
        literal_prefix_population(288, level as u16);
        assert(lengths.take(288) =~= lengths);
    }
    assert(h::valid_histogram(lengths, counts));
    assert(h::capacity(9) == 512) by (compute);
    assert(h::invalid_operation(64)) by (compute);
    reveal(crate::root_table_specs::table);
    assert forall|index: int| 0 <= index < 512 implies
        #[trigger] crate::root_table_specs::entry(h::Alphabet::LiteralLengths,
            lengths, codes[index], index as u32) by {
        literal_selected_prefix(index as u32);
        let symbol = model::literal_symbol(index as u32);
        if 257 <= symbol <= 285 {
            assert(h::length_extra(symbol as nat) <= 5);
            facts::capacity_monotone(h::length_extra(symbol as nat), 5);
            facts::capacity_monotone(h::length_extra(symbol as nat) + 2, 7);
            facts::capacity_positive(h::length_extra(symbol as nat));
            facts::capacity_positive(h::length_extra(symbol as nat) + 2);
            assert(h::capacity(5) == 32 && h::capacity(7) == 128) by (compute);
            assert(0 <= (symbol - 265) % 4 <= 3);
            assert(0 <= h::length_base(symbol as nat) <= 258) by (nonlinear_arith)
                requires 0 <= h::capacity(h::length_extra(symbol as nat)) <= 32,
                    0 <= h::capacity(h::length_extra(symbol as nat) + 2) <= 128,
                    h::length_base(symbol as nat) == if symbol <= 264 {
                        symbol - 254
                    } else if symbol == 285 { 258 } else {
                        3 + h::capacity(h::length_extra(symbol as nat) + 2)
                            + ((symbol - 265) % 4) * h::capacity(h::length_extra(symbol as nat))
                    }, 0 <= (symbol - 265) % 4 <= 3, 257 <= symbol <= 285;
        }
        assert(crate::table_emission_specs::leaf(h::Alphabet::LiteralLengths,
            symbol as nat, lengths[symbol] as nat, codes[index]));
        assert forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, index as u32)
            implies other == symbol by {
            crate::huffman_decode::matching_symbol_unique(lengths, counts,
                symbol, other, index as u32);
        }
    }
}

pub(crate) proof fn independent_literal_cells()
    ensures model::literal_entry(0) == (crate::Code { op: 96, bits: 7, val: 0 }),
        model::literal_entry(384) == (crate::Code { op: 96, bits: 7, val: 0 }),
        model::literal_entry(12) == (crate::Code { op: 0, bits: 8, val: 0 }),
        model::literal_entry(509) == (crate::Code { op: 0, bits: 8, val: 143 }),
        model::literal_entry(19) == (crate::Code { op: 0, bits: 9, val: 144 }),
        model::literal_entry(511) == (crate::Code { op: 0, bits: 9, val: 255 }),
        model::literal_entry(500) == (crate::Code { op: 20, bits: 7, val: 99 }),
        model::literal_entry(3) == (crate::Code { op: 20, bits: 8, val: 115 }),
        model::literal_entry(163) == (crate::Code { op: 16, bits: 8, val: 258 }),
        model::literal_entry(99) == (crate::Code { op: 64, bits: 8, val: 0 }),
        model::literal_entry(483) == (crate::Code { op: 64, bits: 8, val: 0 }),
{
    let eob = crate::Code { op: 96, bits: 7, val: 0 };
    let first = crate::Code { op: 0, bits: 8, val: 0 };
    let last_eight = crate::Code { op: 0, bits: 8, val: 143 };
    let first_nine = crate::Code { op: 0, bits: 9, val: 144 };
    let last = crate::Code { op: 0, bits: 9, val: 255 };
    let last_seven = crate::Code { op: 20, bits: 7, val: 99 };
    let first_eight = crate::Code { op: 20, bits: 8, val: 115 };
    let largest = crate::Code { op: 16, bits: 8, val: 258 };
    let reserved = crate::Code { op: 64, bits: 8, val: 0 };
    assert(model::literal_entry(0) == eob) by (compute);
    assert(model::literal_entry(384) == eob) by (compute);
    assert(model::literal_entry(12) == first) by (compute);
    assert(model::literal_entry(509) == last_eight) by (compute);
    assert(model::literal_entry(19) == first_nine) by (compute);
    assert(model::literal_entry(511) == last) by (compute);
    assert(model::literal_entry(500) == last_seven) by (compute);
    assert(model::literal_entry(3) == first_eight) by (compute);
    assert(model::literal_entry(163) == largest) by (compute);
    assert(model::literal_entry(99) == reserved) by (compute);
    assert(model::literal_entry(483) == reserved) by (compute);
}

pub(crate) proof fn fixed_histograms()
    ensures h::histogram(model::literal_lengths()) =~=
            Seq::new(16, |level: int|
                if level == 7 { 24u16 } else if level == 8 { 152u16 }
                else if level == 9 { 112u16 } else { 0u16 }),
        h::histogram(model::distance_lengths()) =~=
            Seq::new(16, |level: int| if level == 5 { 32u16 } else { 0u16 }),
{
    assert forall|level: int| 0 <= level < 16 implies
        h::histogram(model::literal_lengths())[level]
            == if level == 7 { 24u16 } else if level == 8 { 152u16 }
                else if level == 9 { 112u16 } else { 0u16 } by {
        literal_prefix_population(288, level as u16);
        assert(model::literal_lengths().take(288) =~= model::literal_lengths());
    }
    assert forall|level: int| 0 <= level < 16 implies
        h::histogram(model::distance_lengths())[level]
            == if level == 5 { 32u16 } else { 0u16 } by {
        distance_prefix_population(32, level as u16);
        assert(model::distance_lengths().take(32) =~= model::distance_lengths());
    }
}

pub(crate) proof fn literal_slots(depth: nat)
    requires depth <= 15,
    ensures h::slots(h::histogram(model::literal_lengths()), depth)
        == if depth < 7 { h::capacity(depth) }
            else if depth == 7 { 104int } else if depth == 8 { 56int } else { 0int },
    decreases depth,
{
    fixed_histograms();
    if depth > 0 {
        literal_slots((depth - 1) as nat);
        if depth == 7 { assert(h::capacity(6) == 64) by (compute); }
    }
}

pub(crate) proof fn distance_slots(depth: nat)
    requires depth <= 15,
    ensures h::slots(h::histogram(model::distance_lengths()), depth)
        == if depth < 5 { h::capacity(depth) } else { 0int },
    decreases depth,
{
    fixed_histograms();
    if depth > 0 {
        distance_slots((depth - 1) as nat);
        if depth == 5 { assert(h::capacity(4) == 16) by (compute); }
    }
}

pub(crate) proof fn complete_fixed_distributions()
    ensures h::accepted_lengths(model::literal_lengths(), true),
        h::accepted_lengths(model::distance_lengths(), true),
        h::maximum_length(model::literal_lengths()) == 9,
        h::maximum_length(model::distance_lengths()) == 5,
{
    let literals = model::literal_lengths();
    let distances = model::distance_lengths();
    assert forall|symbol: int| 0 <= symbol < literals.len() implies literals[symbol] <= 9 by {
    }
    assert forall|symbol: int| 0 <= symbol < distances.len() implies distances[symbol] <= 5 by {
    }
    crate::dynamic_header_proofs::maximum_bounded(literals, 9);
    crate::dynamic_header_proofs::maximum_bounded(distances, 5);
    crate::huffman_decode::maximum_symbol_bound(literals, 144);
    crate::huffman_decode::maximum_symbol_bound(distances, 0);
    literal_slots(15);
    distance_slots(15);
    assert forall|depth: nat| depth <= 15 implies
        h::slots(h::histogram(literals), depth) >= 0 by {
        literal_slots(depth);
        facts::capacity_positive(depth);
    }
    assert forall|depth: nat| depth <= 15 implies
        h::slots(h::histogram(distances), depth) >= 0 by {
        distance_slots(depth);
        facts::capacity_positive(depth);
    }
}

pub(crate) proof fn independent_rfc_boundaries()
    ensures h::canonical_code(model::literal_lengths(), 0) == 48,
        h::canonical_code(model::literal_lengths(), 143) == 191,
        h::canonical_code(model::literal_lengths(), 144) == 400,
        h::canonical_code(model::literal_lengths(), 255) == 511,
        h::canonical_code(model::literal_lengths(), 256) == 0,
        h::canonical_code(model::literal_lengths(), 279) == 23,
        h::canonical_code(model::literal_lengths(), 280) == 192,
        h::canonical_code(model::literal_lengths(), 287) == 199,
        h::canonical_code(model::distance_lengths(), 0) == 0,
        h::canonical_code(model::distance_lengths(), 31) == 31,
{
    literal_assignment(0);
    literal_assignment(143);
    literal_assignment(144);
    literal_assignment(255);
    literal_assignment(256);
    literal_assignment(279);
    literal_assignment(280);
    literal_assignment(287);
    distance_assignment(0);
    distance_assignment(31);
}

}
