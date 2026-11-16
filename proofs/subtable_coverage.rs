use crate::canonical_intervals as intervals;
use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::subtable_coverage_specs as model;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_bound};
use vstd::prelude::*;

verus! {

pub proof fn lookahead_boundary(original: Seq<u16>, remaining: Seq<u16>,
    position: nat, length: nat, root: nat, width: nat)
    requires original.len() == 16,
        h::remaining_histogram(original, remaining, position),
        1 <= root < length <= root + width <= 15,
        h::before(original, length) <= position < h::before(original, length + 1),
    ensures
        (h::first_code(original, root + width) + original[(root + width) as int] as nat)
            * h::capacity((32 - root - width) as nat)
        == h::normalized_cursor(original, length, position) + h::capacity((32 - root) as nat)
            - (h::lookahead_space(remaining, (length - root) as nat, root, width)
                - remaining[(root + width) as int] as int)
                * h::capacity((32 - root - width) as nat),
    decreases root + width - length,
{
    let depth = root + width;
    let cell = h::capacity((32 - depth) as nat);
    let space = h::lookahead_space(remaining, (length - root) as nat, root, width);
    facts::capacity_positive((32 - depth) as nat);
    if depth == length {
        facts::capacity_product(width, (32 - depth) as nat);
        let rank = position - h::before(original, length);
        assert(remaining[length as int] == original[length as int] as int - rank);
        assert((h::first_code(original, length) + original[length as int] as nat) * cell
            == (h::first_code(original, length) + rank) * cell
                + h::capacity(width) * cell
                - (h::capacity(width) - remaining[length as int] as int) * cell)
            by (nonlinear_arith)
            requires remaining[length as int] == original[length as int] as int - rank;
    } else {
        lookahead_boundary(original, remaining, position, length, root, (width - 1) as nat);
        facts::before_monotone(original, length + 1, depth);
        assert(remaining[depth as int] == original[depth as int]);
        let previous = h::lookahead_space(remaining, (length - root) as nat, root,
            (width - 1) as nat) - remaining[depth as int - 1] as int;
        let boundary = h::first_code(original, (depth - 1) as nat)
            + original[depth as int - 1] as nat;
        assert(h::capacity((33 - depth) as nat) == 2 * cell);
        assert(space == 2 * previous);
        assert(h::first_code(original, depth) == 2 * boundary);
        assert((2 * boundary + original[depth as int] as nat) * cell
            == boundary * (2 * cell)
                + original[depth as int] as nat * cell) by (nonlinear_arith);
        assert((2 * previous - remaining[depth as int] as int) * cell
            == previous * (2 * cell)
                - remaining[depth as int] as int * cell) by (nonlinear_arith);
    }
}

pub proof fn chosen_width_covers_symbol(lengths: Seq<u16>, original: Seq<u16>,
    remaining: Seq<u16>, position: nat, length: nat, root: nat, max: nat,
    width: nat, symbol: int)
    requires model::source_context(lengths, original, remaining, position, length, root, max),
        h::chosen_width(remaining, (length - root) as nat, root, max, width),
        model::in_root(lengths, symbol, root, h::normalized_cursor(original, length, position)),
    ensures lengths[symbol] <= root + width,
{
    if root + width < lengths[symbol] {
        let depth = root + width;
        let target = lengths[symbol] as nat;
        crate::huffman_decode::maximum_symbol_bound(lengths, symbol);
        assert(depth < max);
        lookahead_boundary(original, remaining, position, length, root, width);
        let cell = h::capacity((32 - depth) as nat);
        let root_cell = h::capacity((32 - root) as nat);
        let cursor = h::normalized_cursor(original, length, position);
        let boundary = (h::first_code(original, depth) + original[depth as int] as nat) * cell;
        let future = h::canonical_code(lengths, symbol) * h::capacity((32 - target) as nat);
        let residue = h::lookahead_space(remaining, (length - root) as nat, root, width)
            - remaining[depth as int] as int;
        facts::capacity_positive((32 - depth) as nat);
        facts::capacity_positive((32 - root) as nat);
        facts::capacity_positive((32 - target) as nat);
        facts::first_code_from_histogram(lengths, original, target);
        intervals::first_code_interval_separation(original, depth, target);
        assert(boundary >= cursor + root_cell) by (nonlinear_arith)
            requires boundary == cursor + root_cell - residue * cell,
                residue <= 0, cell > 0;
        assert(boundary <= future) by (nonlinear_arith)
            requires boundary <= h::first_code(original, target) * h::capacity((32 - target) as nat),
                h::first_code(original, target) <= h::canonical_code(lengths, symbol),
                h::capacity((32 - target) as nat) > 0,
                future == h::canonical_code(lengths, symbol) * h::capacity((32 - target) as nat);
        lemma_fundamental_div_mod(cursor, root_cell);
        lemma_fundamental_div_mod(future, root_cell);
        lemma_mod_bound(cursor, root_cell);
        lemma_mod_bound(future, root_cell);
        assert(future < cursor + root_cell) by (nonlinear_arith)
            requires cursor == root_cell * (cursor / root_cell) + cursor % root_cell,
                future == root_cell * (future / root_cell) + future % root_cell,
                future / root_cell == cursor / root_cell,
                0 <= cursor % root_cell < root_cell, 0 <= future % root_cell < root_cell;
    }
}

pub proof fn width_result(remaining: Seq<u16>, length: nat, root: nat, max: nat, width: nat)
    requires root < length <= max <= 15,
        h::chosen_width(remaining, (length - root) as nat, root, max, width),
    ensures forall|lengths: Seq<u16>, original: Seq<u16>, position: nat|
        #[trigger] model::source_context(lengths, original, remaining, position, length, root, max)
        ==> (forall|symbol: int| #[trigger] model::in_root(lengths, symbol, root,
                h::normalized_cursor(original, length, position))
            ==> lengths[symbol] <= root + width),
{
    assert forall|lengths: Seq<u16>, original: Seq<u16>, position: nat|
        #[trigger] model::source_context(lengths, original, remaining, position, length, root, max)
        implies (forall|symbol: int| #[trigger] model::in_root(lengths, symbol, root,
                h::normalized_cursor(original, length, position))
            ==> lengths[symbol] <= root + width) by {
        assert forall|symbol: int| #[trigger] model::in_root(lengths, symbol, root,
            h::normalized_cursor(original, length, position))
            implies lengths[symbol] <= root + width by {
            chosen_width_covers_symbol(lengths, original, remaining, position, length, root,
                max, width, symbol);
        }
    }
}

pub proof fn ordered_quotients(first: int, second: int, size: int)
    requires first <= second, size > 0,
    ensures first / size <= second / size,
{
    lemma_fundamental_div_mod(first, size);
    lemma_fundamental_div_mod(second, size);
    lemma_mod_bound(first, size);
    lemma_mod_bound(second, size);
    if first / size > second / size {
        assert(first > second) by (nonlinear_arith)
            requires first == size * (first / size) + first % size,
                second == size * (second / size) + second % size,
                first / size >= second / size + 1, size > 0,
                0 <= first % size < size, 0 <= second % size < size;
    }
}

pub proof fn canonical_root_order(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int, root: nat)
    requires h::valid_histogram(lengths, counts),
        0 <= first < lengths.len(), 0 <= second < lengths.len(),
        1 <= root < lengths[first] <= 15, root < lengths[second] <= 15,
        lengths[first] < lengths[second]
            || (lengths[first] == lengths[second] && first < second),
    ensures model::root_prefix(lengths, first, root) <= model::root_prefix(lengths, second, root),
{
    let width = h::capacity((32 - lengths[first]) as nat);
    let left = h::canonical_code(lengths, first) * width;
    let right = h::canonical_code(lengths, second)
        * h::capacity((32 - lengths[second]) as nat);
    facts::capacity_positive((32 - lengths[first]) as nat);
    facts::capacity_positive((32 - root) as nat);
    intervals::canonical_interval_separation(lengths, counts, first, second);
    assert(left + width <= right) by (nonlinear_arith)
        requires (h::canonical_code(lengths, first) + 1) * width <= right,
            left == h::canonical_code(lengths, first) * width;
    ordered_quotients(left, right, h::capacity((32 - root) as nat));
}

pub proof fn no_root_revisit(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int, third: int, root: nat)
    requires h::valid_histogram(lengths, counts),
        0 <= first < lengths.len(), 0 <= second < lengths.len(), 0 <= third < lengths.len(),
        1 <= root < lengths[first] <= 15, root < lengths[second] <= 15,
        root < lengths[third] <= 15,
        lengths[first] < lengths[second]
            || (lengths[first] == lengths[second] && first < second),
        lengths[second] < lengths[third]
            || (lengths[second] == lengths[third] && second < third),
        model::root_prefix(lengths, first, root) != model::root_prefix(lengths, second, root),
    ensures model::root_prefix(lengths, first, root) != model::root_prefix(lengths, third, root),
{
    canonical_root_order(lengths, counts, first, second, root);
    canonical_root_order(lengths, counts, second, third, root);
}

pub proof fn wire_root_equivalence(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int, root: nat)
    requires h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        0 <= first < lengths.len(), 0 <= second < lengths.len(),
        1 <= root < lengths[first] <= 15, root < lengths[second] <= 15,
    ensures ((h::canonical_prefix(lengths, first) as int) % h::capacity(root)
            == (h::canonical_prefix(lengths, second) as int) % h::capacity(root))
        <==> (model::root_prefix(lengths, first, root) == model::root_prefix(lengths, second, root)),
{
    let first_value = h::canonical_code(lengths, first)
        * h::capacity((32 - lengths[first]) as nat);
    let second_value = h::canonical_code(lengths, second)
        * h::capacity((32 - lengths[second]) as nat);
    let first_cursor = first_value as u32;
    let second_cursor = second_value as u32;
    let first_word = h::canonical_prefix(lengths, first);
    let second_word = h::canonical_prefix(lengths, second);
    let r = root as u32;
    let shift = (32 - r) as u32;
    let first_high = first_cursor & !(u32::MAX >> r);
    let second_high = second_cursor & !(u32::MAX >> r);
    let first_low = first_word & (u32::MAX >> shift);
    let second_low = second_word & (u32::MAX >> shift);
    crate::huffman_decode::canonical_word(lengths, counts, first);
    crate::huffman_decode::canonical_word(lengths, counts, second);
    crate::huffman_decode::reversal_symmetric(first_cursor, first_word);
    crate::huffman_decode::reversal_symmetric(second_cursor, second_word);
    crate::huffman_decode::reversal_low_prefix(first_word, first_cursor, r);
    crate::huffman_decode::reversal_low_prefix(second_word, second_cursor, r);
    crate::huffman_decode::low_mask_remainder(first_word, r);
    crate::huffman_decode::low_mask_remainder(second_word, r);
    facts::capacity_is_power((32 - root) as nat);
    vstd::bits::lemma_u32_shr_is_div(first_cursor, shift);
    vstd::bits::lemma_u32_shr_is_div(second_cursor, shift);
    assert((first_high == second_high)
        <==> ((first_cursor >> shift) == (second_cursor >> shift))) by (bit_vector)
        requires 1 <= r <= 15, shift == (32 - r) as u32,
            first_high == first_cursor & !(u32::MAX >> r),
            second_high == second_cursor & !(u32::MAX >> r);
    if first_high == second_high {
        facts::reversal_unique(first_high, first_low, second_low);
    }
    if first_low == second_low {
        crate::huffman_decode::reversal_symmetric(first_high, first_low);
        crate::huffman_decode::reversal_symmetric(second_high, second_low);
        facts::reversal_unique(first_low, first_high, second_high);
    }
}

pub proof fn same_wire_root_covered(lengths: Seq<u16>, original: Seq<u16>,
    remaining: Seq<u16>, position: nat, length: nat, root: nat, max: nat,
    width: nat, current: int, symbol: int)
    requires model::source_context(lengths, original, remaining, position, length, root, max),
        h::valid_prefix(original, 15),
        h::chosen_width(remaining, (length - root) as nat, root, max, width),
        0 <= current < lengths.len(), lengths[current] == length,
        h::canonical_code(lengths, current) * h::capacity((32 - length) as nat)
            == h::normalized_cursor(original, length, position),
        0 <= symbol < lengths.len(), root < lengths[symbol] <= 15,
        (h::canonical_prefix(lengths, current) as int) % h::capacity(root)
            == (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root),
    ensures lengths[symbol] <= root + width,
{
    wire_root_equivalence(lengths, original, current, symbol, root);
    chosen_width_covers_symbol(lengths, original, remaining, position, length, root,
        max, width, symbol);
}

pub proof fn wire_root_no_revisit(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int, third: int, root: nat)
    requires h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        0 <= first < lengths.len(), 0 <= second < lengths.len(), 0 <= third < lengths.len(),
        1 <= root < lengths[first] <= 15, root < lengths[second] <= 15,
        root < lengths[third] <= 15,
        lengths[first] < lengths[second]
            || (lengths[first] == lengths[second] && first < second),
        lengths[second] < lengths[third]
            || (lengths[second] == lengths[third] && second < third),
        (h::canonical_prefix(lengths, first) as int) % h::capacity(root)
            != (h::canonical_prefix(lengths, second) as int) % h::capacity(root),
    ensures (h::canonical_prefix(lengths, first) as int) % h::capacity(root)
        != (h::canonical_prefix(lengths, third) as int) % h::capacity(root),
{
    wire_root_equivalence(lengths, counts, first, second, root);
    wire_root_equivalence(lengths, counts, first, third, root);
    no_root_revisit(lengths, counts, first, second, third, root);
}

pub open spec fn fixture_counts() -> Seq<u16> {
    Seq::new(16, |level: int| if level == 2 { 2u16 }
        else if level == 3 { 4u16 } else { 0u16 })
}

pub proof fn independent_root_coverage()
    ensures model::source_context(seq![2u16, 2, 3, 3, 3, 3], fixture_counts(),
            fixture_counts(), 0, 2, 1, 3),
        h::chosen_width(fixture_counts(), 1, 1, 3, 1),
        model::in_root(seq![2u16, 2, 3, 3, 3, 3], 0, 1, 0),
        model::in_root(seq![2u16, 2, 3, 3, 3, 3], 1, 1, 0),
        !model::in_root(seq![2u16, 2, 3, 3, 3, 3], 2, 1, 0),
        model::root_prefix(seq![2u16, 2, 3, 3, 3, 3], 2, 1) == 1,
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let counts = fixture_counts();
    assert forall|level: int| 1 <= level <= 15 implies
        #[trigger] counts[level] == h::occurrences(lengths, level as u16) by {
        facts::histogram_prefix_step(lengths, 0, level as u16);
        facts::histogram_prefix_step(lengths, 1, level as u16);
        facts::histogram_prefix_step(lengths, 2, level as u16);
        facts::histogram_prefix_step(lengths, 3, level as u16);
        facts::histogram_prefix_step(lengths, 4, level as u16);
        facts::histogram_prefix_step(lengths, 5, level as u16);
        assert(lengths.take(6) =~= lengths);
        assert(lengths.take(0) =~= Seq::<u16>::empty());
    }
    assert(h::remaining_histogram(counts, counts, 0));
    assert(h::maximum_length(seq![2u16, 2, 3, 3, 3, 3]) == 3
        && h::before(fixture_counts(), 2) == 0
        && h::before(fixture_counts(), 3) == 2
        && h::capacity(1) == 2) by (compute);
    assert(h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 0) == 0
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 1) == 1
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 2) == 4
        && h::capacity(29) == 536870912 && h::capacity(30) == 1073741824
        && h::capacity(31) == 2147483648) by (compute);
}

pub proof fn independent_wire_order()
    ensures (h::canonical_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 2) as int) % h::capacity(2) == 2,
        (h::canonical_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 4) as int) % h::capacity(2) == 1,
        (h::canonical_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 6) as int) % h::capacity(2) == 3,
        model::root_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 2, 2) == 1,
        model::root_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 4, 2) == 2,
{
    assert(h::canonical_code(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 2) == 2
        && h::canonical_code(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 4) == 4
        && h::canonical_code(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 6) == 6
        && h::capacity(29) == 536870912 && h::capacity(30) == 1073741824
        && h::capacity(2) == 4) by (compute);
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(2, bit) == h::word_bit(0x4000_0000, (31 - bit) as u32) by {
        assert((2u32 >> bit) & 1 == (0x4000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(1, bit) == h::word_bit(0x8000_0000, (31 - bit) as u32) by {
        assert((1u32 >> bit) & 1 == (0x8000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(3, bit) == h::word_bit(0xc000_0000, (31 - bit) as u32) by {
        assert((3u32 >> bit) & 1 == (0xc000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    facts::reversal_matches_model(0x4000_0000, 2);
    facts::reversal_matches_model(0x8000_0000, 1);
    facts::reversal_matches_model(0xc000_0000, 3);
}

}
