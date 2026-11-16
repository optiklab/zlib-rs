use crate::closing_cost_specs::{certificate, closing, edge, forest, state};
use crate::histogram_cost_proofs as facts;
use crate::histogram_cost_specs as histogram;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) proof fn canonical_frontier_partition(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
    ensures h::first_code(counts, depth) + counts[depth as int] as int
        + h::slots(counts, depth) == h::capacity(depth),
        h::first_code(counts, depth) + 2 * h::slots(counts, (depth - 1) as nat)
            == h::capacity(depth),
{
    crate::huffman_proofs::code_space_partition(counts, depth);
}

pub(crate) proof fn quotient_from_interval(value: int, size: int, quotient: int)
    requires size > 0, quotient * size <= value < (quotient + 1) * size,
    ensures value / size == quotient,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(value, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(value, size);
    assert(value / size == quotient) by (nonlinear_arith)
        requires value == size * (value / size) + value % size,
            0 <= value % size < size, size > 0,
            quotient * size <= value < (quotient + 1) * size;
}

pub(crate) proof fn closing_zero(root: nat, depth: nat)
    ensures closing(root, depth, 0, 0) == 0,
{
    if depth > root {
        let size = h::capacity((depth - root) as nat);
        crate::huffman_proofs::capacity_positive((depth - root) as nat);
        quotient_from_interval(size - 1, size, 0);
    }
}

pub(crate) proof fn complement_quotient(total: int, remaining: int, size: int)
    requires size > 0, total % size == 0,
    ensures (total - remaining) / size
        == total / size - (remaining + size - 1) / size,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(total, size);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(remaining + size - 1, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(remaining + size - 1, size);
    let rounded = (remaining + size - 1) / size;
    let quotient = total / size - rounded;
    assert(quotient * size <= total - remaining < (quotient + 1) * size)
        by (nonlinear_arith)
        requires total == size * (total / size),
            remaining + size - 1 == size * rounded + (remaining + size - 1) % size,
            0 <= (remaining + size - 1) % size < size, size > 0,
            quotient == total / size - rounded;
    quotient_from_interval(total - remaining, size, quotient);
}

pub(crate) proof fn closing_from_quotients(root: nat, depth: nat, available: nat,
    leaves: nat, size: int, before: int, after: int)
    requires 1 <= root < depth <= 15, leaves <= available,
        size == h::capacity((depth - root) as nat), size > 0, after <= before,
        before * size <= available + size - 1 < (before + 1) * size,
        after * size <= available - leaves + size - 1 < (after + 1) * size,
    ensures closing(root, depth, available, leaves) == (before - after) * size,
{
    quotient_from_interval(available + size - 1, size, before);
    quotient_from_interval(available - leaves + size - 1, size, after);
    assert((before - after) * size >= 0) by (nonlinear_arith)
        requires after <= before, size > 0;
}

pub(crate) proof fn closing_counts_boundaries(counts: Seq<u16>, root: nat, depth: nat)
    requires counts.len() == 16, 1 <= root < depth <= 15,
        h::valid_prefix(counts, depth),
    ensures closing(root, depth, (2 * h::slots(counts, (depth - 1) as nat)) as nat,
            counts[depth as int] as nat)
        == ((h::first_code(counts, depth) + counts[depth as int] as int)
                / h::capacity((depth - root) as nat)
            - (h::first_code(counts, depth) as int)
                / h::capacity((depth - root) as nat)) * h::capacity((depth - root) as nat),
{
    let size = h::capacity((depth - root) as nat);
    let total = h::capacity(depth);
    let available = 2 * h::slots(counts, (depth - 1) as nat);
    let leaves = counts[depth as int] as int;
    canonical_frontier_partition(counts, depth);
    crate::huffman_proofs::capacity_positive((depth - root) as nat);
    crate::huffman_proofs::capacity_multiple((depth - root) as nat, depth);
    assert(0 <= leaves <= available);
    complement_quotient(total, available, size);
    complement_quotient(total, available - leaves, size);
    crate::subtable_coverage_proofs::ordered_quotients(
        available - leaves + size - 1, available + size - 1, size);
}

pub(crate) proof fn scaled_unit_gap(unit: int, units: int, blocks: int)
    requires unit > 0, unit * units < unit * blocks,
    ensures unit * units + unit <= unit * blocks,
{
    assert(units < blocks) by (nonlinear_arith)
        requires unit > 0, unit * units < unit * blocks;
    assert(unit * units + unit <= unit * blocks) by (nonlinear_arith)
        requires unit > 0, units + 1 <= blocks;
}

pub(crate) proof fn aligned_leaf_step(cursor: int, cell: int, size: int)
    requires 0 < cell <= size, cursor % cell == 0, size % cell == 0,
    ensures cursor / size == (cursor + cell) / size || (cursor + cell) % size == 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cursor, cell);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size, cell);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cursor, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(cursor, size);
    let quotient = cursor / size;
    let residue = cursor % size;
    let units = cursor / cell - (size / cell) * quotient;
    assert(residue == cell * units) by (nonlinear_arith)
        requires cursor == cell * (cursor / cell), size == cell * (size / cell),
            cursor == size * quotient + residue,
            units == cursor / cell - (size / cell) * quotient;
    scaled_unit_gap(cell, units, size / cell);
    if residue + cell < size {
        assert(quotient * size <= cursor + cell < (quotient + 1) * size)
            by (nonlinear_arith)
            requires cursor == size * quotient + residue,
                0 <= residue, residue + cell < size, cell > 0;
        quotient_from_interval(cursor + cell, size, quotient);
    } else {
        assert(cursor + cell == (quotient + 1) * size) by (nonlinear_arith)
            requires cursor == size * quotient + residue, residue + cell == size;
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(quotient + 1, size);
    }
}

pub(crate) proof fn first_group_aligned(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        histogram::first_group(counts, root, max, position),
    ensures h::normalized_cursor(counts, histogram::source_length(counts, position), position)
        % h::capacity((32 - root) as nat) == 0,
{
    facts::source_length_join(lengths, counts, work, position);
    facts::adjacent_group(lengths, counts, work, root, max, position);
    let length = histogram::source_length(counts, position);
    let size = h::capacity((32 - root) as nat);
    crate::huffman_proofs::capacity_positive((32 - root) as nat);
    if position == h::before(counts, root + 1) {
        crate::huffman_proofs::before_monotone(counts, root + 1, length);
        assert(h::before(counts, length) == position);
        assert forall|level: int| root < level < length implies counts[level] == 0 by {
            crate::huffman_proofs::before_monotone(counts, root + 1, level as nat);
            crate::huffman_proofs::before_monotone(counts, level as nat + 1, length);
        }
        crate::huffman_proofs::first_code_gap(counts, root, length);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
            (h::first_code(counts, root) + counts[root as int] as nat) as int, size);
    } else {
        let previous = (position - 1) as nat;
        facts::source_length_join(lengths, counts, work, previous);
        crate::constructor_pages_proofs::ordered_positions(lengths, counts, work, previous, position);
        let old_length = histogram::source_length(counts, previous);
        assert(h::before(counts, root + 1) <= previous);
        assert(histogram::bucket(counts, previous, old_length));
        if old_length <= root {
            crate::huffman_proofs::before_monotone(counts, old_length + 1, root + 1);
            assert(false);
        }
        assert(root < old_length <= length);
        crate::huffman_proofs::normalized_cursor_next(counts, old_length, length, previous);
        let old = h::normalized_cursor(counts, old_length, previous);
        let cell = h::capacity((32 - old_length) as nat);
        crate::huffman_proofs::capacity_positive((32 - old_length) as nat);
        crate::huffman_proofs::capacity_monotone((32 - old_length) as nat, (32 - root) as nat);
        crate::huffman_proofs::capacity_multiple((32 - old_length) as nat, (32 - root) as nat);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
            h::first_code(counts, old_length) + previous - h::before(counts, old_length), cell);
        aligned_leaf_step(old, cell, size);
        assert(histogram::root_key(counts, root, previous)
            != histogram::root_key(counts, root, position));
    }
}

pub(crate) proof fn complete_suffix_boundary(counts: Seq<u16>, depth: nat) -> (position: nat)
    requires counts.len() == 16, 1 <= depth <= 15, h::slots(counts, 15) == 0,
        0 <= h::first_code(counts, depth) * h::capacity((32 - depth) as nat) < 4294967296,
    ensures position < h::before(counts, 16),
        depth <= histogram::source_length(counts, position) <= 15,
        histogram::bucket(counts, position, histogram::source_length(counts, position)),
        h::normalized_cursor(counts, histogram::source_length(counts, position), position)
            == h::first_code(counts, depth) * h::capacity((32 - depth) as nat),
{
    let index = h::first_code(counts, depth) * h::capacity((32 - depth) as nat);
    crate::canonical_intervals::complete_bucket_coverage(counts, depth, index);
    let level = choose|level: nat| depth <= level <= 15
        && #[trigger] h::first_code(counts, level) * h::capacity((32 - level) as nat) <= index
        < (h::first_code(counts, level) + counts[level as int] as nat)
            * h::capacity((32 - level) as nat);
    let cell = h::capacity((32 - level) as nat);
    let code = h::first_code(counts, depth) * h::capacity((level - depth) as nat);
    crate::huffman_proofs::capacity_positive((32 - level) as nat);
    crate::huffman_proofs::capacity_product((level - depth) as nat, (32 - level) as nat);
    assert(index == code * cell) by (nonlinear_arith)
        requires index == h::first_code(counts, depth) * h::capacity((32 - depth) as nat),
            h::capacity((32 - depth) as nat) == h::capacity((level - depth) as nat) * cell,
            code == h::first_code(counts, depth) * h::capacity((level - depth) as nat);
    assert(h::first_code(counts, level) <= code
        < h::first_code(counts, level) + counts[level as int] as nat)
        by (nonlinear_arith)
        requires cell > 0, index == code * cell,
            h::first_code(counts, level) * cell <= index
                < (h::first_code(counts, level) + counts[level as int] as nat) * cell;
    let ordinal = (code - h::first_code(counts, level)) as nat;
    let position = h::before(counts, level) + ordinal;
    assert(h::before(counts, level + 1) == h::before(counts, level) + counts[level as int] as nat);
    assert(histogram::bucket(counts, position, level));
    assert(exists|selected: nat| #[trigger] histogram::bucket(counts, position, selected));
    assert(histogram::bucket(counts, position, histogram::source_length(counts, position)));
    facts::bucket_unique(counts, position, level, histogram::source_length(counts, position));
    crate::huffman_proofs::before_monotone(counts, level + 1, 16);
    position
}

pub(crate) proof fn aligned_strict_gap(first: int, second: int, size: int)
    requires size > 0, first < second, first % size == 0, second % size == 0,
    ensures first + size <= second,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(first, size);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(second, size);
    let left = first / size;
    let right = second / size;
    assert(left < right) by (nonlinear_arith)
        requires first == size * left, second == size * right, size > 0, first < second;
    assert(first + size <= second) by (nonlinear_arith)
        requires first == size * left, second == size * right, size > 0, left + 1 <= right;
}

pub(crate) proof fn opening_width_attained(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat) -> (selected: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max,
        histogram::first_group(counts, root, max, position),
    ensures selected < h::before(counts, 16),
        histogram::root_key(counts, root, selected) == histogram::root_key(counts, root, position),
        histogram::source_length(counts, selected) == root + crate::constructor_pages_specs::opening_width(
            counts, position, histogram::source_length(counts, position), root, max),
{
    let length = histogram::source_length(counts, position);
    facts::source_length_join(lengths, counts, work, position);
    facts::normalized_width_exists(counts, position, length, root, max);
    let remaining = crate::constructor_pages_specs::opening_population(counts, position);
    let width = crate::constructor_pages_specs::opening_width(counts, position, length, root, max);
    if width == length - root {
        position
    } else {
        first_group_aligned(lengths, counts, work, root, max, position);
        crate::constructor_pages_proofs::canonical_population(counts, position);
        assert(crate::subtable_coverage_specs::source_context(
            lengths, counts, remaining, position, length, root, max));
        let depth = root + width;
        let cursor = h::normalized_cursor(counts, length, position);
        let size = h::capacity((32 - root) as nat);
        let cell = h::capacity((33 - depth) as nat);
        let residue = h::lookahead_space(remaining, (length - root) as nat, root, (width - 1) as nat)
            - remaining[depth as int - 1] as int;
        assert(residue > 0);
        crate::subtable_coverage_proofs::lookahead_boundary(counts, remaining,
            position, length, root, (width - 1) as nat);
        let index = h::first_code(counts, depth) * h::capacity((32 - depth) as nat);
        assert(index == (h::first_code(counts, (depth - 1) as nat)
            + counts[depth as int - 1] as nat) * cell) by (nonlinear_arith)
            requires h::first_code(counts, depth) == 2 * (
                    h::first_code(counts, (depth - 1) as nat) + counts[depth as int - 1] as nat),
                cell == 2 * h::capacity((32 - depth) as nat),
                index == h::first_code(counts, depth) * h::capacity((32 - depth) as nat);
        crate::huffman_proofs::capacity_positive((33 - depth) as nat);
        assert(index < cursor + size) by (nonlinear_arith)
            requires index == cursor + size - residue * cell, residue > 0, cell > 0;
        crate::canonical_intervals::first_code_interval_separation(counts, length, depth);
        crate::huffman_proofs::capacity_positive((32 - length) as nat);
        assert(cursor <= index) by (nonlinear_arith)
            requires h::before(counts, length) <= position < h::before(counts, length + 1),
                h::before(counts, length + 1) == h::before(counts, length) + counts[length as int] as nat,
                cursor == (h::first_code(counts, length) + position - h::before(counts, length))
                    * h::capacity((32 - length) as nat),
                (h::first_code(counts, length) + counts[length as int] as nat)
                    * h::capacity((32 - length) as nat) <= index,
                h::capacity((32 - length) as nat) > 0;
        crate::huffman_proofs::capacity_positive((32 - root) as nat);
        crate::huffman_proofs::normalized_cursor_bound(lengths, counts, work, length, position);
        crate::huffman_proofs::capacity_product(root, (32 - root) as nat);
        crate::huffman_proofs::capacity_positive(root);
        crate::huffman_proofs::capacity_multiple((32 - root) as nat, 32);
        assert(h::capacity(32) == 4294967296) by (compute);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cursor, size);
        aligned_strict_gap(cursor, 4294967296, size);
        let selected = complete_suffix_boundary(counts, depth);
        facts::source_length_join(lengths, counts, work, selected);
        assert(cursor / size * size <= index < (cursor / size + 1) * size)
            by (nonlinear_arith)
            requires cursor == size * (cursor / size), cursor <= index < cursor + size;
        quotient_from_interval(index, size, cursor / size);
        let symbol = work[selected as int] as int;
        assert(crate::subtable_coverage_specs::in_root(lengths, symbol, root, cursor));
        crate::subtable_coverage_proofs::chosen_width_covers_symbol(lengths, counts, remaining,
            position, length, root, max, width, symbol);
        selected
    }
}

pub(crate) proof fn bounds_path(counts: Seq<u16>, root: nat, bound: nat,
    upper: spec_fn(nat, nat, nat) -> Option<nat>, depth: nat,
    available: nat, remaining: nat)
    requires histogram::path(counts, depth, available, remaining),
        remaining <= bound, certificate(upper, root, bound),
        upper(depth, available, remaining) != None,
    ensures forest(counts, root, depth, available) <= upper(depth, available, remaining).unwrap(),
    decreases 15 - depth,
{
    facts::path_leaf_capacity(counts, depth, available, remaining);
    assert(state(bound, depth, available, remaining));
    if depth < 15 {
        let leaves = counts[depth as int] as nat;
        let next_available = 2 * (available - leaves) as nat;
        let next_remaining = (remaining - leaves) as nat;
        assert(histogram::path(counts, depth + 1, next_available, next_remaining));
        facts::path_leaf_capacity(counts, depth + 1, next_available, next_remaining);
        assert(next_available <= next_remaining <= bound);
        assert(state(bound, depth + 1, next_available, next_remaining));
        assert(edge(bound, depth, available, remaining, leaves));
        assert(upper(depth + 1, next_available, next_remaining) != None);
        bounds_path(counts, root, bound, upper, depth + 1, next_available, next_remaining);
    } else {
        assert(available == remaining && available == counts[depth as int]);
    }
}

pub(crate) proof fn bounds_complete_histogram(lengths: Seq<u16>, counts: Seq<u16>,
    root: nat, bound: nat, upper: spec_fn(nat, nat, nat) -> Option<nat>, limit: nat)
    requires h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::slots(counts, 15) == 0, lengths.len() <= bound,
        certificate(upper, root, bound),
        forall|remaining: nat| 2 <= remaining <= bound ==>
            #[trigger] upper(1, 2, remaining) != None
                && upper(1, 2, remaining).unwrap() <= limit,
    ensures forest(counts, root, 1, 2) <= limit,
{
    facts::complete_histogram_path(lengths, counts, bound);
    let remaining = h::before(counts, 16);
    assert(upper(1, 2, remaining) != None);
    bounds_path(counts, root, bound, upper, 1, 2, remaining);
}

pub(crate) open spec fn tiny(depth: nat, available: nat, remaining: nat) -> Option<nat> {
    if (depth == 1 && available == 2 && remaining == 2)
        || (2 <= depth <= 15 && available == 0 && remaining == 0) {
        Some(0)
    } else { None }
}

pub(crate) open spec fn missing_child(depth: nat, available: nat, remaining: nat) -> Option<nat> {
    if depth == 1 && available == 2 && remaining == 2 { Some(0) } else { None }
}

pub(crate) proof fn independent_certificate()
    ensures certificate(|depth: nat, available: nat, remaining: nat|
            tiny(depth, available, remaining), 1, 2),
        !certificate(|depth: nat, available: nat, remaining: nat|
            missing_child(depth, available, remaining), 1, 2),
{
    let upper = |depth: nat, available: nat, remaining: nat| tiny(depth, available, remaining);
    assert forall|depth: nat, available: nat, remaining: nat|
        state(2, depth, available, remaining) implies
        match #[trigger] upper(depth, available, remaining) {
            None => true,
            Some(value) => if depth == 15 {
                closing(1, depth, available, available) <= value
            } else {
                forall|leaves: nat| #[trigger] edge(2, depth, available, remaining, leaves)
                    ==> match upper(depth + 1, 2 * (available - leaves) as nat,
                        (remaining - leaves) as nat) {
                        Some(next) => closing(1, depth, available, leaves) + next <= value,
                        None => false,
                    }
            },
        } by {
        if upper(depth, available, remaining) != None && depth == 15 {
            assert(available == 0 && remaining == 0);
            closing_zero(1, depth);
        }
        if upper(depth, available, remaining) != None && depth < 15 {
            assert forall|leaves: nat| #[trigger] edge(2, depth, available, remaining, leaves)
                implies match upper(depth + 1, 2 * (available - leaves) as nat,
                    (remaining - leaves) as nat) {
                    Some(next) => closing(1, depth, available, leaves) + next <= 0,
                    None => false,
                } by {
                if depth == 1 {
                    assert(available == 2 && remaining == 2 && leaves == 2);
                } else {
                    assert(available == 0 && remaining == 0 && leaves == 0);
                    closing_zero(1, depth);
                }
            }
        }
    }
    let missing = |depth: nat, available: nat, remaining: nat| missing_child(depth, available, remaining);
    if certificate(missing, 1, 2) {
        crate::huffman_proofs::capacity_positive(14);
        assert(state(2, 1, 2, 2));
        assert(missing(1, 2, 2) == Some(0));
        assert(edge(2, 1, 2, 2, 2));
        assert(missing(2, 0, 0) != None);
        assert(false);
    }
}

pub(crate) proof fn independent_two_leaf_bound()
    ensures forest(seq![0u16, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 1, 1, 2) == 0,
{
    let lengths = seq![1u16, 1];
    let counts = seq![0u16, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    independent_certificate();
    assert forall|level: int| 1 <= level <= 15 implies
        #[trigger] counts[level] == h::occurrences(lengths, level as u16) by {
        crate::huffman_proofs::histogram_prefix_step(lengths, 0, level as u16);
        crate::huffman_proofs::histogram_prefix_step(lengths, 1, level as u16);
        assert(lengths.take(0) =~= Seq::<u16>::empty());
        assert(lengths.take(2) =~= lengths);
    }
    assert(h::valid_histogram(lengths, counts));
    assert(h::slots(counts, 0) == 1);
    assert(h::slots(counts, 1) == 0);
    assert forall|level: nat| level <= 15 implies h::slots(counts, level) >= 0 by {
        if level >= 1 {
            crate::huffman_proofs::slots_empty_tail(counts, 1, level);
        }
    }
    crate::huffman_proofs::slots_empty_tail(counts, 1, 15);
    facts::complete_histogram_path(lengths, counts, 2);
    bounds_path(counts, 1, 2,
        |depth: nat, available: nat, remaining: nat| tiny(depth, available, remaining), 1, 2, 2);
}

pub(crate) proof fn independent_maximizing_closed_costs()
    ensures forest(seq![0u16, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 233, 45, 1, 1, 2],
            10, 1, 2) == 308,
        forest(seq![0u16, 0, 3, 1, 1, 1, 1, 0, 0, 0, 13, 5, 1, 1, 1, 2],
            9, 1, 2) == 80,
{
    assert(h::capacity(1) == 2 && h::capacity(2) == 4 && h::capacity(3) == 8
        && h::capacity(4) == 16 && h::capacity(5) == 32 && h::capacity(6) == 64) by (compute);
    let literals = seq![0u16, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 233, 45, 1, 1, 2];
    let distances = seq![0u16, 0, 3, 1, 1, 1, 1, 0, 0, 0, 13, 5, 1, 1, 1, 2];
    closing_from_quotients(10, 15, 2, 2, 32, 1, 0);
    closing_from_quotients(10, 14, 2, 1, 16, 1, 1);
    closing_from_quotients(10, 13, 2, 1, 8, 1, 1);
    closing_from_quotients(10, 12, 46, 45, 4, 12, 1);
    closing_from_quotients(10, 11, 256, 233, 2, 128, 12);
    closing_from_quotients(9, 15, 2, 2, 64, 1, 0);
    closing_from_quotients(9, 14, 2, 1, 32, 1, 1);
    closing_from_quotients(9, 13, 2, 1, 16, 1, 1);
    closing_from_quotients(9, 12, 2, 1, 8, 1, 1);
    closing_from_quotients(9, 11, 6, 5, 4, 2, 1);
    closing_from_quotients(9, 10, 16, 13, 2, 8, 2);
    reveal_with_fuel(forest, 2);
    assert(forest(literals, 10, 15, 2) == 32);
    assert(forest(literals, 10, 14, 2) == 32);
    assert(forest(literals, 10, 13, 2) == 32);
    assert(forest(literals, 10, 12, 46) == 76);
    assert(forest(literals, 10, 11, 256) == 308);
    assert(forest(distances, 9, 15, 2) == 64);
    assert(forest(distances, 9, 14, 2) == 64);
    assert(forest(distances, 9, 13, 2) == 64);
    assert(forest(distances, 9, 12, 2) == 64);
    assert(forest(distances, 9, 11, 6) == 68);
    assert(forest(distances, 9, 10, 16) == 80);
    reveal_with_fuel(forest, 16);
}

}
