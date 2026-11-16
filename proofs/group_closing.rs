use crate::closing_cost_proofs as closing;
use crate::constructor_pages_specs as pages;
use crate::group_closing_specs::{depth_count, selected_depth, weighted};
use crate::histogram_cost_proofs as facts;
use crate::histogram_cost_specs as histogram;
use crate::huffman_proofs as hproofs;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) proof fn weighted_step(counts: Seq<u16>, root: nat, max: nat,
    processed: nat, depth: nat)
    requires counts.len() == 16, 1 <= root <= max <= 15, 1 <= depth <= 16,
    ensures weighted(counts, root, max, processed + 1, depth)
        == weighted(counts, root, max, processed, depth)
            + if histogram::first_group(counts, root, max, processed)
                && depth <= root + pages::opening_width(
                    counts, processed, histogram::source_length(counts, processed), root, max) {
                histogram::charge(counts, root, max, processed) as int
            } else { 0int },
    decreases 16 - depth,
{
    if histogram::first_group(counts, root, max, processed) {
        let length = histogram::source_length(counts, processed);
        facts::normalized_width_exists(counts, processed, length, root, max);
        let width = pages::opening_width(counts, processed, length, root, max);
        hproofs::capacity_positive(width);
        assert(root < root + width <= 15);
    }
    if depth < 16 {
        weighted_step(counts, root, max, processed, depth + 1);
        if depth > root {
            let size = h::capacity((depth - root) as nat);
            let old = depth_count(counts, root, max, depth, processed);
            let new = depth_count(counts, root, max, depth, processed + 1);
            let delta = if selected_depth(counts, root, max, depth, processed) { 1int } else { 0int };
            assert(new == old + delta);
            assert(new * size == old * size + delta * size) by (nonlinear_arith)
                requires new == old + delta;
        }
    }
}

pub(crate) proof fn weighted_zero(counts: Seq<u16>, root: nat, max: nat, depth: nat)
    requires 1 <= depth <= 16,
    ensures weighted(counts, root, max, 0, depth) == 0,
    decreases 16 - depth,
{
    if depth < 16 {
        assert(depth_count(counts, root, max, depth, 0) == 0);
        weighted_zero(counts, root, max, depth + 1);
    }
}

pub(crate) proof fn sum_weighted(counts: Seq<u16>, root: nat, max: nat, processed: nat)
    requires counts.len() == 16, 1 <= root <= max <= 15,
    ensures histogram::sum(counts, root, max, processed) == weighted(counts, root, max, processed, 1),
    decreases processed,
{
    if processed > 0 {
        sum_weighted(counts, root, max, (processed - 1) as nat);
        weighted_step(counts, root, max, (processed - 1) as nat, 1);
    } else {
        weighted_zero(counts, root, max, 1);
    }
}

pub(crate) proof fn count_ordered_window(counts: Seq<u16>, root: nat, max: nat,
    depth: nat, processed: nat, lower: int, upper: int)
    requires lower <= upper,
        forall|position: nat| position < processed
            && #[trigger] selected_depth(counts, root, max, depth, position)
            ==> lower <= histogram::root_key(counts, root, position) < upper,
        forall|first: nat, second: nat| first < second < processed
            && #[trigger] selected_depth(counts, root, max, depth, first)
            && #[trigger] selected_depth(counts, root, max, depth, second)
            ==> histogram::root_key(counts, root, first) < histogram::root_key(counts, root, second),
    ensures depth_count(counts, root, max, depth, processed) <= upper - lower,
    decreases processed,
{
    if processed > 0 {
        let last = (processed - 1) as nat;
        if selected_depth(counts, root, max, depth, last) {
            let key = histogram::root_key(counts, root, last);
            assert(lower <= key < upper);
            assert forall|position: nat| position < last
                && #[trigger] selected_depth(counts, root, max, depth, position)
                implies lower <= histogram::root_key(counts, root, position) < key by {
                assert(histogram::root_key(counts, root, position)
                    < histogram::root_key(counts, root, last));
            }
            count_ordered_window(counts, root, max, depth, last, lower, key);
        } else {
            count_ordered_window(counts, root, max, depth, last, lower, upper);
        }
    }
}

pub(crate) proof fn boundary_quotient_window(first: int, last: int, size: int, key: int)
    requires size > 0, first < key * size <= last,
    ensures first / size < key <= last / size,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(first, size);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(last, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(first, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(last, size);
    assert(first / size < key) by (nonlinear_arith)
        requires first == size * (first / size) + first % size,
            0 <= first % size < size, size > 0, first < key * size;
    assert(key <= last / size) by (nonlinear_arith)
        requires last == size * (last / size) + last % size,
            0 <= last % size < size, size > 0, key * size <= last;
}

pub(crate) proof fn deepest_bucket_closes_group(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max,
        histogram::first_group(counts, root, max, position),
    ensures ({
        let depth = root + pages::opening_width(
            counts, position, histogram::source_length(counts, position), root, max);
        let boundary = (histogram::root_key(counts, root, position) + 1)
            * h::capacity((depth - root) as nat);
        h::first_code(counts, depth) < boundary
            <= h::first_code(counts, depth) + counts[depth as int] as int
    }),
{
    let length = histogram::source_length(counts, position);
    facts::source_length_join(lengths, counts, work, position);
    facts::normalized_width_exists(counts, position, length, root, max);
    let width = pages::opening_width(counts, position, length, root, max);
    let depth = root + width;
    let selected = closing::opening_width_attained(lengths, counts, work, root, max, position);
    facts::source_length_join(lengths, counts, work, selected);
    closing::first_group_aligned(lengths, counts, work, root, max, position);
    let cursor = h::normalized_cursor(counts, length, position);
    let size = h::capacity((32 - root) as nat);
    let unit = h::capacity((32 - depth) as nat);
    let last = h::normalized_cursor(counts, depth, selected);
    let start = h::first_code(counts, depth) * unit;
    let index = (h::first_code(counts, depth) + counts[depth as int] as int) * unit;
    let end = cursor + size;
    hproofs::capacity_positive((32 - root) as nat);
    hproofs::capacity_positive((32 - depth) as nat);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(cursor, size);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(last, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(last, size);
    assert(last < end) by (nonlinear_arith)
        requires cursor == size * (cursor / size),
            last == size * (last / size) + last % size,
            last / size == cursor / size, 0 <= last % size < size,
            end == cursor + size;
    assert(start <= last) by (nonlinear_arith)
        requires h::before(counts, depth) <= selected,
            last == (h::first_code(counts, depth) + selected - h::before(counts, depth)) * unit,
            start == h::first_code(counts, depth) * unit, unit > 0;
    assert(start <= index) by (nonlinear_arith)
        requires start == h::first_code(counts, depth) * unit,
            index == (h::first_code(counts, depth) + counts[depth as int] as int) * unit,
            unit > 0, counts[depth as int] >= 0;
    hproofs::normalized_cursor_bound(lengths, counts, work, length, position);
    hproofs::capacity_multiple((32 - root) as nat, 32);
    assert(h::capacity(32) == 4294967296) by (compute);
    closing::aligned_strict_gap(cursor, 4294967296, size);
    if index < end {
        if depth < 15 {
            if length < depth {
                crate::canonical_intervals::first_code_interval_separation(counts, length, depth);
            }
            hproofs::capacity_positive((32 - length) as nat);
            assert(cursor <= index) by (nonlinear_arith)
                requires h::before(counts, length) <= position < h::before(counts, length + 1),
                    h::before(counts, length + 1) == h::before(counts, length) + counts[length as int] as nat,
                    cursor == (h::first_code(counts, length) + position - h::before(counts, length))
                        * h::capacity((32 - length) as nat),
                    (h::first_code(counts, length) + counts[length as int] as nat)
                        * h::capacity((32 - length) as nat) <= index,
                    h::capacity((32 - length) as nat) > 0;
            assert(h::first_code(counts, depth + 1) * h::capacity((31 - depth) as nat) == index)
                by (nonlinear_arith)
                requires h::first_code(counts, depth + 1)
                        == 2 * (h::first_code(counts, depth) + counts[depth as int] as nat),
                    unit == 2 * h::capacity((31 - depth) as nat),
                    index == (h::first_code(counts, depth) + counts[depth as int] as int) * unit;
            let later = closing::complete_suffix_boundary(counts, depth + 1);
            facts::source_length_join(lengths, counts, work, later);
            assert(cursor / size * size <= index < (cursor / size + 1) * size)
                by (nonlinear_arith)
                requires cursor == size * (cursor / size), cursor <= index < end, end == cursor + size;
            closing::quotient_from_interval(index, size, cursor / size);
            let remaining = pages::opening_population(counts, position);
            crate::constructor_pages_proofs::canonical_population(counts, position);
            assert(crate::subtable_coverage_specs::source_context(
                lengths, counts, remaining, position, length, root, max));
            let symbol = work[later as int] as int;
            assert(crate::subtable_coverage_specs::in_root(lengths, symbol, root, cursor));
            crate::subtable_coverage_proofs::chosen_width_covers_symbol(lengths, counts, remaining,
                position, length, root, max, width, symbol);
            assert(false);
        } else {
            hproofs::code_space_partition(counts, 15);
            hproofs::capacity_product(15, 17);
            assert(index == 4294967296) by (nonlinear_arith)
                requires depth == 15, unit == h::capacity(17),
                    h::first_code(counts, 15) + counts[15] as int == h::capacity(15),
                    h::capacity(15) * h::capacity(17) == 4294967296,
                    index == (h::first_code(counts, 15) + counts[15] as int) * unit;
            assert(false);
        }
    }
    hproofs::capacity_product((depth - root) as nat, (32 - depth) as nat);
    let boundary = (histogram::root_key(counts, root, position) + 1)
        * h::capacity((depth - root) as nat);
    assert(end == boundary * unit) by (nonlinear_arith)
        requires cursor == size * (cursor / size),
            histogram::root_key(counts, root, position) == cursor / size,
            boundary == (histogram::root_key(counts, root, position) + 1)
                * h::capacity((depth - root) as nat),
            size == h::capacity((depth - root) as nat) * unit, end == cursor + size;
    assert(h::first_code(counts, depth) < boundary
        <= h::first_code(counts, depth) + counts[depth as int] as int) by (nonlinear_arith)
        requires unit > 0, start < end <= index,
            start == h::first_code(counts, depth) * unit, end == boundary * unit,
            index == (h::first_code(counts, depth) + counts[depth as int] as int) * unit;
}

pub(crate) proof fn opening_in_closing_window(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max,
        histogram::first_group(counts, root, max, position),
    ensures ({
        let depth = root + pages::opening_width(
            counts, position, histogram::source_length(counts, position), root, max);
        let size = h::capacity((depth - root) as nat);
        (h::first_code(counts, depth) as int) / size < histogram::root_key(counts, root, position) + 1
            <= (h::first_code(counts, depth) + counts[depth as int] as int) / size
    }),
{
    deepest_bucket_closes_group(lengths, counts, work, root, max, position);
    let length = histogram::source_length(counts, position);
    facts::normalized_width_exists(counts, position, length, root, max);
    let depth = root + pages::opening_width(counts, position, length, root, max);
    hproofs::capacity_positive((depth - root) as nat);
    boundary_quotient_window(h::first_code(counts, depth) as int,
        h::first_code(counts, depth) + counts[depth as int] as int,
        h::capacity((depth - root) as nat), histogram::root_key(counts, root, position) + 1);
}

pub(crate) proof fn depth_count_bound(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, depth: nat, processed: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max, 1 <= root < depth <= 15,
        processed <= h::before(counts, 16),
    ensures depth_count(counts, root, max, depth, processed) * h::capacity((depth - root) as nat)
        <= crate::closing_cost_specs::closing(root, depth,
            (2 * h::slots(counts, (depth - 1) as nat)) as nat, counts[depth as int] as nat),
{
    let size = h::capacity((depth - root) as nat);
    let lower = (h::first_code(counts, depth) as int) / size;
    let upper = (h::first_code(counts, depth) + counts[depth as int] as int) / size;
    hproofs::capacity_positive((depth - root) as nat);
    crate::subtable_coverage_proofs::ordered_quotients(h::first_code(counts, depth) as int,
        h::first_code(counts, depth) + counts[depth as int] as int, size);
    assert forall|position: nat| position < processed
        && #[trigger] selected_depth(counts, root, max, depth, position)
        implies lower <= histogram::root_key(counts, root, position) < upper by {
        opening_in_closing_window(lengths, counts, work, root, max, position);
    }
    assert forall|first: nat, second: nat| first < second < processed
        && #[trigger] selected_depth(counts, root, max, depth, first)
        && #[trigger] selected_depth(counts, root, max, depth, second)
        implies histogram::root_key(counts, root, first) < histogram::root_key(counts, root, second) by {
        facts::root_key_monotone(lengths, counts, work, root, first, second);
        assert(histogram::root_key(counts, root, first) != histogram::root_key(counts, root, second));
    }
    count_ordered_window(counts, root, max, depth, processed, lower, upper);
    closing::closing_counts_boundaries(counts, root, depth);
    assert(depth_count(counts, root, max, depth, processed) * size <= (upper - lower) * size)
        by (nonlinear_arith)
        requires depth_count(counts, root, max, depth, processed) <= upper - lower, size > 0;
}

pub(crate) proof fn weighted_forest_bound(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, processed: nat, depth: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max, 1 <= root <= max <= 15,
        processed <= h::before(counts, 16), 1 <= depth <= 15,
    ensures weighted(counts, root, max, processed, depth)
        <= crate::closing_cost_specs::forest(counts, root, depth,
            (2 * h::slots(counts, (depth - 1) as nat)) as nat),
    decreases 15 - depth,
{
    let available = (2 * h::slots(counts, (depth - 1) as nat)) as nat;
    let local = if depth > root {
        depth_count(counts, root, max, depth, processed) * h::capacity((depth - root) as nat)
    } else { 0int };
    let charge = crate::closing_cost_specs::closing(root, depth, available, counts[depth as int] as nat);
    if depth > root {
        depth_count_bound(lengths, counts, work, root, max, depth, processed);
    }
    assert(local <= charge);
    assert(weighted(counts, root, max, processed, depth)
        == local + weighted(counts, root, max, processed, depth + 1));
    if depth < 15 {
        weighted_forest_bound(lengths, counts, work, root, max, processed, depth + 1);
        assert(h::slots(counts, depth) == 2 * h::slots(counts, (depth - 1) as nat)
            - counts[depth as int] as int);
        assert(2 * ((2 * h::slots(counts, (depth - 1) as nat)) as nat
            - counts[depth as int]) as nat == 2 * h::slots(counts, depth));
        assert(crate::closing_cost_specs::forest(counts, root, depth, available)
            == charge + crate::closing_cost_specs::forest(counts, root, depth + 1,
                (2 * h::slots(counts, depth)) as nat));
    } else {
        assert(weighted(counts, root, max, processed, depth + 1) == 0);
        assert(crate::closing_cost_specs::forest(counts, root, depth, available) == charge);
    }
}

pub(crate) proof fn histogram_forest_bound(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, processed: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max, 1 <= root <= max <= 15,
        processed <= h::before(counts, 16),
    ensures histogram::sum(counts, root, max, processed)
        <= crate::closing_cost_specs::forest(counts, root, 1, 2),
{
    sum_weighted(counts, root, max, processed);
    weighted_forest_bound(lengths, counts, work, root, max, processed, 1);
    assert(h::slots(counts, 0) == 1);
}

pub(crate) proof fn certificate_histogram_budget(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, bound: nat, limit: nat,
    upper: spec_fn(nat, nat, nat) -> Option<nat>)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::maximum_length(lengths) <= max, 1 <= root <= max <= 15,
        lengths.len() <= bound, crate::closing_cost_specs::certificate(upper, root, bound),
        forall|remaining: nat| 2 <= remaining <= bound ==>
            #[trigger] upper(1, 2, remaining) != None
                && upper(1, 2, remaining).unwrap() <= limit,
    ensures histogram::sum(counts, root, max, h::before(counts, 16)) <= limit,
{
    histogram_forest_bound(lengths, counts, work, root, max, h::before(counts, 16));
    closing::bounds_complete_histogram(lengths, counts, root, bound, upper, limit);
}

pub(crate) proof fn no_capacity_error_from_certificate(alphabet: h::Alphabet,
    lengths: Seq<u16>, requested: nat, original: Seq<crate::Code>, codes: Seq<crate::Code>,
    original_work: Seq<u16>, work: Seq<u16>, outcome: crate::huffman::InflateTable,
    root: nat, max: nat, bound: nat, child_limit: nat, limit: nat,
    upper: spec_fn(nat, nat, nat) -> Option<nat>)
    requires crate::constructor_table_specs::result(alphabet, lengths, requested,
            original, codes, original_work, work, outcome),
        root == crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
        max == h::maximum_length(lengths), 1 <= root <= max <= 15,
        h::valid_histogram(lengths, h::histogram(lengths)),
        h::valid_prefix(h::histogram(lengths), 15), h::slots(h::histogram(lengths), 15) == 0,
        lengths.len() <= bound, crate::closing_cost_specs::certificate(upper, root, bound),
        forall|remaining: nat| 2 <= remaining <= bound ==>
            #[trigger] upper(1, 2, remaining) != None
                && upper(1, 2, remaining).unwrap() <= child_limit,
        crate::table_preparation_specs::root_capacity_allowed(alphabet, limit),
        h::capacity(root) + child_limit <= limit,
    ensures !matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough),
{
    if matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough) {
        reveal(crate::constructor_table_specs::result);
        assert(h::bucket_ordered(lengths, h::histogram(lengths), work));
        certificate_histogram_budget(lengths, h::histogram(lengths), work, root, max, bound,
            child_limit, upper);
        facts::no_capacity_error(alphabet, lengths, requested, original, codes, original_work,
            work, outcome, root, max, limit);
    }
}

pub(crate) proof fn forest_empty_tail(counts: Seq<u16>, root: nat, depth: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
        forall|level: int| depth <= level <= 15 ==> #[trigger] counts[level] == 0,
    ensures crate::closing_cost_specs::forest(counts, root, depth, 0) == 0,
    decreases 15 - depth,
{
    assert(counts[depth as int] == 0);
    crate::closing_cost_proofs::closing_zero(root, depth);
    if depth < 15 { forest_empty_tail(counts, root, depth + 1); }
}

pub(crate) proof fn independent_two_page_forest()
    ensures histogram::sum(crate::subtable_coverage_proofs::fixture_counts(), 2, 3, 6)
            <= crate::closing_cost_specs::forest(crate::subtable_coverage_proofs::fixture_counts(), 2, 1, 2),
        crate::closing_cost_specs::forest(crate::subtable_coverage_proofs::fixture_counts(), 2, 1, 2) == 4,
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let counts = crate::subtable_coverage_proofs::fixture_counts();
    let work = seq![0u16, 1, 2, 3, 4, 5];
    crate::page_source_proofs::independent_opening();
    facts::independent_complete_path();
    facts::path_sound(counts, 6);
    assert(h::maximum_length(seq![2u16, 2, 3, 3, 3, 3]) == 3) by (compute);
    assert(h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 2, 0)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 2, 1)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 0)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 1)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 2)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 3)) by (compute);
    assert forall|level: int, ordinal: int| 1 <= level <= 15 && 0 <= ordinal < counts[level]
        implies #[trigger] h::bucket_entry(lengths, counts, work, level, ordinal) by {
        assert(level == 2 || level == 3);
    }
    histogram_forest_bound(lengths, counts, work, 2, 3, 6);
    assert(h::capacity(1) == 2) by (compute);
    closing::closing_from_quotients(2, 3, 4, 4, 2, 2, 0);
    forest_empty_tail(counts, 2, 4);
    assert(counts[1] == 0 && counts[2] == 2 && counts[3] == 4);
    assert(crate::closing_cost_specs::forest(counts, 2, 3, 4) == 4);
    assert(crate::closing_cost_specs::forest(counts, 2, 2, 4) == 4);
    assert(crate::closing_cost_specs::forest(counts, 2, 1, 2) == 4);
}

}
