use crate::huffman_proofs as facts;
use crate::huffman_specs as model;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_bound};
use vstd::prelude::*;

verus! {

pub proof fn first_code_interval_separation(counts: Seq<u16>, low: nat, high: nat)
    requires counts.len() == 16, 1 <= low < high <= 15,
    ensures (model::first_code(counts, low) + counts[low as int] as nat)
            * model::capacity((32 - low) as nat)
        <= model::first_code(counts, high) * model::capacity((32 - high) as nat),
    decreases high - low,
{
    let previous = model::first_code(counts, (high - 1) as nat);
    let assigned = counts[high as int - 1] as nat;
    let width = model::capacity((32 - high) as nat);
    facts::capacity_positive((32 - high) as nat);
    assert(model::capacity((33 - high) as nat) == 2 * width);
    assert(2 * (previous + assigned) * width >= previous * (2 * width))
        by (nonlinear_arith) requires assigned >= 0, width > 0;
    if low + 1 < high {
        first_code_interval_separation(counts, low, (high - 1) as nat);
    } else {
        assert(high == low + 1);
        assert(2 * (previous + assigned) * width
            == (previous + assigned) * (2 * width)) by (nonlinear_arith);
    }
}

pub proof fn canonical_interval_separation(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int)
    requires model::valid_histogram(lengths, counts),
        0 <= first < lengths.len(), 0 <= second < lengths.len(),
        1 <= lengths[first] <= 15, 1 <= lengths[second] <= 15,
        lengths[first] < lengths[second]
            || (lengths[first] == lengths[second] && first < second),
    ensures (model::canonical_code(lengths, first) + 1)
            * model::capacity((32 - lengths[first]) as nat)
        <= model::canonical_code(lengths, second)
            * model::capacity((32 - lengths[second]) as nat),
{
    let low = lengths[first] as nat;
    let high = lengths[second] as nat;
    let left = model::canonical_code(lengths, first);
    let right = model::canonical_code(lengths, second);
    let left_width = model::capacity((32 - low) as nat);
    let right_width = model::capacity((32 - high) as nat);
    facts::first_code_from_histogram(lengths, counts, low);
    facts::first_code_from_histogram(lengths, counts, high);
    facts::capacity_positive((32 - low) as nat);
    facts::capacity_positive((32 - high) as nat);
    if low < high {
        facts::histogram_prefix_step(lengths, first, lengths[first]);
        facts::occurrences_prefix_bound(lengths, first + 1, lengths[first]);
        first_code_interval_separation(counts, low, high);
        let end = model::first_code(counts, low) + counts[low as int] as nat;
        let start = model::first_code(counts, high);
        assert((left + 1) * left_width <= end * left_width)
            by (nonlinear_arith) requires left + 1 <= end, left_width > 0;
        assert(start * right_width <= right * right_width)
            by (nonlinear_arith) requires start <= right, right_width > 0;
    } else {
        facts::strict_occurrence_ranks(lengths, first, second, lengths[first]);
        assert(left + 1 <= right);
        assert((left + 1) * left_width <= right * left_width)
            by (nonlinear_arith) requires left + 1 <= right, left_width > 0;
    }
}

pub proof fn canonical_intervals_disjoint(lengths: Seq<u16>, counts: Seq<u16>,
    first: int, second: int)
    requires model::valid_histogram(lengths, counts),
        0 <= first < lengths.len(), 0 <= second < lengths.len(), first != second,
        1 <= lengths[first] <= 15, 1 <= lengths[second] <= 15,
    ensures (model::canonical_code(lengths, first) + 1)
            * model::capacity((32 - lengths[first]) as nat)
        <= model::canonical_code(lengths, second)
            * model::capacity((32 - lengths[second]) as nat)
        || (model::canonical_code(lengths, second) + 1)
            * model::capacity((32 - lengths[second]) as nat)
        <= model::canonical_code(lengths, first)
            * model::capacity((32 - lengths[first]) as nat),
{
    if lengths[first] < lengths[second]
        || (lengths[first] == lengths[second] && first < second) {
        canonical_interval_separation(lengths, counts, first, second);
    } else {
        canonical_interval_separation(lengths, counts, second, first);
    }
}

pub proof fn canonical_interval_bound(lengths: Seq<u16>, counts: Seq<u16>, symbol: int)
    requires model::valid_histogram(lengths, counts),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
        model::valid_prefix(counts, lengths[symbol] as nat),
    ensures 0 <= model::canonical_code(lengths, symbol)
            * model::capacity((32 - lengths[symbol]) as nat)
        < (model::canonical_code(lengths, symbol) + 1)
            * model::capacity((32 - lengths[symbol]) as nat) <= 4294967296,
{
    let length = lengths[symbol] as nat;
    let code = model::canonical_code(lengths, symbol);
    let width = model::capacity((32 - length) as nat);
    let limit = model::capacity(length);
    facts::canonical_code_bound(lengths, counts, symbol);
    facts::capacity_positive((32 - length) as nat);
    facts::capacity_product(length, (32 - length) as nat);
    assert(model::capacity(32) == 4294967296) by (compute);
    assert(0 <= code * width < (code + 1) * width <= limit * width)
        by (nonlinear_arith) requires 0 <= code < limit, width > 0;
}

pub proof fn complete_bucket_coverage(counts: Seq<u16>, depth: nat, index: int)
    requires counts.len() == 16, 1 <= depth <= 15,
        model::slots(counts, 15) == 0,
        model::first_code(counts, depth) * model::capacity((32 - depth) as nat) <= index,
        index < 4294967296,
    ensures exists|level: nat| depth <= level <= 15
        && #[trigger] model::first_code(counts, level) * model::capacity((32 - level) as nat) <= index
        < (model::first_code(counts, level) + counts[level as int] as nat)
            * model::capacity((32 - level) as nat),
    decreases 15 - depth,
{
    let start = model::first_code(counts, depth);
    let assigned = counts[depth as int] as nat;
    let width = model::capacity((32 - depth) as nat);
    let end = (start + assigned) * width;
    if index < end {
        assert(exists|level: nat| depth <= level <= 15
            && #[trigger] model::first_code(counts, level) * model::capacity((32 - level) as nat) <= index
            < (model::first_code(counts, level) + counts[level as int] as nat)
                * model::capacity((32 - level) as nat)) by {
            assert(depth <= depth <= 15);
        }
    } else if depth < 15 {
        let next_width = model::capacity((31 - depth) as nat);
        assert(width == 2 * next_width);
        assert((start + assigned) * width == (2 * (start + assigned)) * next_width)
            by (nonlinear_arith) requires width == 2 * next_width;
        complete_bucket_coverage(counts, depth + 1, index);
    } else {
        facts::code_space_partition(counts, 15);
        facts::capacity_product(15, 17);
        assert(model::capacity(32) == 4294967296) by (compute);
        assert(end == 4294967296);
    }
}

pub proof fn complete_buckets_cover(counts: Seq<u16>, index: int)
    requires counts.len() == 16, model::slots(counts, 15) == 0,
        0 <= index < 4294967296,
    ensures exists|level: nat| 1 <= level <= 15
        && #[trigger] model::first_code(counts, level) * model::capacity((32 - level) as nat) <= index
        < (model::first_code(counts, level) + counts[level as int] as nat)
            * model::capacity((32 - level) as nat),
{
    assert(model::first_code(counts, 1) == 0);
    complete_bucket_coverage(counts, 1, index);
}

pub proof fn complete_canonical_intervals_cover(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, index: int)
    requires model::valid_histogram(lengths, counts),
        model::bucket_ordered(lengths, counts, work),
        model::slots(counts, 15) == 0, 0 <= index < 4294967296,
    ensures exists|symbol: int| 0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15
        && #[trigger] model::canonical_code(lengths, symbol)
            * model::capacity((32 - lengths[symbol]) as nat) <= index
        < (model::canonical_code(lengths, symbol) + 1)
            * model::capacity((32 - lengths[symbol]) as nat),
{
    complete_buckets_cover(counts, index);
    let level = choose|level: nat| 1 <= level <= 15
        && #[trigger] model::first_code(counts, level) * model::capacity((32 - level) as nat) <= index
        < (model::first_code(counts, level) + counts[level as int] as nat)
            * model::capacity((32 - level) as nat);
    let first = model::first_code(counts, level);
    let assigned = counts[level as int] as nat;
    let width = model::capacity((32 - level) as nat);
    let offset = index - first * width;
    facts::capacity_positive((32 - level) as nat);
    let ordinal = offset / width;
    let remainder = offset % width;
    lemma_fundamental_div_mod(offset, width);
    lemma_mod_bound(offset, width);
    assert(0 <= offset < assigned * width) by (nonlinear_arith)
        requires offset == index - first * width,
            first * width <= index < (first + assigned) * width;
    assert(offset == ordinal * width + remainder) by (nonlinear_arith)
        requires offset == width * ordinal + remainder;
    assert(0 <= ordinal < assigned) by (nonlinear_arith)
        requires width > 0, 0 <= offset < assigned * width,
            offset == ordinal * width + remainder, 0 <= remainder < width;
    assert(model::bucket_entry(lengths, counts, work, level as int, ordinal));
    let symbol = work[model::before(counts, level) as int + ordinal] as int;
    facts::first_code_from_histogram(lengths, counts, level);
    assert(model::canonical_code(lengths, symbol) == first + ordinal);
    assert((first + ordinal) * width <= index < (first + ordinal + 1) * width)
        by (nonlinear_arith) requires index - first * width == ordinal * width + remainder,
            0 <= remainder < width;
    assert(exists|candidate: int| 0 <= candidate < lengths.len()
        && 1 <= lengths[candidate] <= 15
        && #[trigger] model::canonical_code(lengths, candidate)
            * model::capacity((32 - lengths[candidate]) as nat) <= index
        < (model::canonical_code(lengths, candidate) + 1)
            * model::capacity((32 - lengths[candidate]) as nat)) by {
        assert(0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15);
    }
}

pub proof fn canonical_intervals_partition(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, index: int)
    requires model::valid_histogram(lengths, counts),
        model::bucket_ordered(lengths, counts, work),
        model::slots(counts, 15) == 0, 0 <= index < 4294967296,
    ensures exists|symbol: int| #[trigger] model::canonical_interval_contains(lengths, symbol, index)
        && (forall|other: int| #[trigger] model::canonical_interval_contains(lengths, other, index)
            ==> other == symbol),
{
    complete_canonical_intervals_cover(lengths, counts, work, index);
    let selected = choose|symbol: int| 0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15
        && #[trigger] model::canonical_code(lengths, symbol)
            * model::capacity((32 - lengths[symbol]) as nat) <= index
        < (model::canonical_code(lengths, symbol) + 1)
            * model::capacity((32 - lengths[symbol]) as nat);
    assert(model::canonical_interval_contains(lengths, selected, index));
    assert forall|other: int| #[trigger] model::canonical_interval_contains(lengths, other, index)
        implies other == selected by {
        if other != selected {
            canonical_intervals_disjoint(lengths, counts, selected, other);
        }
    }
    assert(exists|symbol: int| #[trigger] model::canonical_interval_contains(lengths, symbol, index)
        && (forall|other: int| #[trigger] model::canonical_interval_contains(lengths, other, index)
            ==> other == symbol)) by {
        assert(model::canonical_interval_contains(lengths, selected, index));
    }
}

}
