use crate::constructor_cost_specs as source_cost;
use crate::constructor_pages_specs as ownership;
use crate::histogram_cost_specs::{
    bucket, charge, first_group, path, root_key, source_length, sum,
};
use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) proof fn bucket_unique(counts: Seq<u16>, position: nat, first: nat, second: nat)
    requires bucket(counts, position, first), bucket(counts, position, second),
    ensures first == second,
{
    if first < second {
        facts::before_monotone(counts, first + 1, second);
    } else if second < first {
        facts::before_monotone(counts, second + 1, first);
    }
}

pub(crate) proof fn width_search(counts: Seq<u16>, start: nat, root: nat,
    max: nat, depth: nat) -> (width: nat)
    requires counts.len() == 16, 1 <= start <= depth, depth + root <= max <= 15,
        h::lookahead_space(counts, start, root, depth) > 0,
        forall|earlier: nat| start <= earlier < depth ==>
            #[trigger] h::lookahead_space(counts, start, root, earlier)
                - counts[(earlier + root) as int] > 0,
    ensures h::chosen_width(counts, start, root, max, width),
    decreases max - root - depth,
{
    if depth + root == max
        || h::lookahead_space(counts, start, root, depth) - counts[(depth + root) as int] <= 0 {
        depth
    } else {
        assert(h::lookahead_space(counts, start, root, depth + 1)
            == 2 * (h::lookahead_space(counts, start, root, depth) - counts[(depth + root) as int]));
        assert forall|earlier: nat| start <= earlier < depth + 1 implies
            #[trigger] h::lookahead_space(counts, start, root, earlier)
                - counts[(earlier + root) as int] > 0 by {
            if earlier == depth {} else { assert(earlier < depth); }
        }
        width_search(counts, start, root, max, depth + 1)
    }
}

pub(crate) proof fn normalized_width_exists(counts: Seq<u16>, position: nat,
    length: nat, root: nat, max: nat)
    requires counts.len() == 16, 1 <= root < length <= max <= 15,
    ensures ownership::opening_width_candidate(counts, position, length, root, max,
        ownership::opening_width(counts, position, length, root, max)),
{
    let remaining = ownership::opening_population(counts, position);
    let start = (length - root) as nat;
    facts::capacity_positive(start);
    let width = width_search(remaining, start, root, max, start);
    assert(ownership::opening_width_candidate(counts, position, length, root, max, width));
    assert(exists|candidate: nat| #[trigger] ownership::opening_width_candidate(
        counts, position, length, root, max, candidate));
}

pub(crate) proof fn source_length_join(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        position < h::before(counts, 16),
    ensures position < work.len(), work[position as int] < lengths.len(),
        1 <= source_length(counts, position) <= 15,
        bucket(counts, position, source_length(counts, position)),
        source_length(counts, position) == lengths[work[position as int] as int],
        h::canonical_code(lengths, work[position as int] as int)
            * h::capacity((32 - lengths[work[position as int] as int]) as nat)
            == h::normalized_cursor(counts, source_length(counts, position), position),
{
    let level = facts::ordered_symbol_at(lengths, counts, work, position as int);
    assert(bucket(counts, position, level));
    assert(exists|candidate: nat| #[trigger] bucket(counts, position, candidate));
    assert(bucket(counts, position, source_length(counts, position)));
    bucket_unique(counts, position, level, source_length(counts, position));
    facts::first_code_from_histogram(lengths, counts, level);
}

pub(crate) proof fn root_key_join(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, first: nat, second: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), first < h::before(counts, 16),
        second < h::before(counts, 16),
        1 <= root < source_length(counts, first), root < source_length(counts, second),
    ensures ((h::canonical_prefix(lengths, work[first as int] as int) as int) % h::capacity(root)
        == (h::canonical_prefix(lengths, work[second as int] as int) as int) % h::capacity(root))
        <==> (root_key(counts, root, first) == root_key(counts, root, second)),
{
    source_length_join(lengths, counts, work, first);
    source_length_join(lengths, counts, work, second);
    crate::subtable_coverage_proofs::wire_root_equivalence(lengths, counts,
        work[first as int] as int, work[second as int] as int, root);
}

pub(crate) proof fn first_group_join(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), 1 <= root <= max <= 15,
        position < h::before(counts, 16),
    ensures source_cost::first_source(lengths, counts, work, root, max, position)
        <==> first_group(counts, root, max, position),
{
    source_length_join(lengths, counts, work, position);
    let opening = source_cost::source_at(lengths, counts, work, position);
    let key = (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root);
    if root < source_length(counts, position) <= max {
        assert forall|earlier: nat| earlier < position implies
            #[trigger] source_length(counts, earlier) == lengths[work[earlier as int] as int] by {
            source_length_join(lengths, counts, work, earlier);
        }
        if source_cost::first_source(lengths, counts, work, root, max, position) {
            assert forall|earlier: nat| earlier < position
                && root < source_length(counts, earlier) <= 15 implies
                #[trigger] root_key(counts, root, earlier) != root_key(counts, root, position) by {
                source_length_join(lengths, counts, work, earlier);
                root_key_join(lengths, counts, work, root, earlier, position);
                assert((h::canonical_prefix(lengths, work[earlier as int] as int) as int)
                    % h::capacity(root) != key);
            }
        } else if first_group(counts, root, max, position) {
            assert forall|earlier: int| 0 <= earlier < opening.position
                && work[earlier] < lengths.len() && root < lengths[work[earlier] as int] <= 15 implies
                (#[trigger] h::canonical_prefix(lengths, work[earlier] as int) as int)
                    % h::capacity(root) != key by {
                source_length_join(lengths, counts, work, earlier as nat);
                assert(root_key(counts, root, earlier as nat) != root_key(counts, root, position));
                root_key_join(lengths, counts, work, root, earlier as nat, position);
            }
            assert(ownership::first_opening(lengths, work, root, key, opening));
            assert(source_cost::first_source(lengths, counts, work, root, max, position));
        }
    }
}

pub(crate) proof fn charge_join(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), 1 <= root <= max <= 15,
        position < h::before(counts, 16),
    ensures source_cost::source_cost(lengths, counts, work, root, max, position)
        == charge(counts, root, max, position),
{
    source_length_join(lengths, counts, work, position);
    first_group_join(lengths, counts, work, root, max, position);
}

pub(crate) proof fn sum_join(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, processed: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::valid_prefix(counts, 15), 1 <= root <= max <= 15,
        processed <= h::before(counts, 16),
    ensures source_cost::prefix_cost(lengths, counts, work, root, max, processed)
        == sum(counts, root, max, processed),
    decreases processed,
{
    if processed > 0 {
        let previous = (processed - 1) as nat;
        charge_join(lengths, counts, work, root, max, previous);
        sum_join(lengths, counts, work, root, max, previous);
    }
}

pub(crate) proof fn sum_zero_at_max(counts: Seq<u16>, root: nat, processed: nat)
    ensures sum(counts, root, root, processed) == 0,
    decreases processed,
{
    if processed > 0 {
        sum_zero_at_max(counts, root, (processed - 1) as nat);
    }
}

pub(crate) proof fn root_key_monotone(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, first: nat, second: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        first < second < h::before(counts, 16),
        1 <= root < source_length(counts, first), root < source_length(counts, second),
    ensures root_key(counts, root, first) <= root_key(counts, root, second),
{
    source_length_join(lengths, counts, work, first);
    source_length_join(lengths, counts, work, second);
    crate::constructor_pages_proofs::ordered_positions(lengths, counts, work, first, second);
    crate::subtable_coverage_proofs::canonical_root_order(lengths, counts,
        work[first as int] as int, work[second as int] as int, root);
}

pub(crate) proof fn adjacent_group(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, position: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        1 <= root < source_length(counts, position) <= max <= 15,
        position < h::before(counts, 16),
    ensures first_group(counts, root, max, position) <==>
        (position == h::before(counts, root + 1)
            || (position > h::before(counts, root + 1)
                && root_key(counts, root, (position - 1) as nat) != root_key(counts, root, position))),
{
    source_length_join(lengths, counts, work, position);
    let length = source_length(counts, position);
    assert(bucket(counts, position, length));
    facts::before_monotone(counts, root + 1, length);
    assert(h::before(counts, root + 1) <= position);
    if position == h::before(counts, root + 1) {
        assert forall|earlier: nat| earlier < position && root < source_length(counts, earlier) <= 15
            implies #[trigger] root_key(counts, root, earlier) != root_key(counts, root, position) by {
            source_length_join(lengths, counts, work, earlier);
            assert(bucket(counts, earlier, source_length(counts, earlier)));
            facts::before_monotone(counts, root + 1, source_length(counts, earlier));
            assert(false);
        }
    } else {
        let previous = (position - 1) as nat;
        source_length_join(lengths, counts, work, previous);
        let previous_length = source_length(counts, previous);
        assert(bucket(counts, previous, previous_length));
        if previous_length <= root {
            facts::before_monotone(counts, previous_length + 1, root + 1);
            assert(false);
        }
        root_key_monotone(lengths, counts, work, root, previous, position);
        if root_key(counts, root, previous) != root_key(counts, root, position) {
            assert forall|earlier: nat| earlier < position && root < source_length(counts, earlier) <= 15
                implies #[trigger] root_key(counts, root, earlier) != root_key(counts, root, position) by {
                if earlier < previous {
                    root_key_monotone(lengths, counts, work, root, earlier, previous);
                }
            }
        } else if first_group(counts, root, max, position) {
            assert(root_key(counts, root, previous) != root_key(counts, root, position));
            assert(false);
        }
    }
}

pub(crate) proof fn histogram_budget_excludes_refusal(alphabet: h::Alphabet,
    lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>, root: nat, max: nat,
    original: Seq<crate::Code>, codes: Seq<crate::Code>,
    witness: crate::constructor_table_specs::Refusal, limit: nat)
    requires crate::constructor_table_specs::refused(alphabet, lengths, counts, work,
            root, max, original, codes, witness),
        h::bucket_ordered(lengths, counts, work),
        crate::table_preparation_specs::root_capacity_allowed(alphabet, limit),
        h::capacity(root) + sum(counts, root, max, h::before(counts, 16)) <= limit,
    ensures false,
{
    crate::constructor_cost_proofs::refusal_cost(alphabet, lengths, counts, work,
        root, max, original, codes, witness);
    sum_join(lengths, counts, work, root, max, h::before(counts, 16));
    crate::constructor_cost_proofs::prefix_monotone(lengths, counts, work, root, max,
        witness.processed + 1, h::before(counts, 16));
    facts::capacity_positive(root);
    assert(witness.used + h::capacity(witness.width) <= limit);
    reveal(crate::table_preparation_specs::root_capacity_allowed);
    assert(crate::table_preparation_specs::root_capacity_allowed(alphabet,
        (witness.used + h::capacity(witness.width)) as nat));
}

pub(crate) proof fn no_capacity_error(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<crate::Code>, codes: Seq<crate::Code>,
    original_work: Seq<u16>, work: Seq<u16>, outcome: crate::huffman::InflateTable,
    root: nat, max: nat, limit: nat)
    requires crate::constructor_table_specs::result(alphabet, lengths, requested,
            original, codes, original_work, work, outcome),
        root == crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
        max == h::maximum_length(lengths),
        crate::table_preparation_specs::root_capacity_allowed(alphabet, limit),
        h::capacity(root) + sum(h::histogram(lengths), root, max,
            h::before(h::histogram(lengths), 16)) <= limit,
    ensures !matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough),
{
    facts::capacity_positive(root);
    reveal(crate::constructor_table_specs::result);
    reveal(crate::table_preparation_specs::root_capacity_allowed);
    assert(crate::table_preparation_specs::root_capacity_allowed(alphabet, h::capacity(root) as nat));
    if matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough) {
        let witness = choose|witness: crate::constructor_table_specs::Refusal|
            #[trigger] crate::constructor_table_specs::refused(alphabet, lengths,
                h::histogram(lengths), work, root, max, original, codes, witness);
        histogram_budget_excludes_refusal(alphabet, lengths, h::histogram(lengths),
            work, root, max, original, codes, witness, limit);
    }
}

pub(crate) proof fn independent_histogram_cost()
    ensures sum(crate::subtable_coverage_proofs::fixture_counts(), 2, 3, 6) == 4,
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let counts = crate::subtable_coverage_proofs::fixture_counts();
    let work = seq![0u16, 1, 2, 3, 4, 5];
    crate::constructor_pages_proofs::independent_two_pages();
    crate::constructor_cost_proofs::independent_two_page_cost();
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
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 3))
        by (compute);
    assert forall|level: int, ordinal: int| 1 <= level <= 15 && 0 <= ordinal < counts[level]
        implies #[trigger] h::bucket_entry(lengths, counts, work, level, ordinal) by {
        assert(level == 2 || level == 3);
    }
    assert(h::before(crate::subtable_coverage_proofs::fixture_counts(), 16) == 6) by (compute);
    sum_join(lengths, counts, work, 2, 3, 6);
}

pub(crate) proof fn completion_needs_leaves(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, depth <= 15,
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
    ensures 0 <= h::slots(counts, depth)
        <= h::before(counts, 16) - h::before(counts, depth + 1),
    decreases 15 - depth,
{
    if depth < 15 {
        completion_needs_leaves(counts, depth + 1);
        assert(h::before(counts, depth + 2)
            == h::before(counts, depth + 1) + counts[(depth + 1) as int] as nat);
        assert(h::slots(counts, depth + 1)
            == 2 * h::slots(counts, depth) - counts[(depth + 1) as int] as int);
    }
}

pub(crate) proof fn frontier(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
    ensures 0 <= counts[depth as int] <= 2 * h::slots(counts, (depth - 1) as nat)
        <= h::before(counts, 16) - h::before(counts, depth),
{
    completion_needs_leaves(counts, depth);
    assert(h::slots(counts, depth)
        == 2 * h::slots(counts, (depth - 1) as nat) - counts[depth as int] as int);
    assert(h::before(counts, depth + 1) == h::before(counts, depth) + counts[depth as int] as nat);
}

pub(crate) proof fn complete_path(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
        h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
    ensures path(counts, depth, (2 * h::slots(counts, (depth - 1) as nat)) as nat,
        (h::before(counts, 16) - h::before(counts, depth)) as nat),
    decreases 15 - depth,
{
    frontier(counts, depth);
    if depth < 15 {
        complete_path(counts, depth + 1);
        assert(h::slots(counts, depth)
            == 2 * h::slots(counts, (depth - 1) as nat) - counts[depth as int] as int);
        assert(h::before(counts, depth + 1)
            == h::before(counts, depth) + counts[depth as int] as nat);
    }
}

pub(crate) proof fn slots_from_frontiers(counts: Seq<u16>, frontiers: Seq<int>, depth: nat)
    requires counts.len() == 16, frontiers.len() == 16, depth <= 15,
        frontiers[0] == 1,
        forall|level: int| 1 <= level <= 15 ==>
            #[trigger] frontiers[level] == 2 * frontiers[level - 1] - counts[level] as int,
    ensures h::slots(counts, depth) == frontiers[depth as int],
    decreases depth,
{
    if depth > 0 {
        slots_from_frontiers(counts, frontiers, (depth - 1) as nat);
    }
}

pub(crate) proof fn path_from_frontiers(counts: Seq<u16>, frontiers: Seq<int>, remaining: nat)
    requires counts.len() == 16, frontiers.len() == 16,
        frontiers[0] == 1, frontiers[15] == 0,
        forall|level: int| 0 <= level <= 15 ==> #[trigger] frontiers[level] >= 0,
        forall|level: int| 1 <= level <= 15 ==>
            #[trigger] frontiers[level] == 2 * frontiers[level - 1] - counts[level] as int,
        h::before(counts, 16) == remaining,
    ensures path(counts, 1, 2, remaining),
{
    assert forall|depth: nat| depth <= 15 implies #[trigger] h::slots(counts, depth) >= 0 by {
        slots_from_frontiers(counts, frontiers, depth);
    }
    slots_from_frontiers(counts, frontiers, 15);
    complete_path(counts, 1);
}

pub(crate) proof fn complete_histogram_path(lengths: Seq<u16>, counts: Seq<u16>, bound: nat)
    requires h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::slots(counts, 15) == 0, lengths.len() <= bound,
    ensures 2 <= h::before(counts, 16) <= bound,
        path(counts, 1, 2, h::before(counts, 16)),
{
    facts::histogram_offsets(lengths, counts, 16);
    complete_path(counts, 1);
    frontier(counts, 1);
    assert(h::slots(counts, 0) == 1 && h::before(counts, 1) == 0);
}

pub(crate) proof fn path_suffix_sound(counts: Seq<u16>, depth: nat,
    available: nat, remaining: nat)
    requires path(counts, depth, available, remaining),
        h::valid_prefix(counts, (depth - 1) as nat),
        available == 2 * h::slots(counts, (depth - 1) as nat),
    ensures h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::before(counts, depth) + remaining == h::before(counts, 16),
    decreases 15 - depth,
{
    assert(h::slots(counts, depth) == available - counts[depth as int] as int);
    assert(h::slots(counts, depth) >= 0);
    assert forall|level: nat| level <= depth implies h::slots(counts, level) >= 0 by {
        if level != depth { assert(level <= depth - 1); }
    }
    assert(h::valid_prefix(counts, depth));
    if depth < 15 {
        let next_available = 2 * (available - counts[depth as int]) as nat;
        let next_remaining = (remaining - counts[depth as int]) as nat;
        path_suffix_sound(counts, depth + 1, next_available, next_remaining);
    }
    assert(h::before(counts, depth + 1) == h::before(counts, depth) + counts[depth as int] as nat);
}

pub(crate) proof fn path_sound(counts: Seq<u16>, remaining: nat)
    requires path(counts, 1, 2, remaining),
    ensures h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::before(counts, 16) == remaining,
{
    assert(h::slots(counts, 0) == 1);
    assert(h::valid_prefix(counts, 0));
    path_suffix_sound(counts, 1, 2, remaining);
}

pub(crate) proof fn path_leaf_capacity(counts: Seq<u16>, depth: nat,
    available: nat, remaining: nat)
    requires path(counts, depth, available, remaining),
    ensures remaining <= available * h::capacity((15 - depth) as nat),
    decreases 15 - depth,
{
    facts::capacity_positive((15 - depth) as nat);
    if depth < 15 {
        let next_available = 2 * (available - counts[depth as int]) as nat;
        let next_remaining = (remaining - counts[depth as int]) as nat;
        path_leaf_capacity(counts, depth + 1, next_available, next_remaining);
        let capacity = h::capacity((14 - depth) as nat);
        facts::capacity_positive((14 - depth) as nat);
        assert(h::capacity((15 - depth) as nat) == 2 * capacity);
        assert(remaining <= available * (2 * capacity)) by (nonlinear_arith)
            requires next_remaining <= next_available * capacity,
                next_remaining == remaining - counts[depth as int],
                next_available == 2 * (available - counts[depth as int]),
                0 <= counts[depth as int] <= available <= remaining, capacity >= 1;
    } else {
        assert(h::capacity(0) == 1 && available == remaining);
    }
}

pub(crate) proof fn minimum_leaf_budget(lengths: Seq<u16>, counts: Seq<u16>)
    requires h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::slots(counts, 15) == 0, h::maximum_length(lengths) > 0,
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
    ensures h::capacity(h::minimum_length(lengths) as nat) <= lengths.len(),
{
    facts::metadata_bounds(lengths);
    facts::length_population_bounds(lengths);
    let minimum = h::minimum_length(lengths) as nat;
    assert forall|level: int| 1 <= level < minimum implies counts[level] == 0 by {
        assert(h::occurrences(lengths, level as u16) == 0);
    }
    facts::first_code_empty_range(counts, minimum);
    if minimum > 1 {
        facts::code_space_partition(counts, (minimum - 1) as nat);
        assert(h::first_code(counts, minimum)
            == 2 * (h::first_code(counts, (minimum - 1) as nat) + counts[minimum as int - 1] as nat));
        assert(h::slots(counts, (minimum - 1) as nat) == h::capacity((minimum - 1) as nat));
    } else {
        assert(h::slots(counts, 0) == 1 && h::capacity(0) == 1);
    }
    frontier(counts, minimum);
    facts::histogram_offsets(lengths, counts, 16);
    assert(h::capacity(minimum) == 2 * h::capacity((minimum - 1) as nat));
}

pub(crate) proof fn root_not_raised(lengths: Seq<u16>, counts: Seq<u16>,
    requested: nat, bound: nat)
    requires h::valid_histogram(lengths, counts), h::accepted_lengths(lengths, false),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        1 <= requested <= 15, lengths.len() <= bound < h::capacity(requested),
    ensures crate::table_preparation_specs::clamped_root(requested,
        h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat)
        == if h::maximum_length(lengths) <= requested { h::maximum_length(lengths) as nat }
            else { requested },
{
    facts::metadata_bounds(lengths);
    let minimum = h::minimum_length(lengths) as nat;
    assert(counts =~= h::histogram(lengths));
    if h::maximum_length(lengths) > 1 {
        minimum_leaf_budget(lengths, counts);
        if minimum > requested {
            facts::capacity_monotone(requested, minimum);
            assert(false);
        }
    }
    assert(minimum <= requested);
    reveal(crate::table_preparation_specs::clamped_root);
}

pub(crate) proof fn independent_complete_path()
    ensures path(crate::subtable_coverage_proofs::fixture_counts(), 1, 2, 6),
        !path(crate::subtable_coverage_proofs::fixture_counts(), 1, 2, 5),
        !path(crate::subtable_coverage_proofs::fixture_counts(), 1, 2, 7),
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let counts = crate::subtable_coverage_proofs::fixture_counts();
    crate::page_source_proofs::independent_opening();
    assert(h::slots(counts, 0) == 1);
    assert(h::slots(counts, 1) == 2);
    assert(h::slots(counts, 2) == 2);
    assert(h::slots(counts, 3) == 0);
    facts::slots_empty_tail(counts, 3, 15);
    complete_histogram_path(lengths, counts, 6);
    assert(h::before(crate::subtable_coverage_proofs::fixture_counts(), 16) == 6) by (compute);
    if path(counts, 1, 2, 5) {
        path_sound(counts, 5);
        assert(false);
    }
    if path(counts, 1, 2, 7) {
        path_sound(counts, 7);
        assert(false);
    }
}

}
