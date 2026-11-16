use crate::capacity_bound_specs::*;
use crate::closing_cost_proofs as facts;
use crate::closing_cost_specs as cost;
use crate::huffman_proofs as hp;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) proof fn slack_bounds(available: nat, size: int)
    requires size > 0,
    ensures 0 <= slack(available, size) < size,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(available + size - 1, size);
    vstd::arithmetic::div_mod::lemma_mod_bound(available + size - 1, size);
    assert(slack(available, size) == size - 1 - (available + size - 1) % size)
        by (nonlinear_arith)
        requires available + size - 1 == size * rounded(available, size)
                + (available + size - 1) % size,
            slack(available, size) == rounded(available, size) * size - available;
}

pub(crate) proof fn slack_double(available: nat, size: int)
    requires size > 0,
    ensures rounded(2 * available, 2 * size) == rounded(available, size),
        slack(2 * available, 2 * size) == 2 * slack(available, size),
{
    slack_bounds(available, size);
    let value = rounded(available, size);
    assert(value * (2 * size) <= 2 * available + 2 * size - 1 < (value + 1) * (2 * size))
        by (nonlinear_arith)
        requires 0 <= value * size - available < size, size > 0;
    facts::quotient_from_interval(2 * available + 2 * size - 1, 2 * size, value);
    assert(slack(2 * available, 2 * size) == 2 * slack(available, size)) by (nonlinear_arith)
        requires rounded(2 * available, 2 * size) == value,
            slack(2 * available, 2 * size) == rounded(2 * available, 2 * size) * (2 * size) - 2 * available,
            slack(available, size) == value * size - available;
}

pub(crate) proof fn capacity_linear_gap(low: nat, high: nat)
    requires low <= high,
    ensures h::capacity(high) >= h::capacity(low) + high - low,
    decreases high - low,
{
    if low < high {
        capacity_linear_gap(low, (high - 1) as nat);
        hp::capacity_positive((high - 1) as nat);
    }
}

pub(crate) proof fn upper_nonnegative(root: nat, depth: nat, available: nat, remaining: nat)
    requires 1 <= root < depth <= 15,
    ensures 0 <= remaining + slack(available, h::capacity((depth - root) as nat))
        + h::capacity((15 - root) as nat) - h::capacity((depth - root) as nat) - (15 - depth),
{
    hp::capacity_positive((depth - root) as nat);
    slack_bounds(available, h::capacity((depth - root) as nat));
    capacity_linear_gap((depth - root) as nat, (15 - root) as nat);
}

pub(crate) proof fn closing_slack(root: nat, depth: nat, available: nat, leaves: nat)
    requires 1 <= root < depth <= 15, leaves <= available,
    ensures cost::closing(root, depth, available, leaves)
        == leaves + slack(available, h::capacity((depth - root) as nat))
            - slack((available - leaves) as nat, h::capacity((depth - root) as nat)),
{
    let size = h::capacity((depth - root) as nat);
    let before = rounded(available, size);
    let after = rounded((available - leaves) as nat, size);
    hp::capacity_positive((depth - root) as nat);
    slack_bounds(available, size);
    slack_bounds((available - leaves) as nat, size);
    crate::subtable_coverage_proofs::ordered_quotients(
        available - leaves + size - 1, available + size - 1, size);
    assert(before * size <= available + size - 1 < (before + 1) * size)
        by (nonlinear_arith)
        requires 0 <= before * size - available < size, size > 0;
    assert(after * size <= available - leaves + size - 1 < (after + 1) * size)
        by (nonlinear_arith)
        requires 0 <= after * size - (available - leaves) < size, size > 0;
    facts::closing_from_quotients(root, depth, available, leaves, size, before, after);
    assert((before - after) * size == leaves + slack(available, size)
        - slack((available - leaves) as nat, size)) by (nonlinear_arith)
        requires slack(available, size) == before * size - available,
            slack((available - leaves) as nat, size) == after * size - (available - leaves);
}

pub(crate) proof fn analytic_certificate(root: nat, bound: nat)
    requires 1 <= root <= 14,
    ensures cost::certificate(|depth: nat, available: nat, remaining: nat|
        upper(root, depth, available, remaining), root, bound),
{
    let lookup = |depth: nat, available: nat, remaining: nat| upper(root, depth, available, remaining);
    assert forall|depth: nat, available: nat, remaining: nat|
        cost::state(bound, depth, available, remaining) implies
        match #[trigger] lookup(depth, available, remaining) {
            None => true,
            Some(value) => if depth == 15 {
                cost::closing(root, depth, available, available) <= value
            } else {
                forall|leaves: nat| #[trigger] cost::edge(bound, depth, available, remaining, leaves)
                    ==> match lookup(depth + 1, 2 * (available - leaves) as nat,
                        (remaining - leaves) as nat) {
                        Some(next) => cost::closing(root, depth, available, leaves) + next <= value,
                        None => false,
                    }
            },
        } by {
        if lookup(depth, available, remaining) != None {
            let size = h::capacity((depth - root) as nat);
            hp::capacity_positive((depth - root) as nat);
            upper_nonnegative(root, depth, available, remaining);
            if depth == 15 {
                assert(h::capacity(0) == 1);
                assert(available == remaining);
                closing_slack(root, depth, available, available);
                slack_bounds(0, size);
            } else {
                assert forall|leaves: nat|
                    #[trigger] cost::edge(bound, depth, available, remaining, leaves)
                    implies match lookup(depth + 1, 2 * (available - leaves) as nat,
                        (remaining - leaves) as nat) {
                        Some(next) => cost::closing(root, depth, available, leaves) + next
                            <= lookup(depth, available, remaining).unwrap(),
                        None => false,
                    } by {
                    let rest = (available - leaves) as nat;
                    upper_nonnegative(root, depth + 1, 2 * rest, (remaining - leaves) as nat);
                    closing_slack(root, depth, available, leaves);
                    slack_double(rest, size);
                    slack_bounds(rest, size);
                    assert(h::capacity((depth + 1 - root) as nat) == 2 * size);
                }
            }
        }
    }
}

pub(crate) proof fn tail_bound(counts: Seq<u16>, root: nat, available: nat, remaining: nat)
    requires 1 <= root <= 14, available % 2 == 0,
        crate::histogram_cost_specs::path(counts, root + 1, available, remaining),
    ensures cost::forest(counts, root, root + 1, available)
        <= remaining + h::capacity((15 - root) as nat) - (15 - root) - 1,
{
    analytic_certificate(root, remaining);
    let lookup = |depth: nat, slots: nat, leaves: nat| upper(root, depth, slots, leaves);
    assert(lookup(root + 1, available, remaining) != None);
    facts::bounds_path(counts, root, remaining, lookup, root + 1, available, remaining);
    assert(h::capacity(1) == 2) by (compute);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(available as int, 2);
    facts::quotient_from_interval(available as int + 1, 2, (available as int) / 2);
    assert(slack(available, 2) == 0) by (nonlinear_arith)
        requires available == 2 * ((available as int) / 2),
            rounded(available, 2) == (available as int) / 2,
            slack(available, 2) == rounded(available, 2) * 2 - available;
    upper_nonnegative(root, root + 1, available, remaining);
}

pub(crate) proof fn capacity_remove(depth: nat, removed: nat)
    requires removed <= depth,
    ensures h::capacity(depth) - removed >= h::capacity((depth - removed) as nat),
    decreases removed,
{
    if removed > 0 {
        capacity_remove(depth, (removed - 1) as nat);
        hp::capacity_positive((depth - removed) as nat);
        assert(h::capacity((depth + 1 - removed) as nat)
            == 2 * h::capacity((depth - removed) as nat));
    }
}

pub(crate) proof fn active_frontier(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, depth <= 15, h::valid_prefix(counts, depth),
        h::slots(counts, depth) > 0, h::before(counts, depth + 1) <= depth,
    ensures h::capacity((depth - h::before(counts, depth + 1)) as nat) <= h::slots(counts, depth),
    decreases depth,
{
    if depth > 0 && h::before(counts, depth + 1) < depth {
        assert(h::slots(counts, depth) == 2 * h::slots(counts, (depth - 1) as nat)
            - counts[depth as int] as int);
        assert(h::slots(counts, (depth - 1) as nat) > 0);
        let before = h::before(counts, depth);
        let assigned = counts[depth as int] as nat;
        assert(h::before(counts, depth + 1) == before + assigned);
        active_frontier(counts, (depth - 1) as nat);
        let exponent = (depth - before) as nat;
        capacity_remove(exponent, assigned);
        assert(h::capacity(exponent) == 2 * h::capacity((exponent - 1) as nat));
    } else {
        if depth == 0 {
            assert(h::slots(counts, 0) == 1 && h::before(counts, 1) == 0);
        }
        assert(h::before(counts, depth + 1) == depth);
        assert(h::capacity(0) == 1);
    }
}

pub(crate) proof fn minimum_short_leaves(counts: Seq<u16>, root: nat, bound: nat, minimum: nat)
    requires counts.len() == 16, h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        h::before(counts, 16) <= bound, 1 <= root <= 14,
        h::slots(counts, root) > 0, 1 <= minimum <= root + 1,
        bound < 2 * h::capacity((root + 1 - minimum) as nat),
    ensures h::before(counts, root + 1) >= minimum,
{
    let used = h::before(counts, root + 1);
    if used < minimum {
        active_frontier(counts, root);
        hp::capacity_monotone((root + 1 - minimum) as nat, (root - used) as nat);
        crate::histogram_cost_proofs::frontier(counts, root + 1);
        assert(false);
    }
}

pub(crate) proof fn closing_even(root: nat, depth: nat, available: nat, leaves: nat)
    requires 1 <= root <= 15, 1 <= depth <= 15, leaves <= available,
    ensures (cost::closing(root, depth, available, leaves) as int) % 2 == 0,
{
    if root < depth {
        let size = h::capacity((depth - root) as nat);
        let before = rounded(available, size);
        let after = rounded((available - leaves) as nat, size);
        closing_slack(root, depth, available, leaves);
        hp::capacity_multiple(1, (depth - root) as nat);
        assert(h::capacity(1) == 2) by (compute);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(size, 2);
        assert(cost::closing(root, depth, available, leaves) == (before - after) * size)
            by (nonlinear_arith)
            requires cost::closing(root, depth, available, leaves)
                    == leaves + slack(available, size) - slack((available - leaves) as nat, size),
                slack(available, size) == before * size - available,
                slack((available - leaves) as nat, size) == after * size - (available - leaves);
        assert((before - after) * size == ((before - after) * (size / 2)) * 2)
            by (nonlinear_arith) requires size == 2 * (size / 2);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic((before - after) * (size / 2), 2);
    }
}

pub(crate) proof fn forest_even(counts: Seq<u16>, root: nat, depth: nat,
    available: nat, remaining: nat)
    requires 1 <= root <= 15, crate::histogram_cost_specs::path(counts, depth, available, remaining),
    ensures (cost::forest(counts, root, depth, available) as int) % 2 == 0,
    decreases 15 - depth,
{
    let leaves = counts[depth as int] as nat;
    closing_even(root, depth, available, leaves);
    if depth < 15 {
        let next = 2 * (available - leaves) as nat;
        forest_even(counts, root, depth + 1, next, (remaining - leaves) as nat);
        vstd::arithmetic::div_mod::lemma_mod_adds(
            cost::closing(root, depth, available, leaves) as int,
            cost::forest(counts, root, depth + 1, next) as int, 2);
    }
}

pub(crate) proof fn skip_root(counts: Seq<u16>, root: nat, depth: nat)
    requires counts.len() == 16, h::valid_prefix(counts, 15), 1 <= depth <= root <= 14,
    ensures cost::forest(counts, root, depth, (2 * h::slots(counts, (depth - 1) as nat)) as nat)
        == cost::forest(counts, root, root + 1, (2 * h::slots(counts, root)) as nat),
    decreases root - depth,
{
    let available = (2 * h::slots(counts, (depth - 1) as nat)) as nat;
    assert(h::slots(counts, depth) == 2 * h::slots(counts, (depth - 1) as nat) - counts[depth as int] as int);
    assert(2 * (available - counts[depth as int]) as nat == 2 * h::slots(counts, depth));
    if depth < root { skip_root(counts, root, depth + 1); }
}

pub(crate) proof fn concrete_histogram_bounds(counts: Seq<u16>, root: nat)
    requires counts.len() == 16, h::valid_prefix(counts, 15), h::slots(counts, 15) == 0,
        (root == 10 && h::before(counts, 16) <= 286)
            || (root == 9 && h::before(counts, 16) <= 30),
    ensures cost::forest(counts, root, 1, 2) <= if root == 10 { 308int } else { 80int },
{
    let bound = if root == 10 { 286nat } else { 30nat };
    let minimum = if root == 10 { 3nat } else { 6nat };
    let available = (2 * h::slots(counts, root)) as nat;
    let remaining = (h::before(counts, 16) - h::before(counts, root + 1)) as nat;
    hp::before_monotone(counts, root + 1, 16);
    crate::histogram_cost_proofs::complete_path(counts, root + 1);
    if h::slots(counts, root) > 0 {
        assert(h::capacity(8) == 256 && h::capacity(4) == 16) by (compute);
        minimum_short_leaves(counts, root, bound, minimum);
    } else {
        crate::histogram_cost_proofs::path_leaf_capacity(counts, root + 1, available, remaining);
        assert(remaining == 0);
    }
    assert(remaining <= bound - minimum);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(h::slots(counts, root), 2);
    assert(available % 2 == 0);
    tail_bound(counts, root, available, remaining);
    skip_root(counts, root, 1);
    assert(h::slots(counts, 0) == 1);
    forest_even(counts, root, root + 1, available, remaining);
    assert(h::capacity(5) == 32 && h::capacity(6) == 64) by (compute);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(
        cost::forest(counts, root, root + 1, available) as int, 2);
}

pub(crate) proof fn occurrences_bound(lengths: Seq<u16>, value: u16)
    ensures h::occurrences(lengths, value) <= lengths.len(),
    decreases lengths.len(),
{
    if lengths.len() > 0 { occurrences_bound(lengths.drop_last(), value); }
}

pub(crate) proof fn histogram_faithful(lengths: Seq<u16>)
    requires lengths.len() <= u16::MAX,
    ensures h::valid_histogram(lengths, h::histogram(lengths)),
{
    assert forall|level: int| 1 <= level <= 15 implies
        h::histogram(lengths)[level] == h::occurrences(lengths, level as u16) by {
        occurrences_bound(lengths, level as u16);
    }
}

pub(crate) proof fn dynamic_histogram_budget(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, requested: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::accepted_lengths(lengths, false),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        (requested == 10 && lengths.len() <= 286) || (requested == 9 && lengths.len() <= 30),
    ensures ({
        let root = crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat);
        h::capacity(root) + crate::histogram_cost_specs::sum(counts, root,
            h::maximum_length(lengths) as nat, h::before(counts, 16))
            <= if requested == 10 { 1332int } else { 592int }
    }),
{
    let bound = if requested == 10 { 286nat } else { 30nat };
    let max = h::maximum_length(lengths) as nat;
    let root = crate::table_preparation_specs::clamped_root(requested,
        h::minimum_length(lengths) as nat, max);
    assert(counts =~= h::histogram(lengths));
    hp::metadata_bounds(lengths);
    assert(h::capacity(10) == 1024 && h::capacity(9) == 512) by (compute);
    crate::histogram_cost_proofs::root_not_raised(lengths, counts, requested, bound);
    if max <= requested {
        crate::histogram_cost_proofs::sum_zero_at_max(counts, root, h::before(counts, 16));
        hp::capacity_monotone(root, requested);
    } else {
        assert(h::slots(counts, 15) == 0);
        hp::histogram_offsets(lengths, counts, 16);
        crate::group_closing_proofs::histogram_forest_bound(lengths, counts, work,
            root, max, h::before(counts, 16));
        concrete_histogram_bounds(counts, root);
    }
}

pub(crate) proof fn dynamic_no_capacity_error(alphabet: h::Alphabet,
    lengths: Seq<u16>, requested: nat, original: Seq<crate::Code>, codes: Seq<crate::Code>,
    original_work: Seq<u16>, work: Seq<u16>, outcome: crate::huffman::InflateTable)
    requires crate::constructor_table_specs::result(alphabet, lengths, requested,
            original, codes, original_work, work, outcome),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        (matches!(alphabet, h::Alphabet::LiteralLengths) && requested == 10 && lengths.len() <= 286)
            || (matches!(alphabet, h::Alphabet::Distances) && requested == 9 && lengths.len() <= 30),
    ensures !matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough),
{
    if matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough) {
        reveal(crate::constructor_table_specs::result);
        histogram_faithful(lengths);
        let counts = h::histogram(lengths);
        let root = crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat);
        let limit = if requested == 10 { 1332nat } else { 592nat };
        dynamic_histogram_budget(lengths, counts, work, requested);
        reveal(crate::table_preparation_specs::root_capacity_allowed);
        crate::histogram_cost_proofs::no_capacity_error(alphabet, lengths, requested,
            original, codes, original_work, work, outcome, root,
            h::maximum_length(lengths) as nat, limit);
    }
}

pub(crate) proof fn dynamic_candidate_bound(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, requested: nat, root: nat, max: nat, used: int, processed: nat,
    regions: Seq<Option<crate::table_pages_specs::Page>>,
    openings: Seq<Option<crate::page_source_specs::Opening>>, key: int, width: nat,
    opening: crate::page_source_specs::Opening)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::accepted_lengths(lengths, false),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        (requested == 10 && lengths.len() <= 286) || (requested == 9 && lengths.len() <= 30),
        root == crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
        max == h::maximum_length(lengths), 1 <= root <= max <= 15,
        processed < h::before(counts, 16),
        crate::constructor_pages_specs::ownership(lengths, counts, work, root, max,
            used, processed, regions, openings),
        crate::constructor_pages_specs::first_openings(lengths, work, root, openings),
        crate::constructor_table_specs::assigned(lengths, work, processed, root, regions),
        0 <= key < regions.len(), regions[key] == None, opening.position == processed,
        crate::constructor_pages_specs::first_opening(lengths, work, root, key, opening),
        crate::page_source_specs::valid_window(lengths, counts, root, max, key, width, opening),
    ensures used + h::capacity(width) <= if requested == 10 { 1332int } else { 592int },
{
    crate::constructor_cost_proofs::before_fresh(lengths, counts, work, root, max,
        used, processed, regions, openings, key, opening);
    crate::constructor_cost_proofs::certificate_from_ownership(lengths, counts, work,
        root, max, used, processed, processed, regions, openings);
    crate::constructor_cost_proofs::cells_prefix(lengths, counts, work, root, max,
        processed, regions, openings);
    crate::constructor_cost_proofs::window_cost(lengths, counts, work, root, max, key, width, opening);
    crate::constructor_cost_proofs::prefix_monotone(lengths, counts, work, root, max,
        processed + 1, h::before(counts, 16));
    crate::histogram_cost_proofs::sum_join(lengths, counts, work, root, max, h::before(counts, 16));
    dynamic_histogram_budget(lengths, counts, work, requested);
}

pub(crate) proof fn root_storage(lengths: Seq<u16>, counts: Seq<u16>, requested: nat,
    root: nat, max: nat, extent: int)
    requires h::valid_histogram(lengths, counts), h::accepted_lengths(lengths, false),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        root == crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
        max == h::maximum_length(lengths),
        crate::constructor_pages_specs::backing(root, max, extent)
            || tight_backing(lengths, requested, extent),
    ensures 1 <= root <= max <= 15, h::capacity(root) <= extent,
{
    hp::metadata_bounds(lengths);
    hp::capacity_positive(max);
    if !crate::constructor_pages_specs::backing(root, max, extent) {
        let bound = if requested == 10 { 286nat } else { 30nat };
        assert(h::capacity(10) == 1024 && h::capacity(9) == 512) by (compute);
        crate::histogram_cost_proofs::root_not_raised(lengths, counts, requested, bound);
        hp::capacity_monotone(root, requested);
    }
}

pub(crate) proof fn finite_offsets(root: nat, max: nat, used: int,
    regions: Seq<Option<crate::table_pages_specs::Page>>)
    requires crate::table_pages_specs::valid(root, max, used, regions),
    ensures used <= u16::MAX, used <= usize::MAX - 32768,
{
    hp::capacity_positive(root);
    hp::capacity_positive(max);
    crate::constructor_pages_proofs::storage_bound(root, max, used, regions,
        h::capacity(root) + h::capacity(max));
}

pub(crate) proof fn candidate_storage(lengths: Seq<u16>, counts: Seq<u16>,
    work: Seq<u16>, requested: nat, root: nat, max: nat, used: int, processed: nat,
    regions: Seq<Option<crate::table_pages_specs::Page>>,
    openings: Seq<Option<crate::page_source_specs::Opening>>, key: int, width: nat,
    opening: crate::page_source_specs::Opening, extent: int)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        h::accepted_lengths(lengths, false),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        root == crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
        max == h::maximum_length(lengths), 1 <= root <= max <= 15,
        processed < h::before(counts, 16),
        crate::constructor_pages_specs::ownership(lengths, counts, work, root, max,
            used, processed, regions, openings),
        crate::constructor_pages_specs::first_openings(lengths, work, root, openings),
        crate::constructor_table_specs::assigned(lengths, work, processed, root, regions),
        0 <= key < regions.len(), regions[key] == None, opening.position == processed,
        crate::constructor_pages_specs::first_opening(lengths, work, root, key, opening),
        crate::page_source_specs::valid_window(lengths, counts, root, max, key, width, opening),
        crate::constructor_pages_specs::backing(root, max, extent)
            || tight_backing(lengths, requested, extent),
    ensures used + h::capacity(width) <= extent,
        used <= u16::MAX, used <= usize::MAX - 32768,
{
    finite_offsets(root, max, used, regions);
    if crate::constructor_pages_specs::backing(root, max, extent) {
        crate::constructor_pages_proofs::candidate_storage(root, max, used, regions,
            key, width, extent);
    } else {
        dynamic_candidate_bound(lengths, counts, work, requested, root, max, used,
            processed, regions, openings, key, width, opening);
    }
}

pub(crate) proof fn independent_sharp_bounds()
    ensures crate::histogram_cost_specs::path(
            seq![0u16, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 233, 45, 1, 1, 2], 1, 2, 286),
        crate::histogram_cost_specs::path(
            seq![0u16, 0, 3, 1, 1, 1, 1, 0, 0, 0, 13, 5, 1, 1, 1, 2], 1, 2, 30),
        h::capacity(10) + cost::forest(
            seq![0u16, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 233, 45, 1, 1, 2], 10, 1, 2) == 1332,
        h::capacity(9) + cost::forest(
            seq![0u16, 0, 3, 1, 1, 1, 1, 0, 0, 0, 13, 5, 1, 1, 1, 2], 9, 1, 2) == 592,
{
    let literals = seq![0u16, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 233, 45, 1, 1, 2];
    let distances = seq![0u16, 0, 3, 1, 1, 1, 1, 0, 0, 0, 13, 5, 1, 1, 1, 2];
    let literal_frontiers = seq![1int, 2, 1, 1, 2, 4, 8, 16, 32, 64, 128, 23, 1, 1, 1, 0];
    let distance_frontiers = seq![1int, 2, 1, 1, 1, 1, 1, 2, 4, 8, 3, 1, 1, 1, 1, 0];
    assert forall|level: int| 1 <= level <= 15 implies
        #[trigger] literal_frontiers[level]
            == 2 * literal_frontiers[level - 1] - literals[level] as int by {
    }
    assert forall|level: int| 1 <= level <= 15 implies
        #[trigger] distance_frontiers[level]
            == 2 * distance_frontiers[level - 1] - distances[level] as int by {
    }
    assert forall|level: int| 0 <= level <= 15 implies
        #[trigger] literal_frontiers[level] >= 0 && distance_frontiers[level] >= 0 by {
    }
    assert(h::before(literals, 16) == 286 && h::before(distances, 16) == 30) by {
        reveal_with_fuel(h::before, 17);
    }
    crate::histogram_cost_proofs::path_from_frontiers(literals, literal_frontiers, 286);
    crate::histogram_cost_proofs::path_from_frontiers(distances, distance_frontiers, 30);
    crate::histogram_cost_proofs::path_sound(literals, 286);
    crate::histogram_cost_proofs::path_sound(distances, 30);
    concrete_histogram_bounds(literals, 10);
    concrete_histogram_bounds(distances, 9);
    facts::independent_maximizing_closed_costs();
    assert(h::capacity(10) == 1024 && h::capacity(9) == 512) by (compute);
}

}
