use crate::huffman_specs as model;
use crate::Code;
use vstd::prelude::*;

verus! {

pub proof fn canonical_prefix_at_cursor(lengths: Seq<u16>, symbol: int, cursor: u32, code: u32)
    requires 0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
        model::canonical_code(lengths, symbol) * model::capacity((32 - lengths[symbol]) as nat)
            == cursor,
        model::reversed_word(cursor) == code,
    ensures model::canonical_prefix(lengths, symbol) == code,
{
}

#[verifier::opaque]
pub(crate) open spec fn remaining_symbols(total: nat, processed: nat) -> nat {
    (total - processed) as nat
}

pub(crate) proof fn remaining_symbols_decreases(total: nat, before: nat, after: nat)
    requires before < after <= total,
    ensures remaining_symbols(total, after) < remaining_symbols(total, before),
{
    reveal(remaining_symbols);
}

pub(crate) proof fn subtable_link_bounds(entry: Code, root: nat, next: nat,
    width: nat, used: nat, word: nat)
    requires model::subtable_link(entry, root, next, width, used),
    ensures next <= model::subtable_index(entry, word) < used,
        entry.op & 16 == 0 && entry.op & 32 == 0 && entry.op & 64 == 0,
{
    capacity_positive(width);
    let op = entry.op;
    assert(op < 16);
    assert(op & 16 == 0 && op & 32 == 0 && op & 64 == 0)
        by (bit_vector) requires op < 16;
}

pub(crate) proof fn subtable_link_fixture()
    ensures model::subtable_link(Code { bits: 2, op: 2, val: 6 }, 2, 6, 2, 10),
        !model::subtable_link(Code { bits: 2, op: 2, val: 4 }, 2, 6, 2, 10),
        model::subtable_index(Code { bits: 2, op: 2, val: 6 }, 15) == 9,
        model::subtable_index(Code { bits: 2, op: 2, val: 6 }, 16) == 6,
        model::subtable_link_result(
            Seq::new(16, |i: int| Code { bits: 1, op: 64, val: 0 }),
            Seq::new(16, |i: int| Code { bits: 1, op: 64, val: 0 }),
            3, 2, 6, 6, 2, 10, false),
        !model::subtable_link_result(
            Seq::new(16, |i: int| Code { bits: 1, op: 64, val: 0 }),
            Seq::new(16, |i: int| if i == 3 { Code { bits: 2, op: 2, val: 6 } }
                else { Code { bits: 1, op: 64, val: 0 } }),
            3, 2, 6, 6, 2, 10, false),
{
    assert(model::capacity(2) == 4) by (compute);
    assert(Seq::new(16, |i: int| Code { bits: 1, op: 64, val: 0 })[3]
        != Code { bits: 2, op: 2, val: 6 });
}

pub(crate) proof fn distance_subtable_index_fixture()
    ensures model::subtable_index(Code { bits: 2, op: 1, val: 4 }, 13) == 5,
        model::subtable_index(Code { bits: 2, op: 2, val: 6 }, u64::MAX as nat) == 9,
        model::subtable_index(Code { bits: 1, op: 14, val: 65535 }, u64::MAX as nat) == 81918,
{
    assert(model::capacity(1) == 2 && model::capacity(2) == 4
        && model::capacity(14) == 16384) by (compute);
}

pub(crate) proof fn root_codes_zero(lengths: Seq<u16>, work: Seq<u16>, index: int, original: Code)
    ensures model::root_codes_after(lengths, work, 0, index, original) == original,
{
    reveal(model::root_codes_after);
}

pub(crate) proof fn root_codes_step(lengths: Seq<u16>, work: Seq<u16>, processed: nat,
    index: int, original: Code)
    requires processed < work.len(), (work[processed as int] as int) < lengths.len(),
        1 <= lengths[work[processed as int] as int] <= 7,
    ensures model::root_codes_after(lengths, work, processed + 1, index, original)
        == if model::table_replica(0,
            model::canonical_prefix(lengths, work[processed as int] as int) as nat,
            lengths[work[processed as int] as int] as nat,
            model::maximum_length(lengths) as nat, index) {
            Code { op: 0, bits: lengths[work[processed as int] as int] as u8,
                val: work[processed as int] }
        } else { model::root_codes_after(lengths, work, processed, index, original) },
{
    reveal(model::root_codes_after);
}

pub(crate) proof fn root_codes_frame(lengths: Seq<u16>, work: Seq<u16>, processed: nat,
    index: int, original: Code)
    requires index < 0 || model::capacity(model::maximum_length(lengths) as nat) <= index,
    ensures model::root_codes_after(lengths, work, processed, index, original) == original,
    decreases processed,
{
    reveal(model::root_codes_after);
    if processed > 0 {
        root_codes_frame(lengths, work, (processed - 1) as nat, index, original);
    }
}

pub proof fn distance_base_step(symbol: nat)
    requires 4 <= symbol <= 29,
    ensures model::distance_base(symbol)
            == 2 * model::distance_base((symbol - 2) as nat) - 1,
        model::distance_extra(symbol)
            == model::distance_extra((symbol - 2) as nat) + 1,
{
    if symbol >= 6 {
        let group = model::distance_extra(symbol);
        let previous = model::capacity((group - 1) as nat);
        let width = model::capacity(group);
        let parity = symbol % 2;
        assert((symbol - 2) / 2 == symbol / 2 - 1);
        assert((symbol - 2) % 2 == parity);
        assert(model::distance_extra((symbol - 2) as nat) == group - 1);
        assert(width == 2 * previous);
        assert(parity * width == 2 * (parity * previous)) by (nonlinear_arith)
            requires width == 2 * previous;
        assert(model::distance_base(symbol) == 1 + 2 * width + parity * width);
        assert(model::distance_base((symbol - 2) as nat) == 1 + width + parity * previous);
        assert(1 + 2 * width + parity * width
            == 2 * (1 + width + parity * previous) - 1) by (nonlinear_arith)
            requires width == 2 * previous;
    } else if symbol == 4 {
        assert(model::distance_base(4) == 5 && model::distance_base(2) == 3
            && model::distance_extra(4) == 1 && model::distance_extra(2) == 0) by (compute);
    } else {
        assert(symbol == 5);
        assert(model::distance_base(5) == 7 && model::distance_base(3) == 4
            && model::distance_extra(5) == 1 && model::distance_extra(3) == 0) by (compute);
    }
}

pub proof fn reversal_unique(word: u32, left: u32, right: u32)
    requires model::is_reversal(word, left), model::is_reversal(word, right),
    ensures left == right,
{
    assert forall|index: u32| index < 32 implies
        #[trigger] model::word_bit(left, index) == model::word_bit(right, index) by {}
    assert forall|index: u32| index < 32 implies
        #[trigger] ((left >> index) & 1) == ((right >> index) & 1) by {
        assert(model::word_bit(left, index) == model::word_bit(right, index));
    }
    assert(left == right) by (bit_vector)
        requires forall|index: u32| index < 32 ==>
            #[trigger] ((left >> index) & 1) == ((right >> index) & 1);
}

pub proof fn reversal_matches_model(word: u32, result: u32)
    requires model::is_reversal(word, result),
    ensures result == model::reversed_word(word),
{
    assert(exists|candidate: u32| model::is_reversal(word, candidate));
    let selected = model::reversed_word(word);
    assert(model::is_reversal(word, selected));
    reversal_unique(word, result, selected);
}

pub proof fn zero_reversal()
    ensures model::is_reversal(0, 0), model::reversed_word(0) == 0,
{
    assert forall|index: u32| index < 32 implies
        #[trigger] model::word_bit(0, index) == model::word_bit(0, (31 - index) as u32) by {
        assert((0u32 >> index) & 1 == (0u32 >> ((31 - index) as u32)) & 1)
            by (bit_vector) requires index < 32;
    }
    reversal_matches_model(0, 0);
}

pub proof fn slots_empty_tail(counts: Seq<u16>, low: nat, high: nat)
    requires counts.len() == 16, low <= high <= 15,
        forall|level: int| low < level <= high ==> counts[level] == 0,
    ensures model::slots(counts, high)
        == model::capacity((high - low) as nat) * model::slots(counts, low),
    decreases high - low,
{
    if low < high {
        slots_empty_tail(counts, low, (high - 1) as nat);
        let weight = model::capacity((high - low - 1) as nat);
        let space = model::slots(counts, low);
        assert(2 * (weight * space) == (2 * weight) * space) by (nonlinear_arith);
    } else {
        assert(model::capacity(0) == 1);
    }
}

pub proof fn complete_final_cursor(lengths: Seq<u16>, counts: Seq<u16>, position: nat)
    requires model::valid_histogram(lengths, counts),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        1 <= model::maximum_length(lengths) <= 15,
        model::slots(counts, 15) == 0,
        position + 1 == model::before(counts, 16),
    ensures model::normalized_cursor(counts, model::maximum_length(lengths) as nat, position)
        + model::capacity((32 - model::maximum_length(lengths)) as nat) == 4294967296,
{
    let max = model::maximum_length(lengths) as nat;
    length_population_bounds(lengths);
    assert forall|level: int| max < level <= 15 implies counts[level] == 0 by {
        assert(model::occurrences(lengths, level as u16) == 0);
    }
    before_empty_range(counts, max + 1, 16);
    slots_empty_tail(counts, max, 15);
    capacity_positive((15 - max) as nat);
    let weight = model::capacity((15 - max) as nat);
    let space = model::slots(counts, max);
    assert(space == 0) by (nonlinear_arith) requires weight > 0, weight * space == 0;
    code_space_partition(counts, max);
    capacity_product(max, (32 - max) as nat);
    assert(model::capacity(32) == 4294967296) by (compute);
    let first = model::first_code(counts, max);
    let assigned = counts[max as int] as nat;
    let rank = position - model::before(counts, max);
    let width = model::capacity((32 - max) as nat);
    assert(rank + 1 == assigned);
    assert((first + rank) * width + width == (first + assigned) * width)
        by (nonlinear_arith) requires rank + 1 == assigned;
}

pub proof fn histogram_prefix_step(lengths: Seq<u16>, index: int, value: u16)
    requires 0 <= index < lengths.len(),
    ensures
        model::occurrences(lengths.take(index + 1), value)
            == model::occurrences(lengths.take(index), value)
                + if lengths[index] == value { 1nat } else { 0nat },
        model::minimum_length(lengths.take(index + 1))
            == if lengths[index] > 0 && lengths[index] < model::minimum_length(lengths.take(index)) {
                lengths[index] as usize
            } else { model::minimum_length(lengths.take(index)) },
        model::maximum_length(lengths.take(index + 1))
            == if lengths[index] > model::maximum_length(lengths.take(index)) {
                lengths[index] as usize
            } else { model::maximum_length(lengths.take(index)) },
{
    assert(lengths.take(index + 1).drop_last() == lengths.take(index));
    assert(lengths.take(index + 1).last() == lengths[index]);
}

pub proof fn metadata_bounds(lengths: Seq<u16>)
    requires forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
    ensures 1 <= model::minimum_length(lengths) <= 15,
        model::maximum_length(lengths) <= 15,
        model::maximum_length(lengths) == 0 ==> model::minimum_length(lengths) == 15,
        model::maximum_length(lengths) > 0 ==>
            model::minimum_length(lengths) <= model::maximum_length(lengths),
    decreases lengths.len(),
{
    if lengths.len() > 0 {
        assert forall|index: int| 0 <= index < lengths.drop_last().len()
            implies lengths.drop_last()[index] <= 15 by {
            assert(lengths.drop_last()[index] == lengths[index]);
        }
        metadata_bounds(lengths.drop_last());
        assert(lengths.last() <= 15);
    }
}

pub proof fn length_population_bounds(lengths: Seq<u16>)
    requires forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
    ensures model::maximum_length(lengths) > 0 ==>
            model::occurrences(lengths, model::minimum_length(lengths) as u16) > 0
                && model::occurrences(lengths, model::maximum_length(lengths) as u16) > 0,
        forall|value: u16| 1 <= value <= 15
            && (value < model::minimum_length(lengths) || value > model::maximum_length(lengths)) ==>
                #[trigger] model::occurrences(lengths, value) == 0,
    decreases lengths.len(),
{
    metadata_bounds(lengths);
    if lengths.len() > 0 {
        assert forall|index: int| 0 <= index < lengths.drop_last().len()
            implies lengths.drop_last()[index] <= 15 by {
            assert(lengths.drop_last()[index] == lengths[index]);
        }
        length_population_bounds(lengths.drop_last());
        metadata_bounds(lengths.drop_last());
        assert(lengths.last() <= 15);
        assert forall|value: u16| 1 <= value <= 15
            && (value < model::minimum_length(lengths) || value > model::maximum_length(lengths))
            implies #[trigger] model::occurrences(lengths, value) == 0 by {
            assert(lengths.last() != value);
            assert(value < model::minimum_length(lengths.drop_last())
                || value > model::maximum_length(lengths.drop_last()));
            assert(model::occurrences(lengths.drop_last(), value) == 0);
        }
    }
}

pub proof fn count_before_bounds(lengths: Seq<u16>, level: nat)
    ensures model::count_before(lengths, level) <= lengths.len(),
    decreases lengths.len(),
{
    if lengths.len() > 0 {
        count_before_bounds(lengths.drop_last(), level);
    }
}

pub proof fn count_before_base(lengths: Seq<u16>)
    ensures model::count_before(lengths, 1) == 0,
    decreases lengths.len(),
{
    if lengths.len() > 0 {
        count_before_base(lengths.drop_last());
    }
}

pub proof fn count_before_step(lengths: Seq<u16>, level: nat)
    requires 1 <= level <= 15,
    ensures model::count_before(lengths, level + 1)
        == model::count_before(lengths, level) + model::occurrences(lengths, level as u16),
    decreases lengths.len(),
{
    if lengths.len() > 0 {
        count_before_step(lengths.drop_last(), level);
    }
}

pub proof fn histogram_offsets(lengths: Seq<u16>, counts: Seq<u16>, level: nat)
    requires model::valid_histogram(lengths, counts), 1 <= level <= 16,
    ensures model::before(counts, level) == model::count_before(lengths, level),
        model::before(counts, level) <= lengths.len(),
    decreases level,
{
    if level == 1 {
        count_before_base(lengths);
    } else {
        histogram_offsets(lengths, counts, (level - 1) as nat);
        count_before_step(lengths, (level - 1) as nat);
    }
    count_before_bounds(lengths, level);
}

pub proof fn before_monotone(counts: Seq<u16>, low: nat, high: nat)
    requires low <= high <= counts.len(),
    ensures model::before(counts, low) <= model::before(counts, high),
    decreases high - low,
{
    if low < high {
        before_monotone(counts, low, (high - 1) as nat);
    }
}

pub proof fn before_empty_range(counts: Seq<u16>, low: nat, high: nat)
    requires counts.len() == 16, 1 <= low <= high <= 16,
        forall|level: int| low <= level < high ==> counts[level] == 0,
    ensures model::before(counts, low) == model::before(counts, high),
    decreases high - low,
{
    if low < high {
        before_empty_range(counts, low, (high - 1) as nat);
    }
}

pub proof fn bucket_for_position(counts: Seq<u16>, position: int, depth: nat) -> (level: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
        0 <= position < model::before(counts, depth + 1),
    ensures 1 <= level <= depth,
        model::before(counts, level) <= position < model::before(counts, level + 1),
    decreases depth,
{
    if model::before(counts, depth) <= position {
        depth
    } else {
        assert(depth > 1);
        bucket_for_position(counts, position, (depth - 1) as nat)
    }
}

pub proof fn ordered_symbol_at(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    position: int) -> (level: nat)
    requires model::bucket_ordered(lengths, counts, work),
        0 <= position < model::before(counts, 16),
    ensures 1 <= level <= 15,
        model::before(counts, level) <= position < model::before(counts, level + 1),
        position < work.len(), (work[position] as int) < lengths.len(),
        lengths[work[position] as int] == level,
        model::occurrences(lengths.take(work[position] as int), level as u16)
            == position - model::before(counts, level),
{
    let level = bucket_for_position(counts, position, 15);
    assert(model::bucket_entry(lengths, counts, work, level as int,
        position - model::before(counts, level)));
    level
}

pub proof fn remaining_in_bucket(counts: Seq<u16>, level: nat, position: nat)
    requires counts.len() == 16, 1 <= level <= 15,
        model::before(counts, level) <= position < model::before(counts, level + 1),
    ensures model::remaining_count(counts, level, position)
        == model::before(counts, level + 1) - position,
        model::remaining_count(counts, level, position) > 0,
{
}

pub proof fn remaining_step(counts: Seq<u16>, level: nat, current: nat, position: nat)
    requires counts.len() == 16, 1 <= level <= 15, 1 <= current <= 15,
        model::before(counts, current) <= position < model::before(counts, current + 1),
    ensures model::remaining_count(counts, level, position + 1)
        + if level == current { 1nat } else { 0nat }
        == model::remaining_count(counts, level, position),
{
    if level < current {
        before_monotone(counts, level + 1, current);
    } else if current < level {
        before_monotone(counts, current + 1, level);
    }
}

pub proof fn initial_symbol_state(lengths: Seq<u16>, counts: Seq<u16>)
    requires model::valid_histogram(lengths, counts),
        forall|index: int| 0 <= index < lengths.len() ==> lengths[index] <= 15,
        model::maximum_length(lengths) > 0,
    ensures model::remaining_histogram(counts, counts, 0),
        model::before(counts, model::minimum_length(lengths) as nat) == 0,
        model::before(counts, model::minimum_length(lengths) as nat + 1) > 0,
        model::normalized_cursor(counts, model::minimum_length(lengths) as nat, 0) == 0,
{
    metadata_bounds(lengths);
    length_population_bounds(lengths);
    let min = model::minimum_length(lengths) as nat;
    assert forall|level: int| 1 <= level < min implies counts[level] == 0 by {
        assert(model::occurrences(lengths, level as u16) == 0);
    }
    before_empty_range(counts, 1, min);
    first_code_empty_range(counts, min);
    assert(model::before(counts, min) == 0);
    assert(model::first_code(counts, min) == 0);
    assert(model::normalized_cursor(counts, min, 0) == 0) by (nonlinear_arith)
        requires model::first_code(counts, min) == 0, model::before(counts, min) == 0;
}

pub proof fn first_code_empty_range(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
        forall|level: int| 1 <= level < depth ==> counts[level] == 0,
    ensures model::first_code(counts, depth) == 0,
    decreases depth,
{
    if depth > 1 {
        first_code_empty_range(counts, (depth - 1) as nat);
    }
}

pub proof fn first_code_gap(counts: Seq<u16>, low: nat, high: nat)
    requires counts.len() == 16, 1 <= low < high <= 15,
        forall|level: int| low < level < high ==> counts[level] == 0,
    ensures model::first_code(counts, high) * model::capacity((32 - high) as nat)
        == (model::first_code(counts, low) + counts[low as int] as nat)
            * model::capacity((32 - low) as nat),
    decreases high - low,
{
    if low + 1 < high {
        first_code_gap(counts, low, (high - 1) as nat);
        assert(counts[high as int - 1] == 0);
    }
    let previous = model::first_code(counts, (high - 1) as nat);
    let count = counts[high as int - 1] as nat;
    let width = model::capacity((32 - high) as nat);
    assert(model::capacity((33 - high) as nat) == 2 * width);
    assert(2 * (previous + count) * width == (previous + count) * (2 * width))
        by (nonlinear_arith);
}

pub proof fn normalized_cursor_next(counts: Seq<u16>, current: nat, next: nat, position: nat)
    requires counts.len() == 16, 1 <= current <= next <= 15,
        model::before(counts, current) <= position < model::before(counts, current + 1),
        model::before(counts, next) <= position + 1 < model::before(counts, next + 1),
    ensures model::normalized_cursor(counts, next, position + 1)
        == model::normalized_cursor(counts, current, position)
            + model::capacity((32 - current) as nat),
{
    let width = model::capacity((32 - current) as nat);
    let rank = position - model::before(counts, current);
    let first = model::first_code(counts, current);
    if current < next {
        before_monotone(counts, current + 1, next);
        assert(model::before(counts, next) == position + 1);
        assert(model::before(counts, current + 1) == position + 1);
        assert forall|level: int| current < level < next implies counts[level] == 0 by {
            before_monotone(counts, current + 1, level as nat);
            before_monotone(counts, level as nat + 1, next);
        }
        first_code_gap(counts, current, next);
        assert(counts[current as int] == rank + 1);
    }
    assert((first + rank + 1) * width == (first + rank) * width + width)
        by (nonlinear_arith);
}

pub proof fn occurrences_prefix_bound(lengths: Seq<u16>, index: int, value: u16)
    requires 0 <= index <= lengths.len(),
    ensures model::occurrences(lengths.take(index), value) <= model::occurrences(lengths, value),
    decreases lengths.len(),
{
    if index < lengths.len() {
        occurrences_prefix_bound(lengths.drop_last(), index, value);
        assert(lengths.drop_last().take(index) == lengths.take(index));
    } else {
        assert(lengths.take(index) == lengths);
    }
}

pub proof fn separate_buckets(counts: Seq<u16>, first: nat, second: nat,
    first_position: int, second_position: int)
    requires counts.len() == 16, 1 <= first <= 15, 1 <= second <= 15, first != second,
        model::before(counts, first) <= first_position < model::before(counts, first + 1),
        model::before(counts, second) <= second_position < model::before(counts, second + 1),
    ensures first_position != second_position,
{
    if first < second {
        before_monotone(counts, first + 1, second);
    } else {
        before_monotone(counts, second + 1, first);
    }
}

pub proof fn strict_occurrence_ranks(lengths: Seq<u16>, first: int, second: int, value: u16)
    requires 0 <= first < second <= lengths.len(), lengths[first] == value,
    ensures model::occurrences(lengths.take(first), value)
        < model::occurrences(lengths.take(second), value),
{
    histogram_prefix_step(lengths, first, value);
    occurrences_prefix_bound(lengths.take(second), first + 1, value);
    assert(lengths.take(second).take(first + 1) == lengths.take(first + 1));
}

pub proof fn stable_bucket_order(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    level: int, first: int, second: int)
    requires model::bucket_ordered(lengths, counts, work),
        1 <= level <= 15, 0 <= first < second < counts[level],
    ensures work[model::before(counts, level as nat) as int + first] <
        work[model::before(counts, level as nat) as int + second],
{
    assert(model::bucket_entry(lengths, counts, work, level, first));
    assert(model::bucket_entry(lengths, counts, work, level, second));
    let first_symbol = work[model::before(counts, level as nat) as int + first] as int;
    let second_symbol = work[model::before(counts, level as nat) as int + second] as int;
    if second_symbol < first_symbol {
        strict_occurrence_ranks(lengths, second_symbol, first_symbol, level as u16);
    }
}

pub proof fn sorted_symbol_position(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    symbol: int)
    requires model::valid_histogram(lengths, counts),
        model::bucket_ordered(lengths, counts, work),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
    ensures {
        let level = lengths[symbol];
        let ordinal = model::occurrences(lengths.take(symbol), level);
        let position = model::before(counts, level as nat) as int + ordinal as int;
        0 <= position < model::before(counts, 16) && position < work.len()
            && work[position] == symbol
    },
{
    let level = lengths[symbol];
    let ordinal = model::occurrences(lengths.take(symbol), level);
    histogram_prefix_step(lengths, symbol, level);
    occurrences_prefix_bound(lengths, symbol + 1, level);
    assert(ordinal < counts[level as int]);
    assert(model::bucket_entry(lengths, counts, work, level as int, ordinal as int));
    let position = model::before(counts, level as nat) as int + ordinal as int;
    assert(0 <= position < work.len());
    assert(lengths[work[position] as int] == level);
    let actual = work[position] as int;
    if actual < symbol {
        strict_occurrence_ranks(lengths, actual, symbol, level);
    } else if symbol < actual {
        strict_occurrence_ranks(lengths, symbol, actual, level);
    }
    before_monotone(counts, level as nat + 1, 16);
}

pub proof fn first_code_from_histogram(lengths: Seq<u16>, counts: Seq<u16>, depth: nat)
    requires model::valid_histogram(lengths, counts), 1 <= depth <= 15,
    ensures model::first_code(counts, depth) == model::canonical_start(lengths, depth),
    decreases depth,
{
    if depth > 1 {
        first_code_from_histogram(lengths, counts, (depth - 1) as nat);
    }
}

pub proof fn code_space_partition(counts: Seq<u16>, depth: nat)
    requires counts.len() == 16, 1 <= depth <= 15,
    ensures model::first_code(counts, depth) + counts[depth as int]
        + model::slots(counts, depth) == model::capacity(depth),
    decreases depth,
{
    if depth > 1 {
        code_space_partition(counts, (depth - 1) as nat);
    } else {
        assert(model::slots(counts, 0) == 1);
        assert(model::capacity(0) == 1);
    }
}

pub proof fn canonical_code_bound(lengths: Seq<u16>, counts: Seq<u16>, symbol: int)
    requires model::valid_histogram(lengths, counts),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
        model::valid_prefix(counts, lengths[symbol] as nat),
    ensures model::canonical_code(lengths, symbol) < model::capacity(lengths[symbol] as nat),
{
    let level = lengths[symbol];
    first_code_from_histogram(lengths, counts, level as nat);
    code_space_partition(counts, level as nat);
    histogram_prefix_step(lengths, symbol, level);
    occurrences_prefix_bound(lengths, symbol + 1, level);
}

pub proof fn normalized_cursor_bound(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    level: nat, position: nat)
    requires model::valid_histogram(lengths, counts), model::bucket_ordered(lengths, counts, work),
        1 <= level <= 15, model::valid_prefix(counts, level),
        model::before(counts, level) <= position < model::before(counts, level + 1),
    ensures 0 <= model::normalized_cursor(counts, level, position) < 4294967296,
        position < work.len(), (work[position as int] as int) < lengths.len(),
        lengths[work[position as int] as int] == level,
        model::normalized_cursor(counts, level, position)
            == model::canonical_code(lengths, work[position as int] as int)
                * model::capacity((32 - level) as nat),
{
    assert(model::bucket_entry(lengths, counts, work, level as int,
        position - model::before(counts, level)));
    let symbol = work[position as int] as int;
    first_code_from_histogram(lengths, counts, level);
    canonical_code_bound(lengths, counts, symbol);
    capacity_product(level, (32 - level) as nat);
    capacity_positive((32 - level) as nat);
    assert(model::capacity(32) == 4294967296) by (compute);
    let code = model::canonical_code(lengths, symbol);
    let limit = model::capacity(level);
    let width = model::capacity((32 - level) as nat);
    assert(0 <= code * width < limit * width) by (nonlinear_arith)
        requires 0 <= code < limit, width > 0;
}

pub proof fn rfc_canonical_example()
    ensures ({
        let lengths = seq![3u16, 3, 3, 3, 3, 2, 4, 4];
        model::canonical_code(lengths, 0) == 2
            && model::canonical_code(lengths, 1) == 3
            && model::canonical_code(lengths, 2) == 4
            && model::canonical_code(lengths, 3) == 5
            && model::canonical_code(lengths, 4) == 6
            && model::canonical_code(lengths, 5) == 0
            && model::canonical_code(lengths, 6) == 14
            && model::canonical_code(lengths, 7) == 15
    }),
{
    assert({
        let lengths = seq![3u16, 3, 3, 3, 3, 2, 4, 4];
        model::canonical_code(lengths, 0) == 2
            && model::canonical_code(lengths, 1) == 3
            && model::canonical_code(lengths, 2) == 4
            && model::canonical_code(lengths, 3) == 5
            && model::canonical_code(lengths, 4) == 6
            && model::canonical_code(lengths, 5) == 0
            && model::canonical_code(lengths, 6) == 14
            && model::canonical_code(lengths, 7) == 15
    }) by (compute);
}

pub proof fn rfc_bit_order_example()
    ensures ({
        let lengths = seq![3u16, 3, 3, 3, 3, 2, 4, 4];
        model::canonical_prefix(lengths, 0) == 2
            && model::canonical_prefix(lengths, 1) == 6
            && model::canonical_prefix(lengths, 2) == 1
            && model::canonical_prefix(lengths, 3) == 5
            && model::canonical_prefix(lengths, 4) == 3
            && model::canonical_prefix(lengths, 5) == 0
            && model::canonical_prefix(lengths, 6) == 7
            && model::canonical_prefix(lengths, 7) == 15
    }),
{
    rfc_canonical_example();
    assert(model::capacity(28) == 268435456 && model::capacity(29) == 536870912
        && model::capacity(30) == 1073741824) by (compute);
    assert forall|index: u32| #![trigger model::word_bit(2, index)]
        #![trigger model::word_bit(6, index)] #![trigger model::word_bit(1, index)]
        #![trigger model::word_bit(5, index)] #![trigger model::word_bit(3, index)]
        #![trigger model::word_bit(7, index)] #![trigger model::word_bit(15, index)]
        index < 32 implies model::word_bit(2, index)
            == model::word_bit(0x40000000, (31 - index) as u32)
        && model::word_bit(6, index)
            == model::word_bit(0x60000000, (31 - index) as u32)
        && model::word_bit(1, index)
            == model::word_bit(0x80000000, (31 - index) as u32)
        && model::word_bit(5, index)
            == model::word_bit(0xa0000000, (31 - index) as u32)
        && model::word_bit(3, index)
            == model::word_bit(0xc0000000, (31 - index) as u32)
        && model::word_bit(7, index)
            == model::word_bit(0xe0000000, (31 - index) as u32)
        && model::word_bit(15, index)
            == model::word_bit(0xf0000000, (31 - index) as u32) by {
        assert((2u32 >> index) & 1 == (0x40000000u32 >> ((31 - index) as u32)) & 1
            && (6u32 >> index) & 1 == (0x60000000u32 >> ((31 - index) as u32)) & 1
            && (1u32 >> index) & 1 == (0x80000000u32 >> ((31 - index) as u32)) & 1
            && (5u32 >> index) & 1 == (0xa0000000u32 >> ((31 - index) as u32)) & 1
            && (3u32 >> index) & 1 == (0xc0000000u32 >> ((31 - index) as u32)) & 1
            && (7u32 >> index) & 1 == (0xe0000000u32 >> ((31 - index) as u32)) & 1
            && (15u32 >> index) & 1 == (0xf0000000u32 >> ((31 - index) as u32)) & 1)
            by (bit_vector) requires index < 32;
    }
    reversal_matches_model(0x40000000, 2);
    reversal_matches_model(0x60000000, 6);
    reversal_matches_model(0x80000000, 1);
    reversal_matches_model(0xa0000000, 5);
    reversal_matches_model(0xc0000000, 3);
    reversal_matches_model(0xe0000000, 7);
    reversal_matches_model(0xf0000000, 15);
    zero_reversal();
}

pub proof fn capacity_is_power(depth: nat)
    ensures model::capacity(depth) == vstd::arithmetic::power2::pow2(depth),
    decreases depth,
{
    if depth > 0 {
        capacity_is_power((depth - 1) as nat);
        vstd::arithmetic::power2::lemma_pow2_unfold(depth);
    } else {
        reveal(vstd::arithmetic::power::pow);
    }
}

pub proof fn capacity_product(left: nat, right: nat)
    ensures model::capacity(left + right) == model::capacity(left) * model::capacity(right),
{
    capacity_is_power(left);
    capacity_is_power(right);
    capacity_is_power(left + right);
    vstd::arithmetic::power2::lemma_pow2_adds(left, right);
}

pub proof fn normalized_code_step(length: usize)
    requires 1 <= length <= 15,
    ensures (0x80000000u32 >> ((length - 1) as u32)) as int
        == model::capacity((32 - length) as nat),
{
    let shift = (32 - length) as u64;
    capacity_is_power(shift as nat);
    vstd::bits::lemma_u64_pow2_no_overflow(shift as nat);
    vstd::bits::lemma_u64_shl_is_mul(1, shift);
    assert((0x80000000u32 >> ((length - 1) as u32)) as u64 == 1u64 << ((32 - length) as u64))
        by (bit_vector) requires 1 <= length <= 15;
}

pub proof fn usize_shift_capacity(depth: usize)
    requires depth <= 15,
    ensures 1usize << depth == model::capacity(depth as nat),
{
    capacity_is_power(depth as nat);
    vstd::bits::lemma_usize_pow2_no_overflow(depth as nat);
    vstd::bits::lemma_usize_shl_is_mul(1, depth);
}

pub proof fn u32_shift_capacity(depth: u32)
    requires depth <= 15,
    ensures 1u32 << depth == model::capacity(depth as nat),
{
    capacity_is_power(depth as nat);
    vstd::bits::lemma_u32_pow2_no_overflow(depth as nat);
    vstd::bits::lemma_u32_shl_is_mul(1, depth);
}

pub proof fn aligned_cursor_widen(word: u32, length: u32, next: u32)
    requires 1 <= length <= next <= 15, model::aligned_cursor(word, length),
    ensures model::aligned_cursor(word, next),
{
    assert(word & (u32::MAX >> next) == 0) by (bit_vector)
        requires 1 <= length <= next <= 15, word & (u32::MAX >> length) == 0;
}

pub proof fn shifted_code_bound(word: u32, length: u32, drop: u32)
    requires drop < length <= 15, word < model::capacity(length as nat),
    ensures (word >> drop) < model::capacity((length - drop) as nat),
{
    u32_shift_capacity(length);
    u32_shift_capacity((length - drop) as u32);
    assert(word >> drop < 1u32 << ((length - drop) as u32)) by (bit_vector)
        requires drop < length <= 15, word < 1u32 << length;
}

pub proof fn capacity_multiple(low: nat, high: nat)
    requires low <= high,
    ensures model::capacity(high) % model::capacity(low) == 0,
{
    capacity_is_power(low);
    capacity_is_power(high);
    capacity_is_power((high - low) as nat);
    capacity_positive(low);
    vstd::arithmetic::power2::lemma_pow2_adds((high - low) as nat, low);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(
        model::capacity((high - low) as nat), model::capacity(low));
}

pub proof fn replica_period(position: int, start: int, stride: int, prefix: int)
    requires 0 <= start, 0 < stride, 0 <= prefix < stride,
        start % stride == 0, start <= position < start + stride,
        position % stride == prefix,
    ensures position == start + prefix,
{
    vstd::arithmetic::div_mod::lemma_small_mod((position - start) as nat, stride as nat);
    vstd::arithmetic::div_mod::lemma_mod_adds(start, position - start, stride);
}

pub proof fn capacity_positive(depth: nat)
    ensures model::capacity(depth) > 0,
    decreases depth,
{
    if depth > 0 { capacity_positive((depth - 1) as nat); }
}

pub proof fn capacity_monotone(low: nat, high: nat)
    requires low <= high,
    ensures model::capacity(low) <= model::capacity(high),
    decreases high - low,
{
    capacity_positive(high);
    if low < high {
        capacity_monotone(low, (high - 1) as nat);
    }
}

pub proof fn depth_capacity(depth: nat)
    requires depth <= 15,
    ensures model::capacity(depth) <= 32768,
{
    capacity_monotone(depth, 15);
    assert(model::capacity(15) == 32768) by (compute);
}

pub proof fn doubled_value(value: u32)
    requires value <= 32768,
    ensures (value << 1) as int == 2 * value as int,
{
    assert(value << 1 == (value * 2) as u32) by (bit_vector)
        requires value <= 32768;
}

pub proof fn extend_valid_prefix(counts: Seq<u16>, depth: nat)
    requires 0 < depth < counts.len(), model::valid_prefix(counts, (depth - 1) as nat),
        model::slots(counts, depth) >= 0,
    ensures model::valid_prefix(counts, depth),
{
    assert forall|level: nat| level <= depth implies model::slots(counts, level) >= 0 by {
        if level < depth {
            assert(level <= depth - 1);
        }
    }
}

}
