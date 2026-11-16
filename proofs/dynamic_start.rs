use crate::{dynamic_start_specs as model, header_loop_specs as lengths, Code};
use vstd::prelude::*;

verus! {

pub(crate) proof fn finish(before: lengths::State, after: lengths::State,
    middle: lengths::State, pending: Seq<bool>, before_table: Seq<Code>, table: Seq<Code>,
    before_work: Seq<u16>, work: Seq<u16>, counts: (usize, usize, usize),
    outcome: crate::huffman::HeaderReadOutcome)
    requires model::composed_result(before, after, middle, pending,
        before_table, table, before_work, work, counts, outcome),
    ensures model::result(before, after, pending, before_table, table, before_work, work,
        crate::huffman::DynamicHeaderOutcome::Header { counts, outcome }),
{
    reveal(model::result);
    let answer = crate::huffman::DynamicHeaderOutcome::Header { counts, outcome };
    if let crate::huffman::DynamicHeaderOutcome::Header {
        counts: selected_counts, outcome: selected_outcome
    } = answer {
        assert(model::composed_result(before, after, middle, pending, before_table, table,
            before_work, work, selected_counts, selected_outcome));
        assert(exists|witness: lengths::State| #[trigger] model::composed_result(
            before, after, witness, pending, before_table, table, before_work, work,
            selected_counts, selected_outcome));
    }
}

pub(crate) proof fn compatibility_boundaries()
    ensures model::compatibility_profile(286, 30),
        !model::compatibility_profile(287, 30),
        !model::compatibility_profile(286, 31),
        model::compatibility_profile(257, 1),
{
}

pub(crate) proof fn buffered_count_phase_fixture()
    ensures model::result(
        lengths::state(Seq::new(316, |index: int| 9u16), 37, 0, 13, 0, 0),
        lengths::state(Seq::new(316, |index: int| 9u16), 37, 0, 13, 0, 0),
        Seq::empty(),
        Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 }),
        Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 }),
        Seq::new(19, |index: int| 42u16), Seq::new(19, |index: int| 42u16),
        crate::huffman::DynamicHeaderOutcome::NeedCounts),
        model::result(
            lengths::state(Seq::new(316, |index: int| 9u16), 37, 0, 14, 0, 0),
            lengths::state(Seq::new(316, |index: int| 9u16), 0, 0, 0, 0, 14),
            Seq::empty(),
            Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 }),
            Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 }),
            Seq::new(19, |index: int| 42u16), Seq::new(19, |index: int| 42u16),
            crate::huffman::DynamicHeaderOutcome::Header {
                counts: (257, 1, 4), outcome: crate::huffman::HeaderReadOutcome::NeedAlphabet }),
{
    let lens = Seq::new(316, |index: int| 9u16);
    let empty = Seq::empty();
    let table = Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 });
    let work = Seq::new(19, |index: int| 42u16);
    assert forall|index: nat| index < 64 implies
        !(#[trigger] crate::bit_specs::word_bit(0, index)) by {
        let shift = index as u64;
        assert((0u64 >> shift) & 1 == 0) by (bit_vector);
    }
    assert(0u64 >> 0u64 == 0 && 0u64 >> 14u8 == 0) by (bit_vector);
    assert(empty.take(0) =~= empty);
    assert(empty.skip(0) =~= empty);
    assert(crate::bit_specs::buffered_bits(0, 0) =~= empty);
    reveal(crate::bit_specs::cached_suffix);
    assert(crate::bit_specs::filled_word(0, 13, 0, empty));
    assert(crate::bit_specs::filled_word(0, 14, 0, empty));
    assert(crate::bit_specs::filled_word(0, 0, 0, empty));
    let suspended = lengths::state(lens, 37, 0, 13, 0, 0);
    assert(crate::bit_specs::buffered_bits(0, 13) + empty
        =~= crate::bit_specs::buffered_bits(0, 13));
    assert(crate::bit_specs::buffered_bits(0, 13).skip(0)
        =~= crate::bit_specs::buffered_bits(0, 13));
    assert(model::counts_result(suspended, suspended, empty, None)) by {
        reveal(model::counts_result);
    }
    assert(model::result(suspended, suspended, empty, table, table, work, work,
        crate::huffman::DynamicHeaderOutcome::NeedCounts)) by {
        reveal(model::result);
    }
    let before = lengths::state(lens, 37, 0, 14, 0, 0);
    let middle = lengths::state(lens, 37, 0, 0, 0, 14);
    let after = lengths::state(lens, 0, 0, 0, 0, 14);
    let source = crate::bit_specs::buffered_bits(0, 14);
    assert(source =~= Seq::new(14, |index: int| false));
    assert(source + empty =~= source);
    assert(source.skip(14) =~= empty);
    assert(crate::dynamic_header_specs::header_counts(source) == (257nat, 1nat, 4nat)) by {
        reveal_with_fuel(crate::bit_specs::low_first_value, 6);
    }
    assert(model::counts_result(before, middle, empty, Some((257, 1, 4)))) by {
        reveal(model::counts_result);
        assert(exists|loaded: u64| #[trigger] crate::bit_specs::filled_word(
            before.word, before.count, loaded, empty.take(8 * middle.advanced as int))
            && middle.word == loaded >> 14u8) by {
            let loaded = 0u64;
            assert(crate::bit_specs::filled_word(before.word, before.count,
                loaded, empty.take(8 * middle.advanced as int)));
        }
    }
    let start = model::alphabet_start(middle);
    assert(crate::dynamic_header_specs::length_header(lens, 0, 0, empty, false) =~= lens);
    assert(crate::header_producer_specs::result(start, start, empty, 4, 258,
        table, table, work, work, crate::huffman::HeaderReadOutcome::NeedAlphabet)) by {
        reveal(crate::dynamic_header_specs::prefix_fits);
        reveal(crate::header_producer_specs::result);
        reveal(crate::header_producer_specs::alphabet_result);
    }
    assert(model::composed_result(before, after, middle, empty,
        table, table, work, work, (257, 1, 4), crate::huffman::HeaderReadOutcome::NeedAlphabet)) by {
        reveal(model::composed_result);
    }
    finish(before, after, middle, empty, table, table, work, work,
        (257, 1, 4), crate::huffman::HeaderReadOutcome::NeedAlphabet);
}

}
