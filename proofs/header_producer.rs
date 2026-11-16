use crate::{header_loop_specs as lengths, header_producer_specs as model, Code};
use vstd::prelude::*;

verus! {

pub(crate) proof fn suspend(before: lengths::State, after: lengths::State,
    pending: Seq<bool>, target: nat, total: nat,
    before_table: Seq<Code>, table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>)
    requires model::alphabet_result(before, after, pending, target,
        before_table, table, before_work, work, None),
    ensures model::result(before, after, pending, target, total,
        before_table, table, before_work, work, crate::huffman::HeaderReadOutcome::NeedAlphabet),
{
    reveal(model::result);
}

pub(crate) proof fn finish(before: lengths::State, after: lengths::State,
    middle: lengths::State, pending: Seq<bool>, target: nat, total: nat,
    before_table: Seq<Code>, table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>,
    root: usize, used: usize, outcome: crate::huffman::HeaderOutcome)
    requires model::constructed_result(before, after, middle, pending, target, total,
        before_table, table, before_work, work, root, used, outcome),
    ensures model::result(before, after, pending, target, total, before_table, table,
        before_work, work, crate::huffman::HeaderReadOutcome::Lengths { root, used, outcome }),
{
    reveal(model::result);
    let answer = crate::huffman::HeaderReadOutcome::Lengths { root, used, outcome };
    if let crate::huffman::HeaderReadOutcome::Lengths {
        root: selected_root, used: selected_used, outcome: selected_outcome
    } = answer {
        assert(model::constructed_result(before, after, middle, pending, target, total,
            before_table, table, before_work, work, selected_root, selected_used, selected_outcome));
        assert(exists|witness: lengths::State| #[trigger] model::constructed_result(
            before, after, witness, pending, target, total, before_table, table,
            before_work, work, selected_root, selected_used, selected_outcome));
    }
}

proof fn zero_bits()
    ensures forall|index: nat| index < 64 ==> !(#[trigger] crate::bit_specs::word_bit(0, index)),
        0u64 >> 0u64 == 0, 0u64 >> 12u64 == 0,
{
    assert(0u64 >> 0u64 == 0 && 0u64 >> 12u64 == 0) by (bit_vector);
    assert forall|index: nat| index < 64 implies
        !(#[trigger] crate::bit_specs::word_bit(0, index)) by {
        let shift = index as u64;
        assert((0u64 >> shift) & 1 == 0) by (bit_vector);
    }
}

pub(crate) proof fn no_input_empty_header(lens: Seq<u16>, total: nat)
    requires total > 0,
    ensures lengths::header_result(Seq::new(19, |index: int| 0u16), Seq::empty(), Seq::empty(),
        total, 0, lengths::state(lens, 0, 0, 0, 0, 0), lengths::state(lens, 0, 0, 0, 0, 0),
        crate::huffman::HeaderOutcome::NeedInput),
{
    let alphabet = Seq::new(19, |index: int| 0u16);
    let empty = Seq::empty();
    let initial = lengths::state(lens, 0, 0, 0, 0, 0);
    crate::dynamic_header_proofs::maximum_bounded(alphabet, 0);
    crate::dynamic_header_proofs::symbol_transition_without_code(alphabet, lens, 0, total, empty, 0, 0);
    zero_bits();
    assert(crate::bit_specs::buffered_bits(0, 0) =~= empty);
    assert(empty.skip(0) =~= empty);
    assert(crate::bit_specs::filled_word(0, 0, 0, empty));
    crate::header_loop_proofs::register_from_fill(initial, initial, empty, 0);
    reveal(lengths::symbol_step);
    crate::header_loop_proofs::start(initial, empty);
    crate::header_loop_proofs::finish(alphabet, empty, empty, total, 0, seq![initial], initial, None);
    reveal(lengths::header_result);
}

pub(crate) proof fn empty_alphabet_fixture()
    ensures model::result(lengths::state(Seq::new(257, |index: int| 9u16), 0, 0, 12, 0, 0),
        lengths::state(Seq::new(257, |index: int| if index < 19 { 0u16 } else { 9u16 }),
            0, 0, 0, 0, 12), Seq::empty(), 4, 257,
        Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 }),
        Seq::new(128, |index: int| if index < 2 { Code { op: 64, bits: 1, val: 0 } }
            else { Code { op: 16, bits: 3, val: 123 } }),
        Seq::new(19, |index: int| 42u16), Seq::new(19, |index: int| 42u16),
        crate::huffman::HeaderReadOutcome::Lengths {
            root: 1, used: 2, outcome: crate::huffman::HeaderOutcome::NeedInput }),
{
    let empty = Seq::empty();
    let old_lens = Seq::new(257, |index: int| 9u16);
    let lens = Seq::new(257, |index: int| if index < 19 { 0u16 } else { 9u16 });
    let before = lengths::state(old_lens, 0, 0, 12, 0, 0);
    let middle = lengths::state(lens, 19, 0, 0, 0, 12);
    let after = lengths::state(lens, 0, 0, 0, 0, 12);
    let old_table = Seq::new(128, |index: int| Code { op: 16, bits: 3, val: 123 });
    let table = Seq::new(128, |index: int| if index < 2 { Code { op: 64, bits: 1, val: 0 } }
        else { Code { op: 16, bits: 3, val: 123 } });
    let work = Seq::new(19, |index: int| 42u16);
    let alphabet = Seq::new(19, |index: int| 0u16);
    zero_bits();
    let source = crate::bit_specs::buffered_bits(0, 12);
    assert(source =~= Seq::new(12, |index: int| false));
    assert(lens.take(19) =~= alphabet);
    assert(source.skip(12) =~= empty);
    assert(source + empty =~= source);
    assert(empty.skip(0) =~= empty);
    assert(empty.take(0) =~= empty);
    assert(crate::bit_specs::buffered_bits(0, 0) =~= empty);
    assert(crate::dynamic_header_specs::length_header(old_lens, 0, 4, source, true) =~= lens) by {
        assert forall|index: int| 0 <= index < 257 implies
            crate::dynamic_header_specs::length_header(old_lens, 0, 4, source, true)[index]
                == lens[index] by {
            if index < 19 {
                crate::dynamic_header_proofs::wire_inverse(index as nat);
            }
        }
    }
    assert(crate::dynamic_header_specs::prefix_fits(lens, 19)) by {
        reveal(crate::dynamic_header_specs::prefix_fits);
        assert forall|position: nat| position < 19 implies
            #[trigger] lens[crate::dynamic_header_specs::wire_symbol(position) as int] <= 7 by {
            crate::dynamic_header_proofs::wire_roundtrip(position);
        }
    }
    crate::dynamic_header_proofs::maximum_bounded(alphabet, 0);
    assert(crate::huffman_specs::code_length_result(alphabet, old_table, table, work, work,
        crate::huffman::InflateTable::Success { root: 1, used: 2 }));
    assert(crate::bit_specs::filled_word(0, 12, 0, empty));
    reveal(crate::bit_specs::cached_suffix);
    assert(model::alphabet_result(before, middle, empty, 4, old_table, table, work, work,
        Some(crate::huffman::InflateTable::Success { root: 1, used: 2 }))) by {
        reveal(model::alphabet_result);
        assert(exists|loaded: u64| #[trigger] crate::bit_specs::filled_word(
            before.word, before.count, loaded, empty.take(8 * middle.advanced as int))
            && middle.word == loaded >> (middle.dropped as u64)) by {
            let loaded = 0u64;
            assert(crate::bit_specs::filled_word(before.word, before.count,
                loaded, empty.take(8 * middle.advanced as int)));
        }
    }
    no_input_empty_header(lens, 257);
    assert(lengths::header_result(lens.take(19), (source + empty).skip(12), empty.skip(0),
        257, 0, lengths::state(lens, 0, 0, 0, 0, 0), lengths::state(lens, 0, 0, 0, 0, 0),
        crate::huffman::HeaderOutcome::NeedInput));
    assert(model::constructed_result(before, after, middle, empty, 4, 257,
        old_table, table, work, work, 1, 2, crate::huffman::HeaderOutcome::NeedInput)) by {
        reveal(model::constructed_result);
    }
    finish(before, after, middle, empty, 4, 257, old_table, table, work, work,
        1, 2, crate::huffman::HeaderOutcome::NeedInput);
}

}
