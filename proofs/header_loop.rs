use crate::header_loop_specs as model;
use vstd::prelude::*;

verus! {

pub proof fn start(initial: model::State, pending: Seq<bool>)
    ensures model::register_path(seq![initial], pending),
        forall|alphabet: Seq<u16>, source: Seq<bool>, total: nat, available: nat|
            #[trigger] model::symbol_path(alphabet, source, pending, total, available, seq![initial]),
{
    reveal(model::register_path);
    reveal(model::symbol_path);
}

pub proof fn append_register(path: Seq<model::State>, next: model::State, pending: Seq<bool>)
    requires model::register_path(path, pending),
        model::register_step(path.last(), next, pending),
    ensures model::register_path(path.push(next), pending),
{
    reveal(model::register_path);
    assert forall|index: int| 0 <= index < path.push(next).len() - 1 implies
        #[trigger] model::register_step(path.push(next)[index], path.push(next)[index + 1], pending) by {
        if index < path.len() - 1 {
        } else {
            assert(index == path.len() - 1);
        }
    }
}

pub proof fn register_from_fill(before: model::State, after: model::State,
    pending: Seq<bool>, loaded: u64)
    requires before.advanced <= after.advanced <= pending.len() / 8,
        before.count <= 64, after.count <= 64,
        before.count as int + 8 * (after.advanced as int - before.advanced as int) <= 64,
        before.dropped <= after.dropped <= before.dropped + 14,
        after.count as int == before.count as int
            + 8 * (after.advanced as int - before.advanced as int)
            - (after.dropped as int - before.dropped as int),
        crate::bit_specs::filled_word(before.word, before.count, loaded,
            pending.subrange(8 * before.advanced as int, 8 * after.advanced as int)),
        after.word == loaded >> ((after.dropped - before.dropped) as u8),
    ensures model::register_step(before, after, pending),
{
    reveal(model::register_step);
}

pub proof fn append_symbol(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, path: Seq<model::State>, next: model::State)
    requires model::symbol_path(alphabet, source, pending, total, available, path),
        model::symbol_step(alphabet, source, pending, total, available, path.last(), next, Some(true)),
    ensures model::symbol_path(alphabet, source, pending, total, available, path.push(next)),
{
    reveal(model::symbol_path);
    assert forall|index: int| 0 <= index < path.push(next).len() - 1 implies
        #[trigger] model::symbol_step(alphabet, source, pending, total, available,
            path.push(next)[index], path.push(next)[index + 1], Some(true)) by {
        if index < path.len() - 1 {
        } else {
            assert(index == path.len() - 1);
        }
    }
}

pub proof fn finish(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, path: Seq<model::State>, next: model::State, outcome: Option<bool>)
    requires path.len() > 0,
        path[0].advanced == 0, path[0].dropped == 0, path[0].count <= 64,
        source == crate::bit_specs::buffered_bits(path[0].word, path[0].count) + pending,
        model::symbol_path(alphabet, source, pending, total, available, path),
        outcome == Some(true) ==> path.last() == next && next.have == total,
        outcome != Some(true) ==>
            model::symbol_step(alphabet, source, pending, total, available, path.last(), next, outcome),
    ensures model::result(alphabet, source, pending, total, available, path[0], next, outcome),
{
    reveal(model::result);
}

pub proof fn prefix(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>,
    total: nat, available: nat, path: Seq<model::State>)
    requires path.len() > 1,
        model::symbol_path(alphabet, source, pending, total, available, path),
    ensures model::symbol_path(alphabet, source, pending, total, available, path.drop_last()),
{
    reveal(model::symbol_path);
    assert forall|index: int| 0 <= index < path.drop_last().len() - 1 implies
        #[trigger] model::symbol_step(alphabet, source, pending, total, available,
            path.drop_last()[index], path.drop_last()[index + 1], Some(true)) by {
    }
}

pub proof fn empty_path_zero(source: Seq<bool>, pending: Seq<bool>,
    total: nat, available: nat, path: Seq<model::State>)
    requires path.len() > 0, path[0].have == 0,
        model::symbol_path(Seq::new(19, |index: int| 0u16),
            source, pending, total, available, path),
    ensures forall|index: int| 0 <= index < path.last().lengths.len()
        && index < path.last().have ==> #[trigger] path.last().lengths[index] == 0,
    decreases path.len(),
{
    if path.len() > 1 {
        let alphabet = Seq::new(19, |index: int| 0u16);
        prefix(alphabet, source, pending, total, available, path);
        empty_path_zero(source, pending, total, available, path.drop_last());
        let before = path[path.len() - 2];
        let after = path.last();
        assert(before == path.drop_last().last());
        assert(after == path[path.len() - 1]);
        reveal(model::symbol_path);
        assert(model::symbol_step(alphabet, source, pending, total, available,
            path[path.len() - 2], path[(path.len() - 2) + 1], Some(true)));
        assert(model::symbol_step(alphabet, source, pending, total, available,
            before, after, Some(true)));
        reveal(model::symbol_step);
        crate::dynamic_header_proofs::maximum_bounded(alphabet, 0);
        reveal(crate::dynamic_header_specs::symbol_input_transition);
        reveal(crate::dynamic_header_specs::symbol_input_effect);
        assert(after.have == before.have + 1);
        assert forall|index: int| 0 <= index < after.lengths.len() && index < after.have implies
            #[trigger] after.lengths[index] == 0 by {
            if index != before.have {
                assert(index < before.have);
                assert(before.lengths[index] == 0);
            }
        }
    }
}

pub(crate) proof fn header_completion_fixture()
    ensures model::header_result(Seq::new(19, |index: int| 0u16), Seq::empty(), Seq::empty(), 257, 0,
            model::state(Seq::new(257, |index: int| 0u16), 257, 0, 0, 0, 0),
            model::state(Seq::new(257, |index: int| 0u16), 257, 0, 0, 0, 0),
            crate::huffman::HeaderOutcome::MissingEob),
        model::header_result(Seq::new(19, |index: int| 0u16), Seq::empty(), Seq::empty(), 257, 0,
            model::state(Seq::new(257, |index: int| if index == 256 { 1u16 } else { 0u16 }),
                257, 0, 0, 0, 0),
            model::state(Seq::new(257, |index: int| if index == 256 { 1u16 } else { 0u16 }),
                257, 0, 0, 0, 0), crate::huffman::HeaderOutcome::Complete),
{
    let alphabet = Seq::new(19, |index: int| 0u16);
    let empty = Seq::empty();
    let missing = model::state(Seq::new(257, |index: int| 0u16), 257, 0, 0, 0, 0);
    let complete = model::state(Seq::new(257, |index: int|
        if index == 256 { 1u16 } else { 0u16 }), 257, 0, 0, 0, 0);
    assert(crate::bit_specs::buffered_bits(0, 0) =~= empty);
    start(missing, empty);
    finish(alphabet, empty, empty, 257, 0, seq![missing], missing, Some(true));
    start(complete, empty);
    finish(alphabet, empty, empty, 257, 0, seq![complete], complete, Some(true));
    reveal(model::header_result);
}

pub(crate) proof fn stopped_header_fixture()
    ensures model::header_result(Seq::new(19, |index: int| 0u16), Seq::empty(), Seq::empty(), 257, 0,
            model::state(Seq::new(257, |index: int| 0u16), 0, 0, 0, 0, 0),
            model::state(Seq::new(257, |index: int| 0u16), 0, 0, 0, 0, 0),
            crate::huffman::HeaderOutcome::NeedInput),
        model::header_result(seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![true,false,false], Seq::empty(), 257, 0,
            model::state(Seq::new(257, |index: int| 0u16), 0, 1, 3, 0, 0),
            model::state(Seq::new(257, |index: int| 0u16), 0, 0, 2, 0, 1),
            crate::huffman::HeaderOutcome::InvalidRepeat),
{
    let alphabet = Seq::new(19, |index: int| 0u16);
    let empty = Seq::empty();
    let lengths = Seq::new(257, |index: int| 0u16);
    let initial = model::state(lengths, 0, 0, 0, 0, 0);
    crate::dynamic_header_proofs::maximum_bounded(alphabet, 0);
    crate::dynamic_header_proofs::symbol_transition_without_code(alphabet, lengths, 0, 257, empty, 0, 0);
    fixture_bits();
    assert(0u64 >> 0u8 == 0) by (bit_vector);
    assert(crate::bit_specs::buffered_bits(0, 0) =~= empty);
    assert(crate::bit_specs::filled_word(0, 0, 0, empty));
    register_from_fill(initial, initial, empty, 0);
    assert(empty.skip(0) =~= empty);
    reveal(model::symbol_step);
    start(initial, empty);
    finish(alphabet, empty, empty, 257, 0, seq![initial], initial, None);
    let alphabet = seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0];
    let source = seq![true,false,false];
    let before = model::state(lengths, 0, 1, 3, 0, 0);
    let after = model::state(lengths, 0, 0, 2, 0, 1);
    crate::dynamic_header_proofs::two_symbol_header_codes();
    assert(1u64 >> 1u8 == 0) by (bit_vector);
    assert(source.skip(0) =~= source);
    assert(crate::bit_specs::buffered_bits(1, 3) =~= source);
    assert(crate::bit_specs::filled_word(1, 3, 1, empty));
    register_from_fill(before, after, empty, 1);
    assert(crate::huffman_specs::code_length_source_prefix(alphabet, 16, source)) by {
        reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    }
    assert(crate::dynamic_header_specs::symbol_input_effect(lengths, lengths,
        0, 0, 257, source, 3, 0, 1, 16, 0, 1, Some(false))) by {
        reveal(crate::dynamic_header_specs::symbol_input_effect);
    }
    step_from_effect(alphabet, source, empty, 257, 0, before, after, 16, Some(false));
    start(before, empty);
    finish(alphabet, source, empty, 257, 0, seq![before], after, Some(false));
    reveal(model::header_result);
}

pub(crate) proof fn empty_header_rejected(source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, before: model::State, after: model::State, outcome: crate::huffman::HeaderOutcome)
    requires before.have == 0, total > 256,
        model::header_result(Seq::new(19, |index: int| 0u16), source, pending,
            total, available, before, after, outcome),
    ensures outcome != crate::huffman::HeaderOutcome::Complete,
{
    if outcome == crate::huffman::HeaderOutcome::Complete {
        reveal(model::header_result);
        reveal(model::result);
        empty_result_missing_eob(source, pending, total, available, before, after);
    }
}

pub proof fn empty_result_missing_eob(source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, before: model::State, after: model::State)
    requires before.have == 0, after.have > 256, after.lengths.len() > 256,
        model::result(Seq::new(19, |index: int| 0u16), source, pending,
            total, available, before, after, Some(true)),
    ensures after.lengths[256] == 0,
{
    reveal(model::result);
    let path = choose|path: Seq<model::State>| path.len() > 0 && path[0] == before
        && model::symbol_path(Seq::new(19, |index: int| 0u16),
            source, pending, total, available, path)
        && path.last() == after && after.have == total;
    empty_path_zero(source, pending, total, available, path);
}

proof fn fixture_bits()
    ensures forall|index: nat| index < 64 ==>
            !(#[trigger] crate::bit_specs::word_bit(0, index)),
        forall|index: nat| index < 64 ==>
            (#[trigger] crate::bit_specs::word_bit(1, index)) == (index == 0),
        forall|index: nat| index < 64 ==>
            (#[trigger] crate::bit_specs::word_bit(2, index)) == (index == 1),
        2u64 >> 1u8 == 1, 1u64 >> 3u8 == 0, 1u64 >> 0u8 == 1,
{
    assert(2u64 >> 1u8 == 1 && 1u64 >> 3u8 == 0 && 1u64 >> 0u8 == 1) by (bit_vector);
    assert forall|index: nat| index < 64 implies
        !(#[trigger] crate::bit_specs::word_bit(0, index)) by {
        let shift = index as u64;
        assert((0u64 >> shift) & 1 == 0) by (bit_vector);
    }
    assert forall|index: nat| index < 64 implies
        (#[trigger] crate::bit_specs::word_bit(1, index)) == (index == 0) by {
        let shift = index as u64;
        assert(((1u64 >> shift) & 1 == 1) == (shift == 0))
            by (bit_vector) requires shift < 64;
    }
    assert forall|index: nat| index < 64 implies
        (#[trigger] crate::bit_specs::word_bit(2, index)) == (index == 1) by {
        let shift = index as u64;
        assert(((2u64 >> shift) & 1 == 1) == (shift == 1))
            by (bit_vector) requires shift < 64;
    }
}

proof fn step_from_effect(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>,
    total: nat, available: nat, before: model::State, after: model::State,
    symbol: nat, outcome: Option<bool>)
    requires model::register_step(before, after, pending), before.have < total,
        before.advanced <= after.advanced <= available, before.dropped <= after.dropped,
        crate::huffman_specs::maximum_length(alphabet) > 0,
        crate::huffman_specs::code_length_source_prefix(alphabet, symbol as int,
            source.skip(before.dropped as int)),
        crate::dynamic_header_specs::symbol_input_effect(
            before.lengths, after.lengths, before.have, after.have, total,
            source.skip(before.dropped as int), before.count,
            (available - before.advanced) as nat, alphabet[symbol as int] as nat, symbol,
            (after.advanced - before.advanced) as nat,
            (after.dropped - before.dropped) as nat, outcome),
    ensures model::symbol_step(alphabet, source, pending, total, available, before, after, outcome),
{
    crate::dynamic_header_proofs::symbol_transition_from_effect(alphabet,
        before.lengths, after.lengths, before.have, after.have, total,
        source.skip(before.dropped as int), before.count,
        (available - before.advanced) as nat, alphabet[symbol as int] as nat, symbol,
        (after.advanced - before.advanced) as nat,
        (after.dropped - before.dropped) as nat, outcome);
    reveal(model::symbol_step);
}

pub proof fn completed_repeat_fixture()
    ensures model::result(
        seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
        seq![false,true,false,false,false,false,false,false],
        seq![false,true,false,false,false,false,false,false], 5, 1,
        model::state(seq![7u16,9,9,9,9], 1, 0, 0, 0, 0),
        model::state(seq![7u16,0,0,0,0], 5, 0, 4, 1, 4), Some(true)),
{
    let alphabet = seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0];
    let source = seq![false,true,false,false,false,false,false,false];
    assert(source.skip(0) =~= source);
    let initial = model::state(seq![7u16,9,9,9,9], 1, 0, 0, 0, 0);
    let middle = model::state(seq![7u16,0,9,9,9], 2, 1, 7, 1, 1);
    let final_state = model::state(seq![7u16,0,0,0,0], 5, 0, 4, 1, 4);
    crate::dynamic_header_proofs::two_symbol_header_codes();
    fixture_bits();
    assert(crate::bit_specs::filled_word(0, 0, 2, source));
    assert(crate::bit_specs::filled_word(1, 7, 1, Seq::empty()));
    register_from_fill(initial, middle, source, 2);
    register_from_fill(middle, final_state, source, 1);
    assert(crate::huffman_specs::code_length_source_prefix(alphabet, 0, source)
        && crate::huffman_specs::code_length_source_prefix(alphabet, 16, source.skip(1))) by {
        reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    }
    assert(crate::dynamic_header_specs::symbol_input_effect(initial.lengths, middle.lengths,
            1, 2, 5, source, 0, 1, 1, 0, 1, 1, Some(true))
        && crate::dynamic_header_specs::symbol_input_effect(middle.lengths, final_state.lengths,
            2, 5, 5, source.skip(1), 7, 0, 1, 16, 0, 3, Some(true))) by {
        reveal(crate::dynamic_header_specs::symbol_input_effect);
        reveal(crate::dynamic_header_specs::repeat_extra_value);
        reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    }
    step_from_effect(alphabet, source, source, 5, 1, initial, middle, 0, Some(true));
    step_from_effect(alphabet, source, source, 5, 1, middle, final_state, 16, Some(true));
    start(initial, source);
    let path = seq![initial];
    append_symbol(alphabet, source, source, 5, 1, path, middle);
    let path = path.push(middle);
    append_symbol(alphabet, source, source, 5, 1, path, final_state);
    let path = path.push(final_state);
    finish(alphabet, source, source, 5, 1, path, final_state, Some(true));
}

pub proof fn partial_prefix_fixture()
    ensures model::result(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![false,true], Seq::empty(), 5, 0,
            model::state(seq![7u16,9,9,9,9], 1, 2, 2, 0, 0),
            model::state(seq![7u16,0,9,9,9], 2, 1, 1, 0, 1), None),
        model::result(
            seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0],
            seq![false,true,false,false], Seq::empty(), 4, 0,
            model::state(seq![7u16,9,9,9,9], 1, 2, 4, 0, 0),
            model::state(seq![7u16,0,9,9,9], 2, 0, 0, 0, 4), Some(false)),
{
    let alphabet = seq![1u16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0];
    crate::dynamic_header_proofs::two_symbol_header_codes();
    fixture_bits();
    let pending = Seq::empty();
    let short = seq![false,true];
    assert(short.skip(0) =~= short);
    let first = model::state(seq![7u16,9,9,9,9], 1, 2, 2, 0, 0);
    let second = model::state(seq![7u16,0,9,9,9], 2, 1, 1, 0, 1);
    assert(crate::bit_specs::buffered_bits(2, 2) =~= short);
    assert(crate::bit_specs::filled_word(2, 2, 2, pending));
    assert(crate::bit_specs::filled_word(1, 1, 1, pending));
    register_from_fill(first, second, pending, 2);
    register_from_fill(second, second, pending, 1);
    assert(crate::huffman_specs::code_length_source_prefix(alphabet, 0, short)
        && crate::huffman_specs::code_length_source_prefix(alphabet, 16, short.skip(1))) by {
        reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    }
    assert(crate::dynamic_header_specs::symbol_input_effect(first.lengths, second.lengths,
            1, 2, 5, short, 2, 0, 1, 0, 0, 1, Some(true))
        && crate::dynamic_header_specs::symbol_input_effect(second.lengths, second.lengths,
            2, 2, 5, short.skip(1), 1, 0, 1, 16, 0, 0, None)) by {
        reveal(crate::dynamic_header_specs::symbol_input_effect);
    }
    step_from_effect(alphabet, short, pending, 5, 0, first, second, 0, Some(true));
    step_from_effect(alphabet, short, pending, 5, 0, second, second, 16, None);
    start(first, pending);
    let path = seq![first];
    append_symbol(alphabet, short, pending, 5, 0, path, second);
    let path = path.push(second);
    finish(alphabet, short, pending, 5, 0, path, second, None);
    let full = seq![false,true,false,false];
    assert(full.skip(0) =~= full);
    let first = model::state(seq![7u16,9,9,9,9], 1, 2, 4, 0, 0);
    let second = model::state(seq![7u16,0,9,9,9], 2, 1, 3, 0, 1);
    let last = model::state(seq![7u16,0,9,9,9], 2, 0, 0, 0, 4);
    assert(crate::bit_specs::buffered_bits(2, 4) =~= full);
    assert(crate::bit_specs::filled_word(2, 4, 2, pending));
    assert(crate::bit_specs::filled_word(1, 3, 1, pending));
    register_from_fill(first, second, pending, 2);
    register_from_fill(second, last, pending, 1);
    assert(crate::huffman_specs::code_length_source_prefix(alphabet, 0, full)
        && crate::huffman_specs::code_length_source_prefix(alphabet, 16, full.skip(1))) by {
        reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    }
    assert(crate::dynamic_header_specs::symbol_input_effect(first.lengths, second.lengths,
            1, 2, 4, full, 4, 0, 1, 0, 0, 1, Some(true))
        && crate::dynamic_header_specs::symbol_input_effect(second.lengths, last.lengths,
            2, 2, 4, full.skip(1), 3, 0, 1, 16, 0, 3, Some(false))) by {
        reveal(crate::dynamic_header_specs::symbol_input_effect);
        reveal(crate::dynamic_header_specs::repeat_extra_value);
        reveal_with_fuel(crate::bit_specs::low_first_value, 3);
    }
    step_from_effect(alphabet, full, pending, 4, 0, first, second, 0, Some(true));
    step_from_effect(alphabet, full, pending, 4, 0, second, last, 16, Some(false));
    start(first, pending);
    let path = seq![first];
    append_symbol(alphabet, full, pending, 4, 0, path, second);
    let path = path.push(second);
    finish(alphabet, full, pending, 4, 0, path, last, Some(false));
}

}
