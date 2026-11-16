use crate::{bit_specs, dynamic_header_specs};
use vstd::prelude::*;

verus! {

pub struct State {
    pub lengths: Seq<u16>,
    pub have: nat,
    pub word: u64,
    pub count: u8,
    pub advanced: nat,
    pub dropped: nat,
}

pub open spec fn state(lengths: Seq<u16>, have: nat, word: u64, count: u8,
    advanced: nat, dropped: nat) -> State {
    State { lengths, have, word, count, advanced, dropped }
}

// Exact register effects of one bounded field, including uncounted cached bits.
#[verifier::opaque]
pub open spec fn register_step(before: State, after: State, pending: Seq<bool>) -> bool {
    before.advanced <= after.advanced <= pending.len() / 8
        && before.count <= 64 && after.count <= 64
        && before.count as int + 8 * (after.advanced as int - before.advanced as int) <= 64
        && before.dropped <= after.dropped <= before.dropped + 14
        && after.count as int == before.count as int
            + 8 * (after.advanced as int - before.advanced as int)
            - (after.dropped as int - before.dropped as int)
        && exists|loaded: u64| #[trigger] bit_specs::filled_word(before.word, before.count, loaded,
                pending.subrange(8 * before.advanced as int, 8 * after.advanced as int))
            && after.word == loaded >> ((after.dropped - before.dropped) as u8)
}

#[verifier::opaque]
pub open spec fn register_path(path: Seq<State>, pending: Seq<bool>) -> bool {
    path.len() > 0 && forall|index: int| 0 <= index < path.len() - 1 ==>
        #[trigger] register_step(path[index], path[index + 1], pending)
}

// RFC 1951 3.2.7, with the explicit baseline empty-tree/partial-commit policy.
#[verifier::opaque]
pub open spec fn symbol_step(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, before: State, after: State, outcome: Option<bool>) -> bool {
    register_step(before, after, pending)
        && before.have < total && before.advanced <= after.advanced <= available
        && before.dropped <= after.dropped
        && dynamic_header_specs::symbol_input_transition(alphabet,
            before.lengths, after.lengths, before.have, after.have, total,
            source.skip(before.dropped as int), before.count,
            (available - before.advanced) as nat,
            (after.advanced - before.advanced) as nat,
            (after.dropped - before.dropped) as nat, outcome)
}

#[verifier::opaque]
pub open spec fn symbol_path(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, path: Seq<State>) -> bool {
    path.len() > 0 && forall|index: int| 0 <= index < path.len() - 1 ==>
        #[trigger] symbol_step(alphabet, source, pending, total, available,
            path[index], path[index + 1], Some(true))
}

// A successful prefix followed by completion or the first suspended/error field.
#[verifier::opaque]
pub open spec fn result(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, before: State, after: State, outcome: Option<bool>) -> bool {
    before.advanced == 0 && before.dropped == 0 && before.count <= 64
        && source == bit_specs::buffered_bits(before.word, before.count) + pending
        && exists|path: Seq<State>| path.len() > 0 && path[0] == before
        && symbol_path(alphabet, source, pending, total, available, path)
        && if outcome == Some(true) {
            path.last() == after && after.have == total
        } else {
            symbol_step(alphabet, source, pending, total, available, path.last(), after, outcome)
        }
}

// EOB is inspected only after all lengths, never ahead of a stopped field.
#[verifier::opaque]
pub(crate) open spec fn header_result(alphabet: Seq<u16>, source: Seq<bool>, pending: Seq<bool>, total: nat,
    available: nat, before: State, after: State, outcome: crate::huffman::HeaderOutcome) -> bool {
    match outcome {
        crate::huffman::HeaderOutcome::NeedInput =>
            result(alphabet, source, pending, total, available, before, after, None),
        crate::huffman::HeaderOutcome::InvalidRepeat =>
            result(alphabet, source, pending, total, available, before, after, Some(false)),
        crate::huffman::HeaderOutcome::MissingEob =>
            result(alphabet, source, pending, total, available, before, after, Some(true))
                && after.lengths.len() > 256 && after.lengths[256] == 0,
        crate::huffman::HeaderOutcome::Complete =>
            result(alphabet, source, pending, total, available, before, after, Some(true))
                && after.lengths.len() > 256 && after.lengths[256] != 0,
    }
}

}
