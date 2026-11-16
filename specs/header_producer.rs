use crate::{bit_specs, dynamic_header_specs, header_loop_specs as lengths, huffman_specs, Code};
use vstd::prelude::*;

verus! {

// Actual three-bit alphabet fields, padding, construction, and their raw state.
#[verifier::opaque]
pub(crate) open spec fn alphabet_result(before: lengths::State, after: lengths::State,
    pending: Seq<bool>, target: nat, before_table: Seq<Code>, table: Seq<Code>,
    before_work: Seq<u16>, work: Seq<u16>, built: Option<crate::huffman::InflateTable>) -> bool {
    let available = pending.len() / 8;
    let source = bit_specs::buffered_bits(before.word, before.count) + pending;
    let processed = if built.is_some() { target } else { after.have };
    before.advanced == 0 && before.dropped == 0 && before.count <= 64
        && before.have <= processed <= target <= 19
        && after.advanced <= available && after.count <= 64
        && after.advanced == if bit_specs::needed_bytes(before.count,
                (3 * (target - before.have)) as usize) <= available {
            bit_specs::needed_bytes(before.count, (3 * (target - before.have)) as usize)
        } else { available }
        && after.dropped == 3 * (processed - before.have)
        && before.count as int + 8 * after.advanced <= 64
        && after.count as int == before.count as int + 8 * after.advanced - after.dropped
        && after.lengths == dynamic_header_specs::length_header(
            before.lengths, before.have, processed, source, built.is_some())
        && dynamic_header_specs::prefix_fits(after.lengths, after.have)
        && (built.is_some() ==> after.have == 19)
        && (built.is_none() ==> after.have < target && after.count < 3)
        && bit_specs::buffered_bits(after.word, after.count)
            + pending.skip(8 * after.advanced as int) == source.skip(after.dropped as int)
        && bit_specs::cached_suffix(after.word, after.count, pending.skip(8 * after.advanced as int))
        && (exists|loaded: u64| #[trigger] bit_specs::filled_word(before.word, before.count,
                loaded, pending.take(8 * after.advanced as int))
            && after.word == loaded >> (after.dropped as u64))
        && match built {
            Some(outcome) => huffman_specs::code_length_result(after.lengths.take(19),
                before_table, table, before_work, work, outcome),
            None => table == before_table && work == before_work,
        }
}

pub(crate) open spec fn decoder_start(middle: lengths::State) -> lengths::State {
    lengths::state(middle.lengths, 0, middle.word, middle.count, 0, 0)
}

#[verifier::opaque]
pub(crate) open spec fn constructed_result(before: lengths::State, after: lengths::State,
    middle: lengths::State, pending: Seq<bool>, target: nat, total: nat,
    before_table: Seq<Code>, table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>,
    root: usize, used: usize, decoded: crate::huffman::HeaderOutcome) -> bool {
    let source = bit_specs::buffered_bits(before.word, before.count) + pending;
    alphabet_result(before, middle, pending, target, before_table, table, before_work, work,
        Some(crate::huffman::InflateTable::Success { root, used }))
        && middle.advanced <= after.advanced <= pending.len() / 8
        && middle.dropped <= after.dropped
        && lengths::header_result(middle.lengths.take(19),
            source.skip(middle.dropped as int), pending.skip(8 * middle.advanced as int),
            total, (pending.len() / 8 - middle.advanced) as nat,
            decoder_start(middle),
            lengths::state(after.lengths, after.have, after.word, after.count,
                (after.advanced - middle.advanced) as nat,
                (after.dropped - middle.dropped) as nat), decoded)
}

// One intermediate state is shared by the wire producer, table and symbol loop.
#[verifier::opaque]
pub(crate) open spec fn result(before: lengths::State, after: lengths::State,
    pending: Seq<bool>, target: nat, total: nat, before_table: Seq<Code>, table: Seq<Code>,
    before_work: Seq<u16>, work: Seq<u16>, outcome: crate::huffman::HeaderReadOutcome) -> bool {
    match outcome {
        crate::huffman::HeaderReadOutcome::NeedAlphabet =>
            alphabet_result(before, after, pending, target, before_table, table, before_work, work, None),
        crate::huffman::HeaderReadOutcome::InvalidAlphabet =>
            alphabet_result(before, after, pending, target, before_table, table, before_work, work,
                Some(crate::huffman::InflateTable::InvalidCode)),
        crate::huffman::HeaderReadOutcome::Lengths { root, used, outcome: decoded } =>
            exists|middle: lengths::State| #[trigger] constructed_result(before, after, middle,
                pending, target, total, before_table, table, before_work, work, root, used, decoded),
    }
}

}
