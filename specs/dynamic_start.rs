use crate::{
    bit_specs, dynamic_header_specs, header_loop_specs as lengths,
    header_producer_specs as alphabet, Code,
};
use vstd::prelude::*;

verus! {

// Baseline zlib compatibility policy, not the RFC's raw HDIST range.
pub(crate) open spec fn compatibility_profile(nlen: nat, ndist: nat) -> bool {
    nlen <= 286 && ndist <= 30
}

#[verifier::opaque]
pub(crate) open spec fn counts_result(before: lengths::State, after: lengths::State,
    pending: Seq<bool>, counts: Option<(usize, usize, usize)>) -> bool {
    let available = pending.len() / 8;
    let source = bit_specs::buffered_bits(before.word, before.count) + pending;
    before.advanced == 0 && before.dropped == 0 && before.count <= 64
        && after.lengths == before.lengths && after.have == before.have
        && after.advanced == if bit_specs::needed_bytes(before.count, 14) <= available {
            bit_specs::needed_bytes(before.count, 14)
        } else { available }
        && after.advanced <= available && after.count <= 64
        && counts.is_some() == (before.count as int + 8 * available >= 14)
        && after.dropped == if counts.is_some() { 14nat } else { 0nat }
        && after.count as int == before.count as int + 8 * after.advanced - after.dropped
        && (counts.is_none() ==> after.advanced == available && after.count < 14)
        && bit_specs::buffered_bits(after.word, after.count)
            + pending.skip(8 * after.advanced as int) == source.skip(after.dropped as int)
        && bit_specs::cached_suffix(after.word, after.count, pending.skip(8 * after.advanced as int))
        && (exists|loaded: u64| #[trigger] bit_specs::filled_word(before.word, before.count,
                loaded, pending.take(8 * after.advanced as int))
            && after.word == if counts.is_some() { loaded >> 14u8 } else { loaded })
        && match counts {
            Some(values) => (values.0 as nat, values.1 as nat, values.2 as nat)
                == dynamic_header_specs::header_counts(source),
            None => true,
        }
}

pub(crate) open spec fn alphabet_start(middle: lengths::State) -> lengths::State {
    lengths::state(middle.lengths, 0, middle.word, middle.count, 0, 0)
}

#[verifier::opaque]
pub(crate) open spec fn composed_result(before: lengths::State, after: lengths::State,
    middle: lengths::State, pending: Seq<bool>, before_table: Seq<Code>, table: Seq<Code>,
    before_work: Seq<u16>, work: Seq<u16>, counts: (usize, usize, usize),
    outcome: crate::huffman::HeaderReadOutcome) -> bool {
    counts_result(before, middle, pending, Some(counts))
        && compatibility_profile(counts.0 as nat, counts.1 as nat)
        && middle.advanced <= after.advanced <= pending.len() / 8
        && middle.dropped <= after.dropped
        && alphabet::result(alphabet_start(middle),
            lengths::state(after.lengths, after.have, after.word, after.count,
                (after.advanced - middle.advanced) as nat,
                (after.dropped - middle.dropped) as nat),
            pending.skip(8 * middle.advanced as int), counts.2 as nat,
            counts.0 as nat + counts.1 as nat, before_table, table, before_work, work, outcome)
}

#[verifier::opaque]
pub(crate) open spec fn result(before: lengths::State, after: lengths::State,
    pending: Seq<bool>, before_table: Seq<Code>, table: Seq<Code>,
    before_work: Seq<u16>, work: Seq<u16>,
    outcome: crate::huffman::DynamicHeaderOutcome) -> bool {
    match outcome {
        crate::huffman::DynamicHeaderOutcome::NeedCounts =>
            counts_result(before, after, pending, None)
                && table == before_table && work == before_work,
        crate::huffman::DynamicHeaderOutcome::InvalidCounts { counts } =>
            counts_result(before, after, pending, Some(counts))
                && !compatibility_profile(counts.0 as nat, counts.1 as nat)
                && table == before_table && work == before_work,
        crate::huffman::DynamicHeaderOutcome::Header { counts, outcome: decoded } =>
            exists|middle: lengths::State| #[trigger] composed_result(before, after, middle,
                pending, before_table, table, before_work, work, counts, decoded),
    }
}

}
