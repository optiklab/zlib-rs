use crate::huffman::{InflateTable, TablePreparation};
use crate::huffman_specs as h;
use crate::Code;
use vstd::prelude::*;

verus! {

pub open spec fn require_complete(alphabet: h::Alphabet) -> bool {
    matches!(alphabet, h::Alphabet::CodeLengths)
}

#[verifier::opaque]
pub open spec fn root_capacity_allowed(alphabet: h::Alphabet, used: nat) -> bool {
    match alphabet {
        h::Alphabet::CodeLengths => true,
        h::Alphabet::LiteralLengths => used <= 1332,
        h::Alphabet::Distances => used <= 592,
    }
}

#[verifier::opaque]
pub open spec fn clamped_root(requested: nat, minimum: nat, maximum: nat) -> nat {
    if requested < minimum { minimum }
    else if requested > maximum { maximum }
    else { requested }
}

pub open spec fn sorted_workspace(lengths: Seq<u16>, before: Seq<u16>,
    after: Seq<u16>) -> bool {
    after.len() == before.len()
        && h::bucket_ordered(lengths, h::histogram(lengths), after)
        && forall|index: int| h::before(h::histogram(lengths), 16) <= index < before.len()
            ==> #[trigger] after[index] == before[index]
}

pub(crate) open spec fn empty_table(before: Seq<Code>, after: Seq<Code>) -> bool {
    after.len() == before.len() && before.len() >= 2
        && forall|index: int| 0 <= index < before.len() ==>
            #[trigger] after[index] == if index < 2 {
                Code { op: 64, bits: 1, val: 0 }
            } else { before[index] }
}

pub(crate) open spec fn result(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    before_table: Seq<Code>, table: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>,
    outcome: TablePreparation) -> bool {
    match outcome {
        TablePreparation::Finished(InflateTable::Success { root, used }) =>
            h::maximum_length(lengths) == 0 && root == 1 && used == 2
                && empty_table(before_table, table) && work == before_work,
        TablePreparation::Finished(InflateTable::InvalidCode) =>
            h::maximum_length(lengths) > 0
                && !h::accepted_lengths(lengths, require_complete(alphabet))
                && table == before_table && work == before_work,
        TablePreparation::Finished(InflateTable::EnoughIsNotEnough) =>
            h::accepted_lengths(lengths, require_complete(alphabet))
                && !root_capacity_allowed(alphabet, h::capacity(clamped_root(requested,
                    h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat)) as nat)
                && table == before_table && sorted_workspace(lengths, before_work, work),
        TablePreparation::Ready { count, min, max, root, used, base, extra, threshold } =>
            h::accepted_lengths(lengths, require_complete(alphabet))
                && count@ == h::histogram(lengths) && h::valid_histogram(lengths, count@)
                && min == h::minimum_length(lengths) && max == h::maximum_length(lengths)
                && 1 <= min <= root <= max <= 15
                && root == clamped_root(requested, min as nat, max as nat)
                && used == h::capacity(root as nat)
                && root_capacity_allowed(alphabet, used as nat)
                && h::remaining_histogram(count@, count@, 0)
                && h::before(count@, min as nat) == 0
                && h::before(count@, min as nat + 1) > 0
                && h::normalized_cursor(count@, min as nat, 0) == 0
                && table == before_table && sorted_workspace(lengths, before_work, work)
                && h::tables_match(alphabet, base@, extra@, threshold),
    }
}

}
