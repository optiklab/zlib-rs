use super::{histogram::length_histogram, slots::remaining_code_space, sorting::sort_symbols};

#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) enum LengthAnalysis {
    Empty,
    Invalid,
    Nonempty {
        count: [u16; 16],
        min: usize,
        max: usize,
    },
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lengths.len() <= u16::MAX,
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
    ensures match result {
        LengthAnalysis::Empty => huffman_specs::maximum_length(lengths@) == 0,
        LengthAnalysis::Invalid => huffman_specs::maximum_length(lengths@) > 0
            && !huffman_specs::accepted_lengths(lengths@, require_complete),
        LengthAnalysis::Nonempty { count, min, max } =>
            huffman_specs::accepted_lengths(lengths@, require_complete)
                && count@ == huffman_specs::histogram(lengths@)
                && huffman_specs::valid_histogram(lengths@, count@)
                && min == huffman_specs::minimum_length(lengths@)
                && max == huffman_specs::maximum_length(lengths@)
                && 1 <= min <= max <= 15
                && huffman_specs::remaining_histogram(count@, count@, 0)
                && huffman_specs::before(count@, min as nat) == 0
                && huffman_specs::before(count@, min as nat + 1) > 0
                && huffman_specs::normalized_cursor(count@, min as nat, 0) == 0,
    },
))]
pub(super) fn analyze_lengths(lengths: &[u16], require_complete: bool) -> LengthAnalysis {
    let (count, min, max) = length_histogram(lengths);
    if max == 0 {
        return LengthAnalysis::Empty;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(count@ =~= huffman_specs::histogram(lengths@)); }
    let left = match remaining_code_space(&count) {
        None => return LengthAnalysis::Invalid,
        Some(value) => value,
    };
    if left > 0 && (require_complete || max != 1) {
        return LengthAnalysis::Invalid;
    }
    #[cfg(verus_keep_ghost)]
    proof! { huffman_proofs::initial_symbol_state(lengths@, count@); }
    LengthAnalysis::Nonempty { count, min, max }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lengths.len() <= u16::MAX,
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
        huffman_specs::accepted_lengths(lengths@, require_complete) ==>
            work.len() >= huffman_specs::count_before(lengths@, 16),
    ensures final(work)@.len() == old(work)@.len(),
        match result {
        LengthAnalysis::Empty => huffman_specs::maximum_length(lengths@) == 0
            && final(work)@ == old(work)@,
        LengthAnalysis::Invalid => huffman_specs::maximum_length(lengths@) > 0
            && !huffman_specs::accepted_lengths(lengths@, require_complete)
            && final(work)@ == old(work)@,
        LengthAnalysis::Nonempty { count, min, max } =>
            huffman_specs::accepted_lengths(lengths@, require_complete)
                && count@ == huffman_specs::histogram(lengths@)
                && huffman_specs::valid_histogram(lengths@, count@)
                && min == huffman_specs::minimum_length(lengths@)
                && max == huffman_specs::maximum_length(lengths@)
                && 1 <= min <= max <= 15
                && huffman_specs::remaining_histogram(count@, count@, 0)
                && huffman_specs::before(count@, min as nat) == 0
                && huffman_specs::before(count@, min as nat + 1) > 0
                && huffman_specs::normalized_cursor(count@, min as nat, 0) == 0
                && huffman_specs::bucket_ordered(lengths@, count@, final(work)@)
                && forall|index: int| huffman_specs::before(count@, 16) <= index < old(work).len()
                    ==> final(work)@[index] == old(work)@[index],
    },
))]
pub(super) fn analyze_and_sort_lengths(
    lengths: &[u16],
    require_complete: bool,
    work: &mut [u16],
) -> LengthAnalysis {
    match analyze_lengths(lengths, require_complete) {
        LengthAnalysis::Nonempty { count, min, max } => {
            sort_symbols(lengths, &count, work);
            LengthAnalysis::Nonempty { count, min, max }
        }
        LengthAnalysis::Empty => LengthAnalysis::Empty,
        LengthAnalysis::Invalid => LengthAnalysis::Invalid,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn classify_complete_empty_and_invalid_lengths() {
        assert!(matches!(
            analyze_lengths(&[0, 0], true),
            LengthAnalysis::Empty
        ));
        assert!(matches!(
            analyze_lengths(&[1, 1, 1], false),
            LengthAnalysis::Invalid
        ));
        assert!(matches!(
            analyze_lengths(&[2], false),
            LengthAnalysis::Invalid
        ));
        assert!(matches!(
            analyze_lengths(&[1], true),
            LengthAnalysis::Invalid
        ));
        assert!(matches!(
            analyze_lengths(&[1], false),
            LengthAnalysis::Nonempty { min: 1, max: 1, .. }
        ));
        assert!(matches!(
            analyze_lengths(&[1, 1], true),
            LengthAnalysis::Nonempty { min: 1, max: 1, .. }
        ));
    }

    #[test]
    fn classifier_supplies_stable_table_input() {
        let mut work = [u16::MAX; 3];
        assert!(matches!(
            analyze_and_sort_lengths(&[2, 0, 1, 2], true, &mut work),
            LengthAnalysis::Nonempty { min: 1, max: 2, .. }
        ));
        assert_eq!(work, [2, 0, 3]);
    }

    #[test]
    fn empty_and_invalid_lengths_leave_workspace_unchanged() {
        let mut work = [42; 1];
        assert!(matches!(
            analyze_and_sort_lengths(&[0, 0], true, &mut work),
            LengthAnalysis::Empty
        ));
        assert_eq!(work, [42; 1]);
        assert!(matches!(
            analyze_and_sort_lengths(&[1, 1, 1], false, &mut work),
            LengthAnalysis::Invalid
        ));
        assert_eq!(work, [42; 1]);
    }
}
