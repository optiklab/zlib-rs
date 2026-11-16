use super::{analysis, entries, layout, CodeType, InflateTable};
use crate::{Code, ENOUGH_DISTS, ENOUGH_LENS};

#[cfg(verus_keep_ghost)]
use crate::{huffman_specs, table_preparation_specs as model};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum TablePreparation {
    Finished(InflateTable),
    Ready {
        count: [u16; 16],
        min: usize,
        max: usize,
        root: usize,
        used: usize,
        base: &'static [u16],
        extra: &'static [u8],
        threshold: u16,
    },
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires min <= max,
    ensures result == model::clamped_root(requested as nat, min as nat, max as nat),
        min <= result <= max,
))]
pub(super) fn clamped_root(requested: usize, min: usize, max: usize) -> usize {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(model::clamped_root); }
    Ord::min(Ord::max(requested, min), max)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == model::root_capacity_allowed(entries::alphabet(kind), used as nat),
))]
pub(super) fn root_capacity_allowed(kind: &CodeType, used: usize) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(model::root_capacity_allowed); }
    if matches!(kind, CodeType::Lens) && used > ENOUGH_LENS {
        return false;
    }
    if matches!(kind, CodeType::Dists) && used > ENOUGH_DISTS {
        return false;
    }
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lens.len() <= u16::MAX,
        forall|index: int| 0 <= index < lens.len() ==> lens@[index] <= 15,
        table.len() >= 2,
        huffman_specs::accepted_lengths(lens@, matches!(kind, CodeType::Codes)) ==>
            work.len() >= huffman_specs::count_before(lens@, 16),
    ensures model::result(entries::alphabet(kind), lens@, requested as nat,
        old(table)@, final(table)@, old(work)@, final(work)@, result),
))]
pub(super) fn prepare_table(
    kind: &CodeType,
    lens: &[u16],
    table: &mut [Code],
    requested: usize,
    work: &mut [u16],
) -> TablePreparation {
    let (count, min, max) =
        match analysis::analyze_and_sort_lengths(lens, matches!(kind, CodeType::Codes), work) {
            analysis::LengthAnalysis::Empty => {
                let code = Code {
                    op: 64,
                    bits: 1,
                    val: 0,
                };
                table[0] = code;
                table[1] = code;
                return TablePreparation::Finished(InflateTable::Success { root: 1, used: 2 });
            }
            analysis::LengthAnalysis::Invalid => {
                return TablePreparation::Finished(InflateTable::InvalidCode)
            }
            analysis::LengthAnalysis::Nonempty { count, min, max } => (count, min, max),
        };
    let root = clamped_root(requested, min, max);
    let (base, extra, threshold) = entries::table_parameters(kind);
    let layout = layout::root_layout(root);
    if !root_capacity_allowed(kind, layout.used) {
        return TablePreparation::Finished(InflateTable::EnoughIsNotEnough);
    }
    TablePreparation::Ready {
        count,
        min,
        max,
        root,
        used: layout.used,
        base,
        extra,
        threshold,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_invalid_and_single_bit_preparation_keep_distinct_storage_frames() {
        let sentinel = Code {
            op: 0,
            bits: 3,
            val: 99,
        };
        for kind in [CodeType::Codes, CodeType::Lens, CodeType::Dists] {
            for lengths in [&[0, 0][..], &[1, 1, 1], &[2], &[1]] {
                let mut table = [sentinel; 16];
                let mut work = [42; 19];
                let outcome = prepare_table(&kind, lengths, &mut table, usize::MAX, &mut work);
                if lengths == [0, 0] {
                    assert!(matches!(
                        outcome,
                        TablePreparation::Finished(InflateTable::Success { root: 1, used: 2 })
                    ));
                    assert_eq!(
                        &table[..2],
                        &[Code {
                            op: 64,
                            bits: 1,
                            val: 0
                        }; 2]
                    );
                    assert!(table[2..].iter().all(|entry| *entry == sentinel));
                    assert_eq!(work, [42; 19]);
                } else if lengths == [1] && !matches!(kind, CodeType::Codes) {
                    assert!(matches!(
                        outcome,
                        TablePreparation::Ready {
                            min: 1,
                            max: 1,
                            root: 1,
                            used: 2,
                            ..
                        }
                    ));
                    assert_eq!(table, [sentinel; 16]);
                    assert_eq!(work[0], 0);
                    assert!(work[1..].iter().all(|value| *value == 42));
                } else {
                    assert!(matches!(
                        outcome,
                        TablePreparation::Finished(InflateTable::InvalidCode)
                    ));
                    assert_eq!(table, [sentinel; 16]);
                    assert_eq!(work, [42; 19]);
                }
            }
        }
    }

    #[test]
    fn capacity_errors_follow_sorting_and_root_clamping_without_table_writes() {
        for (kind, maximum, accepted_root, limit) in [
            (CodeType::Lens, 11, 10, ENOUGH_LENS),
            (CodeType::Dists, 10, 9, ENOUGH_DISTS),
        ] {
            let mut lengths = vec![maximum as u16];
            lengths.extend(1..=maximum as u16);
            let mut expected = (1..maximum as u16).collect::<Vec<_>>();
            expected.extend([0, maximum as u16]);
            for (requested, expected_root) in [
                (0, Some(1)),
                (accepted_root, Some(accepted_root)),
                (usize::MAX, None),
            ] {
                let sentinel = Code {
                    op: 64,
                    bits: 1,
                    val: 99,
                };
                let mut table = vec![sentinel; limit];
                let original = table.clone();
                let mut work = [42; 19];
                let outcome = prepare_table(&kind, &lengths, &mut table, requested, &mut work);
                match (outcome, expected_root) {
                    (
                        TablePreparation::Ready {
                            min,
                            max,
                            root,
                            used,
                            ..
                        },
                        Some(expected),
                    ) => {
                        assert_eq!(
                            (min, max, root, used),
                            (1, maximum, expected, 1 << expected)
                        );
                    }
                    (TablePreparation::Finished(InflateTable::EnoughIsNotEnough), None) => {}
                    _ => panic!("incorrect preparation phase"),
                }
                assert_eq!(table, original);
                assert_eq!(&work[..expected.len()], expected.as_slice());
                assert!(work[expected.len()..].iter().all(|value| *value == 42));
            }
        }
    }
}
