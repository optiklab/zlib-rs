use super::{inflate_table, CodeType, InflateTable};
use crate::{Code, ENOUGH_DISTS, ENOUGH_LENS};

#[cfg(verus_keep_ghost)]
use crate::{constructor_table_specs, dynamic_header_specs, huffman_proofs, huffman_specs as h};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(outcome =>
    requires 257 <= nlen <= 286, 1 <= ndist <= 30,
        nlen + ndist <= lengths.len(),
        dynamic_header_specs::decoded_prefix(lengths@, (nlen + ndist) as nat),
        lengths@[256] != 0,
    ensures constructor_table_specs::result(h::Alphabet::LiteralLengths,
            lengths@.subrange(0, nlen as int), 10,
            old(table)@, final(table)@, old(work)@, final(work)@, outcome),
        !matches!(outcome, InflateTable::EnoughIsNotEnough),
))]
pub(crate) fn inflate_completed_literal_table(
    lengths: &[u16],
    nlen: usize,
    ndist: usize,
    table: &mut [Code; ENOUGH_LENS],
    work: &mut [u16; 288],
) -> InflateTable {
    let combined = &lengths[..nlen + ndist];
    let literals = &combined[..nlen];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(literals@ =~= lengths@.subrange(0, nlen as int));
        assert forall|index: int| 0 <= index < literals.len() implies
            #[trigger] literals@[index] <= 15 by {
        }
    }
    inflate_literal_table(literals, table, work)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(outcome =>
    requires 257 <= nlen <= 286, 1 <= ndist <= 30,
        nlen + ndist <= lengths.len(),
        dynamic_header_specs::decoded_prefix(lengths@, (nlen + ndist) as nat),
        lengths@[256] != 0,
    ensures constructor_table_specs::result(h::Alphabet::Distances,
            lengths@.subrange(nlen as int, (nlen + ndist) as int), 9,
            old(table)@, final(table)@, old(work)@, final(work)@, outcome),
        !matches!(outcome, InflateTable::EnoughIsNotEnough),
))]
pub(crate) fn inflate_completed_distance_table(
    lengths: &[u16],
    nlen: usize,
    ndist: usize,
    table: &mut [Code; ENOUGH_DISTS],
    work: &mut [u16; 288],
) -> InflateTable {
    let combined = &lengths[..nlen + ndist];
    let distances = &combined[nlen..];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(distances@ =~= lengths@.subrange(nlen as int, (nlen + ndist) as int));
        assert forall|index: int| 0 <= index < distances.len() implies
            #[trigger] distances@[index] <= 15 by {
        }
    }
    inflate_distance_table(distances, table, work)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(outcome =>
    requires lengths.len() <= 286,
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
    ensures constructor_table_specs::result(h::Alphabet::LiteralLengths,
            lengths@, 10, old(table)@, final(table)@, old(work)@, final(work)@, outcome),
        !matches!(outcome, InflateTable::EnoughIsNotEnough),
        h::accepted_lengths(lengths@, false) ==> matches!(outcome, InflateTable::Success { .. }),
))]
pub(crate) fn inflate_literal_table(
    lengths: &[u16],
    table: &mut [Code; ENOUGH_LENS],
    work: &mut [u16; 288],
) -> InflateTable {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(table@.subrange(0, table@.len() as int) =~= table@);
        assert(work@.subrange(0, work@.len() as int) =~= work@);
        huffman_proofs::metadata_bounds(lengths@);
        huffman_proofs::count_before_bounds(lengths@, 16);
        if h::maximum_length(lengths@) <= 10 {
            huffman_proofs::capacity_monotone(h::maximum_length(lengths@) as nat, 10);
        }
        assert(h::capacity(10) == 1024) by (compute);
    }
    let outcome = inflate_table(CodeType::Lens, lengths, &mut table[..], 10, &mut work[..]);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(table@.subrange(0, table@.len() as int) =~= table@);
        assert(work@.subrange(0, work@.len() as int) =~= work@);
        reveal(constructor_table_specs::result);
    }
    outcome
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(outcome =>
    requires lengths.len() <= 30,
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
    ensures constructor_table_specs::result(h::Alphabet::Distances,
            lengths@, 9, old(table)@, final(table)@, old(work)@, final(work)@, outcome),
        !matches!(outcome, InflateTable::EnoughIsNotEnough),
        h::accepted_lengths(lengths@, false) ==> matches!(outcome, InflateTable::Success { .. }),
))]
pub(crate) fn inflate_distance_table(
    lengths: &[u16],
    table: &mut [Code; ENOUGH_DISTS],
    work: &mut [u16; 288],
) -> InflateTable {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(table@.subrange(0, table@.len() as int) =~= table@);
        assert(work@.subrange(0, work@.len() as int) =~= work@);
        huffman_proofs::metadata_bounds(lengths@);
        huffman_proofs::count_before_bounds(lengths@, 16);
        if h::maximum_length(lengths@) <= 9 {
            huffman_proofs::capacity_monotone(h::maximum_length(lengths@) as nat, 9);
        }
        assert(h::capacity(9) == 512) by (compute);
    }
    let outcome = inflate_table(CodeType::Dists, lengths, &mut table[..], 9, &mut work[..]);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(table@.subrange(0, table@.len() as int) =~= table@);
        assert(work@.subrange(0, work@.len() as int) =~= work@);
        reveal(constructor_table_specs::result);
    }
    outcome
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn completed_header_entries_preserve_exact_slices_and_constructor_frames() {
        let sentinel = Code {
            op: 255,
            bits: 15,
            val: u16::MAX,
        };
        for (invalid_literals, invalid_distances) in [(false, false), (true, false), (false, true)]
        {
            let mut lengths = [0; 320];
            lengths[256] = 1;
            if invalid_literals {
                lengths[..2].fill(1);
            }
            if invalid_distances {
                lengths[257..260].fill(1);
            }
            lengths[260..].fill(u16::MAX);
            let mut literal_table = [sentinel; ENOUGH_LENS];
            let mut expected_literals = literal_table;
            let mut literal_work = [99; 288];
            let mut expected_literal_work = literal_work;
            let expected = inflate_literal_table(
                &lengths[..257],
                &mut expected_literals,
                &mut expected_literal_work,
            );
            assert_eq!(
                inflate_completed_literal_table(
                    &lengths,
                    257,
                    3,
                    &mut literal_table,
                    &mut literal_work,
                ),
                expected
            );
            assert_eq!(literal_table, expected_literals);
            assert_eq!(literal_work, expected_literal_work);
            let mut distance_table = [sentinel; ENOUGH_DISTS];
            let mut expected_distances = distance_table;
            let mut distance_work = [99; 288];
            let mut expected_distance_work = distance_work;
            let expected = inflate_distance_table(
                &lengths[257..260],
                &mut expected_distances,
                &mut expected_distance_work,
            );
            assert_eq!(
                inflate_completed_distance_table(
                    &lengths,
                    257,
                    3,
                    &mut distance_table,
                    &mut distance_work,
                ),
                expected
            );
            assert_eq!(distance_table, expected_distances);
            assert_eq!(distance_work, expected_distance_work);
        }
    }

    #[test]
    fn fixed_arrays_preserve_success_and_invalid_storage_frames() {
        let sentinel = Code {
            op: 255,
            bits: 15,
            val: u16::MAX,
        };
        for lengths in [&[1u16, 1][..], &[1u16, 1, 1][..]] {
            let mut literals = [sentinel; ENOUGH_LENS];
            let mut distances = [sentinel; ENOUGH_DISTS];
            let mut literal_work = [99; 288];
            let mut distance_work = [99; 288];
            let expected = if lengths.len() == 2 {
                InflateTable::Success { root: 1, used: 2 }
            } else {
                InflateTable::InvalidCode
            };
            assert_eq!(
                inflate_literal_table(lengths, &mut literals, &mut literal_work),
                expected
            );
            assert_eq!(
                inflate_distance_table(lengths, &mut distances, &mut distance_work),
                expected
            );
            if lengths.len() == 2 {
                assert_eq!(&literal_work[..2], &[0, 1]);
                assert_eq!(&distance_work[..2], &[0, 1]);
            } else {
                assert_eq!(&literals[..2], &[sentinel; 2]);
                assert_eq!(&distances[..2], &[sentinel; 2]);
                assert_eq!(&literal_work[..2], &[99; 2]);
                assert_eq!(&distance_work[..2], &[99; 2]);
            }
            assert!(literals[2..].iter().all(|entry| *entry == sentinel));
            assert!(distances[2..].iter().all(|entry| *entry == sentinel));
            assert!(literal_work[2..].iter().all(|symbol| *symbol == 99));
            assert!(distance_work[2..].iter().all(|symbol| *symbol == 99));
        }
    }
}
