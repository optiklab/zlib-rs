#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) struct SymbolAdvance {
    pub cursor: u32,
    pub code: u32,
    pub more: bool,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lengths.len() <= u16::MAX,
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
        huffman_specs::valid_histogram(lengths@, huffman_specs::histogram(lengths@)),
        huffman_specs::bucket_ordered(lengths@, huffman_specs::histogram(lengths@), work@),
        huffman_specs::remaining_histogram(huffman_specs::histogram(lengths@), counts@,
            *symbol as nat),
        1 <= *length <= max <= 15,
        max == huffman_specs::maximum_length(lengths@),
        huffman_specs::valid_prefix(huffman_specs::histogram(lengths@), 15),
        cursor as int == huffman_specs::normalized_cursor(huffman_specs::histogram(lengths@),
            *length as nat, *symbol as nat),
        huffman_specs::aligned_cursor(cursor, *length as u32),
        huffman_specs::before(huffman_specs::histogram(lengths@), *length as nat)
            <= *symbol
            < huffman_specs::before(huffman_specs::histogram(lengths@), *length as nat + 1),
    ensures *final(symbol) == *old(symbol) + 1,
        huffman_specs::remaining_histogram(huffman_specs::histogram(lengths@), final(counts)@,
            *final(symbol) as nat),
        result.more == (*final(symbol)
            < huffman_specs::before(huffman_specs::histogram(lengths@), 16)),
        result.cursor as int == (cursor as int
            + huffman_specs::capacity((32 - *old(length)) as nat)) % 4294967296,
        huffman_specs::is_reversal(result.cursor, result.code),
        result.code < huffman_specs::capacity(*old(length) as nat),
        result.more ==> *old(length) <= *final(length) <= max
            && huffman_specs::before(huffman_specs::histogram(lengths@),
                *final(length) as nat) <= *final(symbol)
            && *final(symbol) < huffman_specs::before(huffman_specs::histogram(lengths@),
                *final(length) as nat + 1)
            && *final(symbol) < work.len()
            && work@[*final(symbol) as int] < lengths.len()
            && lengths@[work@[*final(symbol) as int] as int] == *final(length)
            && result.cursor as int == huffman_specs::normalized_cursor(
                huffman_specs::histogram(lengths@), *final(length) as nat, *final(symbol) as nat)
            && result.cursor as int == huffman_specs::canonical_code(lengths@,
                work@[*final(symbol) as int] as int)
                    * huffman_specs::capacity((32 - *final(length)) as nat)
            && huffman_specs::aligned_cursor(result.cursor, *final(length) as u32)
            && result.code < huffman_specs::capacity(*final(length) as nat),
        !result.more ==> *final(symbol)
                == huffman_specs::before(huffman_specs::histogram(lengths@), 16)
            && *final(length) == *old(length) && *final(length) == max,
))]
pub(super) fn advance_symbol(
    lengths: &[u16],
    work: &[u16],
    counts: &mut [u16; 16],
    symbol: &mut usize,
    length: &mut usize,
    max: usize,
    cursor: u32,
) -> SymbolAdvance {
    let current = *length;
    let advanced = super::codes::next_code(cursor, current);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original = huffman_specs::histogram(lengths@);
        let ghost previous_symbol = *symbol;
        let ghost previous_counts = counts@;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::histogram_offsets(lengths@, original, 16);
        huffman_proofs::before_monotone(original, current as nat + 1, 16);
        huffman_proofs::remaining_in_bucket(original, current as nat, *symbol as nat);
        huffman_proofs::length_population_bounds(lengths@);
        assert(original[max as int] > 0);
        assert forall|level: int| max < level <= 15 implies original[level] == 0 by {
            assert(huffman_specs::occurrences(lengths@, level as u16) == 0);
        }
        huffman_proofs::before_empty_range(original, max as nat + 1, 16);
    }
    *symbol += 1;
    counts[current] -= 1;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|level: int| 1 <= level <= 15 implies
            counts@[level] == huffman_specs::remaining_count(original, level as nat,
                *symbol as nat) by {
            huffman_proofs::remaining_step(original, level as nat, current as nat,
                previous_symbol as nat);
            assert(previous_counts[level]
                == huffman_specs::remaining_count(original, level as nat,
                    previous_symbol as nat));
        }
        assert(counts@[current as int] as int
            == huffman_specs::before(original, current as nat + 1) - *symbol);
    }
    if counts[current] == 0 {
        if current == max {
            return SymbolAdvance {
                cursor: advanced.0,
                code: advanced.1,
                more: false,
            };
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            huffman_proofs::before_monotone(original, current as nat + 1, max as nat);
            let next = huffman_proofs::ordered_symbol_at(lengths@, original, work@,
                *symbol as int);
            if next <= current {
                huffman_proofs::before_monotone(original, next + 1, current as nat + 1);
            }
            assert(current < next);
            assert(original[next as int] > 0);
            assert(next <= max);
        }
        *length = lengths[work[*symbol] as usize] as usize;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(huffman_specs::bucket_entry(lengths@, original, work@, *length as int,
            *symbol as int - huffman_specs::before(original, *length as nat)));
        huffman_proofs::normalized_cursor_next(original, current as nat, *length as nat,
            previous_symbol as nat);
        huffman_proofs::normalized_cursor_bound(lengths@, original, work@, *length as nat,
            *symbol as nat);
        huffman_proofs::aligned_cursor_widen(advanced.0, current as u32, *length as u32);
        huffman_proofs::capacity_monotone(current as nat, *length as nat);
    }
    SymbolAdvance {
        cursor: advanced.0,
        code: advanced.1,
        more: true,
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::inflate::inftrees::analysis::{analyze_and_sort_lengths, LengthAnalysis};

    #[test]
    fn consumes_exactly_the_sorted_population_across_empty_buckets() {
        let lengths = [1, 0, 3, 3, 3, 3];
        let mut work = [u16::MAX; 5];
        let LengthAnalysis::Nonempty {
            mut count,
            min,
            max,
        } = analyze_and_sort_lengths(&lengths, true, &mut work)
        else {
            panic!("complete prefix code rejected");
        };
        let mut symbol = 0;
        let mut length = min;
        let mut cursor = 0;
        for expected in 1..=5 {
            let advanced = advance_symbol(
                &lengths,
                &work,
                &mut count,
                &mut symbol,
                &mut length,
                max,
                cursor,
            );
            cursor = advanced.cursor;
            assert_eq!(symbol, expected);
            assert_eq!(length, 3);
            assert_eq!(count[1], 0);
            assert_eq!(count[3], 5 - expected as u16);
            assert_eq!(advanced.more, expected < 5);
        }
        assert_eq!(count, [0; 16]);
    }

    #[test]
    fn last_symbol_does_not_read_past_the_workspace() {
        let mut count = [0; 16];
        count[1] = 1;
        let mut symbol = 0;
        let mut length = 1;
        let advanced = advance_symbol(&[0, 1], &[1], &mut count, &mut symbol, &mut length, 1, 0);
        assert!(!advanced.more);
        assert_eq!((advanced.cursor, advanced.code), (0x80000000, 1));
        assert_eq!((symbol, length, count), (1, 1, [0; 16]));
    }

    #[test]
    fn consumes_the_rfc_canonical_example_with_exact_code_words() {
        let lengths = [3, 3, 3, 3, 3, 2, 4, 4];
        let mut work = [0; 8];
        let LengthAnalysis::Nonempty {
            mut count,
            min,
            max,
        } = analyze_and_sort_lengths(&lengths, true, &mut work)
        else {
            panic!("RFC prefix code rejected");
        };
        let mut symbol = 0;
        let mut length = min;
        let mut cursor = 0;
        for (index, expected) in [
            (0x40000000, 2),
            (0x60000000, 6),
            (0x80000000, 1),
            (0xa0000000, 5),
            (0xc0000000, 3),
            (0xe0000000, 7),
            (0xf0000000, 15),
            (0, 0),
        ]
        .into_iter()
        .enumerate()
        {
            let advanced = advance_symbol(
                &lengths,
                &work,
                &mut count,
                &mut symbol,
                &mut length,
                max,
                cursor,
            );
            assert_eq!((advanced.cursor, advanced.code), expected);
            assert_eq!(advanced.more, index < 7);
            cursor = advanced.cursor;
        }
        assert_eq!(count, [0; 16]);
    }
}
