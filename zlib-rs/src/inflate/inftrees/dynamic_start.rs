#![forbid(unsafe_code)]

#[cfg(verus_keep_ghost)]
use super::HeaderOutcome;
use super::HeaderReadOutcome;
use crate::Code;
#[cfg(verus_keep_ghost)]
use crate::{
    bit_proofs, bit_specs, dynamic_start_proofs, dynamic_start_specs as model,
    header_loop_specs as lengths, header_producer_specs as alphabet,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum DynamicHeaderOutcome {
    NeedCounts,
    InvalidCounts {
        counts: (usize, usize, usize),
    },
    Header {
        counts: (usize, usize, usize),
        outcome: HeaderReadOutcome,
    },
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lens.len() >= 316, table.len() >= 128, work.len() >= 19,
        *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(), *final(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        *final(count) as int <= *old(count) as int + 8 * result.0 as int,
        final(lens)@.len() == old(lens)@.len(),
        final(table)@.len() == old(table)@.len(),
        final(work)@.len() == old(work)@.len(),
        forall|index: int| 19 <= index < old(lens)@.len() && *final(have) <= index
            ==> #[trigger] final(lens)@[index] == old(lens)@[index],
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        match result.1 {
            DynamicHeaderOutcome::NeedCounts =>
                *final(have) == *old(have) && final(lens)@ == old(lens)@
                    && final(table)@ == old(table)@ && final(work)@ == old(work)@
                    && result.0 == input.len() && *final(count) < 14,
            DynamicHeaderOutcome::InvalidCounts { counts } =>
                *final(have) == *old(have) && final(lens)@ == old(lens)@
                    && final(table)@ == old(table)@ && final(work)@ == old(work)@
                    && (counts.0 > 286 || counts.1 > 30),
            DynamicHeaderOutcome::Header { counts, outcome } =>
                257 <= counts.0 <= 286 && 1 <= counts.1 <= 30 && 4 <= counts.2 <= 19
                    && *final(have) <= counts.0 + counts.1
                    && match outcome {
                        HeaderReadOutcome::NeedAlphabet => *final(have) < counts.2
                            && *final(count) < 3
                            && crate::dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat)
                            && final(table)@ == old(table)@ && final(work)@ == old(work)@,
                        HeaderReadOutcome::InvalidAlphabet => *final(have) == 19
                            && final(table)@ == old(table)@ && final(work)@ == old(work)@,
                        HeaderReadOutcome::Lengths { root, used, outcome: decoded } =>
                            1 <= root <= 7 && used <= final(table)@.len()
                                && crate::dynamic_header_specs::decoded_prefix(final(lens)@, *final(have) as nat)
                                && crate::huffman_specs::capacity(root as nat) <= final(table)@.len()
                                && (forall|index: int| 0 <= index < crate::huffman_specs::capacity(root as nat)
                                    ==> 1 <= (#[trigger] final(table)@[index]).bits <= root)
                                && (decoded == HeaderOutcome::Complete
                                    || decoded == HeaderOutcome::MissingEob
                                    <==> *final(have) == counts.0 + counts.1)
                                && (decoded == HeaderOutcome::Complete
                                    <==> *final(have) == counts.0 + counts.1 && final(lens)@[256] != 0)
                                && (decoded == HeaderOutcome::MissingEob
                                    <==> *final(have) == counts.0 + counts.1 && final(lens)@[256] == 0),
                    },
        },
        match result.1 {
            DynamicHeaderOutcome::Header {
                outcome: HeaderReadOutcome::Lengths { root, .. }, ..
            } =>
                (exists|alphabet: Seq<u16>| #[trigger]
                    crate::huffman_specs::header_decoding_table(alphabet, final(table)@, root)),
            _ => true,
        },
        model::result(lengths::state(old(lens)@, *old(have) as nat, *old(word), *old(count), 0, 0),
            lengths::state(final(lens)@, *final(have) as nat, *final(word), *final(count),
                result.0 as nat,
                (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat),
            bit_specs::input_bits(input@), old(table)@, final(table)@,
            old(work)@, final(work)@, result.1),
))]
pub(crate) fn read_dynamic_header(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lens: &mut [u16],
    have: &mut usize,
    table: &mut [Code],
    work: &mut [u16],
) -> (usize, DynamicHeaderOutcome) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = lengths::state(lens@, *have as nat, *word, *count, 0, 0);
        let ghost pending = bit_specs::input_bits(input@);
        let ghost original_table = table@;
        let ghost original_work = work@;
    }
    let (first, counts) = super::super::header_lengths::read_counts(word, count, input);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost middle = lengths::state(lens@, *have as nat, *word, *count,
            first as nat, if counts.is_some() { 14nat } else { 0nat });
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if bit_specs::cached_suffix(initial.word, initial.count, Seq::empty()) {
            assert(((*count as int + 0) as u8) == *count);
            assert(bit_specs::cached_suffix(*word, *count, Seq::empty()));
        }
        assert(pending.len() / 8 == input.len());
        let loaded = choose|loaded: u64| #[trigger] bit_specs::filled_word(
            initial.word, initial.count, loaded, pending.take(8 * first as int))
            && middle.word == if counts.is_some() { loaded >> 14u8 } else { loaded };
        assert(model::counts_result(initial, middle, pending, counts)) by {
            reveal(model::counts_result);
        }
    }
    let Some((nlen, ndist, ncode)) = counts else {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(model::result); }
        return (first, DynamicHeaderOutcome::NeedCounts);
    };
    // TODO pkzit_bug_workaround
    if nlen > 286 || ndist > 30 {
        #[cfg(verus_keep_ghost)]
        proof! { reveal(model::result); }
        return (
            first,
            DynamicHeaderOutcome::InvalidCounts {
                counts: (nlen, ndist, ncode),
            },
        );
    }
    *have = 0;
    let remaining = &input[first..];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(*have as nat == model::alphabet_start(middle).have);
        assert(crate::dynamic_header_specs::prefix_fits(lens@, 0)) by {
            reveal(crate::dynamic_header_specs::prefix_fits);
        }
        bit_proofs::input_suffix(input@, first as int);
        assert(remaining@ =~= input@.skip(first as int));
    }
    let (second, outcome) = super::read_alphabet_header(
        word,
        count,
        remaining,
        lens,
        have,
        ncode,
        nlen + ndist,
        table,
        work,
    );
    let advanced = first + second;
    #[cfg(verus_keep_ghost)]
    proof! {
        if let HeaderReadOutcome::Lengths { root, .. } = outcome {
            assert(((root as int + 0) as usize) == root);
        }
        if outcome == HeaderReadOutcome::NeedAlphabet {
            assert(crate::dynamic_header_specs::prefix_fits(lens@, *have as nat)) by {
                reveal(crate::dynamic_header_specs::prefix_fits);
            }
        }
        assert(alphabet::result(model::alphabet_start(middle),
            lengths::state(lens@, *have as nat, *word, *count, second as nat,
                (middle.count as int + 8 * second as int - *count as int) as nat),
            pending.skip(8 * middle.advanced as int), ncode as nat, nlen as nat + ndist as nat,
            original_table, table@, original_work, work@, outcome));
        assert(bit_specs::input_bits(remaining@).skip(8 * second as int)
            =~= pending.skip(8 * (first as int + second as int)));
        assert((initial.count as int + 8 * (first as int + second as int) - *count as int)
            - middle.dropped == middle.count as int + 8 * second as int - *count as int);
        let after = lengths::state(lens@, *have as nat, *word, *count,
            first as nat + second as nat,
            (initial.count as int + 8 * (first as int + second as int) - *count as int) as nat);
        assert(advanced as nat == after.advanced);
        assert(model::composed_result(initial, after, middle, pending,
            original_table, table@, original_work, work@, (nlen, ndist, ncode), outcome)) by {
            reveal(model::composed_result);
        }
        dynamic_start_proofs::finish(initial, after, middle, pending,
            original_table, table@, original_work, work@, (nlen, ndist, ncode), outcome);
    }
    (
        advanced,
        DynamicHeaderOutcome::Header {
            counts: (nlen, ndist, ncode),
            outcome,
        },
    )
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn count_profile_preserves_raw_boundaries_and_reset_precedence() {
        let sentinel = Code {
            op: 16,
            bits: 3,
            val: 123,
        };
        for (raw, counts, accepted) in [
            (0u64, (257, 1, 4), true),
            (16317, (286, 30, 19), true),
            (30, (287, 1, 4), false),
            (960, (257, 31, 4), false),
        ] {
            let mut word = raw;
            let mut count = 14;
            let mut lens = [9u16; 316];
            let mut have = 37;
            let mut table = [sentinel; 128];
            let mut work = [42u16; 19];
            let result = read_dynamic_header(
                &mut word,
                &mut count,
                &[],
                &mut lens,
                &mut have,
                &mut table,
                &mut work,
            );
            assert_eq!(
                result,
                (
                    0,
                    if accepted {
                        DynamicHeaderOutcome::Header {
                            counts,
                            outcome: HeaderReadOutcome::NeedAlphabet,
                        }
                    } else {
                        DynamicHeaderOutcome::InvalidCounts { counts }
                    }
                )
            );
            assert_eq!((word, count, have), (0, 0, if accepted { 0 } else { 37 }));
            assert_eq!(lens, [9; 316]);
            assert_eq!(table, [sentinel; 128]);
            assert_eq!(work, [42; 19]);
        }
    }

    #[test]
    fn truncated_counts_and_alphabet_preserve_exact_phase_and_input() {
        let sentinel = Code {
            op: 16,
            bits: 3,
            val: 123,
        };
        for (input, expected, final_count, final_have) in [
            (&[0][..], DynamicHeaderOutcome::NeedCounts, 8, 37),
            (
                &[0, 0][..],
                DynamicHeaderOutcome::Header {
                    counts: (257, 1, 4),
                    outcome: HeaderReadOutcome::NeedAlphabet,
                },
                2,
                0,
            ),
            (
                &[0, 0, 0][..],
                DynamicHeaderOutcome::Header {
                    counts: (257, 1, 4),
                    outcome: HeaderReadOutcome::NeedAlphabet,
                },
                1,
                3,
            ),
            (
                &[30, 0, 0xaa][..],
                DynamicHeaderOutcome::InvalidCounts {
                    counts: (287, 1, 4),
                },
                2,
                37,
            ),
        ] {
            let mut word = 0;
            let mut count = 0;
            let mut lens = [9u16; 316];
            let mut have = 37;
            let mut table = [sentinel; 128];
            let mut work = [42u16; 19];
            let (advanced, outcome) = read_dynamic_header(
                &mut word, &mut count, input, &mut lens, &mut have, &mut table, &mut work,
            );
            assert_eq!(outcome, expected);
            assert_eq!(advanced, if input[0] == 30 { 2 } else { input.len() });
            assert_eq!((word, count, have), (0, final_count, final_have));
            for (index, value) in lens.into_iter().enumerate() {
                assert_eq!(
                    value,
                    if final_have == 3 && (16..19).contains(&index) {
                        0
                    } else {
                        9
                    }
                );
            }
            assert_eq!(table, [sentinel; 128]);
            assert_eq!(work, [42; 19]);
        }
    }
}
