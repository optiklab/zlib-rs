#![forbid(unsafe_code)]

use super::{HeaderOutcome, InflateTable};
use crate::Code;
#[cfg(verus_keep_ghost)]
use crate::{
    bit_proofs, bit_specs, dynamic_header_proofs, dynamic_header_specs,
    header_loop_specs as lengths, header_producer_proofs, header_producer_specs as model,
    huffman_lookahead, huffman_specs,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum HeaderReadOutcome {
    NeedAlphabet,
    InvalidAlphabet,
    Lengths {
        root: usize,
        used: usize,
        outcome: HeaderOutcome,
    },
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::prefix_fits(old(lens)@, *old(have) as nat),
        *old(have) <= target <= 19, 257 <= total <= 320, total <= lens.len(),
        table.len() >= 128, work.len() >= 19, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(), *old(count) <= 64, *final(count) <= 64,
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
            HeaderReadOutcome::NeedAlphabet =>
                *old(have) <= *final(have) < target && *final(count) < 3
                    && dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat)
                    && result.0 == input.len() && final(table)@ == old(table)@
                    && final(work)@ == old(work)@,
            HeaderReadOutcome::InvalidAlphabet =>
                *final(have) == 19 && final(table)@ == old(table)@ && final(work)@ == old(work)@,
            HeaderReadOutcome::Lengths { root, used, outcome } =>
                *final(have) <= total && dynamic_header_specs::decoded_prefix(final(lens)@, *final(have) as nat)
                    && 1 <= root <= 7 && used <= final(table)@.len()
                    && huffman_specs::capacity(root as nat) <= final(table)@.len()
                    && (forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
                        ==> 1 <= (#[trigger] final(table)@[index]).bits <= root)
                    && (outcome == HeaderOutcome::Complete || outcome == HeaderOutcome::MissingEob
                        <==> *final(have) == total)
                    && (outcome == HeaderOutcome::Complete
                        <==> *final(have) == total && final(lens)@[256] != 0)
                    && (outcome == HeaderOutcome::MissingEob
                        <==> *final(have) == total && final(lens)@[256] == 0),
        },
        match result.1 {
            HeaderReadOutcome::Lengths { root, .. } =>
                (exists|alphabet: Seq<u16>| #[trigger]
                    huffman_specs::header_decoding_table(alphabet, final(table)@, root)),
            _ => true,
        },
        model::result(lengths::state(old(lens)@, *old(have) as nat, *old(word), *old(count), 0, 0),
            lengths::state(final(lens)@, *final(have) as nat, *final(word), *final(count), result.0 as nat,
                (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat),
            bit_specs::input_bits(input@), target as nat, total as nat,
            old(table)@, final(table)@, old(work)@, final(work)@, result.1),
))]
pub(crate) fn read_alphabet_header(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lens: &mut [u16],
    have: &mut usize,
    target: usize,
    total: usize,
    table: &mut [Code],
    work: &mut [u16],
) -> (usize, HeaderReadOutcome) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = lengths::state(lens@, *have as nat, *word, *count, 0, 0);
        let ghost pending = bit_specs::input_bits(input@);
        let ghost source = bit_specs::buffered_bits(*word, *count) + pending;
        let ghost original_table = table@;
        let ghost original_work = work@;
    }
    let (first, built) =
        super::read_code_length_table(word, count, input, lens, have, target, table, work);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost middle = lengths::state(lens@, *have as nat, *word, *count, first as nat,
            (initial.count as int + 8 * first as int - *count as int) as nat);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if bit_specs::cached_suffix(initial.word, initial.count, Seq::empty()) {
            assert(bit_specs::cached_suffix(*word, *count, Seq::empty())) by {
                reveal(bit_specs::cached_suffix);
            }
        }
        bit_proofs::header_fill_bounds(initial.count, (3 * (target - initial.have)) as usize);
        assert(pending.len() / 8 == input.len());
        let processed = if built.is_some() { target as nat } else { middle.have };
        assert(middle.dropped == 3 * (processed - initial.have));
        let loaded = choose|loaded: u64| #[trigger] bit_specs::filled_word(
            initial.word, initial.count, loaded, pending.take(8 * middle.advanced as int))
            && middle.word == loaded >> ((3 * (processed as int - initial.have as int)) as u64);
        assert(middle.word == loaded >> (middle.dropped as u64));
        assert(model::alphabet_result(initial, middle, pending, target as nat,
            original_table, table@, original_work, work@, built)) by {
            reveal(model::alphabet_result);
        }
        assert forall|index: int| 19 <= index < initial.lengths.len() implies
            #[trigger] lens@[index] == initial.lengths[index] by {
        }
    }
    let (root, used) = match built {
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                header_producer_proofs::suspend(initial, middle, pending, target as nat,
                    total as nat, original_table, table@, original_work, work@);
                reveal(dynamic_header_specs::prefix_fits);
            }
            return (first, HeaderReadOutcome::NeedAlphabet);
        }
        Some(InflateTable::Success { root, used }) => (root, used),
        Some(_) => {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(model::result); }
            return (first, HeaderReadOutcome::InvalidAlphabet);
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_lookahead::constructed_header_table(lens@.take(19),
            original_table, table@, original_work, work@, root, used);
        huffman_lookahead::constructed_root_bounds(lens@.take(19),
            original_table, table@, original_work, work@, root, used);
        dynamic_header_proofs::complete_prefix_bounded(lens@);
        assert forall|index: int| 0 <= index < 19 implies #[trigger] lens@[index] <= 7 by {
            dynamic_header_proofs::wire_inverse(index as nat);
        }
    }
    *have = 0;
    let remaining = &input[first..];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(*have as nat == model::decoder_start(middle).have);
        bit_proofs::input_suffix(input@, first as int);
        assert(remaining@ =~= input@.skip(first as int)) by {}
        assert(bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(remaining@)
            =~= source.skip(middle.dropped as int));
    }
    let (second, outcome) =
        super::read_length_header(word, count, remaining, table, root, lens, have, total);
    let advanced = first + second;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::input_bits(remaining@).skip(8 * second as int)
            =~= pending.skip(8 * (first as int + second as int)));
        assert(lengths::header_result(middle.lengths.take(19),
            source.skip(middle.dropped as int), pending.skip(8 * middle.advanced as int),
            total as nat, (pending.len() / 8 - middle.advanced) as nat,
            lengths::state(middle.lengths, 0, middle.word, middle.count, 0, 0),
            lengths::state(lens@, *have as nat, *word, *count, second as nat,
                (middle.count as int + 8 * second as int - *count as int) as nat), outcome));
        assert((initial.count as int + 8 * (first as int + second as int) - *count as int)
            - middle.dropped == middle.count as int + 8 * second as int - *count as int);
        let after = lengths::state(lens@, *have as nat, *word, *count,
            (first as nat + second as nat),
            (initial.count as int + 8 * (first as int + second as int) - *count as int) as nat);
        assert(advanced as nat == after.advanced);
        assert(model::constructed_result(initial, after, middle, pending, target as nat,
            total as nat, original_table, table@, original_work, work@, root, used, outcome)) by {
            reveal(model::constructed_result);
        }
        header_producer_proofs::finish(initial, after, middle, pending, target as nat,
            total as nat, original_table, table@, original_work, work@, root, used, outcome);
        assert(exists|alphabet: Seq<u16>| #[trigger]
            huffman_specs::header_decoding_table(alphabet, table@, root)) by {
            let alphabet = middle.lengths.take(19);
            assert(huffman_specs::header_decoding_table(alphabet, table@, root));
        }
        assert(((root as int + 0) as usize) == root);
    }
    (
        advanced,
        HeaderReadOutcome::Lengths {
            root,
            used,
            outcome,
        },
    )
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn alphabet_production_preserves_phase_precedence_and_exact_partial_state() {
        let sentinel = Code {
            op: 16,
            bits: 3,
            val: 123,
        };
        for (input, expected, final_count, final_have) in [
            (&[0x01][..], HeaderReadOutcome::NeedAlphabet, 2, 2),
            (&[0x49, 0x02][..], HeaderReadOutcome::InvalidAlphabet, 4, 19),
            (
                &[0x01, 0x02][..],
                HeaderReadOutcome::Lengths {
                    root: 1,
                    used: 2,
                    outcome: HeaderOutcome::NeedInput,
                },
                0,
                4,
            ),
            (
                &[0x01, 0x12][..],
                HeaderReadOutcome::Lengths {
                    root: 1,
                    used: 2,
                    outcome: HeaderOutcome::InvalidRepeat,
                },
                3,
                0,
            ),
        ] {
            let unconstructed = matches!(
                expected,
                HeaderReadOutcome::NeedAlphabet | HeaderReadOutcome::InvalidAlphabet
            );
            let mut lens = [9; 320];
            let mut table = [sentinel; 128];
            let mut work = [42; 19];
            let (mut word, mut count, mut have) = (0, 0, 0);
            assert_eq!(
                read_alphabet_header(
                    &mut word, &mut count, input, &mut lens, &mut have, 4, 257, &mut table,
                    &mut work
                ),
                (input.len(), expected)
            );
            assert_eq!((word, count, have), (0, final_count, final_have));
            assert_eq!(lens[19..], [9; 301]);
            if unconstructed {
                assert_eq!(table, [sentinel; 128]);
                assert_eq!(work, [42; 19]);
            } else {
                assert_eq!(
                    table[..2],
                    [
                        Code {
                            op: 0,
                            bits: 1,
                            val: 0
                        },
                        Code {
                            op: 0,
                            bits: 1,
                            val: 16
                        },
                    ]
                );
                assert_eq!(table[2..], [sentinel; 126]);
                assert_eq!(work[..2], [0, 16]);
                assert_eq!(work[2..], [42; 17]);
            }
        }
    }

    #[test]
    fn alphabet_and_decoded_lengths_consume_exactly_through_missing_eob() {
        let mut input = [0; 35];
        input[..2].copy_from_slice(&[0x01, 0x02]);
        let mut lens = [9; 320];
        let mut table = [Code {
            op: 0,
            bits: 0,
            val: 0,
        }; 128];
        let mut work = [42; 19];
        let (mut word, mut count, mut have) = (0, 0, 0);
        assert_eq!(
            read_alphabet_header(
                &mut word, &mut count, &input, &mut lens, &mut have, 4, 257, &mut table, &mut work
            ),
            (
                34,
                HeaderReadOutcome::Lengths {
                    root: 1,
                    used: 2,
                    outcome: HeaderOutcome::MissingEob
                }
            )
        );
        assert_eq!((word, count, have), (0, 3, 257));
        assert_eq!(lens[..257], [0; 257]);
        assert_eq!(lens[257..], [9; 63]);
    }
}
