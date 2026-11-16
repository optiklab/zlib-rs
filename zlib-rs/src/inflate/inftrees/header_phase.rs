#![forbid(unsafe_code)]

use super::{DynamicHeaderOutcome, HeaderOutcome, HeaderReadOutcome};
use crate::Code;
#[cfg(verus_keep_ghost)]
use crate::{bit_specs, dynamic_header_specs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeaderPhase {
    Counts,
    Alphabet {
        counts: (usize, usize, usize),
    },
    Lengths {
        counts: (usize, usize, usize),
        root: usize,
        used: usize,
    },
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeaderStep {
    NeedCounts,
    InvalidCounts {
        counts: (usize, usize, usize),
    },
    NeedAlphabet {
        counts: (usize, usize, usize),
    },
    InvalidAlphabet {
        counts: (usize, usize, usize),
    },
    Lengths {
        counts: (usize, usize, usize),
        root: usize,
        used: usize,
        outcome: HeaderOutcome,
    },
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn valid_counts(counts: (usize, usize, usize)) -> bool {
    257 <= counts.0 <= 286 && 1 <= counts.1 <= 30 && 4 <= counts.2 <= 19
}

pub(crate) open spec fn phase_valid(
    phase: HeaderPhase, lens: Seq<u16>, have: nat, table: Seq<Code>,
) -> bool {
    match phase {
        HeaderPhase::Counts => true,
        HeaderPhase::Alphabet { counts } =>
            valid_counts(counts) && have <= counts.2
                && dynamic_header_specs::prefix_fits(lens, have),
        HeaderPhase::Lengths { counts, root, used } =>
            valid_counts(counts) && have <= counts.0 + counts.1
                && dynamic_header_specs::decoded_prefix(lens, have)
                && 1 <= root <= 7 && used <= table.len()
                && huffman_specs::capacity(root as nat) <= table.len()
                && (forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
                    ==> 1 <= (#[trigger] table[index]).bits <= root)
                && (exists|alphabet: Seq<u16>| #[trigger]
                    huffman_specs::header_decoding_table(alphabet, table, root)),
    }
}

pub(crate) open spec fn step_valid(
    step: HeaderStep, lens: Seq<u16>, have: nat, table: Seq<Code>,
) -> bool {
    match step {
        HeaderStep::NeedCounts => true,
        HeaderStep::InvalidCounts { counts } => counts.0 > 286 || counts.1 > 30,
        HeaderStep::NeedAlphabet { counts } =>
            phase_valid(HeaderPhase::Alphabet { counts }, lens, have, table)
                && have < counts.2,
        HeaderStep::InvalidAlphabet { counts } => valid_counts(counts) && have == 19,
        HeaderStep::Lengths { counts, root, used, outcome } =>
            phase_valid(HeaderPhase::Lengths { counts, root, used }, lens, have, table)
                && (outcome == HeaderOutcome::Complete || outcome == HeaderOutcome::MissingEob
                    <==> have == counts.0 + counts.1)
                && (outcome == HeaderOutcome::Complete
                    <==> have == counts.0 + counts.1 && lens[256] != 0)
                && (outcome == HeaderOutcome::MissingEob
                    <==> have == counts.0 + counts.1 && lens[256] == 0),
    }
}

pub(crate) open spec fn step_follows(phase: HeaderPhase, step: HeaderStep) -> bool {
    match phase {
        HeaderPhase::Counts => true,
        HeaderPhase::Alphabet { counts } => match step {
            HeaderStep::NeedAlphabet { counts: actual }
            | HeaderStep::InvalidAlphabet { counts: actual }
            | HeaderStep::Lengths { counts: actual, .. } => actual == counts,
            _ => false,
        },
        HeaderPhase::Lengths { counts, root, used } => match step {
            HeaderStep::Lengths { counts: actual, root: r, used: u, .. } =>
                (actual, r, u) == (counts, root, used),
            _ => false,
        },
    }
}
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lens.len() >= 316, table.len() >= 128, work.len() >= 19,
        *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
        phase_valid(phase, old(lens)@, *old(have) as nat, old(table)@),
    ensures result.0 <= input.len(), *final(count) <= 64,
        step_valid(result.1, final(lens)@, *final(have) as nat, final(table)@),
        step_follows(phase, result.1),
        *final(count) as int <= *old(count) as int + 8 * result.0 as int,
        final(lens)@.len() == old(lens)@.len(),
        final(table)@.len() == old(table)@.len(),
        final(work)@.len() == old(work)@.len(),
        forall|index: int| 19 <= index < old(lens)@.len() && *final(have) <= index
            ==> #[trigger] final(lens)@[index] == old(lens)@[index],
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        match result.1 {
            HeaderStep::NeedCounts => phase == HeaderPhase::Counts
                && *final(have) == *old(have) && final(lens)@ == old(lens)@
                && final(table)@ == old(table)@ && final(work)@ == old(work)@
                && result.0 == input.len() && *final(count) < 14,
            HeaderStep::InvalidCounts { .. } => phase == HeaderPhase::Counts
                && *final(have) == *old(have) && final(lens)@ == old(lens)@
                && final(table)@ == old(table)@ && final(work)@ == old(work)@,
            HeaderStep::NeedAlphabet { .. } =>
                final(table)@ == old(table)@ && final(work)@ == old(work)@
                    && *final(count) < 3,
            HeaderStep::InvalidAlphabet { .. } =>
                final(table)@ == old(table)@ && final(work)@ == old(work)@,
            _ => true,
        },
        match phase {
            HeaderPhase::Counts => true,
            HeaderPhase::Alphabet { counts } => match result.1 {
                HeaderStep::NeedAlphabet { counts: actual }
                | HeaderStep::InvalidAlphabet { counts: actual }
                | HeaderStep::Lengths { counts: actual, .. } => actual == counts,
                _ => false,
            },
            HeaderPhase::Lengths { counts, root, used } =>
                final(table)@ == old(table)@ && final(work)@ == old(work)@
                    && *old(have) <= *final(have)
                    && (forall|index: int| 0 <= index < old(lens)@.len()
                        && (index < *old(have) || *final(have) <= index)
                            ==> #[trigger] final(lens)@[index] == old(lens)@[index])
                    && match result.1 {
                        HeaderStep::Lengths { counts: actual, root: r, used: u, .. } =>
                            actual == counts && r == root && u == used,
                        _ => false,
                    },
        },
))]
pub(crate) fn read_header_phase(
    phase: HeaderPhase,
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lens: &mut [u16],
    have: &mut usize,
    table: &mut [Code],
    work: &mut [u16],
) -> (usize, HeaderStep) {
    let (advanced, counts, header) = match phase {
        HeaderPhase::Counts => {
            let (advanced, result) =
                super::read_dynamic_header(word, count, input, lens, have, table, work);
            match result {
                DynamicHeaderOutcome::NeedCounts => return (advanced, HeaderStep::NeedCounts),
                DynamicHeaderOutcome::InvalidCounts { counts } => {
                    return (advanced, HeaderStep::InvalidCounts { counts });
                }
                DynamicHeaderOutcome::Header { counts, outcome } => (advanced, counts, outcome),
            }
        }
        HeaderPhase::Alphabet { counts } => {
            let (advanced, header) = super::read_alphabet_header(
                word,
                count,
                input,
                lens,
                have,
                counts.2,
                counts.0 + counts.1,
                table,
                work,
            );
            (advanced, counts, header)
        }
        HeaderPhase::Lengths { counts, root, used } => {
            let (advanced, outcome) = super::resume_dynamic_header(
                word, count, input, table, root, lens, have, counts.0, counts.1,
            );
            return (
                advanced,
                HeaderStep::Lengths {
                    counts,
                    root,
                    used,
                    outcome,
                },
            );
        }
    };
    let step = match header {
        HeaderReadOutcome::NeedAlphabet => HeaderStep::NeedAlphabet { counts },
        HeaderReadOutcome::InvalidAlphabet => HeaderStep::InvalidAlphabet { counts },
        HeaderReadOutcome::Lengths {
            root,
            used,
            outcome,
        } => HeaderStep::Lengths {
            counts,
            root,
            used,
            outcome,
        },
    };
    (advanced, step)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_phases_resume_at_every_split_and_preserve_empty_retries() {
        for fixture in [
            [0x05u8, 0xc0, 0x81, 0x08, 0, 0, 0, 0, 0x20, 0x7f, 0xeb, 0x07],
            [0x05u8, 0xc1, 0x85, 0x00, 0, 0, 0, 0, 0x20, 0x7f, 0xea, 0x26],
        ] {
            for split in 1..fixture.len() {
                let sentinel = Code {
                    op: 16,
                    bits: 3,
                    val: 123,
                };
                let mut table = [sentinel; 128];
                let mut work = [42; 288];
                let mut lens = [u16::MAX; 320];
                let mut word = u64::from(fixture[0] >> 3);
                let mut count = 5;
                let mut have = 77;
                let mut phase = HeaderPhase::Counts;
                for (index, input) in [&fixture[1..split], &fixture[split..]]
                    .into_iter()
                    .enumerate()
                {
                    let (advanced, step) = read_header_phase(
                        phase, &mut word, &mut count, input, &mut lens, &mut have, &mut table,
                        &mut work,
                    );
                    assert!(advanced <= input.len());
                    phase = match step {
                        HeaderStep::NeedCounts => HeaderPhase::Counts,
                        HeaderStep::NeedAlphabet { counts } => HeaderPhase::Alphabet { counts },
                        HeaderStep::Lengths {
                            counts,
                            root,
                            used,
                            outcome,
                        } => {
                            if index == 1 {
                                assert_eq!(outcome, HeaderOutcome::Complete);
                                assert_eq!(have, counts.0 + counts.1);
                                assert_eq!(lens[256], 1);
                            } else {
                                assert_eq!(outcome, HeaderOutcome::NeedInput);
                            }
                            HeaderPhase::Lengths { counts, root, used }
                        }
                        other => panic!("unexpected header step: {other:?}"),
                    };
                    assert!(lens[have.max(19)..]
                        .iter()
                        .all(|length| *length == u16::MAX));
                    if index == 0 {
                        assert_eq!(advanced, input.len());
                        let before = (word, count, have, lens, table, work);
                        let (advanced, retry) = read_header_phase(
                            phase,
                            &mut word,
                            &mut count,
                            &[],
                            &mut lens,
                            &mut have,
                            &mut table,
                            &mut work,
                        );
                        assert_eq!(advanced, 0);
                        assert_eq!(retry, step);
                        assert_eq!((word, count, have, lens, table, work), before);
                    }
                }
            }
        }
    }

    #[test]
    fn rejected_count_and_alphabet_phases_preserve_constructor_storage() {
        let sentinel = Code {
            op: 16,
            bits: 3,
            val: 123,
        };
        let mut table = [sentinel; 128];
        let mut work = [42; 288];
        let mut lens = [u16::MAX; 320];
        let (mut word, mut count, mut have) = (30, 14, 77);
        assert_eq!(
            read_header_phase(
                HeaderPhase::Counts,
                &mut word,
                &mut count,
                &[],
                &mut lens,
                &mut have,
                &mut table,
                &mut work,
            ),
            (
                0,
                HeaderStep::InvalidCounts {
                    counts: (287, 1, 4)
                }
            )
        );
        assert_eq!((word, count, have), (0, 0, 77));
        assert_eq!(lens, [u16::MAX; 320]);
        assert_eq!(table, [sentinel; 128]);
        assert_eq!(work, [42; 288]);

        for index in [16, 17, 18, 0] {
            lens[index] = 1;
        }
        have = 4;
        assert_eq!(
            read_header_phase(
                HeaderPhase::Alphabet {
                    counts: (257, 1, 4)
                },
                &mut word,
                &mut count,
                &[],
                &mut lens,
                &mut have,
                &mut table,
                &mut work,
            ),
            (
                0,
                HeaderStep::InvalidAlphabet {
                    counts: (257, 1, 4)
                }
            )
        );
        assert_eq!(have, 19);
        assert_eq!(&lens[19..], &[u16::MAX; 301]);
        assert_eq!(table, [sentinel; 128]);
        assert_eq!(work, [42; 288]);
    }
}
