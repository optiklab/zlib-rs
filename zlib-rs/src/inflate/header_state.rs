#![forbid(unsafe_code)]

#[cfg(not(verus_keep_ghost))]
use super::inftrees::{read_header_phase, HeaderOutcome, HeaderPhase, HeaderStep};
use crate::Code;
#[cfg(verus_keep_ghost)]
use crate::{
    bit_specs,
    huffman::{header_phase, read_header_phase, HeaderOutcome, HeaderPhase, HeaderStep},
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum Mode {
    Head,
    Flags,
    Time,
    Os,
    ExLen,
    Extra,
    Name,
    Comment,
    HCrc,
    Sync,
    Mem,
    Length,
    Type,
    TypeDo,
    Stored,
    CopyBlock,
    Check,
    Len_,
    Len,
    Lit,
    LenExt,
    Dist,
    DistExt,
    Match,
    Table,
    LenLens,
    CodeLens,
    DictId,
    Dict,
    Done,
    Bad,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Default, Clone, Copy)]
#[allow(clippy::enum_variant_names)]
pub(crate) enum Codes {
    #[default]
    Fixed,
    Codes,
    Len,
    Dist,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Default, Clone, Copy)]
pub(crate) struct Table {
    pub(crate) codes: Codes,
    pub(crate) bits: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeaderAction {
    NeedInput,
    InvalidCounts,
    InvalidAlphabet,
    InvalidRepeat,
    MissingEob,
    Complete,
}

impl HeaderAction {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match self {
            HeaderAction::InvalidCounts => result == Some("too many length or distance symbols\0"),
            HeaderAction::InvalidAlphabet => result == Some("invalid code lengths set\0"),
            HeaderAction::InvalidRepeat => result == Some("invalid bit length repeat\0"),
            HeaderAction::MissingEob => result == Some("invalid code -- missing end-of-block\0"),
            _ => result == None,
        },
    ))]
    pub(crate) fn error_message(self) -> Option<&'static str> {
        match self {
            Self::InvalidCounts => Some("too many length or distance symbols\0"),
            Self::InvalidAlphabet => Some("invalid code lengths set\0"),
            Self::InvalidRepeat => HeaderOutcome::InvalidRepeat.error_message(),
            Self::MissingEob => HeaderOutcome::MissingEob.error_message(),
            _ => None,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn is_header_mode(mode: Mode) -> bool {
    matches!(mode, Mode::Table | Mode::LenLens | Mode::CodeLens)
}

pub(crate) open spec fn phase(
    mode: Mode, counts: (usize, usize, usize), table: Table, next: usize,
) -> HeaderPhase {
    match mode {
        Mode::Table => HeaderPhase::Counts,
        Mode::LenLens => HeaderPhase::Alphabet { counts },
        _ => HeaderPhase::Lengths { counts, root: table.bits, used: next },
    }
}

pub(crate) open spec fn state_valid(
    mode: Mode, counts: (usize, usize, usize), table: Table, next: usize,
    lens: Seq<u16>, have: nat, codes: Seq<Code>,
) -> bool {
    is_header_mode(mode) ==> header_phase::phase_valid(
        phase(mode, counts, table, next), lens, have, codes)
        && (mode == Mode::CodeLens ==> table.codes == Codes::Codes)
}

pub(crate) open spec fn action(step: HeaderStep) -> HeaderAction {
    match step {
        HeaderStep::NeedCounts | HeaderStep::NeedAlphabet { .. } => HeaderAction::NeedInput,
        HeaderStep::InvalidCounts { .. } => HeaderAction::InvalidCounts,
        HeaderStep::InvalidAlphabet { .. } => HeaderAction::InvalidAlphabet,
        HeaderStep::Lengths { outcome, .. } => match outcome {
            HeaderOutcome::NeedInput => HeaderAction::NeedInput,
            HeaderOutcome::InvalidRepeat => HeaderAction::InvalidRepeat,
            HeaderOutcome::MissingEob => HeaderAction::MissingEob,
            HeaderOutcome::Complete => HeaderAction::Complete,
        },
    }
}
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires is_header_mode(mode),
    ensures result == phase(mode, counts, table, next),
        forall|lens: Seq<u16>, have: nat, codes: Seq<Code>|
            #[trigger] state_valid(mode, counts, table, next, lens, have, codes) ==>
                header_phase::phase_valid(result, lens, have, codes),
))]
pub(crate) fn resume_phase(
    mode: Mode,
    counts: (usize, usize, usize),
    table: Table,
    next: usize,
) -> HeaderPhase {
    match mode {
        Mode::Table => HeaderPhase::Counts,
        Mode::LenLens => HeaderPhase::Alphabet { counts },
        _ => HeaderPhase::Lengths {
            counts,
            root: table.bits,
            used: next,
        },
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires is_header_mode(*old(mode)),
        *old(mode) == Mode::CodeLens ==> old(table).codes == Codes::Codes,
        header_phase::step_follows(
            phase(*old(mode), (*old(nlen), *old(ndist), *old(ncode)), *old(table), *old(next)),
            step),
    ensures result == action(step),
        match step {
            HeaderStep::NeedCounts =>
                *final(mode) == Mode::Table
                && (*final(nlen), *final(ndist), *final(ncode))
                    == (*old(nlen), *old(ndist), *old(ncode)),
            HeaderStep::NeedAlphabet { counts } =>
                *final(mode) == Mode::LenLens
                && (*final(nlen), *final(ndist), *final(ncode)) == counts,
            HeaderStep::InvalidCounts { counts } | HeaderStep::InvalidAlphabet { counts } =>
                *final(mode) == Mode::Bad
                && (*final(nlen), *final(ndist), *final(ncode)) == counts,
            HeaderStep::Lengths { counts, root, used, outcome } =>
                (*final(nlen), *final(ndist), *final(ncode)) == counts
                && final(table).codes == Codes::Codes
                && final(table).bits == root && *final(next) == used
                && *final(mode) == if outcome == HeaderOutcome::NeedInput
                    || outcome == HeaderOutcome::Complete { Mode::CodeLens } else { Mode::Bad },
        },
        !matches!(step, HeaderStep::Lengths { .. }) || *old(mode) == Mode::CodeLens ==>
            final(table).codes == old(table).codes && final(table).bits == old(table).bits
                && *final(next) == *old(next),
        forall|lens: Seq<u16>, have: nat, codes: Seq<Code>|
            #[trigger] header_phase::step_valid(step, lens, have, codes) ==>
                state_valid(*final(mode), (*final(nlen), *final(ndist), *final(ncode)),
                    *final(table), *final(next), lens, have, codes)
                && (result == HeaderAction::Complete ==>
                    have == *final(nlen) + *final(ndist) && lens[256] != 0),
))]
pub(crate) fn apply_header_step(
    step: HeaderStep,
    mode: &mut Mode,
    nlen: &mut usize,
    ndist: &mut usize,
    ncode: &mut usize,
    table: &mut Table,
    next: &mut usize,
) -> HeaderAction {
    let counts = match step {
        HeaderStep::NeedCounts => return HeaderAction::NeedInput,
        HeaderStep::NeedAlphabet { counts }
        | HeaderStep::InvalidCounts { counts }
        | HeaderStep::InvalidAlphabet { counts } => counts,
        HeaderStep::Lengths {
            counts,
            root,
            used,
            outcome,
        } => {
            if !matches!(*mode, Mode::CodeLens) {
                *nlen = counts.0;
                *ndist = counts.1;
                *ncode = counts.2;
                *next = used;
                table.codes = Codes::Codes;
                table.bits = root;
                *mode = Mode::CodeLens;
            }
            return match outcome {
                HeaderOutcome::NeedInput => HeaderAction::NeedInput,
                HeaderOutcome::Complete => HeaderAction::Complete,
                HeaderOutcome::InvalidRepeat => {
                    *mode = Mode::Bad;
                    HeaderAction::InvalidRepeat
                }
                HeaderOutcome::MissingEob => {
                    *mode = Mode::Bad;
                    HeaderAction::MissingEob
                }
            };
        }
    };
    *nlen = counts.0;
    *ndist = counts.1;
    *ncode = counts.2;
    match step {
        HeaderStep::NeedAlphabet { .. } => {
            *mode = Mode::LenLens;
            HeaderAction::NeedInput
        }
        HeaderStep::InvalidCounts { .. } => {
            *mode = Mode::Bad;
            HeaderAction::InvalidCounts
        }
        _ => {
            *mode = Mode::Bad;
            HeaderAction::InvalidAlphabet
        }
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires is_header_mode(*old(mode)), lens.len() >= 316,
            codes.len() >= 128, work.len() >= 19, *old(count) <= 64,
            state_valid(*old(mode), (*old(nlen), *old(ndist), *old(ncode)),
                *old(table), *old(next), old(lens)@, *old(have) as nat, old(codes)@),
            bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
        ensures result.0 <= input.len(), *final(count) <= 64,
            state_valid(*final(mode), (*final(nlen), *final(ndist), *final(ncode)),
                *final(table), *final(next), final(lens)@, *final(have) as nat, final(codes)@),
            result.1 == HeaderAction::NeedInput ==> is_header_mode(*final(mode)),
            result.1 == HeaderAction::Complete ==> *final(mode) == Mode::CodeLens
                && *final(have) == *final(nlen) + *final(ndist)
                && final(lens)@[256] != 0,
            result.1 != HeaderAction::NeedInput && result.1 != HeaderAction::Complete
                ==> *final(mode) == Mode::Bad,
            result.1 == HeaderAction::InvalidCounts ==> *final(nlen) > 286 || *final(ndist) > 30,
            result.1 == HeaderAction::InvalidAlphabet ==> *final(have) == 19,
            result.1 == HeaderAction::MissingEob ==>
                *final(have) == *final(nlen) + *final(ndist) && final(lens)@[256] == 0,
            result.1 == HeaderAction::InvalidRepeat ==>
                *final(have) < *final(nlen) + *final(ndist),
            result.1 == HeaderAction::NeedInput ==> match *final(mode) {
                Mode::Table => *final(count) < 14 && result.0 == input.len(),
                Mode::LenLens => *final(have) < *final(ncode) && *final(count) < 3,
                Mode::CodeLens => *final(have) < *final(nlen) + *final(ndist),
                _ => false,
            },
            *final(count) as int <= *old(count) as int + 8 * result.0 as int,
            final(lens)@.len() == old(lens)@.len(),
            final(codes)@.len() == old(codes)@.len(),
            final(work)@.len() == old(work)@.len(),
            forall|index: int| 19 <= index < old(lens)@.len() && *final(have) <= index
                ==> #[trigger] final(lens)@[index] == old(lens)@[index],
            *old(mode) == Mode::CodeLens ==>
                (*final(nlen), *final(ndist), *final(ncode))
                    == (*old(nlen), *old(ndist), *old(ncode))
                    && final(table).bits == old(table).bits && *final(next) == *old(next)
                    && final(table).codes == old(table).codes
                    && final(codes)@ == old(codes)@ && final(work)@ == old(work)@,
            bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
                bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
            bit_specs::cached_suffix(*final(word), *final(count),
                bit_specs::input_bits(input@).skip(8 * result.0 as int)),
            bit_specs::buffered_bits(*final(word), *final(count))
                + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                    == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                        .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
    ))]
pub(crate) fn read_header_state(
    mode: &mut Mode,
    nlen: &mut usize,
    ndist: &mut usize,
    ncode: &mut usize,
    table: &mut Table,
    next: &mut usize,
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lens: &mut [u16],
    have: &mut usize,
    codes: &mut [Code],
    work: &mut [u16],
) -> (usize, HeaderAction) {
    let phase = resume_phase(*mode, (*nlen, *ndist, *ncode), *table, *next);
    let (advanced, step) = read_header_phase(phase, word, count, input, lens, have, codes, work);
    let action = apply_header_step(step, mode, nlen, ndist, ncode, table, next);
    (advanced, action)
}
