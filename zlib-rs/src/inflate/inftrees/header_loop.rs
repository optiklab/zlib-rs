#![forbid(unsafe_code)]

use crate::Code;
#[cfg(verus_keep_ghost)]
use crate::{
    bit_proofs, bit_specs, dynamic_header_specs, header_loop_proofs, header_loop_specs as model,
    huffman_specs, reader_state_proofs,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeaderOutcome {
    NeedInput,
    InvalidRepeat,
    MissingEob,
    Complete,
}

impl HeaderOutcome {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures match self {
            HeaderOutcome::InvalidRepeat => result == Some("invalid bit length repeat\0"),
            HeaderOutcome::MissingEob => result == Some("invalid code -- missing end-of-block\0"),
            _ => result == None,
        },
    ))]
    pub(crate) fn error_message(self) -> Option<&'static str> {
        match self {
            Self::InvalidRepeat => Some("invalid bit length repeat\0"),
            Self::MissingEob => Some("invalid code -- missing end-of-block\0"),
            _ => None,
        }
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 7, table.len() >= huffman_specs::capacity(root as nat),
        forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
            ==> 1 <= (#[trigger] table@[index]).bits <= root,
        dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) <= total <= lengths.len(), 257 <= total <= 320, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(), *old(count) <= 64, *final(count) <= 64,
        *final(count) as int <= *old(count) as int + 8 * result.0 as int,
        *old(have) <= *final(have) <= total,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        (result.1 == HeaderOutcome::Complete || result.1 == HeaderOutcome::MissingEob)
            <==> *final(have) == total,
        (result.1 == HeaderOutcome::MissingEob)
            <==> *final(have) == total && final(lengths)@[256] == 0,
        (result.1 == HeaderOutcome::Complete)
            <==> *final(have) == total && final(lengths)@[256] != 0,
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        forall|index: int| 0 <= index < old(lengths)@.len()
            && (index < *old(have) || *final(have) <= index)
                ==> #[trigger] final(lengths)@[index] == old(lengths)@[index],
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|path: Seq<model::State>| path.len() > 0
            && path[0] == model::state(old(lengths)@, *old(have) as nat, *old(word), *old(count), 0, 0)
            && path.last() == model::state(final(lengths)@, *final(have) as nat,
                *final(word), *final(count), result.0 as nat,
                (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat)
            && model::register_path(path, bit_specs::input_bits(input@)),
        forall|alphabet: Seq<u16>|
            #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) ==>
                model::header_result(alphabet,
                    bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
                    bit_specs::input_bits(input@), total as nat, input.len() as nat,
                    model::state(old(lengths)@, *old(have) as nat, *old(word), *old(count), 0, 0),
                    model::state(final(lengths)@, *final(have) as nat, *final(word), *final(count),
                        result.0 as nat,
                        (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat),
                    result.1),
        *old(have) == 0 && huffman_specs::header_decoding_table(
            Seq::new(19, |index: int| 0u16), table@, root) ==> result.1 != HeaderOutcome::Complete,
))]
pub(crate) fn read_length_header(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    table: &[Code],
    root: usize,
    lengths: &mut [u16],
    have: &mut usize,
    total: usize,
) -> (usize, HeaderOutcome) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = model::state(lengths@, *have as nat, *word, *count, 0, 0);
        let ghost pending = bit_specs::input_bits(input@);
        let ghost source = bit_specs::buffered_bits(*word, *count) + pending;
    }
    let (consumed, symbol_outcome) =
        read_length_symbols(word, count, input, table, root, lengths, have, total);
    let outcome = match symbol_outcome {
        None => HeaderOutcome::NeedInput,
        Some(false) => HeaderOutcome::InvalidRepeat,
        Some(true) => {
            if lengths[256] == 0 {
                HeaderOutcome::MissingEob
            } else {
                HeaderOutcome::Complete
            }
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        let after = model::state(lengths@, *have as nat, *word, *count, consumed as nat,
            (initial.count as int + 8 * consumed as int - *count as int) as nat);
        if bit_specs::cached_suffix(initial.word, initial.count, Seq::empty()) {
            assert((*count as int + 0) as u8 == *count);
            assert(bit_specs::cached_suffix(*word, *count, Seq::empty()));
        }
        assert forall|alphabet: Seq<u16>|
            #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                model::header_result(alphabet, source, pending, total as nat, input.len() as nat,
                    initial, after, outcome) by {
            reveal(model::header_result);
        }
        if initial.have == 0 && huffman_specs::header_decoding_table(
            Seq::new(19, |index: int| 0u16), table@, root) {
            header_loop_proofs::empty_header_rejected(source, pending, total as nat,
                input.len() as nat, initial, after, outcome);
        }
    }
    (consumed, outcome)
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 7, table.len() >= huffman_specs::capacity(root as nat),
        forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
            ==> 1 <= (#[trigger] table@[index]).bits <= root,
        dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) <= total <= lengths.len(), total <= 320, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(), *old(count) <= 64, *final(count) <= 64,
        *final(count) as int <= *old(count) as int + 8 * result.0 as int,
        *old(have) <= *final(have) <= total,
        result.1 == Some(true) <==> *final(have) == total,
        forall|next_pending: Seq<bool>|
            bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
                #[trigger] bit_specs::cached_suffix(*final(word), *final(count), next_pending),
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        forall|index: int| 0 <= index < old(lengths)@.len()
            && (index < *old(have) || *final(have) <= index)
                ==> #[trigger] final(lengths)@[index] == old(lengths)@[index],
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|path: Seq<model::State>| path.len() > 0
            && path[0] == model::state(old(lengths)@, *old(have) as nat, *old(word), *old(count), 0, 0)
            && path.last() == model::state(final(lengths)@, *final(have) as nat,
                *final(word), *final(count), result.0 as nat,
                (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat)
            && model::register_path(path, bit_specs::input_bits(input@)),
        forall|alphabet: Seq<u16>|
            #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) ==>
                model::result(alphabet,
                    bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
                    bit_specs::input_bits(input@),
                    total as nat, input.len() as nat,
                    model::state(old(lengths)@, *old(have) as nat, *old(word), *old(count), 0, 0),
                    model::state(final(lengths)@, *final(have) as nat, *final(word), *final(count),
                        result.0 as nat,
                        (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat),
                    result.1),
))]
pub(crate) fn read_length_symbols(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    table: &[Code],
    root: usize,
    lengths: &mut [u16],
    have: &mut usize,
    total: usize,
) -> (usize, Option<bool>) {
    let mut advanced = 0;
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost initial = model::state(lengths@, *have as nat, *word, *count, 0, 0);
        let ghost pending = bit_specs::input_bits(input@);
        let ghost source = bit_specs::buffered_bits(*word, *count) + pending;
        let ghost mut path = seq![initial];
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        header_loop_proofs::start(initial, pending);
        assert(pending.skip(0) =~= pending);
        assert(source.skip(0) =~= source);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= root <= 7, table.len() >= huffman_specs::capacity(root as nat),
            forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
                ==> 1 <= (#[trigger] table@[index]).bits <= root,
            initial == model::state(old(lengths)@, *old(have) as nat, *old(word), *old(count), 0, 0),
            initial.count <= 64,
            initial.have <= *have <= total <= lengths.len(), total <= 320,
            dynamic_header_specs::decoded_prefix(lengths@, *have as nat),
            lengths@.len() == initial.lengths.len(),
            forall|index: int| 0 <= index < initial.lengths.len()
                && (index < initial.have || *have <= index)
                    ==> #[trigger] lengths@[index] == initial.lengths[index],
            advanced <= input.len(), *count <= 64,
            *count as int <= initial.count as int + 8 * advanced as int,
            pending == bit_specs::input_bits(input@),
            source == bit_specs::buffered_bits(initial.word, initial.count) + pending,
            bit_specs::buffered_bits(*word, *count) + pending.skip(8 * advanced as int)
                == source.skip(initial.count as int + 8 * advanced as int - *count as int),
            bit_specs::cached_suffix(*word, *count, pending.skip(8 * advanced as int)),
            path.len() > 0, path[0] == initial,
            path.last() == model::state(lengths@, *have as nat, *word, *count, advanced as nat,
                (initial.count as int + 8 * advanced as int - *count as int) as nat),
            model::register_path(path, pending),
            forall|alphabet: Seq<u16>|
                #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) ==>
                    model::symbol_path(alphabet, source, pending, total as nat, input.len() as nat, path),
        decreases total - *have,
    ))]
    while *have < total {
        let remaining = &input[advanced..];
        #[cfg(verus_keep_ghost)]
        proof_decl! { let ghost previous = path.last(); }
        #[cfg(verus_keep_ghost)]
        proof! {
            bit_proofs::input_suffix(input@, advanced as int);
            assert(remaining@ =~= input@.skip(advanced as int));
            assert(bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(remaining@)
                =~= source.skip(previous.dropped as int));
        }
        let (consumed, outcome) =
            super::read_length_symbol(word, count, remaining, table, root, lengths, have, total);
        advanced += consumed;
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost next = model::state(lengths@, *have as nat, *word, *count, advanced as nat,
                (initial.count as int + 8 * advanced as int - *count as int) as nat);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bit_specs::input_bits(remaining@).take(8 * consumed as int)
                =~= pending.subrange(8 * previous.advanced as int, 8 * advanced as int));
            assert(bit_specs::input_bits(remaining@).skip(8 * consumed as int)
                =~= pending.skip(8 * advanced as int));
            assert(next.dropped - previous.dropped
                == previous.count as int + 8 * consumed as int - *count as int);
            assert(model::register_step(previous, next, pending)) by {
                reveal(model::register_step);
                let loaded = choose|loaded: u64| #[trigger] bit_specs::filled_word(
                        previous.word, previous.count, loaded,
                        bit_specs::input_bits(remaining@).take(8 * consumed as int))
                    && *word == loaded
                        >> ((previous.count as int + 8 * consumed as int - *count as int) as u8);
                assert(exists|value: u64| #[trigger] bit_specs::filled_word(
                        previous.word, previous.count, value,
                        pending.subrange(8 * previous.advanced as int, 8 * advanced as int))
                    && next.word == value >> ((next.dropped - previous.dropped) as u8));
            }
            header_loop_proofs::append_register(path, next, pending);
            assert forall|alphabet: Seq<u16>|
                #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                    model::symbol_step(alphabet, source, pending, total as nat, input.len() as nat,
                        previous, next, outcome) by {
                reveal(model::symbol_step);
            }
        }
        if outcome != Some(true) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(exists|trace: Seq<model::State>| trace.len() > 0 && trace[0] == initial
                    && trace.last() == next && model::register_path(trace, pending)) by {
                    let trace = path.push(next);
                    assert(trace.len() > 0 && trace[0] == initial && trace.last() == next);
                }
                assert forall|next_pending: Seq<bool>|
                    bit_specs::cached_suffix(initial.word, initial.count, Seq::empty()) implies
                        #[trigger] bit_specs::cached_suffix(*word, *count, next_pending) by {
                    reader_state_proofs::register_path_retarget(path.push(next), pending, next_pending);
                }
                assert forall|alphabet: Seq<u16>|
                    #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                        model::result(alphabet, source, pending, total as nat, input.len() as nat,
                            initial, next, outcome) by {
                    header_loop_proofs::finish(alphabet, source, pending, total as nat, input.len() as nat,
                        path, next, outcome);
                }
            }
            return (advanced, outcome);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|alphabet: Seq<u16>|
                #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                    model::symbol_path(alphabet, source, pending, total as nat, input.len() as nat,
                        path.push(next)) by {
                header_loop_proofs::append_symbol(alphabet, source, pending, total as nat,
                    input.len() as nat, path, next);
            }
            path = path.push(next);
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(exists|trace: Seq<model::State>| trace.len() > 0 && trace[0] == initial
            && trace.last() == path.last() && model::register_path(trace, pending));
        assert forall|next_pending: Seq<bool>|
            bit_specs::cached_suffix(initial.word, initial.count, Seq::empty()) implies
                #[trigger] bit_specs::cached_suffix(*word, *count, next_pending) by {
            reader_state_proofs::register_path_retarget(path, pending, next_pending);
        }
        assert forall|alphabet: Seq<u16>|
            #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                model::result(alphabet, source, pending, total as nat, input.len() as nat,
                    initial, path.last(), Some(true)) by {
            header_loop_proofs::finish(alphabet, source, pending, total as nat, input.len() as nat,
                path, path.last(), Some(true));
        }
    }
    (advanced, Some(true))
}
