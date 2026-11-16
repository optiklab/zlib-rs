#![forbid(unsafe_code)]

use crate::Code;

#[cfg(not(verus_keep_ghost))]
use super::bitreader::buffer;
#[cfg(verus_keep_ghost)]
use crate::{
    bit_proofs, bit_specs, buffer, dynamic_header_proofs, dynamic_header_specs, huffman_decode,
    huffman_lookahead, huffman_proofs, huffman_specs,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[path = "inftrees/analysis.rs"]
mod analysis;
#[path = "inftrees/codes.rs"]
mod codes;
#[path = "inftrees/dynamic_resume.rs"]
mod dynamic_resume;
#[path = "inftrees/dynamic_start.rs"]
mod dynamic_start;
#[path = "inftrees/dynamic_tables.rs"]
mod dynamic_tables;
#[path = "inftrees/emission.rs"]
mod emission;
#[path = "inftrees/entries.rs"]
mod entries;
#[path = "inftrees/header_loop.rs"]
mod header_loop;
#[path = "inftrees/header_phase.rs"]
pub(crate) mod header_phase;
#[path = "inftrees/header_start.rs"]
mod header_start;
#[path = "inftrees/histogram.rs"]
mod histogram;
#[path = "inftrees/layout.rs"]
mod layout;
#[path = "inftrees/lookahead.rs"]
mod lookahead;
#[path = "inftrees/preparation.rs"]
mod preparation;
#[path = "inftrees/progress.rs"]
mod progress;
#[path = "inftrees/replicate.rs"]
mod replicate;
#[path = "inftrees/slots.rs"]
mod slots;
#[path = "inftrees/sorting.rs"]
mod sorting;

pub(crate) use dynamic_resume::resume_dynamic_header;
pub(crate) use dynamic_start::{read_dynamic_header, DynamicHeaderOutcome};
pub(crate) use dynamic_tables::{
    inflate_completed_distance_table, inflate_completed_literal_table,
};
pub(crate) use entries::CodeType;
pub(crate) use header_loop::{read_length_header, HeaderOutcome};
pub(crate) use header_phase::{read_header_phase, HeaderPhase, HeaderStep};
pub(crate) use header_start::{read_alphabet_header, HeaderReadOutcome};
pub(crate) use preparation::TablePreparation;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[repr(i32)]
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum InflateTable {
    EnoughIsNotEnough = 1,
    Success { root: usize, used: usize } = 0,
    InvalidCode = -1,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 15, table.len() >= huffman_specs::capacity(root as nat),
    ensures result == table@[(word as u32 as int) % huffman_specs::capacity(root as nat)],
        forall|alphabet: huffman_specs::Alphabet, lengths: Seq<u16>|
            #[trigger] crate::root_table_specs::table(alphabet, lengths, root as nat, table@) ==>
                crate::root_table_specs::entry(alphabet, lengths, result, word as u32),
))]
pub(crate) fn lookup_root_entry(table: &[Code], root: usize, word: u64) -> Code {
    let index = buffer::peek_bits(word, root);
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_lookahead::peek_root_index(word, root as u32, index);
        assert forall|alphabet: huffman_specs::Alphabet, lengths: Seq<u16>|
            #[trigger] crate::root_table_specs::table(alphabet, lengths, root as nat, table@)
                implies crate::root_table_specs::entry(alphabet, lengths,
                    table@[(word as u32 as int) % huffman_specs::capacity(root as nat)],
                    word as u32) by {
            crate::root_table_proofs::word_entry(alphabet, lengths, root as nat, table@,
                word as u32);
        }
    }
    table[index as usize]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= link.bits, 1 <= link.op, link.bits as int + link.op as int <= 15,
    ensures result as int == huffman_specs::subtable_index(link, word as nat),
        link.val <= result < link.val as int + huffman_specs::capacity(link.op as nat),
        forall|root: nat, next: nat, width: nat, used: nat|
            #[trigger] huffman_specs::subtable_link(link, root, next, width, used) ==>
                next <= result < used,
        forall|alphabet: huffman_specs::Alphabet, lengths: Seq<u16>, used: nat, codes: Seq<Code>|
            #[trigger] crate::linked_table_specs::table(alphabet, lengths,
                link.bits as nat, used, codes)
                && link == codes[(word as u32 as int)
                    % huffman_specs::capacity(link.bits as nat)] ==>
                huffman_specs::capacity(link.bits as nat) <= result < used
                    && crate::linked_table_specs::leaf(alphabet, lengths, codes[result as int],
                        word as u32, link.bits as nat),
))]
pub(crate) fn lookup_subtable_index(word: u64, link: Code) -> usize {
    let root = link.bits;
    let width = link.op;
    let masked = buffer::peek_bits(word, (root + width) as usize);
    let shifted = masked >> root;
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_lookahead::masked_subtable_index(word, root, width, masked);
        huffman_proofs::depth_capacity(width as nat);
        huffman_proofs::capacity_positive(width as nat);
        assert(shifted < huffman_specs::capacity(width as nat));
    }
    let selected = shifted as usize;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|r: nat, next: nat, w: nat, used: nat|
            #[trigger] huffman_specs::subtable_link(link, r, next, w, used) implies
                next <= (link.val as int + selected as int) < used by {
            huffman_proofs::subtable_link_bounds(link, r, next, w, used, word as nat);
        }
        assert forall|alphabet: huffman_specs::Alphabet, lengths: Seq<u16>,
            used: nat, codes: Seq<Code>|
            #[trigger] crate::linked_table_specs::table(alphabet, lengths,
                link.bits as nat, used, codes)
                && link == codes[(word as u32 as int)
                    % huffman_specs::capacity(link.bits as nat)] implies
                huffman_specs::capacity(link.bits as nat) <= (link.val as int + selected as int) < used
                    && crate::linked_table_specs::leaf(alphabet, lengths,
                        codes[link.val as int + selected as int], word as u32, link.bits as nat) by {
            crate::linked_table_proofs::child_selection(alphabet, lengths, link.bits as nat,
                used, codes, word, link, link.val as int + selected as int);
        }
    }
    link.val as usize + selected
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 7, table.len() >= huffman_specs::capacity(root as nat),
    ensures result == table@[(word as u32 as int) % huffman_specs::capacity(root as nat)],
        forall|lengths: Seq<u16>| #[trigger] huffman_specs::root_decoding_table(lengths, table@)
            && huffman_specs::maximum_length(lengths) == root ==>
                huffman_specs::root_entry_decodes(lengths, result, word as u32),
))]
pub(crate) fn lookup_code_length(table: &[Code], root: usize, word: u64) -> Code {
    let result = lookup_root_entry(table, root, word);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|lengths: Seq<u16>|
            #[trigger] huffman_specs::root_decoding_table(lengths, table@)
                && huffman_specs::maximum_length(lengths) == root implies
                    huffman_specs::root_entry_decodes(lengths,
                        table@[(word as u32 as int) % huffman_specs::capacity(root as nat)],
                        word as u32) by {
            huffman_decode::root_word_decodes(lengths, table@, word as u32);
        }
    }
    result
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 7, table.len() >= huffman_specs::capacity(root as nat),
        forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
            ==> 1 <= (#[trigger] table@[index]).bits <= root,
        *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        result.0 == if table@[
                (*old(word) as u32 as int) % huffman_specs::capacity(root as nat)
            ].bits > *old(count) && input.len() > 0 { 1int } else { 0int },
        result.1.is_some() == (table@[
                (*old(word) as u32 as int) % huffman_specs::capacity(root as nat)
            ].bits <= *old(count) || input.len() > 0),
        *final(count) == *old(count) as int + 8 * result.0 as int,
        *final(count) <= 64,
        result.0 == 0 ==> *final(word) == *old(word),
        bit_specs::filled_word(*old(word), *old(count), *final(word),
            bit_specs::input_bits(input@).take(8 * result.0 as int)),
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        match result.1 {
            Some(entry) => entry == table@[
                    (*final(word) as u32 as int) % huffman_specs::capacity(root as nat)
                ] && entry.bits <= *final(count)
                && (root == 1 ==> result.0 == bit_specs::needed_bytes(*old(count), entry.bits as usize))
                && forall|lengths: Seq<u16>|
                    #[trigger] huffman_specs::root_decoding_table(lengths, table@)
                        && huffman_specs::maximum_length(lengths) == root ==>
                            huffman_specs::root_entry_decodes(lengths, entry, *final(word) as u32)
                                && huffman_specs::code_length_source_prefix(lengths, entry.val as int,
                                    bit_specs::buffered_bits(*old(word), *old(count))
                                        + bit_specs::input_bits(input@))
                                && result.0 == bit_specs::needed_bytes(*old(count), entry.bits as usize),
            None => forall|lengths: Seq<u16>|
                #[trigger] huffman_specs::root_decoding_table(lengths, table@)
                    && huffman_specs::maximum_length(lengths) == root ==>
                        !(exists|symbol: int| huffman_specs::code_length_source_prefix(lengths, symbol,
                            bit_specs::buffered_bits(*old(word), *old(count))
                                + bit_specs::input_bits(input@))),
        },
))]
pub(crate) fn read_code_length(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    table: &[Code],
    root: usize,
) -> (usize, Option<Code>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
    }
    #[cfg(verus_keep_ghost)]
    proof! { huffman_proofs::capacity_positive(root as nat); }
    let here = lookup_code_length(table, root, *word);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::input_bits(input@).skip(0) =~= bit_specs::input_bits(input@));
        assert(bit_specs::filled_word(*word, *count, *word, bit_specs::input_bits(input@).take(0)));
        assert(1 <= here.bits <= root);
    }
    if here.bits <= *count {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|lengths: Seq<u16>|
                #[trigger] huffman_specs::root_decoding_table(lengths, table@)
                    && huffman_specs::maximum_length(lengths) == root implies
                        huffman_specs::code_length_source_prefix(lengths, here.val as int,
                            bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@)) by {
                huffman_lookahead::root_entry_source(lengths, here, *word, *count,
                    bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@),
                    bit_specs::input_bits(input@));
            }
        }
        return (0, Some(here));
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(*count < here.bits); }
    if input.is_empty() {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(bit_specs::input_bits(input@) =~= Seq::empty());
            assert forall|lengths: Seq<u16>|
                #[trigger] huffman_specs::root_decoding_table(lengths, table@)
                    && huffman_specs::maximum_length(lengths) == root implies
                        !(exists|symbol: int| huffman_specs::code_length_source_prefix(lengths, symbol,
                            bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@))) by {
                huffman_lookahead::root_source_ready(lengths, here, *word, *count);
            }
        }
        return (0, None);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::header_fill_bounds(*count, root);
        bit_proofs::needed_bytes_bounds(*count, root);
        assert(bit_specs::needed_bytes(*count, root) == 1);
    }
    let (consumed, _complete) = buffer::fill_from_slice(word, count, input, root);
    let entry = lookup_code_length(table, root, *word);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit_specs::buffered_bits(*word, *count)
            + bit_specs::input_bits(input@).skip(8 * consumed as int)
                =~= bit_specs::buffered_bits(original_word, original_count) + bit_specs::input_bits(input@));
        assert(1 <= entry.bits <= root);
        huffman_lookahead::filled_u32_prefix(original_word, *word, original_count,
            bit_specs::input_bits(input@).take(8 * consumed as int));
        if root == 1 {
            assert(original_count == 0 && entry.bits == 1);
        }
        assert forall|lengths: Seq<u16>|
            #[trigger] huffman_specs::root_decoding_table(lengths, table@)
               && huffman_specs::maximum_length(lengths) == root implies
                   huffman_specs::code_length_source_prefix(lengths, entry.val as int,
                       bit_specs::buffered_bits(original_word, original_count)
                           + bit_specs::input_bits(input@))
                       && consumed == bit_specs::needed_bytes(original_count, entry.bits as usize) by {
            huffman_lookahead::root_entry_source(lengths, entry, *word, *count,
               bit_specs::buffered_bits(original_word, original_count) + bit_specs::input_bits(input@),
               bit_specs::input_bits(input@).skip(8 * consumed as int));
            if entry.bits <= original_count {
                huffman_lookahead::root_lookahead_stable(lengths, table@,
                    *word as u32, original_word as u32, original_count as nat);
                assert(entry == here);
            }
            bit_proofs::needed_bytes_bounds(original_count, entry.bits as usize);
        }
    }
    (consumed, Some(entry))
}

#[inline]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 7, table.len() >= huffman_specs::capacity(root as nat),
        forall|index: int| 0 <= index < huffman_specs::capacity(root as nat)
            ==> 1 <= (#[trigger] table@[index]).bits <= root,
        dynamic_header_specs::decoded_prefix(old(lengths)@, *old(have) as nat),
        *old(have) < total <= lengths.len(), total <= 320, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
    ensures result.0 <= input.len(),
        *final(count) as int <= *old(count) as int + 8 * result.0 as int <= 64,
        *old(count) as int + 8 * result.0 as int - *final(count) as int <= 14,
        *old(have) <= *final(have) <= total,
        dynamic_header_specs::decoded_prefix(final(lengths)@, *final(have) as nat),
        final(lengths)@.len() == old(lengths)@.len(),
        result.1 == Some(true) ==> *old(have) < *final(have),
        result.1 != Some(true) ==> final(lengths)@ == old(lengths)@
            && *final(have) == *old(have),
        forall|index: int| 0 <= index < old(lengths)@.len()
            && (index < *old(have) || *final(have) <= index)
                ==> #[trigger] final(lengths)@[index] == old(lengths)@[index],
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
                == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                    .skip(*old(count) as int + 8 * result.0 as int - *final(count) as int),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == loaded
                >> ((*old(count) as int + 8 * result.0 as int - *final(count) as int) as u8),
        forall|alphabet: Seq<u16>|
            #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) ==>
                dynamic_header_specs::symbol_input_transition(alphabet,
                    old(lengths)@, final(lengths)@, *old(have) as nat, *final(have) as nat,
                    total as nat,
                    bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
                    *old(count), input.len() as nat, result.0 as nat,
                    (*old(count) as int + 8 * result.0 as int - *final(count) as int) as nat,
                    result.1),
))]
pub(crate) fn read_length_symbol(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    table: &[Code],
    root: usize,
    lengths: &mut [u16],
    have: &mut usize,
    total: usize,
) -> (usize, Option<bool>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_word = *word;
        let ghost original_count = *count;
        let ghost original_lengths = lengths@;
        let ghost original_have = *have;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    let (first, entry) = read_code_length(word, count, input, table, root);
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost middle = *word;
        let ghost middle_count = *count;
    }
    let entry = match entry {
        Some(entry) => entry,
        None => {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(first == 0 && *count == original_count && *word == original_word);
                assert(original_word >> 0u8 == original_word) by (bit_vector);
                assert(exists|loaded: u64| #[trigger] bit_specs::filled_word(original_word, original_count,
                        loaded, bit_specs::input_bits(input@).take(0))
                    && *word == loaded >> 0u8);
                assert forall|alphabet: Seq<u16>|
                    #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                        dynamic_header_specs::symbol_input_transition(alphabet,
                            original_lengths, lengths@, original_have as nat, *have as nat,
                            total as nat, source, original_count, input.len() as nat,
                            first as nat, 0, None) by {
                    reveal(huffman_specs::header_decoding_table);
                    if huffman_specs::maximum_length(alphabet) == 0 {
                        assert(huffman_specs::capacity(1) == 2) by (compute);
                        assert(0 <= (original_word as u32 as int) % 2 < 2);
                        assert(original_count == 0 && input.len() == 0);
                    }
                    dynamic_header_proofs::symbol_transition_without_code(alphabet,
                        original_lengths, original_have as nat, total as nat, source,
                        original_count, input.len() as nat);
                }
            }
            return (first, None);
        }
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::capacity_positive(root as nat);
        assert(0 <= (middle as u32 as int) % huffman_specs::capacity(root as nat)
            < huffman_specs::capacity(root as nat));
        assert(1 <= entry.bits <= root);
    }
    let symbol = entry.val.min(18);
    let remaining = &input[first..];
    #[cfg(verus_keep_ghost)]
    proof! {
        bit_proofs::input_suffix(input@, first as int);
        assert(bit_specs::buffered_bits(middle, middle_count) + bit_specs::input_bits(remaining@)
            =~= source);
    }
    let (second, outcome) = super::header_lengths::read_selected_length_symbol(
        word, count, remaining, entry.bits, symbol, lengths, have, total,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        let dropped = (middle_count as int + 8 * second as int - *count as int) as nat;
        let loaded = choose|loaded: u64| #[trigger] bit_specs::filled_word(middle, middle_count,
                loaded, bit_specs::input_bits(remaining@).take(8 * second as int))
            && *word == loaded >> (dropped as u8);
        bit_proofs::filled_word_composes(original_word, original_count, middle, loaded,
            bit_specs::input_bits(input@).take(8 * first as int),
            bit_specs::input_bits(remaining@).take(8 * second as int));
        assert(bit_specs::input_bits(input@).take(8 * first as int)
            + bit_specs::input_bits(remaining@).take(8 * second as int)
                =~= bit_specs::input_bits(input@).take(8 * (first as int + second as int)));
        assert(bit_specs::input_bits(remaining@).skip(8 * second as int)
            =~= bit_specs::input_bits(input@).skip(8 * (first as int + second as int)));
        assert(exists|value: u64| #[trigger] bit_specs::filled_word(original_word, original_count,
                value, bit_specs::input_bits(input@).take(8 * (first as int + second as int)))
            && *word == value >> (dropped as u8));
        assert forall|alphabet: Seq<u16>|
            #[trigger] huffman_specs::header_decoding_table(alphabet, table@, root) implies
                dynamic_header_specs::symbol_input_transition(alphabet,
                    original_lengths, lengths@, original_have as nat, *have as nat,
                    total as nat, source, original_count, input.len() as nat,
                    (first as nat + second as nat), dropped, outcome) by {
            huffman_lookahead::header_entry_symbol(alphabet, table@, root, entry, middle as u32);
            reveal(huffman_specs::header_decoding_table);
            assert(symbol == entry.val);
            if huffman_specs::maximum_length(alphabet) > 0 {
                assert(huffman_specs::code_length_source_prefix(alphabet, entry.val as int, source));
            }
            assert(first == bit_specs::needed_bytes(original_count, entry.bits as usize));
            dynamic_header_proofs::symbol_effect_after_prefix(
                original_lengths, lengths@, original_have as nat, *have as nat,
                total as nat, source, original_count, input.len() as nat,
                entry.bits as nat, entry.val as nat, first as nat, second as nat, dropped, outcome);
            dynamic_header_proofs::symbol_transition_from_effect(alphabet,
                original_lengths, lengths@, original_have as nat, *have as nat,
                total as nat, source, original_count, input.len() as nat,
                entry.bits as nat, entry.val as nat, (first as nat + second as nat), dropped, outcome);
        }
    }
    let result = (first + second, outcome);
    #[cfg(verus_keep_ghost)]
    proof! { assert(result.0 as nat == first as nat + second as nat); }
    result
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::prefix_fits(old(lens)@, *old(have) as nat),
        table.len() >= 128, work.len() >= 19,
    ensures *final(have) == 19,
        dynamic_header_specs::padded_header(old(lens)@, final(lens)@, *old(have) as nat),
        forall|symbol: int| 0 <= symbol < 19 ==> #[trigger] final(lens)@[symbol] <= 7,
        huffman_specs::code_length_result(final(lens)@.take(19),
            old(table)@, final(table)@, old(work)@, final(work)@, result),
))]
pub(crate) fn finish_code_length_table(
    lens: &mut [u16],
    have: &mut usize,
    table: &mut [Code],
    work: &mut [u16],
) -> InflateTable {
    super::header_lengths::finish_length_header(lens, have);
    let lengths = &lens[..19];
    #[cfg(verus_keep_ghost)]
    proof! {
        dynamic_header_proofs::maximum_bounded(lengths@, 7);
        huffman_proofs::count_before_bounds(lengths@, 16);
        huffman_proofs::capacity_monotone(huffman_specs::maximum_length(lengths@) as nat, 7);
        assert(huffman_specs::capacity(7) == 128) by (compute);
    }
    inflate_table(CodeType::Codes, lengths, table, 7, work)
}

#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires dynamic_header_specs::prefix_fits(old(lens)@, *old(have) as nat),
        *old(have) <= target <= 19, *old(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), bit_specs::input_bits(input@)),
        table.len() >= 128, work.len() >= 19,
    ensures result.0 <= input.len(),
        result.0 == if bit_specs::needed_bytes(*old(count), (3 * (target - *old(have))) as usize) <= input.len() {
            bit_specs::needed_bytes(*old(count), (3 * (target - *old(have))) as usize)
        } else { input.len() as nat },
        result.1.is_some() == (*old(count) as int + 8 * input.len() as int
            >= 3 * (target as int - *old(have) as int)),
        result.1.is_some() ==> *final(have) == 19,
        result.1.is_none() ==> *old(have) <= *final(have) < target
            && result.0 == input.len() && *final(count) < 3,
        *final(count) <= 64,
        bit_specs::cached_suffix(*old(word), *old(count), Seq::empty()) ==>
            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),
        *final(count) as int == *old(count) as int + 8 * result.0 as int
            - 3 * ((if result.1.is_some() { target as int } else { *final(have) as int })
                - *old(have) as int),
        final(lens)@ == dynamic_header_specs::length_header(old(lens)@, *old(have) as nat,
            if result.1.is_some() { target as nat } else { *final(have) as nat },
            bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@),
            result.1.is_some()),
        dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat),
        bit_specs::buffered_bits(*final(word), *final(count))
            + bit_specs::input_bits(input@).skip(8 * result.0 as int)
            == (bit_specs::buffered_bits(*old(word), *old(count)) + bit_specs::input_bits(input@))
                .skip(3 * ((if result.1.is_some() { target as int } else { *final(have) as int })
                    - *old(have) as int)),
        bit_specs::cached_suffix(*final(word), *final(count),
            bit_specs::input_bits(input@).skip(8 * result.0 as int)),
        exists|loaded: u64| #[trigger] bit_specs::filled_word(*old(word), *old(count), loaded,
                bit_specs::input_bits(input@).take(8 * result.0 as int))
            && *final(word) == loaded >> ((3 * (
                (if result.1.is_some() { target as int } else { *final(have) as int })
                    - *old(have) as int)) as u64),
        match result.1 {
            Some(outcome) => huffman_specs::code_length_result(final(lens)@.take(19),
                old(table)@, final(table)@, old(work)@, final(work)@, outcome),
            None => final(table)@ == old(table)@ && final(work)@ == old(work)@,
        },
))]
pub(crate) fn read_code_length_table(
    word: &mut u64,
    count: &mut u8,
    input: &[u8],
    lens: &mut [u16],
    have: &mut usize,
    target: usize,
    table: &mut [Code],
    work: &mut [u16],
) -> (usize, Option<InflateTable>) {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_lens = lens@;
        let ghost start = *have;
        let ghost source = bit_specs::buffered_bits(*word, *count) + bit_specs::input_bits(input@);
    }
    let (consumed, complete) =
        super::header_lengths::read_lengths(word, count, input, lens, have, target);
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(dynamic_header_specs::prefix_fits);
        dynamic_header_proofs::header_from_wire(original_lens, lens@, start as nat, *have as nat, source);
    }
    if !complete {
        return (consumed, None);
    }
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost read_lens = lens@;
        let ghost read_have = *have;
        let ghost before_table = table@;
        let ghost before_work = work@;
    }
    let outcome = finish_code_length_table(lens, have, table, work);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(*have == 19);
        assert(dynamic_header_specs::padded_header(read_lens, lens@, read_have as nat));
        assert(huffman_specs::code_length_result(lens@.take(19),
            before_table, table@, before_work, work@, outcome));
        dynamic_header_proofs::pad_read_header(original_lens, lens@, start as nat, target as nat, source);
    }
    (consumed, Some(outcome))
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(true))]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lens.len() <= if matches!(codetype, CodeType::Codes) { 19usize }
            else if matches!(codetype, CodeType::Lens) { 288 } else { 32 },
        forall|index: int| 0 <= index < lens.len() ==> lens@[index] <= 15,
        huffman_specs::accepted_lengths(lens@, matches!(codetype, CodeType::Codes)) ==>
            work.len() >= huffman_specs::count_before(lens@, 16),
        table.len() >= 2,
        huffman_specs::maximum_length(lens@) <= bits ==>
            table.len() >= huffman_specs::capacity(huffman_specs::maximum_length(lens@) as nat),
        huffman_specs::maximum_length(lens@) > bits ==>
            (crate::constructor_pages_specs::backing(
                crate::table_preparation_specs::clamped_root(bits as nat,
                    huffman_specs::minimum_length(lens@) as nat,
                    huffman_specs::maximum_length(lens@) as nat),
                huffman_specs::maximum_length(lens@) as nat, table.len() as int)
                || crate::capacity_bound_specs::tight_backing(lens@, bits as nat, table.len() as int)),
    ensures crate::constructor_table_specs::result(entries::alphabet(&codetype),
        lens@, bits as nat, old(table)@, final(table)@, old(work)@, final(work)@, result),
        ((matches!(codetype, CodeType::Lens) && bits == 10 && lens.len() <= 286)
            || (matches!(codetype, CodeType::Dists) && bits == 9 && lens.len() <= 30))
            ==> !matches!(result, InflateTable::EnoughIsNotEnough),
        huffman_specs::maximum_length(lens@) <= bits ==>
        crate::root_table_specs::result(entries::alphabet(&codetype), lens@,
        old(table)@, final(table)@, old(work)@, final(work)@, result),
        match result {
            InflateTable::Success { root, used } =>
                huffman_specs::maximum_length(lens@) > 0
                    && huffman_specs::slots(huffman_specs::histogram(lens@), 15) == 0 ==>
                        crate::linked_table_specs::table(entries::alphabet(&codetype),
                            lens@, root as nat, used as nat, final(table)@),
            _ => true,
        },
        matches!(codetype, CodeType::Codes) && bits <= 7
            && huffman_specs::maximum_length(lens@) <= bits ==>
            huffman_specs::code_length_result(lens@, old(table)@, final(table)@,
                old(work)@, final(work)@, result),
))]
pub(crate) fn inflate_table(
    codetype: CodeType,
    lens: &[u16],
    table: &mut [Code],
    bits: usize,
    work: &mut [u16],
) -> InflateTable {
    #[cfg(verus_keep_ghost)]
    verus_exec_expr!({
        hide(huffman_specs::histogram);
        hide(huffman_specs::valid_histogram);
        hide(huffman_specs::remaining_histogram);
    });
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost original_table = table@;
        let ghost original_work = work@;
        let ghost original_counts = huffman_specs::histogram(lens@);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        crate::table_preparation_proofs::code_lengths_capacity();
        huffman_proofs::metadata_bounds(lens@);
        if huffman_specs::maximum_length(lens@) > 0
            && huffman_specs::maximum_length(lens@) <= bits {
            crate::table_preparation_proofs::clamped_root_at_upper_bound(bits as nat,
                huffman_specs::minimum_length(lens@) as nat,
                huffman_specs::maximum_length(lens@) as nat);
        }
    }
    let (mut count, min, max, root, used, base, extra, match_) =
        match preparation::prepare_table(&codetype, lens, table, bits, work) {
            TablePreparation::Finished(outcome) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crate::constructor_table_proofs::finished(entries::alphabet(&codetype),
                        lens@, bits as nat, original_table, table@, original_work, work@, outcome);
                    if (matches!(codetype, CodeType::Lens) && bits == 10 && lens.len() <= 286)
                        || (matches!(codetype, CodeType::Dists) && bits == 9 && lens.len() <= 30) {
                        crate::capacity_bound_proofs::dynamic_no_capacity_error(
                            entries::alphabet(&codetype), lens@, bits as nat,
                            original_table, table@, original_work, work@, outcome);
                    }
                    if huffman_specs::maximum_length(lens@) <= bits {
                        crate::root_table_proofs::finished(entries::alphabet(&codetype), lens@,
                            bits as nat, original_table, table@, original_work, work@, outcome);
                    }
                }
                return outcome;
            }
            TablePreparation::Ready {
                count,
                min,
                max,
                root,
                used,
                base,
                extra,
                threshold,
            } => (count, min, max, root, used, base, extra, threshold),
        };
    let mut layout = layout::TableLayout {
        next: 0,
        width: root,
        used,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        if max <= bits {
            crate::table_preparation_proofs::clamped_root_at_upper_bound(
                bits as nat, min as nat, max as nat);
        }
        huffman_proofs::capacity_positive(root as nat);
        assert(layout::valid_layout(&layout));
    }

    let mut huff = 0; // starting code
    let mut reversed_huff = 0u32; // starting code, reversed
    let mut sym = 0;
    let mut len = min;
    let mut drop_ = 0;
    let mut low = usize::MAX; // trigger new subtable when len > root
    let mask = layout.used - 1; /* mask for comparing low */

    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost mut regions = Seq::<Option<crate::table_pages_specs::Page>>::new(
            huffman_specs::capacity(root as nat) as nat, |key: int| None);
        let ghost mut openings = Seq::<Option<crate::page_source_specs::Opening>>::new(
            huffman_specs::capacity(root as nat) as nat, |key: int| None);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::histogram_offsets(lens@, original_counts, 16);
        huffman_proofs::before_monotone(original_counts, min as nat + 1, 16);
        huffman_proofs::capacity_positive(root as nat);
        huffman_proofs::capacity_positive(len as nat);
        assert(huffman_specs::bucket_entry(lens@, original_counts, work@, min as int, 0));
        huffman_proofs::zero_reversal();
        assert(huffman_specs::aligned_cursor(0, len as u32)) by (bit_vector);
        assert forall|symbol: int| 0 <= symbol < lens.len() implies lens@[symbol] <= max by {
            huffman_decode::maximum_symbol_bound(lens@, symbol);
        }
        crate::constructor_pages_proofs::initial(lens@, original_counts, work@,
            root as nat, max as nat);
        assert(crate::constructor_pages_specs::backing(root as nat, max as nat,
            table.len() as int)
            || crate::capacity_bound_specs::tight_backing(lens@, bits as nat, table.len() as int));
        crate::capacity_bound_proofs::root_storage(lens@, original_counts, bits as nat,
            root as nat, max as nat, table.len() as int);
        crate::capacity_bound_proofs::finite_offsets(root as nat, max as nat,
            layout.used as int, regions);
        crate::constructor_table_proofs::initial(entries::alphabet(&codetype),
            lens@, work@, root as nat, original_table);
    }
    // process all codes and make table entries
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant lens.len() <= if matches!(codetype, CodeType::Codes) { 19usize }
                else if matches!(codetype, CodeType::Lens) { 288 } else { 32 },
            forall|index: int| 0 <= index < lens.len() ==> lens@[index] <= max,
            huffman_specs::accepted_lengths(lens@, matches!(codetype, CodeType::Codes)),
            huffman_specs::valid_histogram(lens@, original_counts),
            original_counts == huffman_specs::histogram(lens@),
            max == huffman_specs::maximum_length(lens@),
            1 <= root <= max <= 15, 1 <= len <= max,
            root == crate::table_preparation_specs::clamped_root(bits as nat,
                huffman_specs::minimum_length(lens@) as nat,
                huffman_specs::maximum_length(lens@) as nat),
            max <= bits ==> root == max,
            root == max ==> drop_ == 0 && layout.next == 0 && layout.width == root
                && layout.used == huffman_specs::capacity(root as nat),
            layout::valid_layout(&layout),
            crate::constructor_pages_specs::backing(root as nat, max as nat,
                table.len() as int)
                || crate::capacity_bound_specs::tight_backing(lens@, bits as nat, table.len() as int),
            if drop_ == 0 {
                len <= root && layout.next == 0 && layout.width == root
                    && layout.used == huffman_specs::capacity(root as nat) && low == usize::MAX
            } else {
                drop_ == root && root < len && low < huffman_specs::capacity(root as nat)
                    && regions[low as int] == Some(crate::table_pages_specs::Page {
                        base: layout.next as int, width: layout.width as nat,
                    })
            },
            mask as int == huffman_specs::capacity(root as nat) - 1,
            layout.used <= table.len(), table.len() == original_table.len(),
            original_table == old(table)@, original_work == old(work)@,
            crate::table_preparation_specs::root_capacity_allowed(
                entries::alphabet(&codetype), layout.used as nat),
            crate::table_preparation_specs::sorted_workspace(lens@, original_work, work@),
            huffman_specs::tables_match(entries::alphabet(&codetype), base@, extra@, match_),
            huffman_specs::remaining_histogram(original_counts, count@, sym as nat),
            huffman_specs::bucket_ordered(lens@, original_counts, work@),
            huff <= u32::MAX,
            huffman_specs::is_reversal(reversed_huff, huff as u32),
            crate::constructor_pages_specs::ownership(lens@, original_counts, work@,
                root as nat, max as nat, layout.used as int, sym as nat, regions, openings),
            crate::constructor_pages_specs::first_openings(lens@, work@, root as nat, openings),
            crate::constructor_table_specs::progress(entries::alphabet(&codetype),
                lens@, work@, sym as nat, root as nat, layout.used as int,
                regions, original_table, table@),
        invariant_except_break
            drop_ != 0 ==> low == (huff & mask),
            huffman_specs::before(original_counts, len as nat) <= sym
                < huffman_specs::before(original_counts, len as nat + 1),
            sym < huffman_specs::before(original_counts, 16),
            sym < work.len(), work@[sym as int] < lens.len(),
            lens@[work@[sym as int] as int] == len,
            reversed_huff as int == huffman_specs::normalized_cursor(original_counts,
                len as nat, sym as nat),
            huffman_specs::aligned_cursor(reversed_huff, len as u32),
            huff < huffman_specs::capacity(len as nat),
        ensures sym == huffman_specs::before(original_counts, 16), len == max,
            huff == if huffman_specs::slots(original_counts, 15) == 0 { 0usize } else { 1 },
        decreases huffman_proofs::remaining_symbols(
            huffman_specs::before(original_counts, 16), sym as nat),
    ))]
    'outer: loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost current_symbol = sym;
            let ghost current_length = len;
            let ghost current_cursor = reversed_huff;
            let ghost before_emission = table@;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            huffman_proofs::normalized_cursor_bound(lens@, original_counts, work@,
                len as nat, sym as nat);
            huffman_proofs::reversal_matches_model(reversed_huff, huff as u32);
            assert(huff as u32
                == huffman_specs::canonical_prefix(lens@, work@[sym as int] as int));
            crate::constructor_table_proofs::native_code_parts(huff, root, mask);
            if drop_ == 0 {
                assert(huff >> drop_ == huff) by (bit_vector) requires drop_ == 0;
            }
            assert(crate::constructor_pages_specs::emission_region(lens@,
                root as nat, regions, work@[sym as int] as int, layout.next as nat,
                layout.width as nat, (len - drop_) as nat, (huff >> drop_) as nat));
            crate::constructor_pages_proofs::emission_parameters(lens@, original_counts,
                work@, root as nat, max as nat, layout.used as int, sym as nat,
                regions, openings, work@[sym as int] as int, layout.next as nat,
                layout.width as nat, (len - drop_) as nat, (huff >> drop_) as nat);
        }
        let (here, min) = emission::emit_entry(
            &codetype,
            work[sym],
            emission::EntryPosition {
                length: len,
                drop: drop_,
                prefix: huff >> drop_,
            },
            (base, extra, match_),
            table,
            &layout,
        );
        #[cfg(not(verus_keep_ghost))]
        let _ = here;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(crate::table_emission_specs::result(entries::alphabet(&codetype),
                work@[sym as int] as nat, (len - drop_) as nat,
                layout.next as nat, layout.width as nat, (huff >> drop_) as nat,
                before_emission, table@, here, min as nat));
            assert(crate::constructor_table_specs::progress(entries::alphabet(&codetype),
                lens@, work@, sym as nat + 1, root as nat, layout.used as int,
                regions, original_table, table@));
        }

        // advance the code and consume the current symbol
        let advanced = progress::advance_symbol(
            lens,
            work,
            &mut count,
            &mut sym,
            &mut len,
            max,
            reversed_huff,
        );
        reversed_huff = advanced.cursor;
        huff = advanced.code as usize;
        #[cfg(verus_keep_ghost)]
        proof! {
            crate::constructor_pages_proofs::advanced(lens@, original_counts, work@,
                root as nat, max as nat, layout.used as int,
                current_symbol as nat, sym as nat, regions, openings);
        }
        if !advanced.more {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(current_length == max);
                if huffman_specs::slots(original_counts, 15) == 0 {
                    huffman_proofs::complete_final_cursor(lens@, original_counts,
                        current_symbol as nat);
                    assert(advanced.cursor == 0);
                    huffman_proofs::zero_reversal();
                    huffman_proofs::reversal_unique(0, advanced.code, 0);
                } else {
                    crate::root_table_proofs::incomplete_one_bit_shape(lens@, original_counts);
                    assert(current_symbol == 0 && current_cursor == 0);
                    assert(huffman_specs::capacity(31) == 0x80000000) by (compute);
                    assert(advanced.cursor == 0x80000000);
                    assert(huffman_specs::capacity(1) == 2) by (compute);
                    crate::root_table_proofs::incomplete_cursor_code(advanced.cursor, advanced.code);
                }
            }
            break 'outer;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            huffman_proofs::depth_capacity(len as nat);
            huffman_proofs::normalized_cursor_bound(lens@, original_counts, work@,
                len as nat, sym as nat);
            huffman_proofs::reversal_matches_model(reversed_huff, huff as u32);
            crate::constructor_table_proofs::native_code_parts(huff, root, mask);
        }

        // create new sub-table if needed
        if len > root && (huff & mask) != low {
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_used = layout.used;
                let ghost previous_table = table@;
                let ghost opening = crate::page_source_specs::Opening {
                    symbol: work@[sym as int] as int, position: sym as nat,
                    length: len as nat, remaining: count@,
                };
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                crate::constructor_pages_proofs::fresh_key(lens@, original_counts, work@,
                    root as nat, max as nat, layout.used as int, current_symbol as nat,
                    sym as nat, regions, openings, (huff & mask) as int);
                crate::constructor_pages_proofs::current_opening(lens@, original_counts,
                    work@, count@, sym as nat, len as nat, root as nat, max as nat,
                    reversed_huff, huff as u32);
                huffman_decode::low_mask_remainder(huff as u32, root as u32);
                assert(crate::page_source_specs::context(lens@, original_counts,
                    root as nat, max as nat, (huff & mask) as int, opening));
                reveal(crate::constructor_table_specs::progress);
                crate::constructor_table_proofs::first_opening(lens@, work@, root as nat,
                    regions, (huff & mask) as int, opening);
                crate::capacity_bound_proofs::finite_offsets(root as nat,
                    max as nat, layout.used as int, regions);
            }
            /* if first time, transition to sub-tables */
            if drop_ == 0 {
                drop_ = root;
            }

            if !layout::advance_and_link(
                &mut layout,
                &count,
                len,
                drop_,
                max,
                &codetype,
                min,
                table,
                root,
                huff & mask,
            ) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    reveal(crate::table_preparation_specs::root_capacity_allowed);
                    let key = (huff & mask) as int;
                    assert(table@ == previous_table);
                    crate::page_source_proofs::opening_result(count@, len as nat,
                        root as nat, max as nat, layout.width as nat, key);
                    assert(crate::constructor_pages_specs::ownership(lens@, original_counts,
                        work@, root as nat, max as nat, previous_used as int,
                        sym as nat, regions, openings));
                    crate::capacity_bound_proofs::candidate_storage(lens@, original_counts,
                        work@, bits as nat, root as nat, max as nat, previous_used as int,
                        sym as nat, regions, openings, key, layout.width as nat, opening,
                        table.len() as int);
                    let witness = crate::constructor_table_specs::Refusal {
                        processed: sym as nat, used: previous_used as int, key,
                        width: layout.width as nat, regions, openings, opening,
                    };
                    assert(crate::constructor_table_specs::refused(entries::alphabet(&codetype),
                        lens@, original_counts, work@, root as nat, max as nat,
                        original_table, table@, witness));
                    crate::constructor_table_proofs::refused_result(entries::alphabet(&codetype),
                        lens@, bits as nat, original_table, table@, original_work, work@, witness);
                    assert(crate::constructor_table_specs::result(entries::alphabet(&codetype),
                        lens@, bits as nat, original_table, table@, original_work, work@,
                        InflateTable::EnoughIsNotEnough));
                    if (matches!(codetype, CodeType::Lens) && bits == 10 && lens.len() <= 286)
                        || (matches!(codetype, CodeType::Dists) && bits == 9 && lens.len() <= 30) {
                        crate::capacity_bound_proofs::dynamic_no_capacity_error(
                            entries::alphabet(&codetype), lens@, bits as nat,
                            original_table, table@, original_work, work@,
                            InflateTable::EnoughIsNotEnough);
                    }
                }
                return InflateTable::EnoughIsNotEnough;
            }

            #[cfg(verus_keep_ghost)]
            proof! {
                reveal(crate::table_preparation_specs::root_capacity_allowed);
                let key = (huff & mask) as int;
                crate::page_source_proofs::opening_result(count@, len as nat,
                    root as nat, max as nat, layout.width as nat, key);
                assert(crate::constructor_pages_specs::ownership(lens@, original_counts,
                    work@, root as nat, max as nat, previous_used as int,
                    sym as nat, regions, openings));
                crate::capacity_bound_proofs::candidate_storage(lens@, original_counts,
                    work@, bits as nat, root as nat, max as nat, previous_used as int,
                    sym as nat, regions, openings, key, layout.width as nat, opening,
                    table.len() as int);
                let next_regions = regions.update(key, Some(crate::table_pages_specs::Page {
                    base: layout.next as int, width: layout.width as nat,
                }));
                let next_openings = openings.update(key, Some(opening));
                assert(next_openings == openings.update(key, Some(opening)));
                crate::constructor_pages_proofs::first_openings_updated(lens@, work@,
                    root as nat, openings, key, opening);
                crate::constructor_pages_proofs::opening_ledger_frame(lens@, original_counts,
                    work@, root as nat, max as nat, layout.used as int, sym as nat,
                    next_regions, openings.update(key, Some(opening)), next_openings);
                assert(crate::constructor_table_specs::progress(entries::alphabet(&codetype),
                    lens@, work@, sym as nat, root as nat, layout.used as int,
                    next_regions, original_table, table@));
                regions = next_regions;
                openings = next_openings;
            }
            low = huff & mask;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(low == (huff & mask));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            huffman_proofs::remaining_symbols_decreases(
                huffman_specs::before(original_counts, 16), current_symbol as nat, sym as nat);
        }
    }

    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost completed_table = table@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        if root == max {
            crate::constructor_table_proofs::root_corollary(entries::alphabet(&codetype),
                lens@, work@, sym as nat, root as nat, layout.used as int,
                regions, original_table, table@);
        }
    }
    /* fill in remaining table entry if code is incomplete (guaranteed to have
    at most one remaining entry, since if the code is incomplete, the
    maximum code length that was allowed to get this far is one bit) */
    if huff != 0 {
        let here = Code {
            op: 64,
            bits: (len - drop_) as u8,
            val: 0,
        };

        table[layout.next..][huff] = here;
    }

    #[cfg(verus_keep_ghost)]
    proof! {
        if huffman_specs::slots(original_counts, 15) == 0 {
            crate::constructor_table_proofs::complete(entries::alphabet(&codetype),
                lens@, original_counts, work@, root as nat, max as nat,
                layout.used as int, sym as nat, regions, openings, original_table, table@);
            if root == max {
                crate::root_table_proofs::complete(entries::alphabet(&codetype), lens@, work@,
                    root as nat, original_table, table@);
            }
        } else {
            crate::root_table_proofs::incomplete(entries::alphabet(&codetype), lens@, work@,
                original_table, completed_table, table@);
            crate::linked_table_proofs::direct_table(entries::alphabet(&codetype),
                lens@, root as nat, table@);
        }
        if matches!(codetype, CodeType::Codes) && bits <= 7 && max <= bits {
            crate::root_table_proofs::legacy_codes(lens@, work@, original_table, table@);
            assert(huffman_specs::root_entry_decodes(lens@, table@[0], 0));
        }
    }
    /* set return parameters */
    #[cfg(verus_keep_ghost)]
    proof! {
        if matches!(codetype, CodeType::Codes) && bits <= 7 && max <= bits {
            assert(table@[0].op == 0);
        }
        if root == max {
            crate::root_table_proofs::ready_result(entries::alphabet(&codetype), lens@,
                original_table, table@, original_work, work@, root, layout.used);
        }
        crate::constructor_table_proofs::ready_result(entries::alphabet(&codetype),
            lens@, bits as nat, original_table, table@, original_work, work@, root, layout.used);
    }
    InflateTable::Success {
        root,
        used: layout.used,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn maximizing_dynamic_histograms_fit_the_exact_native_buffers() {
        let sentinel = Code {
            op: 255,
            bits: 15,
            val: u16::MAX,
        };
        for (kind, counts, root, limit) in [
            (
                CodeType::Lens,
                [0usize, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 233, 45, 1, 1, 2],
                10,
                crate::ENOUGH_LENS,
            ),
            (
                CodeType::Dists,
                [0usize, 0, 3, 1, 1, 1, 1, 0, 0, 0, 13, 5, 1, 1, 1, 2],
                9,
                crate::ENOUGH_DISTS,
            ),
        ] {
            let lengths = counts
                .iter()
                .enumerate()
                .skip(1)
                .flat_map(|(length, &count)| std::iter::repeat(length as u16).take(count))
                .collect::<Vec<_>>();
            let mut table = vec![sentinel; limit + 2];
            let mut work = vec![u16::MAX; lengths.len()];
            assert_eq!(
                inflate_table(kind, &lengths, &mut table[..limit], root, &mut work),
                InflateTable::Success { root, used: limit }
            );
            assert_eq!(&table[limit..], &[sentinel; 2]);
            assert!(work.iter().copied().eq(0..lengths.len() as u16));
        }
    }

    #[test]
    fn literal_and_distance_constructors_install_two_absolute_subtable_links() {
        let sentinel = Code {
            op: 64,
            bits: 1,
            val: 99,
        };
        for (kind, values, operations) in [
            (CodeType::Lens, [0, 1, 2, 3, 4, 5, 6], [0; 7]),
            (
                CodeType::Dists,
                [1, 2, 3, 4, 5, 7, 9],
                [16, 16, 16, 16, 17, 17, 18],
            ),
        ] {
            let mut table = [sentinel; 16];
            let mut work = [99; 7];
            let result = inflate_table(kind, &[1, 3, 3, 4, 4, 4, 4], &mut table, 2, &mut work);
            assert_eq!(result, InflateTable::Success { root: 2, used: 10 });
            assert_eq!(
                table[1],
                Code {
                    bits: 2,
                    op: 1,
                    val: 4
                }
            );
            assert_eq!(
                table[3],
                Code {
                    bits: 2,
                    op: 2,
                    val: 6
                }
            );
            assert_eq!(lookup_root_entry(&table, 2, u64::MAX - 2), table[1]);
            assert_eq!(lookup_root_entry(&table, 2, u64::MAX), table[3]);
            for (index, symbol) in [
                (0, 0),
                (2, 0),
                (4, 1),
                (5, 2),
                (6, 3),
                (8, 4),
                (7, 5),
                (9, 6),
            ] {
                assert_eq!(
                    table[index],
                    Code {
                        bits: if symbol <= 2 { 1 } else { 2 },
                        op: operations[symbol],
                        val: values[symbol],
                    }
                );
            }
            assert!(table[10..].iter().all(|entry| *entry == sentinel));
            for (word, expected) in [
                (1, 4),
                (5, 5),
                (9, 4),
                (13, 5),
                (3, 6),
                (7, 7),
                (11, 8),
                (15, 9),
            ] {
                let link = table[(word & 3) as usize];
                assert_eq!(lookup_subtable_index(word, link), expected);
                assert_eq!(lookup_subtable_index(word | !15, link), expected);
            }
        }
    }

    #[test]
    fn literal_constructor_emits_length_leaf_in_both_subtable_completions() {
        let sentinel = Code {
            bits: 1,
            op: 64,
            val: 99,
        };
        let mut lengths = [0; 266];
        lengths[..2].fill(2);
        lengths[2..4].fill(4);
        lengths[4..23].fill(6);
        lengths[256] = 6;
        lengths[264..].fill(5);
        let mut table = [sentinel; 40];
        let mut work = [42; 266];
        assert_eq!(
            inflate_table(CodeType::Lens, &lengths, &mut table, 2, &mut work),
            InflateTable::Success { root: 2, used: 36 },
        );
        assert_eq!(
            table[1],
            Code {
                bits: 2,
                op: 4,
                val: 4,
            },
        );
        assert_eq!(
            table[3],
            Code {
                bits: 2,
                op: 4,
                val: 20,
            },
        );
        for (word, index) in [(21, 9), (53, 17)] {
            assert_eq!(lookup_subtable_index(word, table[1]), index);
            assert_eq!(
                table[index],
                Code {
                    bits: 3,
                    op: 17,
                    val: 11,
                },
            );
        }
        assert_eq!(
            table[35],
            Code {
                bits: 4,
                op: 96,
                val: 0,
            },
        );
        assert!(table[36..].iter().all(|entry| *entry == sentinel));
        assert_eq!(work[..6], [0, 1, 2, 3, 264, 265]);
        assert!(work[26..].iter().all(|symbol| *symbol == 42));
    }

    #[test]
    fn subtable_index_handles_maximum_width_and_full_offset_without_narrowing() {
        for (link, word, expected) in [
            (
                Code {
                    bits: 14,
                    op: 1,
                    val: 32768,
                },
                0,
                32768,
            ),
            (
                Code {
                    bits: 14,
                    op: 1,
                    val: 32768,
                },
                u64::MAX,
                32769,
            ),
            (
                Code {
                    bits: 1,
                    op: 14,
                    val: 65535,
                },
                u64::MAX,
                81918,
            ),
        ] {
            assert_eq!(lookup_subtable_index(word, link), expected);
        }
    }

    #[test]
    fn resumed_dynamic_header_preserves_counts_completion_and_partial_frames() {
        let table = [
            Code {
                op: 0,
                bits: 1,
                val: 0,
            },
            Code {
                op: 0,
                bits: 1,
                val: 16,
            },
        ];
        for (nlen, ndist, initial_have, eob, initial_count, initial_word, expected, final_have) in [
            (257, 1, 0, 0, 1, 1, HeaderOutcome::NeedInput, 0),
            (257, 1, 0, 0, 3, 1, HeaderOutcome::InvalidRepeat, 0),
            (257, 1, 257, 0, 1, 0, HeaderOutcome::MissingEob, 258),
            (257, 1, 257, 1, 1, 0, HeaderOutcome::Complete, 258),
            (286, 30, 315, 1, 1, 0, HeaderOutcome::Complete, 316),
        ] {
            let mut lens = [u16::MAX; 320];
            lens[..nlen + ndist].fill(0);
            lens[256] = eob;
            let original = lens;
            let (mut word, mut count, mut have) = (initial_word, initial_count, initial_have);
            assert_eq!(
                resume_dynamic_header(
                    &mut word,
                    &mut count,
                    &[],
                    &table,
                    1,
                    &mut lens,
                    &mut have,
                    nlen,
                    ndist,
                ),
                (0, expected)
            );
            assert_eq!(have, final_have);
            assert_eq!(&lens[..initial_have], &original[..initial_have]);
            assert_eq!(&lens[have..], &original[have..]);
            match expected {
                HeaderOutcome::NeedInput => assert_eq!((word, count), (1, 1)),
                HeaderOutcome::InvalidRepeat => assert_eq!((word, count), (0, 2)),
                _ => assert_eq!((word, count), (0, 0)),
            }
        }
    }

    #[test]
    fn length_header_checks_eob_only_after_completion_and_preserves_stopped_fields() {
        for (symbol, initial_count, initial_have, eob, expected, final_count, final_have) in [
            (0, 1, 0, 0, HeaderOutcome::NeedInput, 1, 0),
            (0, 3, 0, 0, HeaderOutcome::InvalidRepeat, 2, 0),
            (0, 1, 256, 1, HeaderOutcome::MissingEob, 0, 257),
            (1, 1, 256, 0, HeaderOutcome::Complete, 0, 257),
            (0, 7, 257, 0, HeaderOutcome::MissingEob, 7, 257),
            (0, 7, 257, 1, HeaderOutcome::Complete, 7, 257),
        ] {
            let table = [
                Code {
                    op: 0,
                    bits: 1,
                    val: symbol,
                },
                Code {
                    op: 0,
                    bits: 1,
                    val: 16,
                },
            ];
            let mut lengths = [9u16; 260];
            lengths[..257].fill(0);
            lengths[256] = eob;
            let original = lengths;
            let mut have = initial_have;
            let mut count = initial_count;
            let mut word = u64::from(initial_have == 0);
            let initial_word = word;
            assert_eq!(
                read_length_header(
                    &mut word,
                    &mut count,
                    &[],
                    &table,
                    1,
                    &mut lengths,
                    &mut have,
                    257
                ),
                (0, expected)
            );
            assert_eq!(
                (word, count, have),
                (
                    if expected == HeaderOutcome::NeedInput || initial_have == 257 {
                        initial_word
                    } else {
                        0
                    },
                    final_count,
                    final_have
                )
            );
            assert_eq!(&lengths[..initial_have], &original[..initial_have]);
            assert_eq!(&lengths[final_have..], &original[final_have..]);
        }
    }

    #[test]
    fn streamed_header_table_join_preserves_exhaustion_and_constructor_frames() {
        let sentinel = Code {
            op: 16,
            bits: 3,
            val: 123,
        };
        let mut table = [sentinel; 130];
        let mut work = [42; 23];
        let mut lens = [u16::MAX; 23];
        let (mut word, mut count, mut have) = (0, 0, 0);
        assert_eq!(
            read_code_length_table(
                &mut word,
                &mut count,
                &[0x41],
                &mut lens,
                &mut have,
                4,
                &mut table,
                &mut work
            ),
            (1, None)
        );
        assert_eq!((word, count, have), (1, 2, 2));
        assert_eq!((lens[16], lens[17]), (1, 0));
        assert!(lens
            .iter()
            .enumerate()
            .all(|(symbol, &value)| symbol == 16 || symbol == 17 || value == u16::MAX));
        assert_eq!(table, [sentinel; 130]);
        assert_eq!(work, [42; 23]);
        assert_eq!(
            read_code_length_table(
                &mut word,
                &mut count,
                &[0],
                &mut lens,
                &mut have,
                4,
                &mut table,
                &mut work
            ),
            (1, Some(InflateTable::Success { root: 1, used: 2 }))
        );
        assert_eq!((word, count, have), (0, 4, 19));
        for (symbol, &value) in lens.iter().enumerate() {
            assert_eq!(
                value,
                match symbol {
                    16 | 18 => 1,
                    0..=18 => 0,
                    _ => u16::MAX,
                }
            );
        }
        assert_eq!(
            table[0],
            Code {
                op: 0,
                bits: 1,
                val: 16
            }
        );
        assert_eq!(
            table[1],
            Code {
                op: 0,
                bits: 1,
                val: 18
            }
        );
        assert_eq!(table[2..], [sentinel; 128]);
        assert_eq!(work[..2], [16, 18]);
        assert_eq!(work[2..], [42; 21]);

        table.fill(sentinel);
        work.fill(42);
        lens.fill(u16::MAX);
        (word, count, have) = (0, 0, 0);
        assert_eq!(
            read_code_length_table(
                &mut word,
                &mut count,
                &[0x49, 0],
                &mut lens,
                &mut have,
                4,
                &mut table,
                &mut work
            ),
            (2, Some(InflateTable::InvalidCode))
        );
        assert_eq!((word, count, have), (0, 4, 19));
        assert_eq!((lens[16], lens[17], lens[18]), (1, 1, 1));
        assert!(lens[..16].iter().all(|&value| value == 0));
        assert_eq!(lens[19..], [u16::MAX; 4]);
        assert_eq!(table, [sentinel; 130]);
        assert_eq!(work, [42; 23]);
    }

    #[test]
    fn rfc_canonical_example() {
        let lengths = [3, 3, 3, 3, 3, 2, 4, 4];
        let mut table = [Code::default(); 16];
        let mut work = [0; 8];
        assert_eq!(
            inflate_table(CodeType::Codes, &lengths, &mut table, 4, &mut work),
            InflateTable::Success { root: 4, used: 16 }
        );
        let symbols = [5, 2, 0, 4, 5, 3, 1, 6, 5, 2, 0, 4, 5, 3, 1, 7];
        let bits = [2, 3, 3, 3, 2, 3, 3, 4, 2, 3, 3, 3, 2, 3, 3, 4];
        for (index, code) in table.iter().enumerate() {
            assert_eq!(
                (code.op, code.bits, code.val),
                (0, bits[index], symbols[index])
            );
        }
    }

    #[test]
    fn root_only_fifteen_bit_codes_preserve_canonical_endpoints_and_suffixes() {
        let sentinel = Code {
            op: 64,
            bits: 3,
            val: 99,
        };
        let mut lengths = (1..=15).collect::<Vec<u16>>();
        lengths.push(15);
        let mut table = vec![sentinel; 32770];
        let mut work = [42; 18];
        assert_eq!(
            inflate_table(CodeType::Codes, &lengths, &mut table, usize::MAX, &mut work),
            InflateTable::Success {
                root: 15,
                used: 32768
            }
        );
        assert_eq!(
            table[0],
            Code {
                op: 0,
                bits: 1,
                val: 0
            }
        );
        assert_eq!(table[32766], table[0]);
        assert_eq!(
            table[16383],
            Code {
                op: 0,
                bits: 15,
                val: 14
            }
        );
        assert_eq!(
            table[32767],
            Code {
                op: 0,
                bits: 15,
                val: 15
            }
        );
        for high in [0, 0x1234_5678_9abc_0000, !32767u64] {
            assert_eq!(lookup_root_entry(&table, 15, high | 32766), table[0]);
            assert_eq!(
                lookup_root_entry(&table, 15, high | 16383),
                Code {
                    op: 0,
                    bits: 15,
                    val: 14
                }
            );
            assert_eq!(
                lookup_root_entry(&table, 15, high | 32767),
                Code {
                    op: 0,
                    bits: 15,
                    val: 15
                }
            );
        }
        assert_eq!(&table[32768..], &[sentinel; 2]);
        assert!(work[..16].iter().copied().eq(0..16));
        assert_eq!(&work[16..], &[42; 2]);
    }

    #[test]
    fn root_only_capacity_rejection_follows_sorting_without_table_writes() {
        for (kind, root, accepted) in [
            (CodeType::Lens, 10, true),
            (CodeType::Lens, 11, false),
            (CodeType::Dists, 9, true),
            (CodeType::Dists, 10, false),
        ] {
            let first = if matches!(kind, CodeType::Lens) {
                Code {
                    op: 0,
                    bits: 1,
                    val: 0,
                }
            } else {
                Code {
                    op: 16,
                    bits: 1,
                    val: 1,
                }
            };
            let mut lengths = (1..=root as u16).collect::<Vec<_>>();
            lengths.push(root as u16);
            let sentinel = Code {
                op: 64,
                bits: 3,
                val: 99,
            };
            let used = 1 << root;
            let mut table = vec![sentinel; used + 2];
            let mut work = vec![42; lengths.len() + 2];
            assert_eq!(
                inflate_table(kind, &lengths, &mut table, usize::MAX, &mut work),
                if accepted {
                    InflateTable::Success { root, used }
                } else {
                    InflateTable::EnoughIsNotEnough
                }
            );
            assert!(work[..lengths.len()]
                .iter()
                .copied()
                .eq(0..lengths.len() as u16));
            assert_eq!(&work[lengths.len()..], &[42; 2]);
            if accepted {
                assert_eq!(table[0], first);
                assert_eq!(&table[used..], &[sentinel; 2]);
            } else {
                assert!(table.iter().all(|entry| *entry == sentinel));
            }
        }
    }

    #[test]
    fn incomplete_one_bit_roots_keep_leaf_roles_and_write_only_the_invalid_hole() {
        for (kind, symbol, op, val) in [
            (CodeType::Lens, 65, 0, 65),
            (CodeType::Lens, 256, 96, 0),
            (CodeType::Lens, 265, 17, 11),
            (CodeType::Lens, 286, 77, 0),
            (CodeType::Dists, 0, 16, 1),
            (CodeType::Dists, 29, 29, 24577),
            (CodeType::Dists, 30, 64, 0),
            (CodeType::Dists, 31, 64, 0),
        ] {
            let mut lengths = vec![0; symbol + 1];
            lengths[symbol] = 1;
            let sentinel = Code {
                op: 64,
                bits: 3,
                val: 99,
            };
            let mut table = [sentinel; 4];
            let mut work = [42; 3];
            assert_eq!(
                inflate_table(kind, &lengths, &mut table, usize::MAX, &mut work),
                InflateTable::Success { root: 1, used: 2 }
            );
            assert_eq!(
                table,
                [
                    Code { op, bits: 1, val },
                    Code {
                        op: 64,
                        bits: 1,
                        val: 0
                    },
                    sentinel,
                    sentinel,
                ]
            );
            assert_eq!(work, [symbol as u16, 42, 42]);
            assert_eq!(
                lookup_root_entry(&table, 1, u64::MAX - 1),
                Code { op, bits: 1, val }
            );
            assert_eq!(
                lookup_root_entry(&table, 1, u64::MAX),
                Code {
                    op: 64,
                    bits: 1,
                    val: 0
                }
            );
        }
    }

    #[test]
    fn root_only_outcomes_preserve_the_required_error_and_empty_frames() {
        let sentinel = Code {
            op: 16,
            bits: 3,
            val: 123,
        };
        let mut table = [sentinel; 4];
        let mut work = [42; 1];
        for lengths in [&[1, 1, 1][..], &[2][..]] {
            assert_eq!(
                inflate_table(CodeType::Codes, lengths, &mut table, 7, &mut work),
                InflateTable::InvalidCode
            );
            assert_eq!(table, [sentinel; 4]);
            assert_eq!(work, [42]);
        }
        assert_eq!(
            inflate_table(CodeType::Codes, &[0, 0], &mut table, 7, &mut work),
            InflateTable::Success { root: 1, used: 2 }
        );
        assert_eq!(work, [42]);
        let invalid = Code {
            op: 64,
            bits: 1,
            val: 0,
        };
        assert_eq!(table, [invalid, invalid, sentinel, sentinel]);
    }

    #[test]
    fn root_only_canonical_output_preserves_table_and_workspace_suffixes() {
        let sentinel = Code {
            op: 64,
            bits: 7,
            val: 123,
        };
        let mut table = [sentinel; 6];
        let mut work = [42; 6];
        assert_eq!(
            inflate_table(CodeType::Codes, &[2, 0, 1, 2], &mut table, 7, &mut work),
            InflateTable::Success { root: 2, used: 4 }
        );
        assert_eq!(work, [2, 0, 3, 42, 42, 42]);
        assert_eq!(&table[4..], &[sentinel; 2]);
        let expected = [(1, 2), (2, 0), (1, 2), (2, 3)];
        for (code, (bits, symbol)) in table[..4].iter().zip(expected) {
            assert_eq!((code.op, code.bits, code.val), (0, bits, symbol));
        }
    }

    #[test]
    fn subtable_entries_consume_only_the_remaining_code_bits() {
        let mut table = [Code::default(); 6];
        let mut work = [0; 5];
        assert_eq!(
            inflate_table(
                CodeType::Codes,
                &[1, 0, 3, 3, 3, 3],
                &mut table,
                1,
                &mut work
            ),
            InflateTable::Success { root: 1, used: 6 }
        );
        let expected = [
            (0, 1, 0),
            (2, 1, 2),
            (0, 2, 2),
            (0, 2, 4),
            (0, 2, 3),
            (0, 2, 5),
        ];
        for (code, expected) in table.iter().zip(expected) {
            assert_eq!((code.op, code.bits, code.val), expected);
        }
    }

    #[test]
    fn entry_semantics_cover_alphabet_and_reserved_symbol_boundaries() {
        let cases = [
            (CodeType::Codes, [16, 18], [(0, 16), (0, 18)]),
            (CodeType::Lens, [255, 256], [(0, 255), (96, 0)]),
            (CodeType::Lens, [257, 285], [(16, 3), (16, 258)]),
            (CodeType::Lens, [284, 287], [(21, 227), (202, 0)]),
            (CodeType::Lens, [286, 287], [(77, 0), (202, 0)]),
            (CodeType::Dists, [0, 29], [(16, 1), (29, 24577)]),
            (CodeType::Dists, [30, 31], [(64, 0), (64, 0)]),
        ];
        for (kind, symbols, expected) in cases {
            let mut lengths = [0; 288];
            lengths[symbols[0]] = 1;
            lengths[symbols[1]] = 1;
            let mut table = [Code::default(); 2];
            let mut work = [0; 2];
            assert_eq!(
                inflate_table(kind, &lengths[..=symbols[1]], &mut table, 1, &mut work),
                InflateTable::Success { root: 1, used: 2 }
            );
            for (code, expected) in table.iter().zip(expected) {
                assert_eq!((code.op, code.val), expected);
                assert_eq!(code.bits, 1);
            }
        }
    }

    #[test]
    fn not_enough_errors() {
        // we need to call inflate_table() directly in order to manifest
        // not-enough errors, since zlib insures that enough is always enough

        let table = [Code::default(); crate::ENOUGH_DISTS];

        let mut work = [0; 16];
        let mut lens: [_; 16] = core::array::from_fn(|i| (i + 1) as u16);
        lens[15] = 15;

        let mut next = table;
        let bits = 15;
        let ret = inflate_table(CodeType::Dists, &lens[..16], &mut next, bits, &mut work);
        assert_eq!(ret, InflateTable::EnoughIsNotEnough);

        let mut next = table;
        let bits = 1;
        let ret = inflate_table(CodeType::Dists, &lens[..16], &mut next, bits, &mut work);
        assert_eq!(ret, InflateTable::EnoughIsNotEnough);
    }

    fn build_fixed_length_table(work: &mut [u16]) -> [Code; 512] {
        let mut lens = [0; 288];

        // literal/length table
        let mut sym = 0usize;
        while sym < 144 {
            lens[sym] = 8;
            sym += 1;
        }
        while sym < 256 {
            lens[sym] = 9;
            sym += 1;
        }
        while sym < 280 {
            lens[sym] = 7;
            sym += 1;
        }
        while sym < 288 {
            lens[sym] = 8;
            sym += 1;
        }

        let mut next = [Code::default(); 512];
        let bits = 9;
        inflate_table(CodeType::Lens, &lens[..288], &mut next, bits, work);

        core::array::from_fn(|i| {
            let mut code = next[i];

            code.op = if i & 0b0111_1111 == 99 { 64 } else { code.op };

            code
        })
    }

    #[test]
    fn generate_fixed_length_table() {
        let mut work = [0; 512];
        let generated = build_fixed_length_table(&mut work);

        assert_eq!(generated, crate::inflate::inffixed_tbl::LENFIX);
        let table = crate::inflate::inffixed_tbl::fixed_literal_table();
        assert_eq!(*table, generated);
        for (index, expected) in generated.iter().enumerate() {
            for high in [0, !511u64] {
                assert_eq!(lookup_root_entry(table, 9, high | index as u64), *expected);
            }
        }
        for index in [0, 128, 256, 384] {
            assert_eq!(
                table[index],
                Code {
                    op: 96,
                    bits: 7,
                    val: 0
                }
            );
        }
        for index in [99, 227, 355, 483] {
            assert_eq!(
                table[index],
                Code {
                    op: 64,
                    bits: 8,
                    val: 0
                }
            );
        }
        assert_eq!(
            table[12],
            Code {
                op: 0,
                bits: 8,
                val: 0
            }
        );
        assert_eq!(
            table[511],
            Code {
                op: 0,
                bits: 9,
                val: 255
            }
        );
    }

    fn build_fixed_distance_table(work: &mut [u16]) -> [Code; 32] {
        let mut lens = [0; 288];

        let mut sym = 0;
        while sym < 32 {
            lens[sym] = 5;
            sym += 1;
        }

        let mut next = [Code::default(); 32];
        let bits = 5;
        inflate_table(CodeType::Dists, &lens[..32], &mut next, bits, work);

        next
    }

    #[test]
    fn generate_fixed_distance_table() {
        let mut work = [0; 512];
        let generated = build_fixed_distance_table(&mut work);

        assert_eq!(generated, crate::inflate::inffixed_tbl::DISTFIX);
        let table = crate::inflate::inffixed_tbl::fixed_distance_table();
        assert_eq!(*table, generated);
        for (index, expected) in generated.iter().enumerate() {
            for high in [0, !31u64] {
                assert_eq!(lookup_root_entry(table, 5, high | index as u64), *expected);
            }
        }
        assert_eq!(
            table[0],
            Code {
                op: 16,
                bits: 5,
                val: 1
            }
        );
        assert_eq!(
            table[15],
            Code {
                op: 64,
                bits: 5,
                val: 0
            }
        );
        assert_eq!(
            table[23],
            Code {
                op: 29,
                bits: 5,
                val: 24577
            }
        );
        assert_eq!(
            table[31],
            Code {
                op: 64,
                bits: 5,
                val: 0
            }
        );
    }
}
