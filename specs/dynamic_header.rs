use crate::{bit_specs, huffman_specs};
use vstd::prelude::*;

verus! {

pub open spec fn wire_symbol(position: nat) -> nat
    recommends position < 19,
{
    if position < 3 { 16 + position }
    else if position == 3 { 0 }
    else if position % 2 == 0 { 6 + position / 2 }
    else { ((19 - position) / 2) as nat }
}

pub open spec fn wire_position(symbol: nat) -> nat
    recommends symbol < 19,
{
    if symbol >= 16 { (symbol - 16) as nat }
    else if symbol == 0 { 3 }
    else if symbol <= 7 { (19 - 2 * symbol) as nat }
    else { (2 * (symbol - 6)) as nat }
}

#[verifier::opaque]
pub open spec fn prefix_fits(lengths: Seq<u16>, processed: nat) -> bool {
    lengths.len() >= 19 && processed <= 19
        && forall|position: nat| position < processed ==>
            #[trigger] lengths[wire_symbol(position) as int] <= 7
}

// RFC 1951 3.2.7: HLIT (5 bits), HDIST (5 bits), HCLEN (4 bits).
pub open spec fn header_counts(source: Seq<bool>) -> (nat, nat, nat)
    recommends source.len() >= 14,
{
    (257 + bit_specs::low_first_value(source.take(5)),
        1 + bit_specs::low_first_value(source.subrange(5, 10)),
        4 + bit_specs::low_first_value(source.subrange(10, 14)))
}

// RFC 1951 3.2.7: three-bit fields in wire order, then zero omitted lengths.
pub open spec fn length_header(before: Seq<u16>, start: nat, end: nat,
    source: Seq<bool>, padded: bool) -> Seq<u16>
    recommends before.len() >= 19, start <= end <= 19, 3 * (end - start) <= source.len(),
{
    Seq::new(before.len(), |index: int|
        if index < 19 && start <= wire_position(index as nat) < end {
            bit_specs::three_bit_value(source.skip(3 * (wire_position(index as nat) - start)))
        } else if padded && index < 19 && end <= wire_position(index as nat) {
            0
        } else { before[index] })
}

pub open spec fn padded_header(before: Seq<u16>, after: Seq<u16>, processed: nat) -> bool {
    before.len() >= 19 && after.len() == before.len() && processed <= 19
        && (forall|position: nat| position < 19 ==>
            #[trigger] after[wire_symbol(position) as int]
                == if position < processed { before[wire_symbol(position) as int] } else { 0 })
        && (forall|index: int| 19 <= index < before.len() ==>
            #[trigger] after[index] == before[index])
}

pub open spec fn decoded_prefix(lengths: Seq<u16>, processed: nat) -> bool {
    processed <= lengths.len()
        && forall|index: int| 0 <= index < processed ==> #[trigger] lengths[index] <= 15
}

pub open spec fn repeat_extra_limit(symbol: nat) -> nat {
    if symbol == 16 { 4 } else if symbol == 17 { 8 } else { 128 }
}

// RFC 1951 3.2.7: repeat extra fields use two, three, or seven low-first bits.
pub open spec fn repeat_extra_width(symbol: nat) -> nat {
    if symbol == 16 { 2 } else if symbol == 17 { 3 } else { 7 }
}

#[verifier::opaque]
pub open spec fn repeat_extra_value(source: Seq<bool>, code_bits: nat, symbol: nat) -> nat
    recommends source.len() >= code_bits + repeat_extra_width(symbol),
{
    bit_specs::low_first_value(source.subrange(code_bits as int,
        (code_bits + repeat_extra_width(symbol)) as int))
}

// Baseline 5dbef50 CodeLens partial-commit policy, not an RFC error-code rule.
pub open spec fn repeat_consumed_bits(available: nat, code_bits: nat, symbol: nat, have: nat) -> nat {
    if available < code_bits + repeat_extra_width(symbol) { 0 }
    else if symbol == 16 && have == 0 { code_bits }
    else { code_bits + repeat_extra_width(symbol) }
}

pub open spec fn repeat_count(symbol: nat, extra: nat) -> nat {
    if symbol == 18 { 11 + extra } else { 3 + extra }
}

pub open spec fn repeat_value(lengths: Seq<u16>, processed: nat, symbol: nat) -> u16 {
    if symbol == 16 && 0 < processed <= lengths.len() { lengths[processed as int - 1] } else { 0 }
}

pub open spec fn repeat_fits(processed: nat, total: nat, symbol: nat, extra: nat) -> bool {
    (symbol != 16 || processed > 0) && processed + repeat_count(symbol, extra) <= total
}

pub open spec fn repeat_transition(before: Seq<u16>, after: Seq<u16>,
    processed: nat, final_processed: nat, total: nat, symbol: nat, extra: nat, success: bool) -> bool {
    let fits = repeat_fits(processed, total, symbol, extra);
    let count = repeat_count(symbol, extra);
    after.len() == before.len()
        && success == fits
        && final_processed == if fits { processed + count } else { processed }
        && forall|index: int| 0 <= index < before.len() ==>
            #[trigger] after[index] == if fits && processed <= index < processed + count {
                repeat_value(before, processed, symbol)
            } else { before[index] }
}

pub open spec fn repeat_input_transition(before: Seq<u16>, after: Seq<u16>,
    processed: nat, final_processed: nat, total: nat, source: Seq<bool>,
    code_bits: nat, symbol: nat, outcome: Option<bool>) -> bool {
    if source.len() < code_bits + repeat_extra_width(symbol) {
        outcome.is_none() && after == before && final_processed == processed
    } else {
        match outcome {
            Some(success) => repeat_transition(before, after, processed, final_processed,
                total, symbol, repeat_extra_value(source, code_bits, symbol), success),
            None => false,
        }
    }
}

pub open spec fn direct_transition(before: Seq<u16>, after: Seq<u16>,
    processed: nat, final_processed: nat, value: u16) -> bool {
    after.len() == before.len() && final_processed == processed + 1
        && forall|index: int| 0 <= index < before.len() ==>
            #[trigger] after[index] == if index == processed { value } else { before[index] }
}

// RFC 1951 3.2.7; byte accounting and partial commits follow baseline 5dbef50.
#[verifier::opaque]
pub open spec fn symbol_input_effect(before: Seq<u16>, after: Seq<u16>,
    processed: nat, final_processed: nat, total: nat, source: Seq<bool>,
    count: u8, available: nat, code_bits: nat, symbol: nat,
    reported: nat, dropped: nat, outcome: Option<bool>) -> bool {
    let target = if symbol < 16 { code_bits }
        else { code_bits + repeat_extra_width(symbol) };
    let needed = bit_specs::needed_bytes(count, target as usize);
    reported == if needed <= available { needed } else { available }
        && if symbol < 16 {
            outcome == Some(true) && dropped == code_bits
                && direct_transition(before, after, processed, final_processed, symbol as u16)
        } else {
            dropped == repeat_consumed_bits(source.len(), code_bits, symbol, processed)
                && repeat_input_transition(before, after, processed, final_processed,
                    total, source, code_bits, symbol, outcome)
        }
}

#[verifier::opaque]
pub open spec fn symbol_input_transition(alphabet: Seq<u16>,
    before: Seq<u16>, after: Seq<u16>, processed: nat, final_processed: nat,
    total: nat, source: Seq<bool>, count: u8, available: nat,
    reported: nat, dropped: nat, outcome: Option<bool>) -> bool {
    // The successful empty constructor uses one-bit invalid entries with value zero.
    // This is baseline error timing, not an RFC interpretation of an empty tree.
    if huffman_specs::maximum_length(alphabet) == 0 && source.len() > 0 {
        symbol_input_effect(before, after, processed, final_processed, total,
            source, count, available, 1, 0, reported, dropped, outcome)
    } else if huffman_specs::maximum_length(alphabet) > 0
        && exists|symbol: int| huffman_specs::code_length_source_prefix(alphabet, symbol, source) {
        exists|symbol: int| #[trigger] huffman_specs::code_length_source_prefix(alphabet, symbol, source)
            && symbol_input_effect(before, after, processed, final_processed, total,
                source, count, available, alphabet[symbol] as nat, symbol as nat,
                reported, dropped, outcome)
    } else {
        outcome.is_none() && reported == 0 && dropped == 0
            && after == before && final_processed == processed
    }
}

}
