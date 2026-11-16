use crate::Code;

#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum CodeType {
    Codes,
    Lens,
    Dists,
}

/// Length codes 257..285 base
#[cfg_attr(verus_keep_ghost, verus_verify)]
const LBASE: [u16; 31] = [
    3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131,
    163, 195, 227, 258, 0, 0,
];
/// Length codes 257..285 extra
#[cfg_attr(verus_keep_ghost, verus_verify)]
const LEXT: [u8; 31] = [
    16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 20, 20,
    21, 21, 21, 21, 16, 77, 202,
];
/// Distance codes 0..29 base
#[cfg_attr(verus_keep_ghost, verus_verify)]
const DBASE: [u16; 32] = [
    1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537,
    2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577, 0, 0,
];
/// Distance codes 0..29 extra
#[cfg_attr(verus_keep_ghost, verus_verify)]
const DEXT: [u8; 32] = [
    16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22, 23, 23, 24, 24, 25, 25, 26, 26,
    27, 27, 28, 28, 29, 29, 64, 64,
];

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn alphabet(kind: &CodeType) -> huffman_specs::Alphabet {
    match kind {
        CodeType::Codes => huffman_specs::Alphabet::CodeLengths,
        CodeType::Lens => huffman_specs::Alphabet::LiteralLengths,
        CodeType::Dists => huffman_specs::Alphabet::Distances,
    }
}

proof fn distance_table_entry(index: int)
    requires 0 <= index < 30,
    ensures DBASE@[index] == huffman_specs::distance_base(index as nat),
        DEXT@[index] == 16 + huffman_specs::distance_extra(index as nat),
    decreases index,
{
    if index >= 4 {
        distance_table_entry(index - 2);
        huffman_proofs::distance_base_step(index as nat);
        assert(DBASE@[index] == 2 * DBASE@[index - 2] - 1);
        assert(DEXT@[index] == DEXT@[index - 2] + 1);
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures huffman_specs::tables_match(alphabet(kind), result.0@, result.1@, result.2),
))]
pub(super) fn table_parameters(kind: &CodeType) -> (&'static [u16], &'static [u8], u16) {
    match kind {
        CodeType::Codes => (&[], &[], 20),
        CodeType::Lens => {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(huffman_specs::invalid_operation(77)) by (compute);
                assert(huffman_specs::invalid_operation(202)) by (compute);
                assert forall|index: int| 0 <= index < 29 implies
                    #[trigger] LBASE@[index] == huffman_specs::length_base((index + 257) as nat)
                        && #[trigger] LEXT@[index]
                            == 16 + huffman_specs::length_extra((index + 257) as nat) by {
                    reveal_with_fuel(huffman_specs::capacity, 8);
                }
                assert forall|index: int| 29 <= index < 31 implies
                    #[trigger] LBASE@[index] == 0
                        && huffman_specs::invalid_operation(#[trigger] LEXT@[index]) by {}
            }
            (&LBASE, &LEXT, 257)
        }
        CodeType::Dists => {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|index: int| 0 <= index < 30 implies
                    #[trigger] DBASE@[index] == huffman_specs::distance_base(index as nat)
                        && #[trigger] DEXT@[index]
                            == 16 + huffman_specs::distance_extra(index as nat) by {
                    distance_table_entry(index);
                }
                assert(huffman_specs::invalid_operation(64)) by (compute);
                assert forall|index: int| 30 <= index < 32 implies
                    #[trigger] DBASE@[index] == 0
                        && huffman_specs::invalid_operation(#[trigger] DEXT@[index]) by {}
            }
            (&DBASE, &DEXT, 0)
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires drop < length <= 15,
        huffman_specs::symbol_domain(alphabet(kind), symbol as nat),
        huffman_specs::tables_match(alphabet(kind), base@, extra@, threshold),
    ensures result.bits == length - drop,
        huffman_specs::entry_meaning(alphabet(kind), symbol as nat, result.op, result.val),
))]
pub(super) fn make_entry(
    kind: &CodeType,
    symbol: u16,
    length: usize,
    drop: usize,
    base: &[u16],
    extra: &[u8],
    threshold: u16,
) -> Code {
    let _ = kind;
    if symbol >= threshold {
        Code {
            bits: (length - drop) as u8,
            op: extra[(symbol - threshold) as usize],
            val: base[(symbol - threshold) as usize],
        }
    } else if symbol + 1 < threshold {
        Code {
            bits: (length - drop) as u8,
            op: 0,
            val: symbol,
        }
    } else {
        Code {
            bits: (length - drop) as u8,
            op: 0b01100000,
            val: 0,
        }
    }
}
