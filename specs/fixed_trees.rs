use crate::huffman_specs as h;
use crate::Code;
use vstd::prelude::*;

verus! {

// RFC 1951 (May 1996), section 3.2.6. These are source symbol ranges,
// independent of the checked-in decoding tables and their cell order.
pub(crate) open spec fn literal_length(symbol: int) -> u16 {
    if symbol < 144 { 8 } else if symbol < 256 { 9 }
    else if symbol < 280 { 7 } else { 8 }
}

pub(crate) open spec fn literal_lengths() -> Seq<u16> {
    Seq::new(288, |symbol: int| literal_length(symbol))
}

pub(crate) open spec fn distance_lengths() -> Seq<u16> {
    Seq::new(32, |symbol: int| 5u16)
}

pub(crate) open spec fn reverse_five(word: u32) -> u32 {
    ((word & 1) << 4) | ((word & 2) << 2) | (word & 4)
        | ((word & 8) >> 2) | ((word & 16) >> 4)
}

pub(crate) open spec fn distance_entry(index: int) -> Code
    recommends 0 <= index < 32,
{
    let symbol = reverse_five(index as u32) as nat;
    Code { op: if symbol <= 29 { (16 + h::distance_extra(symbol)) as u8 } else { 64 },
        bits: 5, val: if symbol <= 29 { h::distance_base(symbol) as u16 } else { 0 } }
}

pub(crate) open spec fn reverse_nine(word: u32) -> u32 {
    ((word & 1) << 8) | ((word & 2) << 6) | ((word & 4) << 4)
        | ((word & 8) << 2) | (word & 16) | ((word & 32) >> 2)
        | ((word & 64) >> 4) | ((word & 128) >> 6) | ((word & 256) >> 8)
}

pub(crate) open spec fn literal_symbol(index: u32) -> int {
    let reversed = reverse_nine(index) as int;
    if reversed < 96 { 256 + reversed / 4 }
    else if reversed < 384 { reversed / 2 - 48 }
    else if reversed < 400 { reversed / 2 + 88 }
    else { reversed - 256 }
}

pub(crate) open spec fn literal_entry(index: int) -> Code
    recommends 0 <= index < 512,
{
    let symbol = literal_symbol(index as u32);
    Code { op: if symbol < 256 { 0 } else if symbol == 256 { 96 }
            else if symbol <= 285 { (16 + h::length_extra(symbol as nat)) as u8 }
            else { 64 },
        bits: literal_length(symbol) as u8,
        val: if symbol < 256 { symbol as u16 } else if symbol == 256 { 0 }
            else if symbol <= 285 { h::length_base(symbol as nat) as u16 }
            else { 0 } }
}

pub(crate) open spec fn literal_code(symbol: int) -> nat
    recommends 0 <= symbol < 288,
{
    if symbol < 144 { (symbol + 48) as nat }
    else if symbol < 256 { (symbol + 256) as nat }
    else if symbol < 280 { (symbol - 256) as nat }
    else { (symbol - 88) as nat }
}

}
