use vstd::prelude::*;

verus! {

// RFC 1952, May 1996, section 2.3.1 and section 8.
// Polynomial arithmetic is over GF(2); coefficients are represented reflected.
pub const POLYNOMIAL: u32 = 0xedb8_8320;
pub const ONE: u32 = 0x8000_0000;

pub open spec fn times_x(value: u32) -> u32 {
    if value & 1 != 0 { (value >> 1) ^ POLYNOMIAL } else { value >> 1 }
}

pub open spec fn shift_bits(value: u32, count: nat) -> u32
    decreases count,
{
    if count == 0 { value } else { times_x(shift_bits(value, (count - 1) as nat)) }
}

pub open spec fn coefficient_mask(index: nat) -> u32 {
    if index < 32 { ONE >> (index as u32) } else { 0 }
}

pub open spec fn remaining_mask(index: nat) -> u32 {
    if index < 32 { u32::MAX >> (index as u32) } else { 0 }
}

// Schoolbook multiplication: XOR the monomials selected by a's coefficients.
pub open spec fn product_terms(a: u32, b: u32, index: nat) -> u32
    decreases 32 - index,
{
    if index >= 32 { 0 } else {
        (if a & coefficient_mask(index) != 0 { shift_bits(b, index) } else { 0 })
            ^ product_terms(a, b, index + 1)
    }
}

pub open spec fn product(a: u32, b: u32) -> u32 {
    product_terms(a, b, 0)
}

pub open spec fn byte_step(crc: u32, byte: u8) -> u32 {
    shift_bits(crc ^ byte as u32, 8)
}

pub open spec fn raw_update(start: u32, bytes: Seq<u8>) -> u32
    decreases bytes.len(),
{
    if bytes.len() == 0 { start }
    else { byte_step(raw_update(start, bytes.drop_last()), bytes.last()) }
}

pub open spec fn checksum_update(start: u32, bytes: Seq<u8>) -> u32 {
    !raw_update(!start, bytes)
}

}
