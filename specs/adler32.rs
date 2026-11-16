use vstd::prelude::*;

verus! {

// RFC 1950 (May 1996), section 2.2 ADLER32, section 8.2.
pub const MODULUS: u32 = 65521;
pub const WORD: u32 = 65536;

pub open spec fn byte_sum(bytes: Seq<u8>) -> int
    decreases bytes.len(),
{
    if bytes.len() == 0 { 0 }
    else { byte_sum(bytes.drop_last()) + bytes.last() as int }
}

// Each byte's coefficient is its distance from the end, plus one.
pub open spec fn weighted_sum(bytes: Seq<u8>) -> int
    decreases bytes.len(),
{
    if bytes.len() == 0 { 0 }
    else { weighted_sum(bytes.drop_last()) + byte_sum(bytes) }
}

pub open spec fn update(a: int, b: int, bytes: Seq<u8>) -> int {
    ((b + bytes.len() as int * a + weighted_sum(bytes)) % (MODULUS as int)) * WORD
        + (a + byte_sum(bytes)) % (MODULUS as int)
}

pub open spec fn checksum(bytes: Seq<u8>) -> int {
    update(1, 0, bytes)
}

pub open spec fn scalar_update(start: u32, bytes: Seq<u8>) -> int {
    if bytes.len() == 0 { start as int }
    else { update(low(start), high(start), bytes) }
}

pub open spec fn low(checksum: u32) -> int {
    (checksum & 0xffff) as int
}

pub open spec fn high(checksum: u32) -> int {
    ((checksum >> 16) & 0xffff) as int
}

pub open spec fn canonical(checksum: u32) -> bool {
    low(checksum) < MODULUS && high(checksum) < MODULUS
}

// Algebraic consequence of RFC 1950 section 2.2, not a separate wire format.
// The second operand is a checksum initialized with (s1,s2) = (1,0).
pub open spec fn combine(first: u32, second: u32, second_len: int) -> int {
    ((high(first) + high(second) + second_len * (low(first) - 1)) % (MODULUS as int)) * WORD
        + (low(first) + low(second) - 1) % (MODULUS as int)
}

}
