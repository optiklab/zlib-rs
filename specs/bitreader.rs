use vstd::prelude::*;

verus! {

pub open spec fn word_bit(word: u64, index: nat) -> bool
    recommends index < 64,
{
    (word >> (index as u64)) & 1 == 1
}

pub open spec fn buffered_bits(word: u64, count: u8) -> Seq<bool>
    recommends count <= 64,
{
    Seq::new(count as nat, |index: int| word_bit(word, index as nat))
}

pub open spec fn append_compatible(word: u64, count: u8, read: u64, added: u8) -> bool
    recommends count as nat + added as nat <= 64,
{
    forall|index: nat| index < added ==>
        #[trigger] word_bit(word, count as nat + index) ==> word_bit(read, index)
}

// RFC 1951 3.1.1: cached lookahead belongs to the unread low-first input.
// Zero cache bits need not have been read; set cache bits must agree with it.
#[verifier::opaque]
pub open spec fn cached_suffix(word: u64, count: u8, pending: Seq<bool>) -> bool
    recommends count <= 64,
{
    forall|index: nat| count <= index < 64 && #[trigger] word_bit(word, index) ==>
        index - count < pending.len() && pending[(index - count) as int]
}

pub open spec fn read_agrees(read: u64, pending: Seq<bool>) -> bool {
    forall|index: nat| index < 64 && #[trigger] word_bit(read, index) ==>
        index < pending.len() && pending[index as int]
}

// RFC 1951 3.1.1: non-Huffman fields consume each octet least-significant bit first.
pub open spec fn input_bits(bytes: Seq<u8>) -> Seq<bool> {
    Seq::new(8 * bytes.len(), |index: int|
        word_bit(bytes[index / 8] as u64, (index % 8) as nat))
}

pub open spec fn needed_bytes(count: u8, target: usize) -> nat {
    if target <= count { 0 } else { ((target as int - count as int + 7) / 8) as nat }
}

pub open spec fn filled_word(before: u64, count: u8, after: u64, added: Seq<bool>) -> bool {
    forall|index: nat| index < 64 ==> #[trigger] word_bit(after, index)
        == (word_bit(before, index)
            || (count <= index && index - count < added.len() && added[(index - count) as int]))
}

pub open spec fn three_bit_value(bits: Seq<bool>) -> u16
    recommends bits.len() >= 3,
{
    ((if bits[0] { 1u16 } else { 0u16 })
        + (if bits[1] { 2u16 } else { 0u16 })
        + (if bits[2] { 4u16 } else { 0u16 })) as u16
}

// RFC 1951 3.1.1: ordinary integer fields have least-significant bits first.
pub open spec fn low_first_value(bits: Seq<bool>) -> nat
    decreases bits.len(),
{
    if bits.len() == 0 { 0 }
    else { (if bits[0] { 1nat } else { 0nat }) + 2 * low_first_value(bits.skip(1)) }
}

// Buffered bits are consumed least-significant first. Discard the partial
// octet before searching the remaining whole octets for a sync marker.
pub open spec fn sync_bytes(word: u64, count: u8) -> Seq<u8> {
    Seq::new(count as nat / 8, |index: int|
        (word >> ((count as int % 8 + 8 * index) as u64)) as u8)
}

}
