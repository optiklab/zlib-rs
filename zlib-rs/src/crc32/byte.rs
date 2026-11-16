use super::tables::CRC32_BYTE_TABLE;

#[cfg(verus_keep_ghost)]
use crate::{crc_proofs, crc_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(table =>
    ensures forall|index: int| 0 <= index < 256 ==>
        table@[index] == crc_specs::shift_bits(index as u32, 8),
))]
pub(crate) fn get_crc_table() -> &'static [u32; 256] {
    &CRC32_BYTE_TABLE[0]
}

#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == crc_specs::raw_update(start, data@),
))]
pub(super) fn crc32_naive_inner(data: &[u8], start: u32) -> u32 {
    crc32_table_update(data, start, get_crc_table())
}

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires forall|index: int| 0 <= index < 256 ==>
        table@[index] == crc_specs::shift_bits(index as u32, 8),
    ensures result == crc_specs::raw_update(start, data@),
))]
pub(super) fn crc32_table_update(data: &[u8], start: u32, table: &[u32; 256]) -> u32 {
    let mut crc = start;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= data.len(),
            crc == crc_specs::raw_update(start, data@.take(index as int)),
        decreases data.len() - index,
    ))]
    while index < data.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            crc_proofs::raw_prefix_step(start, data@, index as int);
            crc_proofs::byte_table_rule(crc, data[index as int]);
        }
        let crc32_lsb = crc as u8;
        crc = table[usize::from(crc32_lsb ^ data[index])] ^ (crc >> 8);
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(data@.take(data.len() as int) == data@); }
    crc
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn native_zlib_fixtures() {
        let table = crate::crc32::get_crc_table();
        for (seed, expected) in [
            (0, 0xcbf4_3926),
            (0x1234_5678, 0x01f4_807b),
            (u32::MAX, 0xd202_d277),
        ] {
            assert_eq!(!crc32_table_update(b"123456789", !seed, table), expected);
            assert_eq!(!crc32_table_update(b"", !seed, table), seed);
        }
    }
}
