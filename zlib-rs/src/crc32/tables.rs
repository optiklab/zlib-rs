use super::constants::CRC32_LSB_POLY;

#[cfg(verus_keep_ghost)]
use crate::{crc_proofs, crc_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures forall|index: int| 0 <= index < 256 ==>
        CRC32_BYTE_TABLE@[0]@[index] == crc_specs::shift_bits(index as u32, 8),
))]
pub(super) static CRC32_BYTE_TABLE: [[u32; 256]; 1] = build_crc32_table::<256, 1, 1>();

// Each column is a byte shifted by the row's polynomial power.
// Expand nested cfg attributes before Verus erases the const-evaluated body.
#[cfg_attr(verus_keep_ghost, cfg_eval)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires A <= 256, N >= 1, W as int * N as int <= usize::MAX as int / 8,
    ensures forall|row: int, col: int| 0 <= row < W && 0 <= col < A ==>
        result@[row]@[col] == crc_specs::shift_bits(col as u32,
            (8 * (W as int * N as int - row)) as nat),
))]
pub(super) const fn build_crc32_table<const A: usize, const W: usize, const N: usize>(
) -> [[u32; A]; W] {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(W as int <= W as int * N as int) by (nonlinear_arith)
            requires N >= 1;
    }
    let width = W * N;
    let mut arr = [[0u32; A]; W];
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= W,
            forall|row: int, col: int| 0 <= row < W && 0 <= col < A ==>
                arr@[row]@[col] == if row < i {
                    crc_specs::shift_bits(col as u32, (8 * (width as int - row)) as nat)
                } else { 0 },
        decreases W - i,
    ))]
    while i < W {
        let mut j = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant j <= A,
                forall|row: int, col: int| 0 <= row < W && 0 <= col < A ==>
                    arr@[row]@[col] == if row < i || (row == i && col < j) {
                        crc_specs::shift_bits(col as u32, (8 * (width as int - row)) as nat)
                    } else { 0 },
            decreases A - j,
        ))]
        while j < A {
            let mut c = j as u32;
            let mut k = 0;
            let limit = 8 * (width - i);
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant k <= limit,
                    c == crc_specs::shift_bits(j as u32, k as nat),
                decreases limit - k,
            ))]
            while k < limit {
                #[cfg(verus_keep_ghost)]
                proof! {
                    crc_proofs::shift_step(j as u32, k as nat);
                    crc_proofs::xor_commutes(CRC32_LSB_POLY as u32, c >> 1);
                }
                if c & 1 != 0 {
                    c = CRC32_LSB_POLY as u32 ^ (c >> 1);
                } else {
                    c >>= 1;
                }
                k += 1;
            }
            arr[i][j] = c;
            j += 1;
        }
        i += 1;
    }
    arr
}
