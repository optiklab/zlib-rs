//! The adler32 checksum algorithm.

#[cfg(target_arch = "x86_64")]
mod avx2;
#[cfg(feature = "avx512")]
#[cfg(target_arch = "x86_64")]
mod avx512;
#[cfg(feature = "avx512")]
#[cfg(target_arch = "x86_64")]
mod avx512_vnni;
mod combine;
mod constants;
mod generic;
#[cfg(all(target_arch = "loongarch64", feature = "lsx"))]
mod lsx;
#[cfg(target_arch = "aarch64")]
mod neon;
mod short;
#[cfg(any(target_arch = "wasm32", target_arch = "wasm64"))]
mod wasm;

pub fn adler32(start_checksum: u32, data: &[u8]) -> u32 {
    #[cfg(feature = "avx512")]
    #[cfg(target_arch = "x86_64")]
    if cfg!(all(target_feature = "avx512f", target_feature = "avx512bw")) {
        return avx512::adler32_avx512(start_checksum, data);
    }

    #[cfg(target_arch = "x86_64")]
    if crate::cpu_features::is_enabled_avx2_and_bmi2() {
        return avx2::adler32_avx2(start_checksum, data);
    }

    #[cfg(target_arch = "aarch64")]
    if crate::cpu_features::is_enabled_neon() {
        return self::neon::adler32_neon(start_checksum, data);
    }

    #[cfg(any(target_arch = "wasm32", target_arch = "wasm64"))]
    if crate::cpu_features::is_enabled_simd128() {
        return self::wasm::adler32_wasm(start_checksum, data);
    }

    #[cfg(all(target_arch = "loongarch64", feature = "lsx"))]
    if crate::cpu_features::is_enabled_lsx() {
        return self::lsx::adler32_lsx(start_checksum, data);
    }

    generic::adler32_rust(start_checksum, data)
}

pub(crate) fn adler32_fold_copy(start_checksum: u32, dst: &mut [u8], src: &[u8]) -> u32 {
    debug_assert!(dst.len() >= src.len(), "{} < {}", dst.len(), src.len());

    // integrating the memcpy into the adler32 function did not have any benefits, and in fact was
    // a bit slower for very small chunk sizes.
    dst[..src.len()].copy_from_slice(src);
    adler32(start_checksum, src)
}

pub use combine::adler32_combine;

// inefficient but correct, useful for testing
#[cfg(test)]
fn naive_adler32(start_checksum: u32, data: &[u8]) -> u32 {
    const MOD_ADLER: u32 = 65521; // Largest prime smaller than 2^16

    let mut a = start_checksum & 0xFFFF;
    let mut b = (start_checksum >> 16) & 0xFFFF;

    for &byte in data {
        a = (a + byte as u32) % MOD_ADLER;
        b = (b + a) % MOD_ADLER;
    }

    (b << 16) | a
}

use constants::{BASE, NMAX};

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn independent_adler_vectors() {
        // Frozen outputs from CPython 3.11.9's native zlib 1.3.1.
        for (input, expected) in [
            (&b""[..], 1),
            (&b"Wikipedia"[..], 0x11e6_0398),
            (&b"123456789"[..], 0x091e_01de),
        ] {
            assert_eq!(generic::adler32_rust(1, input), expected);
            assert_eq!(adler32(1, input), expected);
        }

        for (len, expected) in [
            (15, 0x7797_0ef2),
            (16, 0x8788_0ff1),
            (17, 0x9878_10f0),
            (5551, 0x5603_9a8d),
            (5552, 0xf18f_9b8c),
            (5553, 0x8e29_9c8b),
            (11104, 0xff6f_3726),
            (11105, 0x37a3_3825),
        ] {
            let input = vec![255; len];
            assert_eq!(generic::adler32_rust(1, &input), expected, "len={len}");
            assert_eq!(adler32(1, &input), expected, "len={len}");
        }
    }

    #[test]
    fn scalar_seed_and_reduction_boundaries() {
        for start in [0, 1, 42, 0x0000_ffff, 0xffff_0000, u32::MAX] {
            for len in [
                0, 1, 7, 8, 15, 16, 17, 31, 32, 63, 64, 65, 5551, 5552, 5553, 11104, 11105,
            ] {
                for byte in [0, 255] {
                    let input = vec![byte; len];
                    let expected = naive_adler32(start, &input);
                    assert_eq!(
                        generic::adler32_rust(start, &input),
                        expected,
                        "start={start:#x}, len={len}, byte={byte}"
                    );
                    assert_eq!(adler32(start, &input), expected);
                }
            }
        }
    }

    #[test]
    fn checksum_chunk_and_combine_composition() {
        let input: Vec<u8> = (0..11105).map(|i| (i * 197 + 101) as u8).collect();
        let expected = generic::adler32_rust(1, &input);
        for split in [0, 1, 15, 16, 17, 5551, 5552, 5553, 11104, 11105] {
            let (left, right) = input.split_at(split);
            let first = generic::adler32_rust(1, left);
            let second = generic::adler32_rust(1, right);
            assert_eq!(generic::adler32_rust(first, right), expected);
            assert_eq!(adler32_combine(first, second, right.len() as u64), expected);
        }
        for chunk_size in [1, 7, 8, 15, 16, 17, 5552, 5553] {
            let result = input.chunks(chunk_size).fold(1, generic::adler32_rust);
            assert_eq!(result, expected, "chunk_size={chunk_size}");
        }
    }

    #[test]
    fn naive_is_fancy_small_inputs() {
        for i in 0..128 {
            let v = (0u8..i).collect::<Vec<_>>();
            assert_eq!(naive_adler32(1, &v), generic::adler32_rust(1, &v));
        }
    }

    #[test]
    fn test_adler32_combine() {
        ::quickcheck::quickcheck(test as fn(_) -> _);

        fn test(data: Vec<u8>) -> bool {
            let Some(buf_len) = data.first().copied() else {
                return true;
            };

            let buf_size = Ord::max(buf_len, 1) as usize;

            let mut adler1 = 1;
            let mut adler2 = 1;

            for chunk in data.chunks(buf_size) {
                adler1 = adler32(adler1, chunk);
            }

            adler2 = adler32(adler2, &data);

            assert_eq!(adler1, adler2);

            let combine1 = adler32_combine(adler1, adler2, data.len() as _);
            let combine2 = adler32_combine(adler1, adler1, data.len() as _);
            assert_eq!(combine1, combine2);

            true
        }
    }
}
