// Several implementations of CRC-32:
// * A naive byte-granularity approach
// * A word-sized approach that processes a usize word at a time
// * A "braid" implementation that processes a block of N words
//   at a time, based on the algorithm in section 4.11 from
//   https://github.com/zlib-ng/zlib-ng/blob/develop/doc/crc-doc.1.0.pdf.

use super::byte::crc32_naive_inner;
pub(crate) use super::byte::get_crc_table;
use super::tables::build_crc32_table;

const W: usize = core::mem::size_of::<usize>();

// The logic assumes that W >= sizeof(u32).
// In Rust, this is generally true.
const _: () = assert!(W >= core::mem::size_of::<u32>());

// Pre-computed tables for the CRC32 algorithm.
// CRC32_BYTE_TABLE corresponds to MulByXPowD from the paper.
// CRC32_WORD_TABLE is MulWordByXpowD.
static CRC32_WORD_TABLE: [[u32; 256]; W] = build_crc32_table::<256, W, 1>();

// Work-around for not being able to define generic consts or statics
// Crc32BraidTable::<N>::TABLE is the generic table for any braid size N.
struct Crc32BraidTable<const N: usize>;

impl<const N: usize> Crc32BraidTable<N> {
    const TABLE: [[u32; 256]; W] = build_crc32_table::<256, W, N>();
}

fn crc32_words_inner(words: &[usize], start: u32, per_word_crcs: &[u32]) -> u32 {
    words.iter().enumerate().fold(start, |crc, (i, word)| {
        let value = word.to_le() ^ (crc ^ per_word_crcs.get(i).unwrap_or(&0)) as usize;
        value
            .to_le_bytes()
            .into_iter()
            // The & is load-bearing for performance, using the table directly will memcpy it.
            // See also https://github.com/trifectatechfoundation/zlib-rs/pull/571.
            .zip(&CRC32_WORD_TABLE)
            .fold(0u32, |crc, (b, tab)| crc ^ tab[usize::from(b)])
    })
}

pub fn crc32_braid<const N: usize>(start: u32, data: &[u8]) -> u32 {
    // Get a word-aligned sub-slice of the input data
    // SAFETY: it is safe to transmute a slice of u8 into a usize.
    let (prefix, words, suffix) = unsafe { data.align_to::<usize>() };
    let crc = !start;
    let crc = crc32_naive_inner(prefix, crc);

    let mut crcs = [0u32; N];
    crcs[0] = crc;

    // TODO: this would normally use words.chunks_exact(N), but
    // we need to pass the last full block to crc32_words_inner
    // because we accumulate partial crcs in the array and we
    // need to roll those into the final value. The last call to
    // crc32_words_inner does that for us with its per_word_crcs
    // argument.
    let blocks = words.len() / N;
    let blocks = blocks.saturating_sub(1);
    for i in 0..blocks {
        // Load the next N words.
        let mut buffer: [usize; N] =
            core::array::from_fn(|j| usize::to_le(words[i * N + j]) ^ (crcs[j] as usize));

        crcs.fill(0);
        for j in 0..W {
            braid_core(&mut crcs, &mut buffer, j);
        }
    }

    let crc = core::mem::take(&mut crcs[0]);
    let crc = crc32_words_inner(&words[blocks * N..], crc, &crcs);
    let crc = crc32_naive_inner(suffix, crc);
    !crc
}

// A workaround for https://github.com/trifectatechfoundation/zlib-rs/issues/407.
//
// We're seeing misoptimization with rust versions that use LLVM 20, earlier LLVMs are fine, and
// LLVM 21 similarly appears to do fine. The offending feature is `+avx512vl`,  the
// "Vector Length Extension", which extends some instructions operating on 512-bit operands with
// variants that support 256-bit or 128-bit operands.
//
// The avx512vl target feature only became stable in 1.89.0: before that, we can't detect it
// statically. Therefore we use avx2 as a proxy, it is implied by avx512vl.
#[cfg_attr(all(target_arch = "x86_64", target_feature = "avx2"), inline(never))]
#[cfg_attr(not(target_arch = "x86_64"), inline(always))]
fn braid_core<const N: usize>(crcs: &mut [u32; N], buffer: &mut [usize; N], j: usize) {
    for k in 0..N {
        crcs[k] ^= Crc32BraidTable::<N>::TABLE[j][buffer[k] & 0xff];
        buffer[k] >>= 8;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn crc32_naive(data: &[u8], start: u32) -> u32 {
        let crc = !start;
        let crc = crc32_naive_inner(data, crc);
        !crc
    }

    fn crc32_words(data: &[u8], start: u32) -> u32 {
        // Get a word-aligned sub-slice of the input data
        let (prefix, words, suffix) = unsafe { data.align_to::<usize>() };
        let crc = !start;
        let crc = crc32_naive_inner(prefix, crc);
        let crc = crc32_words_inner(words, crc, &[]);
        let crc = crc32_naive_inner(suffix, crc);
        !crc
    }

    #[test]
    fn empty_is_identity() {
        assert_eq!(crc32_naive(&[], 32), 32);
    }

    #[test]
    fn words_endianness() {
        let v = [0, 0, 0, 0, 0, 16, 0, 1];
        let start = 1534327806;

        let mut h = crc32fast::Hasher::new_with_initial(start);
        h.update(&v[..]);
        assert_eq!(crc32_words(&v[..], start), h.finalize());
    }

    #[test]
    fn crc32_naive_inner_endianness_and_alignment() {
        assert_eq!(crc32_naive_inner(&[0, 1], 0), 1996959894);

        let v: Vec<_> = (0..1024).map(|i| i as u8).collect();
        let start = 0;

        // test alignment
        for i in 0..8 {
            let mut h = crc32fast::Hasher::new_with_initial(start);
            h.update(&v[i..]);
            assert_eq!(crc32_braid::<5>(start, &v[i..]), h.finalize());
        }
    }

    quickcheck::quickcheck! {
        fn naive_is_crc32fast(v: Vec<u8>, start: u32) -> bool {
            let mut h = crc32fast::Hasher::new_with_initial(start);
            h.update(&v[..]);
            crc32_naive(&v[..], start) == h.finalize()
        }

        fn words_is_crc32fast(v: Vec<u8>, start: u32) -> bool {
            let mut h = crc32fast::Hasher::new_with_initial(start);
            h.update(&v[..]);
            crc32_words(&v[..], start) == h.finalize()
        }

        #[cfg_attr(miri, ignore)]
        fn braid_4_is_crc32fast(v: Vec<u8>, start: u32) -> bool {
            let mut h = crc32fast::Hasher::new_with_initial(start);
            h.update(&v[..]);
            crc32_braid::<4>(start, &v[..]) == h.finalize()
        }

        #[cfg_attr(miri, ignore)]
        fn braid_5_is_crc32fast(v: Vec<u8>, start: u32) -> bool {
            let mut h = crc32fast::Hasher::new_with_initial(start);
            h.update(&v[..]);
            crc32_braid::<5>(start, &v[..]) == h.finalize()
        }

        #[cfg_attr(miri, ignore)]
        fn braid_6_is_crc32fast(v: Vec<u8>, start: u32) -> bool {
            let mut h = crc32fast::Hasher::new_with_initial(start);
            h.update(&v[..]);
            crc32_braid::<6>(start, &v[..]) == h.finalize()
        }
    }
}
