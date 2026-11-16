#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs, subtable_coverage_proofs, subtable_coverage_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires drop < length <= max <= 15,
    ensures length - drop <= result, result + drop <= max,
        huffman_specs::chosen_width(counts@, (length - drop) as nat, drop as nat,
            max as nat, result as nat),
        forall|lengths: Seq<u16>, original: Seq<u16>, position: nat|
            #[trigger] subtable_coverage_specs::source_context(lengths, original, counts@,
                position, length as nat, drop as nat, max as nat)
            ==> (forall|symbol: int| #[trigger] subtable_coverage_specs::in_root(lengths,
                    symbol, drop as nat,
                    huffman_specs::normalized_cursor(original, length as nat, position))
                ==> lengths[symbol] <= result + drop),
))]
pub(super) fn subtable_width(counts: &[u16; 16], length: usize, drop: usize, max: usize) -> usize {
    let mut curr = length - drop;
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::usize_shift_capacity(curr);
        assert(huffman_specs::capacity(14) == 16384) by (compute);
    }
    let mut left = 1i32 << curr;
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::depth_capacity(curr as nat);
        huffman_proofs::capacity_positive(curr as nat);
        assert(1i32 << curr == (1usize << curr) as i32) by (bit_vector)
            requires 1 <= curr <= 15;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= length - drop <= curr,
            curr + drop <= max <= 15,
            0 < left <= huffman_specs::capacity(curr as nat),
            left == huffman_specs::lookahead_space(counts@, (length - drop) as nat,
                drop as nat, curr as nat),
            forall|depth: nat| (length - drop) as nat <= depth < curr ==>
                #[trigger] huffman_specs::lookahead_space(counts@, (length - drop) as nat,
                    drop as nat, depth) - counts@[(depth + drop) as int] > 0,
        decreases max - curr - drop,
    ))]
    while curr + drop < max {
        #[cfg(verus_keep_ghost)]
        proof! {
            huffman_proofs::capacity_monotone(curr as nat, 14);
        }
        left -= counts[curr + drop] as i32;
        if left <= 0 {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(huffman_specs::chosen_width(counts@, (length - drop) as nat,
                    drop as nat, max as nat, curr as nat));
                subtable_coverage_proofs::width_result(counts@, length as nat, drop as nat,
                    max as nat, curr as nat);
            }
            return curr;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|depth: nat| (length - drop) as nat <= depth < curr + 1 implies
                #[trigger] huffman_specs::lookahead_space(counts@, (length - drop) as nat,
                    drop as nat, depth) - counts@[(depth + drop) as int] > 0 by {
                if depth == curr {
                    assert(left == huffman_specs::lookahead_space(counts@,
                        (length - drop) as nat, drop as nat, depth)
                            - counts@[(depth + drop) as int]);
                }
            }
            assert(huffman_specs::lookahead_space(counts@, (length - drop) as nat,
                drop as nat, curr as nat + 1) == 2 * left);
            assert(left << 1 == (left * 2) as i32) by (bit_vector)
                requires 0 < left <= 16384;
        }
        curr += 1;
        left <<= 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(huffman_specs::chosen_width(counts@, (length - drop) as nat,
            drop as nat, max as nat, curr as nat));
        subtable_coverage_proofs::width_result(counts@, length as nat, drop as nat,
            max as nat, curr as nat);
    }
    curr
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn stops_at_the_first_filled_depth() {
        let mut counts = [0; 16];
        counts[3] = 1;
        counts[5] = 2;
        for (count, expected) in [(5, 4), (6, 3), (7, 3)] {
            counts[4] = count;
            assert_eq!(subtable_width(&counts, 3, 1, 15), expected);
        }
    }

    #[test]
    fn handles_empty_and_maximum_populations_without_overflow() {
        assert_eq!(subtable_width(&[0; 16], 2, 1, 15), 14);
        let mut counts = [0; 16];
        counts[1] = u16::MAX;
        assert_eq!(subtable_width(&counts, 1, 0, 15), 1);
        assert_eq!(subtable_width(&counts, 15, 14, 15), 1);
    }
}
