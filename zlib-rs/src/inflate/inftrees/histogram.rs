#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires lengths.len() <= u16::MAX,
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
    ensures
        result.0@[0] == 0,
        forall|value: int| 1 <= value <= 15 ==>
            result.0@[value] == huffman_specs::occurrences(lengths@, value as u16),
        result.1 == huffman_specs::minimum_length(lengths@),
        result.2 == huffman_specs::maximum_length(lengths@),
        1 <= result.1 <= 15,
        result.2 <= 15,
        result.2 == 0 ==> result.1 == 15,
        result.2 > 0 ==> result.1 <= result.2,
))]
pub(super) fn length_histogram(lengths: &[u16]) -> ([u16; 16], usize, usize) {
    let mut count = [0u16; 16];
    let (mut min, mut max) = (15usize, 0usize);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= lengths.len(),
            count@[0] == 0,
            forall|value: int| 1 <= value <= 15 ==>
                count@[value] == huffman_specs::occurrences(lengths@.take(index as int), value as u16),
            forall|value: int| 0 <= value <= 15 ==> count@[value] <= index,
            min == huffman_specs::minimum_length(lengths@.take(index as int)),
            max == huffman_specs::maximum_length(lengths@.take(index as int)),
        decreases lengths.len() - index,
    ))]
    while index < lengths.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|value: u16| 1 <= value <= 15 implies
                huffman_specs::occurrences(lengths@.take(index as int + 1), value)
                    == huffman_specs::occurrences(lengths@.take(index as int), value)
                        + if lengths@[index as int] == value { 1nat } else { 0nat } by {
                huffman_proofs::histogram_prefix_step(lengths@, index as int, value);
            }
            huffman_proofs::histogram_prefix_step(lengths@, index as int, 0);
        }
        let len = lengths[index];
        if len > 0 {
            count[len as usize] += 1;
            max = Ord::max(max, usize::from(len));
            min = Ord::min(min, usize::from(len));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(lengths@.take(lengths.len() as int) == lengths@);
        huffman_proofs::metadata_bounds(lengths@);
    }
    (count, min, max)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn unused_symbols_and_length_bounds() {
        let (count, min, max) = length_histogram(&[0, 2, 1, 2, 15]);
        assert_eq!((min, max), (1, 15));
        assert_eq!((count[0], count[1], count[2], count[15]), (0, 1, 2, 1));
        let (count, min, max) = length_histogram(&[0, 0]);
        assert_eq!(count, [0; 16]);
        assert_eq!((min, max), (15, 0));
    }
}
