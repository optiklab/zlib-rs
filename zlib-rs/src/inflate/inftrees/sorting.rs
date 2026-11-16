#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires huffman_specs::before(counts@, 16) <= u16::MAX,
    ensures result@[0] == 0,
        forall|level: int| 1 <= level <= 15 ==>
            result@[level] == huffman_specs::before(counts@, level as nat),
))]
pub(super) fn build_offsets(counts: &[u16; 16]) -> [u16; 16] {
    let mut offsets = [0u16; 16];
    let mut level = 1;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= level <= 15,
            offsets@[0] == 0,
            forall|done: int| 1 <= done <= level ==>
                offsets@[done] == huffman_specs::before(counts@, done as nat),
        decreases 15 - level,
    ))]
    while level < 15 {
        #[cfg(verus_keep_ghost)]
        proof! { huffman_proofs::before_monotone(counts@, level as nat + 1, 16); }
        offsets[level + 1] = offsets[level] + counts[level];
        level += 1;
    }
    offsets
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires lengths.len() <= u16::MAX,
        work.len() >= huffman_specs::count_before(lengths@, 16),
        forall|index: int| 0 <= index < lengths.len() ==> lengths@[index] <= 15,
        huffman_specs::valid_histogram(lengths@, counts@),
    ensures huffman_specs::bucket_ordered(lengths@, counts@, final(work)@),
        final(work)@.len() == old(work)@.len(),
        forall|index: int| huffman_specs::before(counts@, 16) <= index < old(work).len() ==>
            final(work)@[index] == old(work)@[index],
))]
pub(super) fn sort_symbols(lengths: &[u16], counts: &[u16; 16], work: &mut [u16]) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original_work = work@; }
    #[cfg(verus_keep_ghost)]
    proof! { huffman_proofs::histogram_offsets(lengths@, counts@, 16); }
    let mut offsets = build_offsets(counts);
    let mut symbol = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant symbol <= lengths.len(),
            work.len() == original_work.len(),
            huffman_specs::before(counts@, 16) <= work.len(),
            forall|level: int| 1 <= level <= 15 ==>
                offsets@[level] == huffman_specs::before(counts@, level as nat)
                    + huffman_specs::occurrences(lengths@.take(symbol as int), level as u16),
            forall|level: int| 1 <= level <= 15 ==>
                offsets@[level] <= huffman_specs::before(counts@, level as nat + 1),
            forall|level: int, position: int|
                #![trigger offsets@[level], work@[position]]
                1 <= level <= 15
                    && huffman_specs::before(counts@, level as nat) <= position < offsets@[level] ==> {
                        let previous = work@[position] as int;
                        previous < symbol && lengths@[previous] == level
                            && huffman_specs::occurrences(lengths@.take(previous), level as u16)
                                == position - huffman_specs::before(counts@, level as nat)
                    },
            forall|index: int| #![trigger work@[index]]
                huffman_specs::before(counts@, 16) <= index < work.len() ==>
                    work@[index] == original_work[index],
        decreases lengths.len() - symbol,
    ))]
    while symbol < lengths.len() {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|level: u16| #![trigger counts@[level as int]]
                1 <= level <= 15 implies
                huffman_specs::occurrences(lengths@.take(symbol as int + 1), level)
                    == huffman_specs::occurrences(lengths@.take(symbol as int), level)
                        + if lengths@[symbol as int] == level { 1nat } else { 0nat }
                && huffman_specs::occurrences(lengths@.take(symbol as int + 1), level)
                    <= counts@[level as int] by {
                huffman_proofs::histogram_prefix_step(lengths@, symbol as int, level);
                huffman_proofs::occurrences_prefix_bound(lengths@, symbol as int + 1, level);
            }

        }
        let len = lengths[symbol];
        if len != 0 {
            let offset = offsets[len as usize];
            #[cfg(verus_keep_ghost)]
            proof_decl! {
                let ghost previous_offsets = offsets@;
                let ghost previous_work = work@;
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                huffman_proofs::before_monotone(counts@, len as nat + 1, 16);
                assert(offset < huffman_specs::before(counts@, len as nat + 1));
            }
            offsets[len as usize] += 1;
            work[offset as usize] = symbol as u16;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall|level: int| 1 <= level <= 15 implies
                    offsets@[level] == huffman_specs::before(counts@, level as nat)
                        + huffman_specs::occurrences(lengths@.take(symbol as int + 1), level as u16)
                    && offsets@[level] <= huffman_specs::before(counts@, level as nat + 1) by {}
                assert forall|level: int, position: int|
                    #![trigger offsets@[level], work@[position]]
                    1 <= level <= 15
                        && huffman_specs::before(counts@, level as nat) <= position < offsets@[level]
                    implies {
                        let previous = work@[position] as int;
                        previous <= symbol && lengths@[previous] == level
                            && huffman_specs::occurrences(lengths@.take(previous), level as u16)
                                == position - huffman_specs::before(counts@, level as nat)
                    } by {
                        if position == offset {
                            if level != len {
                                huffman_proofs::separate_buckets(counts@, len as nat, level as nat,
                                    offset as int, position);
                            }
                            assert(work@[position] == symbol);
                        } else {
                            assert(position < previous_offsets[level]);
                            assert(work@[position] == previous_work[position]);
                        }
                    }
            }
        }
        symbol += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(work@.len() == work.len());
        assert(lengths@.len() == lengths.len());
        assert(counts@.len() == 16);
        assert(lengths@.take(lengths.len() as int) == lengths@);
        assert forall|level: int, ordinal: int|
            1 <= level <= 15 && 0 <= ordinal < counts@[level]
            implies #[trigger] huffman_specs::bucket_entry(lengths@, counts@, work@, level, ordinal) by {
                let position = huffman_specs::before(counts@, level as nat) as int + ordinal;
                huffman_proofs::before_monotone(counts@, level as nat + 1, 16);
                assert(position < offsets@[level]);
            }
        assert(huffman_specs::bucket_ordered(lengths@, counts@, work@));
    }
}

#[cfg(test)]
mod test {
    use super::super::histogram::length_histogram;
    use super::*;

    #[test]
    fn sorts_stably_and_preserves_unused_workspace() {
        let lengths = [3, 0, 1, 2, 1, 3];
        let (counts, _, _) = length_histogram(&lengths);
        let mut work = [u16::MAX; 8];
        sort_symbols(&lengths, &counts, &mut work);
        assert_eq!(work, [2, 4, 3, 0, 5, u16::MAX, u16::MAX, u16::MAX]);
    }

    #[test]
    fn supports_maximum_representable_histogram() {
        let lengths = vec![15; u16::MAX as usize];
        let (counts, _, _) = length_histogram(&lengths);
        let mut work = vec![u16::MAX; lengths.len() + 1];
        sort_symbols(&lengths, &counts, &mut work);
        assert!(work[..lengths.len()]
            .iter()
            .enumerate()
            .all(|(index, &symbol)| symbol as usize == index));
        assert_eq!(work[lengths.len()], u16::MAX);
    }
}
