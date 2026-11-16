#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures
        result.is_some() == huffman_specs::valid_prefix(counts@, 15),
        result.is_some() ==> result.unwrap() as int == huffman_specs::slots(counts@, 15),
))]
pub(super) fn remaining_code_space(counts: &[u16; 16]) -> Option<u32> {
    let mut left = 1u32;
    let mut depth = 1usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= depth <= 16,
            left as int == huffman_specs::slots(counts@, (depth - 1) as nat),
            left as int <= huffman_specs::capacity((depth - 1) as nat),
            huffman_specs::valid_prefix(counts@, (depth - 1) as nat),
        decreases 16 - depth,
    ))]
    while depth < 16 {
        #[cfg(verus_keep_ghost)]
        proof! {
            huffman_proofs::depth_capacity((depth - 1) as nat);
            huffman_proofs::doubled_value(left);
        }
        let available = left << 1;
        if available < u32::from(counts[depth]) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(huffman_specs::slots(counts@, depth as nat) < 0);
                assert(!huffman_specs::valid_prefix(counts@, 15));
            }
            return None;
        }
        left = available - u32::from(counts[depth]);
        #[cfg(verus_keep_ghost)]
        proof! { huffman_proofs::extend_valid_prefix(counts@, depth as nat); }
        depth += 1;
    }
    Some(left)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn complete_incomplete_and_oversubscribed_counts() {
        let mut counts = [0; 16];
        counts[1] = 2;
        assert_eq!(remaining_code_space(&counts), Some(0));
        counts[1] = 1;
        assert_eq!(remaining_code_space(&counts), Some(16384));
        counts[2] = 2;
        assert_eq!(remaining_code_space(&counts), Some(0));
        counts[15] = 1;
        assert_eq!(remaining_code_space(&counts), None);
        counts[1] = u16::MAX;
        assert_eq!(remaining_code_space(&counts), None);
    }
}
