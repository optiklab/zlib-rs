use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn tight_backing(lengths: Seq<u16>, requested: nat, extent: int) -> bool {
    (requested == 10 && lengths.len() <= 286 && extent >= 1332)
        || (requested == 9 && lengths.len() <= 30 && extent >= 592)
}

pub(crate) open spec fn rounded(available: nat, size: int) -> int {
    (available + size - 1) / size
}

pub(crate) open spec fn slack(available: nat, size: int) -> int {
    rounded(available, size) * size - available
}

pub(crate) open spec fn upper(root: nat, depth: nat, available: nat, remaining: nat) -> Option<nat> {
    if 1 <= root < depth <= 15 {
        let size = h::capacity((depth - root) as nat);
        Some((remaining + slack(available, size) + h::capacity((15 - root) as nat)
            - size - (15 - depth)) as nat)
    } else { None }
}

}
