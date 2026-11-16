use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn state(bound: nat, depth: nat, available: nat, remaining: nat) -> bool {
    1 <= depth <= 15 && available <= remaining <= bound
        && remaining <= available * h::capacity((15 - depth) as nat)
}

pub(crate) open spec fn edge(bound: nat, depth: nat, available: nat, remaining: nat,
    leaves: nat) -> bool {
    depth < 15 && leaves <= available <= remaining
        && state(bound, depth + 1, 2 * (available - leaves) as nat, (remaining - leaves) as nat)
}

pub(crate) open spec fn closing(root: nat, depth: nat, available: nat, leaves: nat) -> nat {
    if depth <= root { 0 }
    else {
        let capacity = h::capacity((depth - root) as nat);
        (((available + capacity - 1) / capacity
            - (((available - leaves) as nat + capacity - 1) / capacity)) * capacity) as nat
    }
}

pub(crate) open spec fn forest(counts: Seq<u16>, root: nat, depth: nat,
    available: nat) -> nat
    decreases 16 - depth,
{
    if counts.len() != 16 || depth == 0 || depth > 15 { 0 }
    else {
        closing(root, depth, available, counts[depth as int] as nat)
            + if depth == 15 { 0 } else {
                forest(counts, root, depth + 1, 2 * (available - counts[depth as int]) as nat)
            }
    }
}

pub(crate) open spec fn certificate(upper: spec_fn(nat, nat, nat) -> Option<nat>,
    root: nat, bound: nat) -> bool {
    1 <= root <= 15
        && forall|depth: nat, available: nat, remaining: nat|
            state(bound, depth, available, remaining) ==>
            match #[trigger] upper(depth, available, remaining) {
                None => true,
                Some(value) => if depth == 15 {
                    closing(root, depth, available, available) <= value
                } else {
                    forall|leaves: nat| #[trigger] edge(bound, depth, available, remaining, leaves)
                        ==> match upper(depth + 1, 2 * (available - leaves) as nat,
                            (remaining - leaves) as nat) {
                            Some(next) => closing(root, depth, available, leaves) + next <= value,
                            None => false,
                        }
                },
            }
}

}
