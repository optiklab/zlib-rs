use crate::constructor_pages_specs as ownership;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn bucket(counts: Seq<u16>, position: nat, level: nat) -> bool {
    counts.len() == 16 && 1 <= level <= 15
        && h::before(counts, level) <= position < h::before(counts, level + 1)
}

pub(crate) open spec fn source_length(counts: Seq<u16>, position: nat) -> nat {
    choose|level: nat| #[trigger] bucket(counts, position, level)
}

pub(crate) open spec fn root_key(counts: Seq<u16>, root: nat, position: nat) -> int {
    h::normalized_cursor(counts, source_length(counts, position), position)
        / h::capacity((32 - root) as nat)
}

pub(crate) open spec fn first_group(counts: Seq<u16>, root: nat, max: nat,
    position: nat) -> bool {
    counts.len() == 16 && position < h::before(counts, 16)
        && 1 <= root < source_length(counts, position) <= max <= 15
        && forall|earlier: nat| earlier < position && root < source_length(counts, earlier) <= 15
            ==> #[trigger] root_key(counts, root, earlier) != root_key(counts, root, position)
}

pub(crate) open spec fn charge(counts: Seq<u16>, root: nat, max: nat,
    position: nat) -> nat {
    if first_group(counts, root, max, position) {
        h::capacity(ownership::opening_width(counts, position,
            source_length(counts, position), root, max)) as nat
    } else { 0 }
}

pub(crate) open spec fn sum(counts: Seq<u16>, root: nat, max: nat, processed: nat) -> nat
    decreases processed,
{
    if processed == 0 { 0 }
    else { sum(counts, root, max, (processed - 1) as nat)
        + charge(counts, root, max, (processed - 1) as nat) }
}

pub(crate) open spec fn path(counts: Seq<u16>, depth: nat, available: nat,
    remaining: nat) -> bool
    decreases 16 - depth,
{
    counts.len() == 16 && 1 <= depth <= 15 && available <= remaining
        && counts[depth as int] <= available
        && if depth == 15 {
            available == counts[depth as int] && remaining == counts[depth as int]
        } else {
            path(counts, depth + 1, 2 * (available - counts[depth as int]) as nat,
                (remaining - counts[depth as int]) as nat)
        }
}

}
