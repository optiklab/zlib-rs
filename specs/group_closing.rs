use crate::constructor_pages_specs as pages;
use crate::histogram_cost_specs as histogram;
use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn selected_depth(counts: Seq<u16>, root: nat, max: nat,
    depth: nat, position: nat) -> bool {
    histogram::first_group(counts, root, max, position)
        && depth == root + pages::opening_width(
            counts, position, histogram::source_length(counts, position), root, max)
}

pub(crate) open spec fn depth_count(counts: Seq<u16>, root: nat, max: nat,
    depth: nat, processed: nat) -> nat
    decreases processed,
{
    if processed == 0 { 0 }
    else {
        depth_count(counts, root, max, depth, (processed - 1) as nat)
            + if selected_depth(counts, root, max, depth, (processed - 1) as nat) { 1nat } else { 0nat }
    }
}

pub(crate) open spec fn weighted(counts: Seq<u16>, root: nat, max: nat,
    processed: nat, depth: nat) -> int
    decreases 16 - depth,
{
    if depth == 0 || depth >= 16 { 0 }
    else {
        (if depth > root {
            depth_count(counts, root, max, depth, processed) * h::capacity((depth - root) as nat)
        } else { 0int }) + weighted(counts, root, max, processed, depth + 1)
    }
}

}
