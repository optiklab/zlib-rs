use crate::huffman_specs as h;
use crate::subtable_coverage_specs as coverage;
use vstd::prelude::*;

verus! {

// Keep the opening population, not the subsequently mutated live histogram.
pub struct Opening {
    pub symbol: int,
    pub position: nat,
    pub length: nat,
    pub remaining: Seq<u16>,
}

pub open spec fn context(lengths: Seq<u16>, original: Seq<u16>,
    root: nat, max: nat, key: int, opening: Opening) -> bool {
    coverage::source_context(lengths, original, opening.remaining,
        opening.position, opening.length, root, max)
        && h::valid_prefix(original, 15)
        && 0 <= opening.symbol < lengths.len()
        && lengths[opening.symbol] == opening.length
        && h::canonical_code(lengths, opening.symbol)
            * h::capacity((32 - opening.length) as nat)
            == h::normalized_cursor(original, opening.length, opening.position)
        && 0 <= key < h::capacity(root)
        && key == (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root)
}

pub open spec fn valid_window(lengths: Seq<u16>, original: Seq<u16>,
    root: nat, max: nat, key: int, width: nat, opening: Opening) -> bool {
    context(lengths, original, root, max, key, opening)
        && h::chosen_width(opening.remaining, (opening.length - root) as nat,
            root, max, width)
}

}
