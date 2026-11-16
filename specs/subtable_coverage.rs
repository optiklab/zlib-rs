use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

// RFC 1951 3.2.2: a root prefix is a block in the normalized canonical space.
pub open spec fn root_prefix(lengths: Seq<u16>, symbol: int, root: nat) -> int
    recommends 0 <= symbol < lengths.len(), root < lengths[symbol] <= 15,
{
    h::canonical_code(lengths, symbol) * h::capacity((32 - lengths[symbol]) as nat)
        / h::capacity((32 - root) as nat)
}

pub open spec fn in_root(lengths: Seq<u16>, symbol: int, root: nat, cursor: int) -> bool {
    0 <= symbol < lengths.len() && root < lengths[symbol] <= 15
        && root_prefix(lengths, symbol, root) == cursor / h::capacity((32 - root) as nat)
}

pub open spec fn source_context(lengths: Seq<u16>, original: Seq<u16>,
    remaining: Seq<u16>, position: nat, length: nat, root: nat, max: nat) -> bool {
    1 <= root < length <= max <= 15
        && h::valid_histogram(lengths, original)
        && h::maximum_length(lengths) <= max
        && h::before(original, length) <= position < h::before(original, length + 1)
        && h::remaining_histogram(original, remaining, position)
}

}
