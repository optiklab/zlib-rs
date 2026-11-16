use crate::huffman_specs as h;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn leaf(alphabet: h::Alphabet, symbol: nat, bits: nat,
    entry: Code) -> bool {
    h::symbol_domain(alphabet, symbol) && 1 <= bits <= 15
        && entry.bits == bits && h::entry_meaning(alphabet, symbol, entry.op, entry.val)
}

pub(crate) open spec fn child_context(lengths: Seq<u16>, counts: Seq<u16>,
    symbol: nat, length: nat, root: nat, prefix: nat, base: nat, width: nat,
    used: nat, link: Code, word: u64) -> bool {
    symbol < lengths.len() && lengths[symbol as int] == length
        && 1 <= root < length <= 15
        && h::valid_histogram(lengths, counts) && h::valid_prefix(counts, 15)
        && h::subtable_link(link, root, base, width, used)
        && prefix == (h::canonical_prefix(lengths, symbol as int) as int) / h::capacity(root)
        && prefix < h::capacity((length - root) as nat)
        && (word as u32 as int) % h::capacity(root)
            == (h::canonical_prefix(lengths, symbol as int) as int) % h::capacity(root)
}

#[verifier::opaque]
pub(crate) open spec fn result(alphabet: h::Alphabet, symbol: nat, bits: nat,
    base: nat, width: nat, prefix: nat, before: Seq<Code>, after: Seq<Code>,
    entry: Code, previous_size: nat) -> bool {
    1 <= bits <= width <= 15 && prefix < h::capacity(bits)
        && base + h::capacity(width) <= before.len()
        && previous_size == h::capacity(width)
        && leaf(alphabet, symbol, bits, entry)
        && after.len() == before.len()
        && forall|index: int| 0 <= index < before.len() ==>
            #[trigger] after[index] == if h::table_replica(base, prefix, bits, width, index) {
                entry
            } else { before[index] }
}

}
