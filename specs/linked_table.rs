use crate::huffman_specs as h;
use crate::root_table_specs as direct;
use crate::table_emission_specs as emission;
use crate::Code;
use vstd::prelude::*;

verus! {

// RFC 1951 canonical prefixes; root/child layout is an implementation representation.
pub(crate) open spec fn is_link(code: Code) -> bool {
    1 <= code.op < 16
}

pub(crate) open spec fn region(root: nat, used: nat, code: Code) -> bool {
    is_link(code)
        && h::subtable_link(code, root, code.val as nat, code.op as nat,
            (code.val as int + h::capacity(code.op as nat)) as nat)
        && code.val as int + h::capacity(code.op as nat) <= used
}

pub(crate) open spec fn leaf(alphabet: h::Alphabet, lengths: Seq<u16>,
    code: Code, word: u32, dropped: nat) -> bool {
    (exists|symbol: int| #[trigger] h::code_prefix_matches(lengths, symbol, word)
        && dropped < lengths[symbol]
        && emission::leaf(alphabet, symbol as nat,
            (lengths[symbol] as int - dropped) as nat, code)
        && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word)
            ==> other == symbol))
        || (dropped == 0 && code == direct::invalid_hole()
            && forall|symbol: int| !h::code_prefix_matches(lengths, symbol, word))
}

#[verifier::opaque]
pub(crate) open spec fn table(alphabet: h::Alphabet, lengths: Seq<u16>,
    root: nat, used: nat, codes: Seq<Code>) -> bool {
    1 <= root <= 15 && h::capacity(root) <= used <= codes.len()
        && (forall|index: int| 0 <= index < h::capacity(root)
            && is_link(#[trigger] codes[index]) ==> region(root, used, codes[index]))
        && forall|word: u64| {
            let first = #[trigger] codes[(word as u32 as int) % h::capacity(root)];
            if is_link(first) {
                leaf(alphabet, lengths, codes[h::subtable_index(first, word as nat)],
                    word as u32, root)
            } else {
                leaf(alphabet, lengths, first, word as u32, 0)
            }
        }
}

}
