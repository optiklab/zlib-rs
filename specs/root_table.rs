use crate::huffman::InflateTable;
use crate::huffman_specs as h;
use crate::table_emission_specs as emission;
use crate::table_preparation_specs as preparation;
use crate::Code;
use vstd::prelude::*;

verus! {

// RFC 1951 (May 1996), 3.2.2 and 3.2.5-3.2.7: canonical prefixes
// select alphabet-specific leaves; an unused one-bit prefix is invalid.
pub(crate) open spec fn invalid_hole() -> Code {
    Code { op: 64, bits: 1, val: 0 }
}

pub(crate) open spec fn entry(alphabet: h::Alphabet, lengths: Seq<u16>,
    code: Code, word: u32) -> bool {
    (exists|symbol: int| #[trigger] h::code_prefix_matches(lengths, symbol, word)
        && emission::leaf(alphabet, symbol as nat, lengths[symbol] as nat, code)
        && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word)
            ==> other == symbol))
        || (code == invalid_hole()
            && forall|symbol: int| !h::code_prefix_matches(lengths, symbol, word))
}

#[verifier::opaque]
pub(crate) open spec fn table(alphabet: h::Alphabet, lengths: Seq<u16>,
    root: nat, codes: Seq<Code>) -> bool {
    root == h::maximum_length(lengths) && 1 <= root <= 15
        && h::capacity(root) <= codes.len()
        && forall|index: int| 0 <= index < h::capacity(root) ==>
            #[trigger] entry(alphabet, lengths, codes[index], index as u32)
}

// Capacity rejection is the inherited implementation policy, not an RFC limit.
#[verifier::opaque]
pub(crate) open spec fn result(alphabet: h::Alphabet, lengths: Seq<u16>,
    before: Seq<Code>, codes: Seq<Code>, before_work: Seq<u16>, work: Seq<u16>,
    outcome: InflateTable) -> bool {
    codes.len() == before.len() && work.len() == before_work.len()
        && match outcome {
            InflateTable::InvalidCode =>
                h::maximum_length(lengths) > 0
                    && !h::accepted_lengths(lengths, preparation::require_complete(alphabet))
                    && codes == before && work == before_work,
            InflateTable::EnoughIsNotEnough =>
                h::accepted_lengths(lengths, preparation::require_complete(alphabet))
                    && !preparation::root_capacity_allowed(alphabet,
                        h::capacity(h::maximum_length(lengths) as nat) as nat)
                    && codes == before && preparation::sorted_workspace(lengths, before_work, work),
            InflateTable::Success { root, used } =>
                if h::maximum_length(lengths) == 0 {
                    root == 1 && used == 2 && work == before_work
                        && preparation::empty_table(before, codes)
                } else {
                    h::accepted_lengths(lengths, preparation::require_complete(alphabet))
                        && root == h::maximum_length(lengths) && used == h::capacity(root as nat)
                        && preparation::root_capacity_allowed(alphabet, used as nat)
                        && table(alphabet, lengths, root as nat, codes)
                        && preparation::sorted_workspace(lengths, before_work, work)
                        && forall|index: int| used <= index < codes.len() ==>
                            #[trigger] codes[index] == before[index]
                },
        }
}

pub(crate) open spec fn seen(lengths: Seq<u16>, work: Seq<u16>, processed: nat,
    word: u32) -> bool {
    exists|position: int| 0 <= position < processed && position < work.len()
        && h::code_prefix_matches(lengths, work[position] as int, word)
}

pub(crate) open spec fn written(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, word: u32, code: Code) -> bool {
    exists|position: int| 0 <= position < processed && position < work.len()
        && h::code_prefix_matches(lengths, work[position] as int, word)
        && emission::leaf(alphabet, work[position] as nat,
            lengths[work[position] as int] as nat, code)
}

#[verifier::opaque]
pub(crate) open spec fn progress(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, original: Seq<Code>,
    codes: Seq<Code>) -> bool {
    processed <= work.len() && codes.len() == original.len()
        && forall|index: int| 0 <= index < codes.len() ==>
            if index < h::capacity(root) && seen(lengths, work, processed, index as u32) {
                written(alphabet, lengths, work, processed, index as u32, codes[index])
            } else { codes[index] == original[index] }
}

}
