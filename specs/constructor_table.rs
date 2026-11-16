use crate::huffman_specs as h;
use crate::page_source_specs as source;
use crate::table_emission_specs as emission;
use crate::table_pages_specs as pages;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) struct Refusal {
    pub processed: nat,
    pub used: int,
    pub key: int,
    pub width: nat,
    pub regions: Seq<Option<pages::Page>>,
    pub openings: Seq<Option<source::Opening>>,
    pub opening: source::Opening,
}

pub(crate) open spec fn refused(alphabet: h::Alphabet, lengths: Seq<u16>,
    counts: Seq<u16>, work: Seq<u16>, root: nat, max: nat,
    original: Seq<Code>, codes: Seq<Code>, witness: Refusal) -> bool {
    0 < witness.processed < h::before(counts, 16)
        && witness.processed < work.len()
        && crate::constructor_pages_specs::ownership(lengths, counts, work, root, max,
            witness.used, witness.processed, witness.regions, witness.openings)
        && crate::constructor_pages_specs::first_openings(lengths, work, root, witness.openings)
        && progress(alphabet, lengths, work, witness.processed, root, witness.used,
            witness.regions, original, codes)
        && 0 <= witness.key < witness.regions.len()
        && witness.regions[witness.key] == None
        && witness.opening.position == witness.processed
        && witness.opening.symbol == work[witness.processed as int] as int
        && crate::constructor_pages_specs::first_opening(lengths, work, root,
            witness.key, witness.opening)
        && source::valid_window(lengths, counts, root, max, witness.key,
            witness.width, witness.opening)
        && witness.used + h::capacity(witness.width) <= original.len()
        && !crate::table_preparation_specs::root_capacity_allowed(alphabet,
            (witness.used + h::capacity(witness.width)) as nat)
}

#[verifier::opaque]
pub(crate) open spec fn result(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    outcome: crate::huffman::InflateTable) -> bool {
    let root = crate::table_preparation_specs::clamped_root(requested,
        h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat);
    codes.len() == original.len() && work.len() == original_work.len()
        && match outcome {
            crate::huffman::InflateTable::InvalidCode =>
                h::maximum_length(lengths) > 0
                    && !h::accepted_lengths(lengths,
                        crate::table_preparation_specs::require_complete(alphabet))
                    && codes == original && work == original_work,
            crate::huffman::InflateTable::EnoughIsNotEnough =>
                h::accepted_lengths(lengths,
                    crate::table_preparation_specs::require_complete(alphabet))
                    && crate::table_preparation_specs::sorted_workspace(lengths, original_work, work)
                    && ((!crate::table_preparation_specs::root_capacity_allowed(alphabet,
                            h::capacity(root) as nat) && codes == original)
                        || exists|witness: Refusal| #[trigger] refused(alphabet, lengths,
                            h::histogram(lengths), work, root,
                            h::maximum_length(lengths) as nat, original, codes, witness)),
            crate::huffman::InflateTable::Success { root: actual_root, used } =>
                if h::maximum_length(lengths) == 0 {
                    actual_root == 1 && used == 2 && work == original_work
                        && crate::table_preparation_specs::empty_table(original, codes)
                } else {
                    h::accepted_lengths(lengths,
                        crate::table_preparation_specs::require_complete(alphabet))
                        && actual_root == root
                        && crate::table_preparation_specs::root_capacity_allowed(alphabet, used as nat)
                        && crate::linked_table_specs::table(alphabet, lengths, root, used as nat, codes)
                        && crate::table_preparation_specs::sorted_workspace(lengths, original_work, work)
                        && forall|index: int| used <= index < codes.len() ==>
                            #[trigger] codes[index] == original[index]
                },
        }
}

pub(crate) open spec fn lookup_page(root: nat, regions: Seq<Option<pages::Page>>,
    word: u64) -> Option<pages::Page> {
    let key = (word as u32 as int) % h::capacity(root);
    if 0 <= key < regions.len() { regions[key] } else { None }
}

pub(crate) open spec fn lookup_index(root: nat, regions: Seq<Option<pages::Page>>,
    word: u64) -> int {
    match lookup_page(root, regions, word) {
        Some(page) => page.base + ((word as int) / h::capacity(root)) % h::capacity(page.width),
        None => (word as u32 as int) % h::capacity(root),
    }
}

pub(crate) open spec fn lookup_drop(root: nat, regions: Seq<Option<pages::Page>>,
    word: u64) -> nat {
    match lookup_page(root, regions, word) { Some(_) => root, None => 0 }
}

pub(crate) open spec fn region_for(lengths: Seq<u16>, root: nat,
    regions: Seq<Option<pages::Page>>, symbol: int) -> Option<pages::Page> {
    if !(0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15) {
        None
    } else if lengths[symbol] <= root {
        Some(pages::Page { base: 0, width: root })
    } else {
        let key = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
        if 0 <= key < regions.len() { regions[key] } else { None }
    }
}

pub(crate) open spec fn symbol_bits(lengths: Seq<u16>, root: nat, symbol: int) -> nat
    recommends 0 <= symbol < lengths.len(),
{
    if lengths[symbol] <= root { lengths[symbol] as nat }
    else { (lengths[symbol] - root) as nat }
}

#[verifier::opaque]
pub(crate) open spec fn target(lengths: Seq<u16>, work: Seq<u16>, position: int,
    root: nat, regions: Seq<Option<pages::Page>>, index: int) -> bool {
    0 <= position < work.len() && {
        let symbol = work[position] as int;
        match region_for(lengths, root, regions, symbol) {
            Some(page) => h::table_replica(page.base as nat,
                if lengths[symbol] <= root { h::canonical_prefix(lengths, symbol) as nat }
                else { ((h::canonical_prefix(lengths, symbol) as int) / h::capacity(root)) as nat },
                symbol_bits(lengths, root, symbol), page.width, index),
            None => false,
        }
    }
}

pub(crate) open spec fn seen(lengths: Seq<u16>, work: Seq<u16>, processed: nat,
    root: nat, regions: Seq<Option<pages::Page>>, index: int) -> bool {
    exists|position: int| 0 <= position < processed
        && target(lengths, work, position, root, regions, index)
}

pub(crate) open spec fn written(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat,
    regions: Seq<Option<pages::Page>>, index: int, code: Code) -> bool {
    exists|position: int| 0 <= position < processed
        && target(lengths, work, position, root, regions, index)
        && emission::leaf(alphabet, work[position] as nat,
            symbol_bits(lengths, root, work[position] as int), code)
}

pub(crate) open spec fn assigned(lengths: Seq<u16>, work: Seq<u16>, processed: nat,
    root: nat, regions: Seq<Option<pages::Page>>) -> bool {
    processed <= work.len()
        && forall|position: int| 0 <= position < processed ==>
            #[trigger] region_for(lengths, root, regions, work[position] as int) != None
}

#[verifier::opaque]
pub(crate) open spec fn progress(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, used: int,
    regions: Seq<Option<pages::Page>>, original: Seq<Code>, codes: Seq<Code>) -> bool {
    1 <= root <= 15 && regions.len() == h::capacity(root)
        && h::capacity(root) <= used <= codes.len() && codes.len() == original.len()
        && assigned(lengths, work, processed, root, regions)
        && forall|index: int| 0 <= index < codes.len() ==>
            if index < regions.len() && regions[index] != None {
                match regions[index] {
                    Some(page) => h::subtable_link(codes[index], root,
                        page.base as nat, page.width,
                        (page.base + h::capacity(page.width)) as nat),
                    None => false,
                }
            } else if seen(lengths, work, processed, root, regions, index) {
                written(alphabet, lengths, work, processed, root, regions, index, codes[index])
            } else { codes[index] == original[index] }
}

}
