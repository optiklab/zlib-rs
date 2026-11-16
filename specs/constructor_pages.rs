use crate::huffman_specs as h;
use crate::page_source_specs as source;
use crate::table_pages_specs as pages;
use vstd::prelude::*;

verus! {

pub open spec fn backing(root: nat, max: nat, extent: int) -> bool {
    1 <= root <= max <= 15
        && extent >= if root == max { h::capacity(max) }
            else { h::capacity(root) + h::capacity(max) }
}

// The epoch is the source position of the last available opening witness.
pub open spec fn ownership(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>) -> bool {
    pages::valid(root, max, used, regions)
        && openings.len() == regions.len()
        && (forall|key: int| 0 <= key < regions.len() ==>
            match (#[trigger] regions[key], #[trigger] openings[key]) {
                (None, None) => true,
                (Some(region), Some(opening)) =>
                    source::valid_window(lengths, original, root, max, key,
                        region.width, opening)
                    && opening.position <= epoch
                    && opening.position < work.len()
                    && work[opening.position as int] as int == opening.symbol,
                _ => false,
            })
}

pub open spec fn first_opening(lengths: Seq<u16>, work: Seq<u16>,
    root: nat, key: int, opening: source::Opening) -> bool {
    opening.position < work.len()
        && 0 <= opening.symbol < lengths.len()
        && opening.symbol == work[opening.position as int] as int
        && 1 <= root < opening.length <= 15
        && opening.length == lengths[opening.symbol]
        && (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root) == key
        && forall|position: int| 0 <= position < opening.position
            && work[position] < lengths.len()
            && root < lengths[work[position] as int] <= 15 ==>
                (#[trigger] h::canonical_prefix(lengths, work[position] as int) as int)
                    % h::capacity(root) != key
}

pub open spec fn first_openings(lengths: Seq<u16>, work: Seq<u16>,
    root: nat, openings: Seq<Option<source::Opening>>) -> bool {
    forall|key: int| 0 <= key < openings.len() ==>
        match #[trigger] openings[key] {
            Some(opening) => first_opening(lengths, work, root, key, opening),
            None => true,
        }
}

pub open spec fn opening_population(original: Seq<u16>, position: nat) -> Seq<u16> {
    Seq::new(16, |level: int| if level == 0 { 0u16 }
        else { h::remaining_count(original, level as nat, position) as u16 })
}

pub open spec fn opening_width_candidate(original: Seq<u16>, position: nat, length: nat,
    root: nat, max: nat, width: nat) -> bool {
    h::chosen_width(opening_population(original, position),
        (length - root) as nat, root, max, width)
}

pub open spec fn opening_width(original: Seq<u16>, position: nat, length: nat,
    root: nat, max: nat) -> nat {
    choose|width: nat| #[trigger] opening_width_candidate(original, position, length, root, max, width)
}

pub open spec fn emission_region(lengths: Seq<u16>, root: nat,
    regions: Seq<Option<pages::Page>>, symbol: int,
    base: nat, width: nat, bits: nat, prefix: nat) -> bool {
    0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15
        && if lengths[symbol] <= root {
            base == 0 && width == root && bits == lengths[symbol]
                && prefix == h::canonical_prefix(lengths, symbol)
        } else {
            let key = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
            bits == lengths[symbol] - root
                && prefix == (h::canonical_prefix(lengths, symbol) as int) / h::capacity(root)
                && 0 <= key < regions.len()
                && match regions[key] {
                    Some(page) => base == page.base && width == page.width,
                    None => false,
                }
        }
}

}
