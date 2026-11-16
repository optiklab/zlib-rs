use crate::constructor_pages_specs as ownership;
use crate::constructor_table_specs as table;
use crate::huffman_specs as h;
use crate::page_source_specs as source;
use crate::table_pages_specs as pages;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn source_at(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    position: nat) -> source::Opening
    recommends position < work.len(), work[position as int] < lengths.len(),
{
    source::Opening {
        symbol: work[position as int] as int, position,
        length: lengths[work[position as int] as int] as nat,
        remaining: ownership::opening_population(original, position),
    }
}

pub(crate) open spec fn first_source(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, position: nat) -> bool {
    original.len() == 16 && position < work.len() && work[position as int] < lengths.len()
        && 1 <= root < lengths[work[position as int] as int] <= max <= 15
        && ownership::first_opening(lengths, work, root,
            (h::canonical_prefix(lengths, work[position as int] as int) as int) % h::capacity(root),
            source_at(lengths, original, work, position))
}

pub(crate) open spec fn source_cost(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, position: nat) -> nat {
    if first_source(lengths, original, work, root, max, position) {
        h::capacity(ownership::opening_width(original, position,
            lengths[work[position as int] as int] as nat, root, max)) as nat
    } else { 0 }
}

pub(crate) open spec fn prefix_cost(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, processed: nat) -> nat
    decreases processed,
{
    if processed == 0 { 0 }
    else {
        prefix_cost(lengths, original, work, root, max, (processed - 1) as nat)
            + source_cost(lengths, original, work, root, max, (processed - 1) as nat)
    }
}

pub(crate) open spec fn candidate_extent(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, position: nat) -> nat {
    h::capacity(root) as nat + prefix_cost(lengths, original, work, root, max, position + 1)
}

// Removing a page preserves its source cost, not the physical placement of other pages.
pub(crate) open spec fn certificate(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, processed: nat, regions: Seq<Option<pages::Page>>,
    openings: Seq<Option<source::Opening>>) -> bool {
    original.len() == 16 && 1 <= root <= max <= 15 && regions.len() == openings.len()
        && table::assigned(lengths, work, processed, root, regions)
        && forall|key: int| 0 <= key < regions.len() ==>
            match (#[trigger] regions[key], #[trigger] openings[key]) {
                (None, None) => true,
                (Some(page), Some(opening)) =>
                    source::valid_window(lengths, original, root, max, key, page.width, opening)
                    && ownership::first_opening(lengths, work, root, key, opening)
                    && opening.position < processed,
                _ => false,
            }
}

}
