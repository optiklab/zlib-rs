use crate::constructor_cost_specs as model;
use crate::constructor_pages_proofs as facts;
use crate::constructor_pages_specs as ownership;
use crate::constructor_table_specs as table;
use crate::huffman_specs as h;
use crate::page_source_specs as source;
use crate::table_pages_specs as pages;
use vstd::prelude::*;

verus! {

pub(crate) proof fn window_cost(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, key: int, width: nat, opening: source::Opening)
    requires source::valid_window(lengths, original, root, max, key, width, opening),
        ownership::first_opening(lengths, work, root, key, opening),
    ensures model::first_source(lengths, original, work, root, max, opening.position),
        model::source_cost(lengths, original, work, root, max, opening.position) == h::capacity(width),
{
    facts::normalized_window(lengths, original, root, max, key, width, opening);
    crate::huffman_proofs::capacity_positive(width);
    assert(model::source_at(lengths, original, work, opening.position) == opening);
}

pub(crate) proof fn before_fresh(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, processed: nat, regions: Seq<Option<pages::Page>>,
    openings: Seq<Option<source::Opening>>, key: int, candidate: source::Opening)
    requires ownership::ownership(lengths, original, work, root, max, used,
            processed, regions, openings),
        0 <= key < regions.len(), regions[key] == None,
        ownership::first_opening(lengths, work, root, key, candidate),
        candidate.position == processed,
    ensures forall|index: int| 0 <= index < openings.len() ==>
        match #[trigger] openings[index] {
            Some(opening) => opening.position < processed,
            None => true,
        },
{
    assert forall|index: int| 0 <= index < openings.len() implies
        match #[trigger] openings[index] {
            Some(opening) => opening.position < processed,
            None => true,
        } by {
        match (regions[index], openings[index]) {
            (Some(page), Some(opening)) => {
                if opening.position == processed {
                    assert(opening.symbol == candidate.symbol);
                    assert(index == (h::canonical_prefix(lengths, opening.symbol) as int)
                        % h::capacity(root));
                    assert(index == key);
                    assert(false);
                }
            },
            (None, None) => {},
            _ => { assert(false); },
        }
    }
}

pub(crate) proof fn certificate_from_ownership(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat, processed: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>)
    requires original.len() == 16,
        ownership::ownership(lengths, original, work, root, max, used, epoch, regions, openings),
        ownership::first_openings(lengths, work, root, openings),
        table::assigned(lengths, work, processed, root, regions),
        forall|key: int| 0 <= key < openings.len() ==>
            match #[trigger] openings[key] {
                Some(opening) => opening.position < processed,
                None => true,
            },
    ensures model::certificate(lengths, original, work, root, max, processed, regions, openings),
{
}

pub(crate) proof fn prefix_monotone(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, first: nat, second: nat)
    requires first <= second,
    ensures model::prefix_cost(lengths, original, work, root, max, first)
        <= model::prefix_cost(lengths, original, work, root, max, second),
    decreases second,
{
    if first < second {
        prefix_monotone(lengths, original, work, root, max, first, (second - 1) as nat);
    }
}

pub(crate) proof fn remove_last_source(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, processed: nat, regions: Seq<Option<pages::Page>>,
    openings: Seq<Option<source::Opening>>, key: int, opening: source::Opening)
    requires model::certificate(lengths, original, work, root, max, processed + 1, regions, openings),
        0 <= key < regions.len(), openings[key] == Some(opening), opening.position == processed,
    ensures model::certificate(lengths, original, work, root, max, processed,
        regions.update(key, None), openings.update(key, None)),
{
    let next_regions = regions.update(key, None);
    let next_openings = openings.update(key, None);
    assert(regions[key] != None);
    assert(ownership::first_opening(lengths, work, root, key, opening));
    assert forall|position: int| 0 <= position < processed implies
        #[trigger] table::region_for(lengths, root, next_regions, work[position] as int) != None by {
        let symbol = work[position] as int;
        assert(table::region_for(lengths, root, regions, symbol) != None);
        assert(0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15);
        if root < lengths[symbol] {
            let other = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
            assert(0 <= other < regions.len());
            assert(other != key);
            assert(next_regions[other] == regions[other]);
        }
    }
    assert(table::assigned(lengths, work, processed, root, next_regions));
    assert forall|index: int| 0 <= index < next_regions.len() implies
        match (#[trigger] next_regions[index], #[trigger] next_openings[index]) {
            (None, None) => true,
            (Some(page), Some(witness)) =>
                source::valid_window(lengths, original, root, max, index, page.width, witness)
                && ownership::first_opening(lengths, work, root, index, witness)
                && witness.position < processed,
            _ => false,
        } by {
        if index != key {
            assert(next_regions[index] == regions[index]);
            assert(next_openings[index] == openings[index]);
            match openings[index] {
                Some(witness) => {
                    if witness.position == processed {
                        assert(witness.symbol == opening.symbol);
                        assert(index == key);
                        assert(false);
                    }
                },
                None => {},
            }
        }
    }
}

pub(crate) proof fn skip_last_source(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, processed: nat, regions: Seq<Option<pages::Page>>,
    openings: Seq<Option<source::Opening>>)
    requires model::certificate(lengths, original, work, root, max, processed + 1, regions, openings),
        !model::first_source(lengths, original, work, root, max, processed),
    ensures model::certificate(lengths, original, work, root, max, processed, regions, openings),
{
    assert(table::assigned(lengths, work, processed, root, regions));
    assert forall|key: int| 0 <= key < regions.len() implies
        match (#[trigger] regions[key], #[trigger] openings[key]) {
            (None, None) => true,
            (Some(page), Some(opening)) =>
                source::valid_window(lengths, original, root, max, key, page.width, opening)
                && ownership::first_opening(lengths, work, root, key, opening)
                && opening.position < processed,
            _ => false,
        } by {
        match (regions[key], openings[key]) {
            (Some(page), Some(opening)) => {
                if opening.position == processed {
                    window_cost(lengths, original, work, root, max, key, page.width, opening);
                    assert(false);
                }
            },
            (None, None) => {},
            _ => { assert(false); },
        }
    }
}

pub(crate) proof fn cells_prefix(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, processed: nat, regions: Seq<Option<pages::Page>>,
    openings: Seq<Option<source::Opening>>)
    requires model::certificate(lengths, original, work, root, max, processed, regions, openings),
    ensures pages::cells(regions) == model::prefix_cost(lengths, original, work, root, max, processed),
    decreases processed,
{
    if processed == 0 {
        assert forall|key: int| 0 <= key < regions.len() implies
            pages::cost(#[trigger] regions[key]) == 0 by {
            match (regions[key], openings[key]) {
                (Some(_), Some(opening)) => { assert(false); },
                (None, None) => {},
                _ => { assert(false); },
            }
        }
        crate::table_pages_proofs::uniform_cells(regions, 0);
    } else {
        let previous = (processed - 1) as nat;
        if model::first_source(lengths, original, work, root, max, previous) {
            let symbol = work[previous as int] as int;
            let key = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
            assert(table::region_for(lengths, root, regions, symbol) != None);
            assert(0 <= key < regions.len());
            match (regions[key], openings[key]) {
                (Some(page), Some(opening)) => {
                    facts::first_opening_unique(lengths, work, root, key, opening,
                        model::source_at(lengths, original, work, previous));
                    assert(opening.position == previous);
                    window_cost(lengths, original, work, root, max, key, page.width, opening);
                    remove_last_source(lengths, original, work, root, max, previous,
                        regions, openings, key, opening);
                    cells_prefix(lengths, original, work, root, max, previous,
                        regions.update(key, None), openings.update(key, None));
                    crate::table_pages_proofs::updated_cells(regions, key, None);
                },
                _ => { assert(false); },
            }
        } else {
            skip_last_source(lengths, original, work, root, max, previous, regions, openings);
            cells_prefix(lengths, original, work, root, max, previous, regions, openings);
        }
    }
}

pub(crate) proof fn refusal_cost(alphabet: h::Alphabet, lengths: Seq<u16>, original: Seq<u16>,
    work: Seq<u16>, root: nat, max: nat, original_codes: Seq<crate::Code>,
    codes: Seq<crate::Code>, witness: table::Refusal)
    requires table::refused(alphabet, lengths, original, work, root, max,
        original_codes, codes, witness),
    ensures witness.used + h::capacity(witness.width)
        == model::candidate_extent(lengths, original, work, root, max, witness.processed),
{
    reveal(table::progress);
    before_fresh(lengths, original, work, root, max, witness.used, witness.processed,
        witness.regions, witness.openings, witness.key, witness.opening);
    certificate_from_ownership(lengths, original, work, root, max, witness.used,
        witness.processed, witness.processed, witness.regions, witness.openings);
    cells_prefix(lengths, original, work, root, max, witness.processed,
        witness.regions, witness.openings);
    window_cost(lengths, original, work, root, max, witness.key, witness.width, witness.opening);
    crate::huffman_proofs::capacity_positive(root);
}

pub(crate) proof fn independent_two_page_cost()
    ensures model::prefix_cost(seq![2u16, 2, 3, 3, 3, 3],
        crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 2, 3, 6) == 4,
        model::candidate_extent(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 2, 3, 2) == 6,
        model::candidate_extent(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 2, 3, 4) == 8,
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let original = crate::subtable_coverage_proofs::fixture_counts();
    let work = seq![0u16, 1, 2, 3, 4, 5];
    let regions = seq![None, Some(pages::Page { base: 4, width: 1 }),
        None, Some(pages::Page { base: 6, width: 1 })];
    let openings = seq![None, Some(source::Opening { symbol: 2, position: 2, length: 3,
            remaining: crate::page_source_proofs::fixture_remaining() }),
        None, Some(source::Opening { symbol: 4, position: 4, length: 3,
            remaining: Seq::new(16, |level: int| if level == 3 { 2u16 } else { 0u16 }) })];
    facts::independent_two_pages();
    facts::independent_first_openings();
    crate::constructor_table_proofs::independent_complete_progress();
    reveal(table::progress);
    assert(table::assigned(lengths, work, 6, 2, regions));
    assert(ownership::first_openings(lengths, work, 2, openings));
    assert forall|key: int| 0 <= key < openings.len() implies
        match #[trigger] openings[key] {
            Some(opening) => opening.position < 6,
            None => true,
        } by {}
    certificate_from_ownership(lengths, original, work, 2, 3, 8, 5, 6, regions, openings);
    cells_prefix(lengths, original, work, 2, 3, 6, regions, openings);
    assert(h::capacity(2) == 4) by (compute);
    window_cost(lengths, original, work, 2, 3, 1, 1, openings[1].unwrap());
    window_cost(lengths, original, work, 2, 3, 3, 1, openings[3].unwrap());
    reveal_with_fuel(model::prefix_cost, 7);
    assert(model::prefix_cost(lengths, original, work, 2, 3, 3) == 2);
    prefix_monotone(lengths, original, work, 2, 3, 5, 6);
}

}
