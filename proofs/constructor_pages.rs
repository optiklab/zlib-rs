use crate::constructor_pages_specs as model;
use crate::huffman_decode as decode;
use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::page_source_specs as source;
use crate::subtable_coverage_proofs as coverage;
use crate::table_emission_specs as emission;
use crate::table_pages_proofs as allocations;
use crate::table_pages_specs as pages;
use crate::Code;
use vstd::prelude::*;

verus! {

pub proof fn canonical_population(original: Seq<u16>, position: nat)
    requires original.len() == 16,
    ensures h::remaining_histogram(original, model::opening_population(original, position), position),
{
    assert forall|level: int| 1 <= level <= 15 implies
        h::remaining_count(original, level as nat, position) <= original[level] by {
        let start = h::before(original, level as nat);
        let end = start + original[level] as nat;
        if position <= start {
        } else if end <= position {
        } else {
            assert(end - position <= original[level]);
        }
    }
}

pub proof fn remaining_unique(original: Seq<u16>, first: Seq<u16>, second: Seq<u16>,
    position: nat)
    requires h::remaining_histogram(original, first, position),
        h::remaining_histogram(original, second, position),
    ensures first == second,
{
    assert forall|level: int| 0 <= level < first.len() implies
        #[trigger] first[level] == second[level] by {
        if level == 0 {
            assert(first[level] == 0 && second[level] == 0);
        } else {
            assert(first[level] == h::remaining_count(original, level as nat, position));
            assert(second[level] == h::remaining_count(original, level as nat, position));
        }
    }
    assert(first =~= second);
}

pub proof fn chosen_width_unique(counts: Seq<u16>, start: nat, drop: nat, max: nat,
    first: nat, second: nat)
    requires counts.len() == 16, 1 <= start, start + drop <= max <= 15,
        h::chosen_width(counts, start, drop, max, first),
        h::chosen_width(counts, start, drop, max, second),
    ensures first == second,
{
    if first != second {
        let small = if first < second { first } else { second };
        let large = if first < second { second } else { first };
        assert(h::chosen_width(counts, start, drop, max, small));
        assert(h::chosen_width(counts, start, drop, max, large));
        assert(start <= small < large && small + drop < max);
        assert(h::lookahead_space(counts, start, drop, small)
            - counts[(small + drop) as int] <= 0);
        assert(h::lookahead_space(counts, start, drop, small)
            - counts[(small + drop) as int] > 0);
        assert(false);
    }
}

pub proof fn first_opening_unique(lengths: Seq<u16>, work: Seq<u16>, root: nat,
    key: int, first: source::Opening, second: source::Opening)
    requires model::first_opening(lengths, work, root, key, first),
        model::first_opening(lengths, work, root, key, second),
    ensures first.position == second.position, first.symbol == second.symbol,
        first.length == second.length,
{
    if first.position < second.position {
        assert((h::canonical_prefix(lengths, work[first.position as int] as int) as int)
            % h::capacity(root) != key);
        assert(false);
    } else if second.position < first.position {
        assert((h::canonical_prefix(lengths, work[second.position as int] as int) as int)
            % h::capacity(root) != key);
        assert(false);
    }
}

pub proof fn window_unique(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, key: int, first_width: nat, second_width: nat,
    first: source::Opening, second: source::Opening)
    requires source::valid_window(lengths, original, root, max, key, first_width, first),
        source::valid_window(lengths, original, root, max, key, second_width, second),
        model::first_opening(lengths, work, root, key, first),
        model::first_opening(lengths, work, root, key, second),
    ensures first == second, first_width == second_width,
{
    first_opening_unique(lengths, work, root, key, first, second);
    remaining_unique(original, first.remaining, second.remaining, first.position);
    chosen_width_unique(first.remaining, (first.length - root) as nat, root, max,
        first_width, second_width);
}

pub proof fn normalized_window(lengths: Seq<u16>, original: Seq<u16>, root: nat,
    max: nat, key: int, width: nat, opening: source::Opening)
    requires source::valid_window(lengths, original, root, max, key, width, opening),
    ensures opening.remaining == model::opening_population(original, opening.position),
        width == model::opening_width(original, opening.position, opening.length, root, max),
{
    canonical_population(original, opening.position);
    remaining_unique(original, opening.remaining, model::opening_population(original, opening.position),
        opening.position);
    assert(model::opening_width_candidate(original, opening.position, opening.length,
        root, max, width));
    assert(exists|candidate: nat| #[trigger] model::opening_width_candidate(original,
        opening.position, opening.length, root, max, candidate));
    assert(model::opening_width_candidate(original, opening.position, opening.length,
        root, max, model::opening_width(original, opening.position, opening.length, root, max)));
    chosen_width_unique(model::opening_population(original, opening.position),
        (opening.length - root) as nat, root, max, width,
        model::opening_width(original, opening.position, opening.length, root, max));
}

pub proof fn ordered_positions(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    first: nat, second: nat)
    requires h::valid_histogram(lengths, counts), h::bucket_ordered(lengths, counts, work),
        first < second < h::before(counts, 16),
    ensures first < work.len(), second < work.len(),
        work[first as int] < lengths.len(), work[second as int] < lengths.len(),
        1 <= lengths[work[first as int] as int] <= lengths[work[second as int] as int] <= 15,
        lengths[work[first as int] as int] < lengths[work[second as int] as int]
            || (lengths[work[first as int] as int] == lengths[work[second as int] as int]
                && work[first as int] < work[second as int]),
{
    let first_length = facts::ordered_symbol_at(lengths, counts, work, first as int);
    let second_length = facts::ordered_symbol_at(lengths, counts, work, second as int);
    if first_length > second_length {
        facts::before_monotone(counts, second_length + 1, first_length);
        assert(false);
    }
    if first_length == second_length {
        facts::stable_bucket_order(lengths, counts, work, first_length as int,
            first as int - h::before(counts, first_length) as int,
            second as int - h::before(counts, first_length) as int);
    }
}

pub proof fn first_openings_updated(lengths: Seq<u16>, work: Seq<u16>, root: nat,
    openings: Seq<Option<source::Opening>>, key: int, opening: source::Opening)
    requires model::first_openings(lengths, work, root, openings),
        0 <= key < openings.len(),
        model::first_opening(lengths, work, root, key, opening),
    ensures model::first_openings(lengths, work, root, openings.update(key, Some(opening))),
{
    assert forall|index: int| 0 <= index < openings.len() implies
        match #[trigger] openings.update(key, Some(opening))[index] {
            Some(witness) => model::first_opening(lengths, work, root, index, witness),
            None => true,
        } by {
        if index != key {
            assert(openings.update(key, Some(opening))[index] == openings[index]);
        }
    }
}

pub proof fn opening_ledger_frame(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat, regions: Seq<Option<pages::Page>>,
    expected: Seq<Option<source::Opening>>, actual: Seq<Option<source::Opening>>)
    requires actual == expected,
        model::ownership(lengths, counts, work, root, max, used, epoch, regions, expected),
        model::first_openings(lengths, work, root, expected),
    ensures model::ownership(lengths, counts, work, root, max, used, epoch, regions, actual),
        model::first_openings(lengths, work, root, actual),
{
}

pub proof fn independent_first_openings()
    ensures model::first_openings(seq![2u16, 2, 3, 3, 3, 3], seq![0u16, 1, 2, 3, 4, 5], 2,
        seq![None, Some(source::Opening { symbol: 2, position: 2, length: 3,
                remaining: Seq::empty() }), None,
            Some(source::Opening { symbol: 4, position: 4, length: 3,
                remaining: Seq::empty() })]),
        !model::first_openings(seq![2u16, 2, 3, 3, 3, 3], seq![0u16, 1, 2, 3, 4, 5], 2,
            seq![None, Some(source::Opening { symbol: 3, position: 3, length: 3,
                remaining: Seq::empty() }), None,
                Some(source::Opening { symbol: 4, position: 4, length: 3,
                    remaining: Seq::empty() })]),
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let work = seq![0u16, 1, 2, 3, 4, 5];
    let first = source::Opening { symbol: 2, position: 2, length: 3, remaining: Seq::empty() };
    let second = source::Opening { symbol: 4, position: 4, length: 3, remaining: Seq::empty() };
    let late = source::Opening { symbol: 3, position: 3, length: 3, remaining: Seq::empty() };
    assert(h::capacity(2) == 4 && h::capacity(29) == 536870912
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 2) == 4
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 3) == 5
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 4) == 6) by (compute);
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(0x8000_0000, bit) == h::word_bit(1, (31 - bit) as u32) by {
        assert((0x8000_0000u32 >> bit) & 1 == (1u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(0xa000_0000, bit) == h::word_bit(5, (31 - bit) as u32) by {
        assert((0xa000_0000u32 >> bit) & 1 == (5u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(0xc000_0000, bit) == h::word_bit(3, (31 - bit) as u32) by {
        assert((0xc000_0000u32 >> bit) & 1 == (3u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    facts::reversal_matches_model(0x8000_0000, 1);
    facts::reversal_matches_model(0xa000_0000, 5);
    facts::reversal_matches_model(0xc000_0000, 3);
    facts::canonical_prefix_at_cursor(lengths, 2, 0x8000_0000, 1);
    facts::canonical_prefix_at_cursor(lengths, 3, 0xa000_0000, 5);
    facts::canonical_prefix_at_cursor(lengths, 4, 0xc000_0000, 3);
    assert forall|position: int| 0 <= position < 4
        && work[position] < lengths.len() && 2 < lengths[work[position] as int] <= 15 implies
            (#[trigger] h::canonical_prefix(lengths, work[position] as int) as int)
                % h::capacity(2) != 3 by {
        assert(position == 2 || position == 3);
        if position == 2 {
            assert(h::canonical_prefix(lengths, work[position] as int) == 1);
        } else {
            assert(h::canonical_prefix(lengths, work[position] as int) == 5);
        }
    }
    assert(model::first_opening(lengths, work, 2, 1, first));
    assert(model::first_opening(lengths, work, 2, 3, second));
    assert(!model::first_opening(lengths, work, 2, 1, late));
}

pub proof fn initial(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat)
    requires 1 <= root <= max <= 15,
    ensures model::ownership(lengths, counts, work, root, max, h::capacity(root), 0,
        Seq::new(h::capacity(root) as nat, |key: int| None),
        Seq::new(h::capacity(root) as nat, |key: int| None)),
{
    allocations::initial(root, max);
}

pub proof fn advanced(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, previous: nat, current: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>)
    requires model::ownership(lengths, counts, work, root, max, used, previous, regions, openings),
        previous <= current,
    ensures model::ownership(lengths, counts, work, root, max, used, current, regions, openings),
{
    assert forall|key: int| 0 <= key < regions.len() implies
        match (#[trigger] regions[key], #[trigger] openings[key]) {
            (None, None) => true,
            (Some(region), Some(opening)) =>
                source::valid_window(lengths, counts, root, max, key, region.width, opening)
                && opening.position <= current && opening.position < work.len()
                && work[opening.position as int] as int == opening.symbol,
            _ => false,
        } by {}
}

pub proof fn current_opening(lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
    remaining: Seq<u16>, position: nat, length: nat, root: nat, max: nat,
    cursor: u32, code: u32)
    requires h::valid_histogram(lengths, original), h::bucket_ordered(lengths, original, work),
        h::valid_prefix(original, 15), h::maximum_length(lengths) <= max,
        1 <= root < length <= max <= 15,
        h::before(original, length) <= position < h::before(original, length + 1),
        h::remaining_histogram(original, remaining, position),
        cursor as int == h::normalized_cursor(original, length, position),
        h::is_reversal(cursor, code),
    ensures position < work.len(), work[position as int] < lengths.len(),
        code == h::canonical_prefix(lengths, work[position as int] as int),
        source::context(lengths, original, root, max,
            (code & (u32::MAX >> ((32 - root) as u32))) as int,
            source::Opening {
                symbol: work[position as int] as int, position, length, remaining,
            }),
{
    facts::normalized_cursor_bound(lengths, original, work, length, position);
    facts::reversal_matches_model(cursor, code);
    crate::huffman_decode::low_mask_remainder(code, root as u32);
    facts::capacity_positive(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(code as int, h::capacity(root));
}

pub proof fn active_page(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    key: int, page: pages::Page, symbol: int)
    requires model::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        0 <= key < regions.len(), regions[key] == Some(page),
        0 <= symbol < lengths.len(), root < lengths[symbol] <= 15,
        (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root) == key,
    ensures lengths[symbol] <= root + page.width,
        h::capacity(root) <= page.base,
        page.base + h::capacity(page.width) <= used,
{
    match openings[key] {
        Some(opening) => {
            crate::page_source_proofs::covered(lengths, counts, root, max, key,
                page.width, opening, symbol);
        },
        None => { assert(false); },
    }
}

pub proof fn canonical_self(lengths: Seq<u16>, counts: Seq<u16>, symbol: int)
    requires h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= 15,
    ensures h::code_prefix_matches(lengths, symbol, h::canonical_prefix(lengths, symbol)),
        h::canonical_prefix(lengths, symbol) < h::capacity(lengths[symbol] as nat),
{
    decode::canonical_word(lengths, counts, symbol);
    let length = lengths[symbol] as u32;
    let prefix = h::canonical_prefix(lengths, symbol);
    let cursor = (h::canonical_code(lengths, symbol)
        * h::capacity((32 - length) as nat)) as u32;
    decode::reversal_symmetric(cursor, prefix);
    decode::reversal_low_prefix(prefix, cursor, length);
    assert(cursor & !(u32::MAX >> length) == cursor) by (bit_vector)
        requires cursor & (u32::MAX >> length) == 0;
    facts::reversal_unique(cursor, prefix,
        prefix & (u32::MAX >> ((32 - length) as u32)));
    decode::low_mask_remainder(prefix, length);
    facts::capacity_positive(length as nat);
    vstd::arithmetic::div_mod::lemma_mod_bound(prefix as int, h::capacity(length as nat));
}

pub proof fn short_root_free(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    symbol: int, key: int)
    requires model::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        0 <= symbol < lengths.len(), 1 <= lengths[symbol] <= root,
        0 <= key < regions.len(), h::code_prefix_matches(lengths, symbol, key as u32),
    ensures regions[key] == None,
{
    facts::depth_capacity(root);
    match (regions[key], openings[key]) {
        (Some(_), Some(opening)) => {
            canonical_self(lengths, counts, opening.symbol);
            let word = h::canonical_prefix(lengths, opening.symbol);
            decode::prefix_root_projection(lengths, symbol, word, root);
            assert((word as int) % h::capacity(root) == key);
            decode::matching_symbol_unique(lengths, counts, symbol, opening.symbol, word);
            assert(false);
        },
        (None, None) => {},
        _ => { assert(false); },
    }
}

pub proof fn storage_bound(root: nat, max: nat, used: int,
    regions: Seq<Option<pages::Page>>, extent: int)
    requires pages::valid(root, max, used, regions), model::backing(root, max, extent),
    ensures h::capacity(root) <= used <= extent,
        used <= u16::MAX, used <= usize::MAX - 32768,
{
    allocations::budget(root, max, used, regions);
    if root < max {
        allocations::bounded_cells(regions, (max - root) as nat);
        facts::capacity_product(root, (max - root) as nat);
    }
}

pub proof fn candidate_storage(root: nat, max: nat, used: int,
    regions: Seq<Option<pages::Page>>, key: int, width: nat, extent: int)
    requires pages::valid(root, max, used, regions), model::backing(root, max, extent),
        0 <= key < regions.len(), regions[key] == None,
        1 <= width, width + root <= max,
    ensures used <= u16::MAX, used <= usize::MAX - 32768,
        used + h::capacity(width) <= extent,
{
    storage_bound(root, max, used, regions, extent);
    allocations::allocated(root, max, used, regions, key, width);
    storage_bound(root, max, used + h::capacity(width),
        regions.update(key, Some(pages::Page { base: used, width })), extent);
}

pub proof fn emission_parameters(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    symbol: int, base: nat, width: nat, bits: nat, prefix: nat)
    requires model::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        model::emission_region(lengths, root, regions, symbol, base, width, bits, prefix),
    ensures 1 <= bits <= width <= 15, prefix < h::capacity(bits),
        base + h::capacity(width) <= used,
{
    canonical_self(lengths, counts, symbol);
    if lengths[symbol] > root {
        let word = h::canonical_prefix(lengths, symbol) as int;
        let key = word % h::capacity(root);
        match regions[key] {
            Some(page) => {
                active_page(lengths, counts, work, root, max, used, epoch,
                    regions, openings, key, page, symbol);
            },
            None => { assert(false); },
        }
        facts::capacity_product(root, bits);
        facts::capacity_positive(root);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(word, h::capacity(root));
        vstd::arithmetic::div_mod::lemma_mod_bound(word, h::capacity(root));
        assert(prefix < h::capacity(bits)) by (nonlinear_arith)
            requires h::capacity(root) > 0,
                word < h::capacity(root) * h::capacity(bits),
                word == h::capacity(root) * prefix + word % h::capacity(root),
                word % h::capacity(root) >= 0;
    } else {
        allocations::budget(root, max, used, regions);
    }
}

pub(crate) proof fn emission_keeps_links(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    alphabet: h::Alphabet, symbol: int, base: nat, width: nat, bits: nat, prefix: nat,
    before: Seq<Code>, after: Seq<Code>, entry: Code)
    requires model::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        model::emission_region(lengths, root, regions, symbol, base, width, bits, prefix),
        emission::result(alphabet, symbol as nat, bits, base, width, prefix,
            before, after, entry, h::capacity(width) as nat),
    ensures forall|key: int| 0 <= key < regions.len() && regions[key] != None
        ==> #[trigger] after[key] == before[key],
{
    reveal(emission::result);
    facts::depth_capacity(root);
    facts::capacity_positive(root);
    facts::capacity_positive(width);
    assert forall|key: int| 0 <= key < regions.len() && regions[key] != None implies
        #[trigger] after[key] == before[key] by {
        if lengths[symbol] <= root {
            if h::table_replica(base, prefix, bits, width, key) {
                assert(h::code_prefix_matches(lengths, symbol, key as u32));
                short_root_free(lengths, counts, work, root, max, used, epoch,
                    regions, openings, symbol, key);
                assert(false);
            }
        } else {
            let active = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
            match regions[active] {
                Some(page) => { assert(h::capacity(root) <= page.base); },
                None => { assert(false); },
            }
        }
        assert(!h::table_replica(base, prefix, bits, width, key));
    }
}

pub(crate) proof fn emission_keeps_other_pages(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    alphabet: h::Alphabet, symbol: int, base: nat, width: nat, bits: nat, prefix: nat,
    before: Seq<Code>, after: Seq<Code>, entry: Code)
    requires model::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        model::emission_region(lengths, root, regions, symbol, base, width, bits, prefix),
        emission::result(alphabet, symbol as nat, bits, base, width, prefix,
            before, after, entry, h::capacity(width) as nat),
        used <= before.len(),
    ensures forall|key: int, index: int| 0 <= key < regions.len() ==>
        match #[trigger] regions[key] {
            Some(page) => page.base <= index < page.base + h::capacity(page.width)
                && (page.base != base || page.width != width)
                ==> #[trigger] after[index] == before[index],
            None => true,
        },
{
    reveal(emission::result);
    facts::capacity_positive(root);
    assert forall|key: int, index: int| 0 <= key < regions.len() implies
        match #[trigger] regions[key] {
            Some(page) => page.base <= index < page.base + h::capacity(page.width)
                && (page.base != base || page.width != width)
                ==> #[trigger] after[index] == before[index],
            None => true,
        } by {
        match regions[key] {
            Some(page) => {
                if page.base <= index < page.base + h::capacity(page.width)
                    && (page.base != base || page.width != width) {
                    if lengths[symbol] > root {
                        let active = (h::canonical_prefix(lengths, symbol) as int)
                            % h::capacity(root);
                        assert(active != key);
                        if active < key {
                            assert(match (regions[active], regions[key]) {
                                (Some(left), Some(right)) => pages::disjoint(left, right),
                                _ => true,
                            });
                        } else {
                            assert(match (regions[key], regions[active]) {
                                (Some(left), Some(right)) => pages::disjoint(left, right),
                                _ => true,
                            });
                        }
                    }
                    assert(!h::table_replica(base, prefix, bits, width, index));
                }
            },
            None => {},
        }
    }
}

pub proof fn allocated(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    key: int, width: nat, opening: source::Opening)
    requires model::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        0 <= key < regions.len(), regions[key] == None,
        source::valid_window(lengths, counts, root, max, key, width, opening),
        opening.position == epoch, epoch < work.len(),
        work[epoch as int] as int == opening.symbol,
    ensures model::ownership(lengths, counts, work, root, max,
        used + h::capacity(width), epoch,
        regions.update(key, Some(pages::Page { base: used, width })),
        openings.update(key, Some(opening))),
{
    allocations::allocated(root, max, used, regions, key, width);
    let next_regions = regions.update(key, Some(pages::Page { base: used, width }));
    let next_openings = openings.update(key, Some(opening));
    assert forall|index: int| 0 <= index < next_regions.len() implies
        match (#[trigger] next_regions[index], #[trigger] next_openings[index]) {
            (None, None) => true,
            (Some(region), Some(witness)) =>
                source::valid_window(lengths, counts, root, max, index, region.width, witness)
                && witness.position <= epoch && witness.position < work.len()
                && work[witness.position as int] as int == witness.symbol,
            _ => false,
        } by {
        if index != key {
            assert(next_regions[index] == regions[index]);
            assert(next_openings[index] == openings[index]);
        }
    }
}

pub proof fn fresh_key(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, previous: nat, current: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>, key: int)
    requires model::ownership(lengths, counts, work, root, max, used, previous, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::bucket_ordered(lengths, counts, work),
        previous < current < h::before(counts, 16),
        previous < work.len(), current < work.len(),
        work[current as int] < lengths.len(), work[previous as int] < lengths.len(),
        root < lengths[work[current as int] as int] <= 15,
        0 <= key < regions.len(),
        key == (h::canonical_prefix(lengths, work[current as int] as int) as int)
            % h::capacity(root),
        lengths[work[previous as int] as int] <= root
            || (h::canonical_prefix(lengths, work[previous as int] as int) as int)
                % h::capacity(root) != key,
    ensures regions[key] == None,
{
    ordered_positions(lengths, counts, work, previous, current);
    match (regions[key], openings[key]) {
        (Some(_), Some(opening)) => {
            if opening.position < previous {
                ordered_positions(lengths, counts, work, opening.position, previous);
                assert(root < lengths[work[previous as int] as int]);
                coverage::wire_root_no_revisit(lengths, counts,
                    opening.symbol, work[previous as int] as int, work[current as int] as int, root);
            } else {
                assert(opening.position == previous);
                assert(root < lengths[work[previous as int] as int]);
            }
            assert(false);
        },
        (None, None) => {},
        _ => { assert(false); },
    }
}

pub proof fn independent_two_pages()
    ensures model::ownership(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
        seq![0u16, 1, 2, 3, 4, 5], 2, 3, 8, 5,
        seq![None, Some(pages::Page { base: 4, width: 1 }),
            None, Some(pages::Page { base: 6, width: 1 })],
        seq![None, Some(source::Opening {
                symbol: 2, position: 2, length: 3,
                remaining: crate::page_source_proofs::fixture_remaining(),
            }), None, Some(source::Opening {
                symbol: 4, position: 4, length: 3,
                remaining: Seq::new(16, |level: int| if level == 3 { 2u16 } else { 0u16 }),
            })]),
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let original = coverage::fixture_counts();
    let work = seq![0u16, 1, 2, 3, 4, 5];
    let first_remaining = crate::page_source_proofs::fixture_remaining();
    let second_remaining = Seq::new(16, |level: int| if level == 3 { 2u16 } else { 0u16 });
    let first = source::Opening {
        symbol: 2, position: 2, length: 3, remaining: first_remaining,
    };
    let second = source::Opening {
        symbol: 4, position: 4, length: 3, remaining: second_remaining,
    };
    crate::page_source_proofs::independent_opening();
    assert(h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 2, 0)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 2, 1)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 3, 0)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 3, 1)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 3, 2)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            seq![0u16, 1, 2, 3, 4, 5], 3, 3)) by (compute);
    assert(h::bucket_ordered(lengths, original, work));
    assert(h::before(coverage::fixture_counts(), 3) == 2
        && h::before(coverage::fixture_counts(), 4) == 6
        && h::before(coverage::fixture_counts(), 16) == 6
        && h::normalized_cursor(coverage::fixture_counts(), 3, 4) == 0xc000_0000
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 3) == 5
        && h::capacity(29) == 536870912
        && h::capacity(1) == 2 && h::capacity(2) == 4) by (compute);
    assert forall|level: int| 1 <= level <= 15 implies
        second_remaining[level] == h::remaining_count(original, level as nat, 4) by {
        if level >= 4 { facts::before_monotone(original, 4, level as nat); }
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(0xc000_0000, bit) == h::word_bit(3, (31 - bit) as u32) by {
        assert((0xc000_0000u32 >> bit) & 1 == (3u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(0xa000_0000, bit) == h::word_bit(5, (31 - bit) as u32) by {
        assert((0xa000_0000u32 >> bit) & 1 == (5u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    facts::reversal_matches_model(0xa000_0000, 5);
    current_opening(lengths, original, work, second_remaining, 4, 3, 2, 3,
        0xc000_0000, 3);
    assert(3u32 & (u32::MAX >> 30) == 3) by (bit_vector);
    assert(h::chosen_width(second_remaining, 1, 2, 3, 1));
    initial(lengths, original, work, 2, 3);
    let empty_regions = Seq::<Option<pages::Page>>::new(4, |key: int| None);
    let empty_openings = Seq::<Option<source::Opening>>::new(4, |key: int| None);
    advanced(lengths, original, work, 2, 3, 4, 0, 2, empty_regions, empty_openings);
    allocated(lengths, original, work, 2, 3, 4, 2, empty_regions, empty_openings, 1, 1, first);
    let one_region = empty_regions.update(1, Some(pages::Page { base: 4, width: 1 }));
    let one_opening = empty_openings.update(1, Some(first));
    active_page(lengths, original, work, 2, 3, 6, 2,
        one_region, one_opening, 1, pages::Page { base: 4, width: 1 }, 3);
    advanced(lengths, original, work, 2, 3, 6, 2, 3, one_region, one_opening);
    fresh_key(lengths, original, work, 2, 3, 6, 3, 4, one_region, one_opening, 3);
    advanced(lengths, original, work, 2, 3, 6, 3, 4, one_region, one_opening);
    allocated(lengths, original, work, 2, 3, 6, 4, one_region, one_opening, 3, 1, second);
    let two_regions = one_region.update(3, Some(pages::Page { base: 6, width: 1 }));
    let two_openings = one_opening.update(3, Some(second));
    advanced(lengths, original, work, 2, 3, 8, 4, 5, two_regions, two_openings);
    assert(two_regions =~= seq![None, Some(pages::Page { base: 4, width: 1 }),
        None, Some(pages::Page { base: 6, width: 1 })]);
    assert(two_openings =~= seq![None, Some(first), None, Some(second)]);
}

}
