use crate::constructor_pages_specs as ownership;
use crate::constructor_table_specs as model;
use crate::huffman_decode as decode;
use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::page_source_specs as source;
use crate::table_emission_specs as emission;
use crate::table_pages_specs as pages;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) proof fn finished(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    outcome: crate::huffman::InflateTable)
    requires crate::table_preparation_specs::result(alphabet, lengths, requested,
        original, codes, original_work, work, crate::huffman::TablePreparation::Finished(outcome)),
    ensures model::result(alphabet, lengths, requested,
        original, codes, original_work, work, outcome),
{
    reveal(model::result);
}

pub(crate) proof fn refused_result(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    witness: model::Refusal)
    requires h::accepted_lengths(lengths, crate::table_preparation_specs::require_complete(alphabet)),
        crate::table_preparation_specs::sorted_workspace(lengths, original_work, work),
        model::refused(alphabet, lengths, h::histogram(lengths), work,
            crate::table_preparation_specs::clamped_root(requested,
                h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
            h::maximum_length(lengths) as nat, original, codes, witness),
    ensures model::result(alphabet, lengths, requested, original, codes,
        original_work, work, crate::huffman::InflateTable::EnoughIsNotEnough),
{
    reveal(model::result);
    reveal(model::progress);
}

pub(crate) proof fn ready_result(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    root: usize, used: usize)
    requires h::maximum_length(lengths) > 0,
        h::accepted_lengths(lengths, crate::table_preparation_specs::require_complete(alphabet)),
        root == crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
        codes.len() == original.len(),
        crate::table_preparation_specs::root_capacity_allowed(alphabet, used as nat),
        crate::table_preparation_specs::sorted_workspace(lengths, original_work, work),
        crate::linked_table_specs::table(alphabet, lengths, root as nat, used as nat, codes),
        forall|index: int| used <= index < codes.len() ==> #[trigger] codes[index] == original[index],
    ensures model::result(alphabet, lengths, requested, original, codes,
        original_work, work, crate::huffman::InflateTable::Success { root, used }),
{
    reveal(model::result);
}

pub(crate) proof fn no_capacity_error(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    outcome: crate::huffman::InflateTable)
    requires model::result(alphabet, lengths, requested,
            original, codes, original_work, work, outcome),
        ownership::backing(crate::table_preparation_specs::clamped_root(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat),
            h::maximum_length(lengths) as nat, original.len() as int),
        crate::table_preparation_specs::root_capacity_allowed(alphabet, original.len()),
    ensures !matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough),
{
    reveal(model::result);
    reveal(crate::table_preparation_specs::root_capacity_allowed);
    let root = crate::table_preparation_specs::clamped_root(requested,
        h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat);
    facts::capacity_positive(root);
    facts::capacity_positive(h::maximum_length(lengths) as nat);
    assert(h::capacity(root) <= original.len());
    if matches!(outcome, crate::huffman::InflateTable::EnoughIsNotEnough) {
        assert(crate::table_preparation_specs::root_capacity_allowed(alphabet,
            h::capacity(root) as nat));
        let witness = choose|witness: model::Refusal| #[trigger] model::refused(alphabet,
            lengths, h::histogram(lengths), work, root,
            h::maximum_length(lengths) as nat, original, codes, witness);
        reveal(model::progress);
        facts::capacity_positive(witness.width);
        assert(h::capacity(root) <= witness.used);
        assert(0 <= witness.used + h::capacity(witness.width));
        assert(witness.used + h::capacity(witness.width) <= original.len());
        let candidate = (witness.used + h::capacity(witness.width)) as nat;
        assert(candidate <= original.len());
        assert(!crate::table_preparation_specs::root_capacity_allowed(alphabet, candidate));
        assert(crate::table_preparation_specs::root_capacity_allowed(alphabet, candidate));
        assert(false);
    }
}

pub(crate) proof fn native_code_parts(code: usize, root: usize, mask: usize)
    requires 1 <= root <= 15, mask as int == h::capacity(root as nat) - 1,
    ensures (code & mask) as int == (code as int) % h::capacity(root as nat),
        (code >> root) as int == (code as int) / h::capacity(root as nat),
{
    facts::usize_shift_capacity(root);
    facts::capacity_is_power(root as nat);
    vstd::bits::lemma_usize_shr_is_div(code, root);
    vstd::bits::lemma_usize_low_bits_mask_is_mod(code, root as nat);
    assert(mask as nat == vstd::bits::low_bits_mask(root as nat));
}

pub(crate) proof fn first_opening(lengths: Seq<u16>, work: Seq<u16>, root: nat,
    regions: Seq<Option<pages::Page>>, key: int, opening: source::Opening)
    requires model::assigned(lengths, work, opening.position, root, regions),
        0 <= key < regions.len(), regions[key] == None,
        opening.position < work.len(), 0 <= opening.symbol < lengths.len(),
        work[opening.position as int] as int == opening.symbol,
        1 <= root < opening.length <= 15, opening.length == lengths[opening.symbol],
        (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root) == key,
    ensures ownership::first_opening(lengths, work, root, key, opening),
{
    assert forall|position: int| 0 <= position < opening.position
        && work[position] < lengths.len()
        && root < lengths[work[position] as int] <= 15 implies
            (#[trigger] h::canonical_prefix(lengths, work[position] as int) as int)
                % h::capacity(root) != key by {
        assert(model::region_for(lengths, root, regions, work[position] as int) != None);
        if (h::canonical_prefix(lengths, work[position] as int) as int) % h::capacity(root) == key {
            assert(model::region_for(lengths, root, regions, work[position] as int) == None);
            assert(false);
        }
    }
}

proof fn unique_region(root: nat, max: nat, used: int,
    regions: Seq<Option<pages::Page>>, first: int, second: int, index: int)
    requires pages::valid(root, max, used, regions),
        0 <= first < regions.len(), 0 <= second < regions.len(),
        match regions[first] {
            Some(page) => page.base <= index < page.base + h::capacity(page.width),
            None => false,
        },
        match regions[second] {
            Some(page) => page.base <= index < page.base + h::capacity(page.width),
            None => false,
        },
    ensures first == second,
{
    if first < second {
        assert(match (regions[first], regions[second]) {
            (Some(left), Some(right)) => pages::disjoint(left, right),
            _ => true,
        });
        assert(false);
    } else if second < first {
        assert(match (regions[second], regions[first]) {
            (Some(left), Some(right)) => pages::disjoint(left, right),
            _ => true,
        });
        assert(false);
    }
}

pub(crate) proof fn selected_target(lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
    root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    position: int, word: u64)
    requires ownership::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        0 <= position < work.len(),
        model::region_for(lengths, root, regions, work[position] as int) != None,
    ensures 0 <= model::lookup_index(root, regions, word) < used,
        model::lookup_page(root, regions, word) != None ==>
            h::capacity(root) <= model::lookup_index(root, regions, word),
        model::target(lengths, work, position, root, regions,
            model::lookup_index(root, regions, word))
            == h::code_prefix_matches(lengths, work[position] as int, word as u32),
        model::target(lengths, work, position, root, regions,
            model::lookup_index(root, regions, word)) ==>
                model::lookup_drop(root, regions, word) < lengths[work[position] as int]
                && model::symbol_bits(lengths, root, work[position] as int)
                    == lengths[work[position] as int] - model::lookup_drop(root, regions, word),
{
    reveal(model::target);
    crate::table_pages_proofs::budget(root, max, used, regions);
    facts::capacity_positive(root);
    facts::depth_capacity(root);
    let key = (word as u32 as int) % h::capacity(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as u32 as int, h::capacity(root));
    let symbol = work[position] as int;
    assert(0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15);
    crate::constructor_pages_proofs::canonical_self(lengths, counts, symbol);
    let whole = h::canonical_prefix(lengths, symbol);
    let source_key = (whole as int) % h::capacity(root);
    let index = model::lookup_index(root, regions, word);
    crate::child_emission_proofs::cached_word_projection(word, root as u32);
    if lengths[symbol] <= root {
        decode::prefix_root_projection(lengths, symbol, word as u32, root);
        match regions[key] {
            Some(page) => {
                facts::capacity_positive(page.width);
                vstd::arithmetic::div_mod::lemma_mod_bound(
                    (word as int) / h::capacity(root), h::capacity(page.width));
                assert(h::capacity(root) <= page.base);
                assert(page.base + h::capacity(page.width) <= used);
                if h::code_prefix_matches(lengths, symbol, word as u32) {
                    crate::constructor_pages_proofs::short_root_free(lengths, counts, work,
                        root, max, used, epoch, regions, openings, symbol, key);
                    assert(false);
                }
            },
            None => {},
        }
    } else {
        let bits = (lengths[symbol] - root) as nat;
        crate::child_emission_proofs::prefix_split(word as u32 as nat,
            whole as nat, root, bits);
        assert(0 <= source_key < regions.len());
        match regions[source_key] {
            Some(source_page) => {
                assert(h::capacity(root) <= source_page.base);
                match regions[key] {
                    Some(page) => {
                        facts::capacity_positive(page.width);
                        vstd::arithmetic::div_mod::lemma_mod_bound(
                            (word as int) / h::capacity(root), h::capacity(page.width));
                        assert(h::capacity(root) <= page.base);
                        assert(page.base + h::capacity(page.width) <= used);
                        if source_key == key {
                            crate::constructor_pages_proofs::active_page(lengths, counts, work,
                                root, max, used, epoch, regions, openings, key, page, symbol);
                            crate::child_emission_proofs::cached_word_projection(
                                word, lengths[symbol] as u32);
                            crate::child_emission_proofs::selected_replica(word as nat,
                                whole as nat, root, bits, page.width, page.base as nat);
                        } else {
                            if model::target(lengths, work, position, root, regions, index) {
                                unique_region(root, max, used, regions, source_key, key, index);
                                assert(false);
                            }
                            assert(!h::code_prefix_matches(lengths, symbol, word as u32));
                        }
                    },
                    None => {
                        assert(index < source_page.base);
                        assert(!h::code_prefix_matches(lengths, symbol, word as u32));
                    },
                }
            },
            None => { assert(false); },
        }
    }
}

proof fn leaf_not_link(alphabet: h::Alphabet, symbol: nat, bits: nat, code: Code)
    requires emission::leaf(alphabet, symbol, bits, code),
    ensures !crate::linked_table_specs::is_link(code),
{
    if crate::linked_table_specs::is_link(code) {
        let op = code.op;
        assert(op & 64 == 0) by (bit_vector) requires op < 16;
        match alphabet {
            h::Alphabet::CodeLengths => {},
            h::Alphabet::LiteralLengths => {},
            h::Alphabet::Distances => {},
        }
        assert(false);
    }
}

pub(crate) proof fn written_lookup_leaf(alphabet: h::Alphabet, lengths: Seq<u16>,
    counts: Seq<u16>, work: Seq<u16>, processed: nat, root: nat, max: nat,
    used: int, epoch: nat, regions: Seq<Option<pages::Page>>,
    openings: Seq<Option<source::Opening>>, word: u64, code: Code)
    requires ownership::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        model::assigned(lengths, work, processed, root, regions),
        model::written(alphabet, lengths, work, processed, root, regions,
            model::lookup_index(root, regions, word), code),
    ensures crate::linked_table_specs::leaf(alphabet, lengths, code, word as u32,
            model::lookup_drop(root, regions, word)),
        !crate::linked_table_specs::is_link(code),
{
    let index = model::lookup_index(root, regions, word);
    let position = choose|position: int| 0 <= position < processed
        && model::target(lengths, work, position, root, regions, index)
        && emission::leaf(alphabet, work[position] as nat,
            model::symbol_bits(lengths, root, work[position] as int), code);
    assert(model::region_for(lengths, root, regions, work[position] as int) != None);
    selected_target(lengths, counts, work, root, max, used, epoch, regions, openings, position, word);
    let symbol = work[position] as int;
    assert forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word as u32)
        implies other == symbol by {
        decode::matching_symbol_unique(lengths, counts, symbol, other, word as u32);
    }
    leaf_not_link(alphabet, symbol as nat,
        model::symbol_bits(lengths, root, symbol), code);
}

pub(crate) proof fn lookup_written(alphabet: h::Alphabet, lengths: Seq<u16>,
    counts: Seq<u16>, work: Seq<u16>, root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    original: Seq<Code>, codes: Seq<Code>, word: u64)
    requires ownership::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::bucket_ordered(lengths, counts, work), h::slots(counts, 15) == 0,
        model::progress(alphabet, lengths, work, h::before(counts, 16), root, used,
            regions, original, codes),
    ensures 0 <= model::lookup_index(root, regions, word) < used <= codes.len(),
        model::written(alphabet, lengths, work, h::before(counts, 16), root, regions,
            model::lookup_index(root, regions, word), codes[model::lookup_index(root, regions, word)]),
{
    reveal(model::progress);
    decode::matching_symbol_exists(lengths, counts, work, word as u32);
    let symbol = choose|symbol: int| #[trigger] h::code_prefix_matches(lengths, symbol, word as u32);
    facts::sorted_symbol_position(lengths, counts, work, symbol);
    let position = h::before(counts, lengths[symbol] as nat)
        + h::occurrences(lengths.take(symbol), lengths[symbol]);
    assert(model::region_for(lengths, root, regions, work[position as int] as int) != None);
    selected_target(lengths, counts, work, root, max, used, epoch,
        regions, openings, position as int, word);
    let index = model::lookup_index(root, regions, word);
    facts::capacity_positive(root);
    let key = (word as u32 as int) % h::capacity(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as u32 as int, h::capacity(root));
    assert(model::seen(lengths, work, h::before(counts, 16), root, regions, index));
    match regions[key] {
        Some(_) => { assert(index >= regions.len()); },
        None => { assert(index == key && regions[index] == None); },
    }
    assert(!(index < regions.len() && regions[index] != None));
}

pub(crate) proof fn decoded_word(alphabet: h::Alphabet, lengths: Seq<u16>,
    counts: Seq<u16>, work: Seq<u16>, root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    original: Seq<Code>, codes: Seq<Code>, word: u64)
    requires ownership::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::bucket_ordered(lengths, counts, work), h::slots(counts, 15) == 0,
        model::progress(alphabet, lengths, work, h::before(counts, 16), root, used,
            regions, original, codes),
    ensures {
        let first = codes[(word as u32 as int) % h::capacity(root)];
        if crate::linked_table_specs::is_link(first) {
            crate::linked_table_specs::region(root, used as nat, first)
                && crate::linked_table_specs::leaf(alphabet, lengths,
                    codes[h::subtable_index(first, word as nat)], word as u32, root)
        } else {
            crate::linked_table_specs::leaf(alphabet, lengths, first, word as u32, 0)
        }
    },
{
    reveal(model::progress);
    lookup_written(alphabet, lengths, counts, work, root, max, used, epoch,
        regions, openings, original, codes, word);
    let index = model::lookup_index(root, regions, word);
    written_lookup_leaf(alphabet, lengths, counts, work, h::before(counts, 16),
        root, max, used, epoch, regions, openings, word, codes[index]);
    facts::capacity_positive(root);
    let key = (word as u32 as int) % h::capacity(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as u32 as int, h::capacity(root));
    match regions[key] {
        Some(page) => {
            assert(h::subtable_link(codes[key], root, page.base as nat, page.width,
                (page.base + h::capacity(page.width)) as nat));
            assert(page.base + h::capacity(page.width) <= used);
            assert(crate::linked_table_specs::region(root, used as nat, codes[key]));
            assert(h::subtable_index(codes[key], word as nat) == index);
        },
        None => { assert(index == key); },
    }
}

pub(crate) proof fn complete(alphabet: h::Alphabet, lengths: Seq<u16>,
    counts: Seq<u16>, work: Seq<u16>, root: nat, max: nat, used: int, epoch: nat,
    regions: Seq<Option<pages::Page>>, openings: Seq<Option<source::Opening>>,
    original: Seq<Code>, codes: Seq<Code>)
    requires ownership::ownership(lengths, counts, work, root, max, used, epoch, regions, openings),
        h::valid_histogram(lengths, counts), h::valid_prefix(counts, 15),
        h::bucket_ordered(lengths, counts, work), h::slots(counts, 15) == 0,
        model::progress(alphabet, lengths, work, h::before(counts, 16), root, used,
            regions, original, codes),
    ensures crate::linked_table_specs::table(alphabet, lengths, root, used as nat, codes),
        forall|index: int| used <= index < codes.len() ==> #[trigger] codes[index] == original[index],
{
    reveal(model::progress);
    reveal(crate::linked_table_specs::table);
    facts::capacity_positive(root);
    facts::depth_capacity(root);
    tail_frame(alphabet, lengths, work, h::before(counts, 16),
        root, max, used, regions, original, codes);
    assert forall|index: int| 0 <= index < h::capacity(root)
        && crate::linked_table_specs::is_link(#[trigger] codes[index]) implies
        crate::linked_table_specs::region(root, used as nat, codes[index]) by {
        vstd::arithmetic::div_mod::lemma_small_mod(index as nat, h::capacity(root) as nat);
        decoded_word(alphabet, lengths, counts, work, root, max, used, epoch,
            regions, openings, original, codes, index as u64);
    }
    assert forall|word: u64| {
        let first = #[trigger] codes[(word as u32 as int) % h::capacity(root)];
        if crate::linked_table_specs::is_link(first) {
            crate::linked_table_specs::leaf(alphabet, lengths,
                codes[h::subtable_index(first, word as nat)], word as u32, root)
        } else {
            crate::linked_table_specs::leaf(alphabet, lengths, first, word as u32, 0)
        }
    } by {
        decoded_word(alphabet, lengths, counts, work, root, max, used, epoch,
            regions, openings, original, codes, word);
    }
}

pub(crate) proof fn initial(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, root: nat, original: Seq<Code>)
    requires 1 <= root <= 15, h::capacity(root) <= original.len(),
    ensures model::progress(alphabet, lengths, work, 0, root, h::capacity(root),
        Seq::new(h::capacity(root) as nat, |key: int| None), original, original),
{
    reveal(model::progress);
    crate::huffman_proofs::capacity_positive(root);
}

pub(crate) proof fn emission_target(lengths: Seq<u16>, work: Seq<u16>, position: int,
    root: nat, regions: Seq<Option<pages::Page>>,
    base: nat, width: nat, bits: nat, prefix: nat, index: int)
    requires 0 <= position < work.len(),
        ownership::emission_region(lengths, root, regions, work[position] as int,
            base, width, bits, prefix),
    ensures model::region_for(lengths, root, regions, work[position] as int)
            == Some(pages::Page { base: base as int, width }),
        model::symbol_bits(lengths, root, work[position] as int) == bits,
        model::target(lengths, work, position, root, regions, index)
            == h::table_replica(base, prefix, bits, width, index),
{
    reveal(model::target);
}

pub(crate) proof fn emitted(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, used: int,
    regions: Seq<Option<pages::Page>>, original: Seq<Code>,
    before: Seq<Code>, after: Seq<Code>, entry: Code,
    base: nat, width: nat, bits: nat, prefix: nat)
    requires model::progress(alphabet, lengths, work, processed, root, used,
            regions, original, before),
        processed < work.len(),
        ownership::emission_region(lengths, root, regions, work[processed as int] as int,
            base, width, bits, prefix),
        emission::result(alphabet, work[processed as int] as nat, bits, base, width,
            prefix, before, after, entry, h::capacity(width) as nat),
        forall|key: int| 0 <= key < regions.len() && regions[key] != None
            ==> #[trigger] after[key] == before[key],
    ensures model::progress(alphabet, lengths, work, processed + 1, root, used,
        regions, original, after),
{
    reveal(model::progress);
    reveal(emission::result);
    emission_target(lengths, work, processed as int, root, regions,
        base, width, bits, prefix, 0);
    assert(model::assigned(lengths, work, processed + 1, root, regions));
    assert forall|index: int| 0 <= index < after.len() implies
        if index < regions.len() && regions[index] != None {
            match regions[index] {
                Some(page) => h::subtable_link(after[index], root,
                    page.base as nat, page.width,
                    (page.base + h::capacity(page.width)) as nat),
                None => false,
            }
        } else if model::seen(lengths, work, processed + 1, root, regions, index) {
            model::written(alphabet, lengths, work, processed + 1, root, regions,
                index, after[index])
        } else { after[index] == original[index] } by {
        if !(index < regions.len() && regions[index] != None) {
            emission_target(lengths, work, processed as int, root, regions,
                base, width, bits, prefix, index);
            if model::target(lengths, work, processed as int, root, regions, index) {
                assert(model::written(alphabet, lengths, work, processed + 1,
                    root, regions, index, after[index]));
            } else if model::seen(lengths, work, processed, root, regions, index) {
                let position = choose|position: int| 0 <= position < processed
                    && model::target(lengths, work, position, root, regions, index)
                    && emission::leaf(alphabet, work[position] as nat,
                        model::symbol_bits(lengths, root, work[position] as int), before[index]);
                assert(model::written(alphabet, lengths, work, processed + 1,
                    root, regions, index, after[index]));
            } else if model::seen(lengths, work, processed + 1, root, regions, index) {
                let position = choose|position: int| 0 <= position < processed + 1
                    && model::target(lengths, work, position, root, regions, index);
                assert(position < processed);
                assert(false);
            }
        }
    }
}

pub(crate) proof fn past_targets_after_allocation(lengths: Seq<u16>, work: Seq<u16>,
    processed: nat, root: nat, regions: Seq<Option<pages::Page>>,
    key: int, page: pages::Page)
    requires model::assigned(lengths, work, processed, root, regions),
        0 <= key < regions.len(), regions[key] == None,
    ensures model::assigned(lengths, work, processed, root, regions.update(key, Some(page))),
        forall|position: int, index: int| 0 <= position < processed ==>
            #[trigger] model::target(lengths, work, position, root,
                regions.update(key, Some(page)), index)
                == model::target(lengths, work, position, root, regions, index),
{
    reveal(model::target);
    let updated = regions.update(key, Some(page));
    assert forall|position: int| 0 <= position < processed implies
        #[trigger] model::region_for(lengths, root, updated, work[position] as int)
            == model::region_for(lengths, root, regions, work[position] as int) by {
        let symbol = work[position] as int;
        assert(model::region_for(lengths, root, regions, symbol) != None);
        assert(0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15);
        if lengths[symbol] > root {
            let old_key = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
            assert(old_key != key);
        }
    }
}

pub(crate) proof fn allocated(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, used: int,
    regions: Seq<Option<pages::Page>>, original: Seq<Code>,
    before: Seq<Code>, after: Seq<Code>, key: int, width: nat)
    requires model::progress(alphabet, lengths, work, processed, root, used,
            regions, original, before),
        0 <= key < regions.len(), regions[key] == None,
        used + h::capacity(width) <= before.len(),
        h::subtable_link_result(before, after, key as nat, root, used as nat,
            used as nat, width, (used + h::capacity(width)) as nat, true),
    ensures model::progress(alphabet, lengths, work, processed, root,
        used + h::capacity(width), regions.update(key, Some(pages::Page { base: used, width })),
        original, after),
{
    reveal(model::progress);
    crate::huffman_proofs::capacity_positive(root);
    crate::huffman_proofs::capacity_positive(width);
    let updated = regions.update(key, Some(pages::Page { base: used, width }));
    past_targets_after_allocation(lengths, work, processed, root, regions,
        key, pages::Page { base: used, width });
    assert forall|index: int| 0 <= index < after.len() implies
        if index < updated.len() && updated[index] != None {
            match updated[index] {
                Some(page) => h::subtable_link(after[index], root,
                    page.base as nat, page.width,
                    (page.base + h::capacity(page.width)) as nat),
                None => false,
            }
        } else if model::seen(lengths, work, processed, root, updated, index) {
            model::written(alphabet, lengths, work, processed, root, updated, index, after[index])
        } else { after[index] == original[index] } by {
        if index != key {
            assert(after[index] == before[index]);
            if !(index < updated.len() && updated[index] != None) {
                if model::seen(lengths, work, processed, root, updated, index) {
                    let position = choose|position: int| 0 <= position < processed
                        && model::target(lengths, work, position, root, updated, index);
                    assert(model::seen(lengths, work, processed, root, regions, index));
                    assert(model::written(alphabet, lengths, work, processed,
                        root, regions, index, before[index]));
                    let written = choose|position: int| 0 <= position < processed
                        && model::target(lengths, work, position, root, regions, index)
                        && emission::leaf(alphabet, work[position] as nat,
                            model::symbol_bits(lengths, root, work[position] as int), before[index]);
                    assert(model::target(lengths, work, written, root, updated, index));
                    assert(model::written(alphabet, lengths, work, processed,
                        root, updated, index, after[index]));
                } else if model::seen(lengths, work, processed, root, regions, index) {
                    let position = choose|position: int| 0 <= position < processed
                        && model::target(lengths, work, position, root, regions, index);
                    assert(model::target(lengths, work, position, root, updated, index));
                    assert(model::seen(lengths, work, processed, root, updated, index));
                    assert(false);
                }
            }
        }
    }
}

pub(crate) proof fn target_bounds(lengths: Seq<u16>, work: Seq<u16>, position: int,
    root: nat, max: nat, used: int, regions: Seq<Option<pages::Page>>, index: int)
    requires pages::valid(root, max, used, regions),
        model::target(lengths, work, position, root, regions, index),
    ensures 0 <= index < used,
{
    reveal(model::target);
    crate::table_pages_proofs::budget(root, max, used, regions);
    crate::huffman_proofs::capacity_positive(root);
    assert(0 <= position < work.len());
    let symbol = work[position] as int;
    assert(0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15);
    if lengths[symbol] > root {
        let key = (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root);
        assert(0 <= key < regions.len());
        match regions[key] {
            Some(page) => {
                assert(model::region_for(lengths, root, regions, symbol) == Some(page));
                assert(h::capacity(root) <= page.base);
                assert(page.base + h::capacity(page.width) <= used);
                assert(page.base <= index < page.base + h::capacity(page.width));
            },
            None => { assert(false); },
        }
    } else {
        assert(0 <= index < h::capacity(root));
    }
}

pub(crate) proof fn tail_frame(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, max: nat, used: int,
    regions: Seq<Option<pages::Page>>, original: Seq<Code>, codes: Seq<Code>)
    requires model::progress(alphabet, lengths, work, processed, root, used,
            regions, original, codes),
        pages::valid(root, max, used, regions),
    ensures forall|index: int| used <= index < codes.len() ==>
        #[trigger] codes[index] == original[index],
{
    reveal(model::progress);
    assert forall|index: int| used <= index < codes.len() implies
        #[trigger] codes[index] == original[index] by {
        if model::seen(lengths, work, processed, root, regions, index) {
            let position = choose|position: int| 0 <= position < processed
                && model::target(lengths, work, position, root, regions, index);
            target_bounds(lengths, work, position, root, max, used, regions, index);
        }
    }
}

pub(crate) proof fn root_target(lengths: Seq<u16>, work: Seq<u16>, processed: nat,
    root: nat, regions: Seq<Option<pages::Page>>, position: int, index: int)
    requires 1 <= root <= 15, model::assigned(lengths, work, processed, root, regions),
        forall|key: int| 0 <= key < regions.len() ==> #[trigger] regions[key] == None,
        0 <= position < processed, 0 <= index < h::capacity(root),
    ensures 0 <= work[position] < lengths.len(), 1 <= lengths[work[position] as int] <= root,
        model::target(lengths, work, position, root, regions, index)
            == h::code_prefix_matches(lengths, work[position] as int, index as u32),
{
    reveal(model::target);
    crate::huffman_proofs::depth_capacity(root);
    assert(model::region_for(lengths, root, regions, work[position] as int) != None);
}

pub(crate) proof fn root_corollary(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, used: int,
    regions: Seq<Option<pages::Page>>, original: Seq<Code>, codes: Seq<Code>)
    requires model::progress(alphabet, lengths, work, processed, root, used,
            regions, original, codes),
        pages::valid(root, root, used, regions),
    ensures crate::root_table_specs::progress(alphabet, lengths, work, processed,
        root, original, codes),
{
    reveal(model::progress);
    reveal(crate::root_table_specs::progress);
    crate::table_pages_proofs::budget(root, root, used, regions);
    assert forall|key: int| 0 <= key < regions.len() implies
        #[trigger] regions[key] == None by {
        match regions[key] {
            Some(page) => { assert(1 <= page.width && page.width + root <= root); },
            None => {},
        }
    }
    tail_frame(alphabet, lengths, work, processed, root, root, used, regions, original, codes);
    assert forall|index: int| 0 <= index < codes.len() implies
        if index < h::capacity(root)
            && crate::root_table_specs::seen(lengths, work, processed, index as u32) {
            crate::root_table_specs::written(alphabet, lengths, work, processed,
                index as u32, codes[index])
        } else { codes[index] == original[index] } by {
        if index < h::capacity(root) {
            if crate::root_table_specs::seen(lengths, work, processed, index as u32) {
                let position = choose|position: int| 0 <= position < processed
                    && position < work.len()
                    && h::code_prefix_matches(lengths, work[position] as int, index as u32);
                root_target(lengths, work, processed, root, regions, position, index);
                assert(model::seen(lengths, work, processed, root, regions, index));
                assert(model::written(alphabet, lengths, work, processed,
                    root, regions, index, codes[index]));
                let written = choose|position: int| 0 <= position < processed
                    && model::target(lengths, work, position, root, regions, index)
                    && emission::leaf(alphabet, work[position] as nat,
                        model::symbol_bits(lengths, root, work[position] as int), codes[index]);
                root_target(lengths, work, processed, root, regions, written, index);
                assert(crate::root_table_specs::written(alphabet, lengths, work, processed,
                    index as u32, codes[index]));
            } else if model::seen(lengths, work, processed, root, regions, index) {
                let position = choose|position: int| 0 <= position < processed
                    && model::target(lengths, work, position, root, regions, index);
                root_target(lengths, work, processed, root, regions, position, index);
                assert(crate::root_table_specs::seen(lengths, work, processed, index as u32));
                assert(false);
            }
        }
    }
}

proof fn fixture_reversal(cursor: u32, code: u32)
    requires (cursor == 0 && code == 0)
        || (cursor == 0x4000_0000 && code == 2)
        || (cursor == 0x8000_0000 && code == 1)
        || (cursor == 0xa000_0000 && code == 5)
        || (cursor == 0xc000_0000 && code == 3)
        || (cursor == 0xe000_0000 && code == 7),
    ensures h::reversed_word(cursor) == code,
{
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(cursor, bit) == h::word_bit(code, (31 - bit) as u32) by {
        assert((cursor >> bit) & 1 == (code >> ((31 - bit) as u32)) & 1) by (bit_vector)
            requires bit < 32,
                (cursor == 0 && code == 0)
                    || (cursor == 0x4000_0000 && code == 2)
                    || (cursor == 0x8000_0000 && code == 1)
                    || (cursor == 0xa000_0000 && code == 5)
                    || (cursor == 0xc000_0000 && code == 3)
                    || (cursor == 0xe000_0000 && code == 7);
    }
    crate::huffman_proofs::reversal_matches_model(cursor, code);
}

pub(crate) proof fn independent_complete_progress()
    ensures model::progress(h::Alphabet::LiteralLengths, seq![2u16, 2, 3, 3, 3, 3],
        seq![0u16, 1, 2, 3, 4, 5], 6, 2, 8,
        seq![None, Some(pages::Page { base: 4, width: 1 }),
            None, Some(pages::Page { base: 6, width: 1 })],
        Seq::new(12, |index: int| Code { op: 255, bits: 15, val: u16::MAX }),
        seq![Code { op: 0, bits: 2, val: 0 }, Code { op: 1, bits: 2, val: 4 },
            Code { op: 0, bits: 2, val: 1 }, Code { op: 1, bits: 2, val: 6 },
            Code { op: 0, bits: 1, val: 2 }, Code { op: 0, bits: 1, val: 3 },
            Code { op: 0, bits: 1, val: 4 }, Code { op: 0, bits: 1, val: 5 }]
            + Seq::new(4, |index: int| Code { op: 255, bits: 15, val: u16::MAX })),
{
    reveal(model::progress);
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let work = seq![0u16, 1, 2, 3, 4, 5];
    let regions = seq![None, Some(pages::Page { base: 4, width: 1 }),
        None, Some(pages::Page { base: 6, width: 1 })];
    let original = Seq::new(12, |index: int| Code { op: 255, bits: 15, val: u16::MAX });
    let codes = seq![
        Code { op: 0, bits: 2, val: 0 }, Code { op: 1, bits: 2, val: 4 },
        Code { op: 0, bits: 2, val: 1 }, Code { op: 1, bits: 2, val: 6 },
        Code { op: 0, bits: 1, val: 2 }, Code { op: 0, bits: 1, val: 3 },
        Code { op: 0, bits: 1, val: 4 }, Code { op: 0, bits: 1, val: 5 },
    ] + Seq::new(4, |index: int| Code { op: 255, bits: 15, val: u16::MAX });
    crate::constructor_pages_proofs::independent_two_pages();
    assert(h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 0) == 0
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 1) == 1
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 2) == 4
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 3) == 5
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 4) == 6
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 5) == 7
        && h::capacity(1) == 2 && h::capacity(2) == 4
        && h::capacity(29) == 536870912 && h::capacity(30) == 1073741824) by (compute);
    fixture_reversal(0, 0);
    fixture_reversal(0x4000_0000, 2);
    fixture_reversal(0x8000_0000, 1);
    fixture_reversal(0xa000_0000, 5);
    fixture_reversal(0xc000_0000, 3);
    fixture_reversal(0xe000_0000, 7);
    facts::canonical_prefix_at_cursor(lengths, 0, 0, 0);
    facts::canonical_prefix_at_cursor(lengths, 1, 0x4000_0000, 2);
    facts::canonical_prefix_at_cursor(lengths, 2, 0x8000_0000, 1);
    facts::canonical_prefix_at_cursor(lengths, 3, 0xa000_0000, 5);
    facts::canonical_prefix_at_cursor(lengths, 4, 0xc000_0000, 3);
    facts::canonical_prefix_at_cursor(lengths, 5, 0xe000_0000, 7);
    emission_target(lengths, work, 0, 2, regions, 0, 2, 2, 0, 0);
    emission_target(lengths, work, 1, 2, regions, 0, 2, 2, 2, 2);
    emission_target(lengths, work, 2, 2, regions, 4, 1, 1, 0, 4);
    emission_target(lengths, work, 3, 2, regions, 4, 1, 1, 1, 5);
    emission_target(lengths, work, 4, 2, regions, 6, 1, 1, 0, 6);
    emission_target(lengths, work, 5, 2, regions, 6, 1, 1, 1, 7);
    assert forall|position: int| 0 <= position < 6 implies
        #[trigger] model::region_for(lengths, 2, regions, work[position] as int) != None by {
        if position == 0 {} else if position == 1 {} else if position == 2 {}
        else if position == 3 {} else if position == 4 {} else { assert(position == 5); }
    }
    assert(model::assigned(lengths, work, 6, 2, regions));
    assert forall|index: int| 0 <= index < codes.len() implies
        if index < regions.len() && regions[index] != None {
            match regions[index] {
                Some(page) => h::subtable_link(codes[index], 2,
                    page.base as nat, page.width,
                    (page.base + h::capacity(page.width)) as nat),
                None => false,
            }
        } else if model::seen(lengths, work, 6, 2, regions, index) {
            model::written(h::Alphabet::LiteralLengths, lengths, work, 6,
                2, regions, index, codes[index])
        } else { codes[index] == original[index] } by {
        if index == 0 || index == 2 {
            let position = if index == 0 { 0int } else { 1int };
            if index == 0 {
                assert(model::target(lengths, work, 0, 2, regions, 0));
            } else {
                assert(index == 2);
                assert(model::target(lengths, work, 1, 2, regions, 2));
            }
            assert(model::target(lengths, work, position, 2, regions, index));
            assert(emission::leaf(h::Alphabet::LiteralLengths, position as nat, 2, codes[index]));
            assert(model::written(h::Alphabet::LiteralLengths, lengths, work, 6,
                2, regions, index, codes[index]));
        } else if 4 <= index < 8 {
            let position = index - 2;
            if index == 4 {
                assert(model::target(lengths, work, 2, 2, regions, 4));
            } else if index == 5 {
                assert(model::target(lengths, work, 3, 2, regions, 5));
            } else if index == 6 {
                assert(model::target(lengths, work, 4, 2, regions, 6));
            } else {
                assert(index == 7);
                assert(model::target(lengths, work, 5, 2, regions, 7));
            }
            assert(model::target(lengths, work, position, 2, regions, index));
            assert(emission::leaf(h::Alphabet::LiteralLengths, position as nat, 1, codes[index]));
            assert(model::written(h::Alphabet::LiteralLengths, lengths, work, 6,
                2, regions, index, codes[index]));
        } else if index >= 8 && model::seen(lengths, work, 6, 2, regions, index) {
            let position = choose|position: int| 0 <= position < 6
                && model::target(lengths, work, position, 2, regions, index);
            target_bounds(lengths, work, position, 2, 3, 8, regions, index);
        }
    }
}

pub(crate) proof fn independent_complete_table()
    ensures crate::linked_table_specs::table(h::Alphabet::LiteralLengths,
        seq![2u16, 2, 3, 3, 3, 3], 2, 8,
        seq![Code { op: 0, bits: 2, val: 0 }, Code { op: 1, bits: 2, val: 4 },
            Code { op: 0, bits: 2, val: 1 }, Code { op: 1, bits: 2, val: 6 },
            Code { op: 0, bits: 1, val: 2 }, Code { op: 0, bits: 1, val: 3 },
            Code { op: 0, bits: 1, val: 4 }, Code { op: 0, bits: 1, val: 5 }]
            + Seq::new(4, |index: int| Code { op: 255, bits: 15, val: u16::MAX })),
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let counts = crate::subtable_coverage_proofs::fixture_counts();
    let work = seq![0u16, 1, 2, 3, 4, 5];
    let regions = seq![None, Some(pages::Page { base: 4, width: 1 }),
        None, Some(pages::Page { base: 6, width: 1 })];
    let openings = seq![None, Some(source::Opening {
            symbol: 2, position: 2, length: 3,
            remaining: crate::page_source_proofs::fixture_remaining(),
        }), None, Some(source::Opening {
            symbol: 4, position: 4, length: 3,
            remaining: Seq::new(16, |level: int| if level == 3 { 2u16 } else { 0u16 }),
        })];
    let original = Seq::new(12, |index: int| Code { op: 255, bits: 15, val: u16::MAX });
    let codes = seq![
        Code { op: 0, bits: 2, val: 0 }, Code { op: 1, bits: 2, val: 4 },
        Code { op: 0, bits: 2, val: 1 }, Code { op: 1, bits: 2, val: 6 },
        Code { op: 0, bits: 1, val: 2 }, Code { op: 0, bits: 1, val: 3 },
        Code { op: 0, bits: 1, val: 4 }, Code { op: 0, bits: 1, val: 5 },
    ] + Seq::new(4, |index: int| Code { op: 255, bits: 15, val: u16::MAX });
    crate::constructor_pages_proofs::independent_two_pages();
    crate::subtable_coverage_proofs::independent_root_coverage();
    assert(h::before(crate::subtable_coverage_proofs::fixture_counts(), 16) == 6
        && h::slots(crate::subtable_coverage_proofs::fixture_counts(), 15) == 0) by (compute);
    assert(h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 2, 0)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 2, 1)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 0)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 1)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 2)
        && h::bucket_entry(seq![2u16, 2, 3, 3, 3, 3],
            crate::subtable_coverage_proofs::fixture_counts(), seq![0u16, 1, 2, 3, 4, 5], 3, 3))
        by (compute);
    assert(h::bucket_ordered(lengths, counts, work));
    independent_complete_progress();
    complete(h::Alphabet::LiteralLengths, lengths, counts, work, 2, 3, 8, 5,
        regions, openings, original, codes);
}

}
