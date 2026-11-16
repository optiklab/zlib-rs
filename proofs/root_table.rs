use crate::huffman::{InflateTable, TablePreparation};
use crate::huffman_decode as decode;
use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::root_table_specs as model;
use crate::table_emission_specs as emission;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) proof fn initial(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, root: nat, original: Seq<Code>)
    ensures model::progress(alphabet, lengths, work, 0, root, original, original),
{
    reveal(model::progress);
}

pub(crate) proof fn word_entry(alphabet: h::Alphabet, lengths: Seq<u16>,
    root: nat, codes: Seq<Code>, word: u32)
    requires model::table(alphabet, lengths, root, codes),
    ensures model::entry(alphabet, lengths,
        codes[(word as int) % h::capacity(root)], word),
{
    reveal(model::table);
    facts::capacity_positive(root);
    facts::depth_capacity(root);
    let index = (word as int) % h::capacity(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as int, h::capacity(root));
    assert(index as u32 as int == index);
    assert forall|symbol: int|
        #[trigger] h::code_prefix_matches(lengths, symbol, word)
            <==> h::code_prefix_matches(lengths, symbol, index as u32) by {
        if 0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15 {
            decode::maximum_symbol_bound(lengths, symbol);
            decode::prefix_root_projection(lengths, symbol, word, root);
        }
    }
    assert(model::entry(alphabet, lengths, codes[index], index as u32));
    if exists|symbol: int|
        #[trigger] h::code_prefix_matches(lengths, symbol, index as u32) {
        let selected = choose|symbol: int|
            #[trigger] h::code_prefix_matches(lengths, symbol, index as u32)
            && emission::leaf(alphabet, symbol as nat, lengths[symbol] as nat, codes[index])
            && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, index as u32)
                ==> other == symbol);
        assert(h::code_prefix_matches(lengths, selected, word));
        assert forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word)
            implies other == selected by {
        }
    } else {
        assert(codes[index] == model::invalid_hole());
        assert forall|symbol: int| !h::code_prefix_matches(lengths, symbol, word) by {
        }
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn emitted(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, processed: nat, root: nat, original: Seq<Code>,
    before: Seq<Code>, after: Seq<Code>, code: Code)
    requires processed < work.len(),
        0 <= work[processed as int] < lengths.len(),
        1 <= lengths[work[processed as int] as int] <= root <= 15,
        model::progress(alphabet, lengths, work, processed, root, original, before),
        emission::result(alphabet, work[processed as int] as nat,
            lengths[work[processed as int] as int] as nat, 0, root,
            h::canonical_prefix(lengths, work[processed as int] as int) as nat,
            before, after, code, h::capacity(root) as nat),
    ensures model::progress(alphabet, lengths, work, processed + 1, root, original, after),
{
    reveal(model::progress);
    reveal(emission::result);
    let symbol = work[processed as int] as int;
    facts::depth_capacity(root);
    assert forall|index: int| 0 <= index < after.len() implies
        if index < h::capacity(root)
            && model::seen(lengths, work, processed + 1, index as u32) {
            model::written(alphabet, lengths, work, processed + 1, index as u32, after[index])
        } else { after[index] == original[index] } by {
        if index < h::capacity(root) {
            assert(index as u32 as int == index);
            assert(h::table_replica(0, h::canonical_prefix(lengths, symbol) as nat,
                lengths[symbol] as nat, root, index)
                == h::code_prefix_matches(lengths, symbol, index as u32));
            if h::code_prefix_matches(lengths, symbol, index as u32) {
                assert(model::seen(lengths, work, processed + 1, index as u32));
                assert(model::written(alphabet, lengths, work, processed + 1,
                    index as u32, after[index]));
            } else if model::seen(lengths, work, processed, index as u32) {
                assert(model::written(alphabet, lengths, work, processed,
                    index as u32, before[index]));
                let position = choose|position: int| 0 <= position < processed
                    && position < work.len()
                    && h::code_prefix_matches(lengths, work[position] as int, index as u32)
                    && emission::leaf(alphabet, work[position] as nat,
                        lengths[work[position] as int] as nat, before[index]);
                assert(model::seen(lengths, work, processed + 1, index as u32));
                assert(model::written(alphabet, lengths, work, processed + 1,
                    index as u32, after[index]));
            } else if model::seen(lengths, work, processed + 1, index as u32) {
                let position = choose|position: int| 0 <= position < processed + 1
                    && position < work.len()
                    && h::code_prefix_matches(lengths, work[position] as int, index as u32);
                assert(position < processed);
                assert(model::seen(lengths, work, processed, index as u32));
            }
        }
    }
}

pub(crate) proof fn complete(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, root: nat, original: Seq<Code>, codes: Seq<Code>)
    requires h::valid_histogram(lengths, h::histogram(lengths)),
        h::valid_prefix(h::histogram(lengths), 15),
        h::bucket_ordered(lengths, h::histogram(lengths), work),
        h::slots(h::histogram(lengths), 15) == 0,
        root == h::maximum_length(lengths), 1 <= root <= 15,
        h::capacity(root) <= codes.len(),
        model::progress(alphabet, lengths, work,
            h::before(h::histogram(lengths), 16), root, original, codes),
    ensures model::table(alphabet, lengths, root, codes),
        codes.len() == original.len(),
        forall|index: int| h::capacity(root) <= index < codes.len() ==>
            #[trigger] codes[index] == original[index],
{
    reveal(model::progress);
    reveal(model::table);
    let counts = h::histogram(lengths);
    let total = h::before(counts, 16);
    facts::depth_capacity(root);
    facts::capacity_positive(root);
    assert forall|index: int| h::capacity(root) <= index < codes.len() implies
        #[trigger] codes[index] == original[index] by {
        assert(0 <= index < codes.len());
    }
    assert forall|index: int| 0 <= index < h::capacity(root) implies
        #[trigger] model::entry(alphabet, lengths, codes[index], index as u32) by {
        assert(index as u32 as int == index);
        decode::matching_symbol_exists(lengths, counts, work, index as u32);
        let selected = choose|symbol: int|
            #[trigger] h::code_prefix_matches(lengths, symbol, index as u32);
        facts::sorted_symbol_position(lengths, counts, work, selected);
        let position = h::before(counts, lengths[selected] as nat)
            + h::occurrences(lengths.take(selected), lengths[selected]);
        assert(work[position as int] == selected);
        assert(model::seen(lengths, work, total, index as u32));
        assert(model::written(alphabet, lengths, work, total, index as u32, codes[index]));
        let written = choose|position: int| 0 <= position < total && position < work.len()
            && h::code_prefix_matches(lengths, work[position] as int, index as u32)
            && emission::leaf(alphabet, work[position] as nat,
                lengths[work[position] as int] as nat, codes[index]);
        let symbol = work[written] as int;
        assert forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, index as u32)
            implies other == symbol by {
            decode::matching_symbol_unique(lengths, counts, symbol, other, index as u32);
        }
        assert(model::entry(alphabet, lengths, codes[index], index as u32));
    }
}

pub(crate) proof fn incomplete_one_bit_shape(lengths: Seq<u16>, counts: Seq<u16>)
    requires h::valid_histogram(lengths, counts),
        forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= 15,
        h::maximum_length(lengths) == 1, h::valid_prefix(counts, 15),
        h::slots(counts, 15) != 0,
    ensures counts[1] == 1, h::before(counts, 16) == 1,
        h::normalized_cursor(counts, 1, 0) == 0,
{
    facts::length_population_bounds(lengths);
    assert forall|level: int| 1 < level <= 15 implies counts[level] == 0 by {
        assert(h::occurrences(lengths, level as u16) == 0);
    }
    facts::slots_empty_tail(counts, 1, 15);
    assert(h::slots(counts, 1) >= 0);
    assert(h::slots(counts, 0) == 1);
    assert(h::slots(counts, 1) == 2 - counts[1]);
    assert(counts[1] == h::occurrences(lengths, 1));
    assert(counts[1] > 0);
    if counts[1] == 2 {
        assert(h::slots(counts, 1) == 0);
        assert(h::slots(counts, 15) == 0) by (nonlinear_arith)
            requires h::slots(counts, 15) == h::capacity(14) * h::slots(counts, 1),
                h::slots(counts, 1) == 0;
    }
    assert(counts[1] == 1);
    facts::before_empty_range(counts, 2, 16);
    assert(h::before(counts, 1) == 0);
    assert(h::before(counts, 2) == h::before(counts, 1) + counts[1]);
    assert(h::first_code(counts, 1) == 0);
    assert(h::normalized_cursor(counts, 1, 0) == 0int * h::capacity(31));
    assert(0int * h::capacity(31) == 0) by (nonlinear_arith);
}

pub(crate) proof fn single_symbol_prefix(lengths: Seq<u16>, work: Seq<u16>)
    requires h::valid_histogram(lengths, h::histogram(lengths)),
        h::bucket_ordered(lengths, h::histogram(lengths), work),
        h::maximum_length(lengths) == 1, h::before(h::histogram(lengths), 16) == 1,
    ensures work.len() >= 1, work[0] < lengths.len(), lengths[work[0] as int] == 1,
        h::canonical_prefix(lengths, work[0] as int) == 0,
{
    let counts = h::histogram(lengths);
    facts::ordered_symbol_at(lengths, counts, work, 0);
    let symbol = work[0] as int;
    decode::maximum_symbol_bound(lengths, symbol);
    assert(lengths[symbol] == 1);
    assert(h::before(counts, 1) == 0);
    assert(h::occurrences(lengths.take(symbol), 1) == 0);
    assert(h::canonical_start(lengths, 1) == 0);
    assert(h::canonical_code(lengths, symbol) == 0);
    assert(0int * h::capacity(31) == 0) by (nonlinear_arith);
    facts::zero_reversal();
}

pub(crate) proof fn incomplete_cursor_code(cursor: u32, code: u32)
    requires cursor == 0x80000000, code < 2, h::is_reversal(cursor, code),
    ensures code == 1,
{
    if code == 0 {
        decode::reversal_symmetric(cursor, code);
        facts::zero_reversal();
        facts::reversal_unique(0, cursor, 0);
    }
}

#[verifier::spinoff_prover]
pub(crate) proof fn incomplete(alphabet: h::Alphabet, lengths: Seq<u16>,
    work: Seq<u16>, original: Seq<Code>, before: Seq<Code>, after: Seq<Code>)
    requires h::valid_histogram(lengths, h::histogram(lengths)),
        forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= 15,
        h::valid_prefix(h::histogram(lengths), 15),
        h::bucket_ordered(lengths, h::histogram(lengths), work),
        h::slots(h::histogram(lengths), 15) != 0, h::maximum_length(lengths) == 1,
        before.len() >= 2, after.len() == before.len(),
        model::progress(alphabet, lengths, work,
            h::before(h::histogram(lengths), 16), 1, original, before),
        forall|index: int| 0 <= index < before.len() ==>
            #[trigger] after[index] == if index == 1 {
                model::invalid_hole()
            } else { before[index] },
    ensures model::table(alphabet, lengths, 1, after),
        after.len() == original.len(),
        forall|index: int| 2 <= index < after.len() ==>
            #[trigger] after[index] == original[index],
{
    let counts = h::histogram(lengths);
    incomplete_one_bit_shape(lengths, counts);
    single_symbol_prefix(lengths, work);
    reveal(model::progress);
    reveal(model::table);
    let symbol = work[0] as int;
    assert(h::capacity(1) == 2) by (compute);
    assert(h::code_prefix_matches(lengths, symbol, 0));
    assert(model::seen(lengths, work, 1, 0));
    assert(model::written(alphabet, lengths, work, 1, 0, before[0]));
    let written = choose|position: int| 0 <= position < 1 && position < work.len()
        && h::code_prefix_matches(lengths, work[position] as int, 0)
        && emission::leaf(alphabet, work[position] as nat,
            lengths[work[position] as int] as nat, before[0]);
    assert(written == 0);
    assert forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, 0)
        implies other == symbol by {
        decode::matching_symbol_unique(lengths, counts, symbol, other, 0);
    }
    assert(model::entry(alphabet, lengths, after[0], 0));
    assert(1int % 2 == 1) by (compute);
    assert((1u32 as int) % h::capacity(lengths[symbol] as nat) == 1);
    assert(!h::code_prefix_matches(lengths, symbol, 1));
    assert forall|other: int| !h::code_prefix_matches(lengths, other, 1) by {
        if h::code_prefix_matches(lengths, other, 1) {
            facts::sorted_symbol_position(lengths, counts, work, other);
            let position = h::before(counts, lengths[other] as nat)
                + h::occurrences(lengths.take(other), lengths[other]);
            assert(position == 0);
            assert(other == symbol);
        }
    }
    assert(model::entry(alphabet, lengths, after[1], 1));
    assert forall|index: int| 0 <= index < h::capacity(1) implies
        #[trigger] model::entry(alphabet, lengths, after[index], index as u32) by {
        assert(index == 0 || index == 1);
    }
    assert forall|index: int| 2 <= index < after.len() implies
        #[trigger] after[index] == original[index] by {
        assert(before[index] == original[index]);
    }
}

pub(crate) proof fn finished(alphabet: h::Alphabet, lengths: Seq<u16>, requested: nat,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    outcome: InflateTable)
    requires forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= 15,
        h::maximum_length(lengths) <= requested,
        crate::table_preparation_specs::result(alphabet, lengths, requested,
            original, codes, original_work, work, TablePreparation::Finished(outcome)),
    ensures model::result(alphabet, lengths, original, codes, original_work, work, outcome),
        matches!(alphabet, h::Alphabet::CodeLengths) && requested <= 7 ==>
            h::code_length_result(lengths, original, codes, original_work, work, outcome),
{
    reveal(model::result);
    facts::metadata_bounds(lengths);
    crate::table_preparation_proofs::code_lengths_capacity();
    if h::maximum_length(lengths) > 0 {
        crate::table_preparation_proofs::clamped_root_at_upper_bound(requested,
            h::minimum_length(lengths) as nat, h::maximum_length(lengths) as nat);
    }
}

pub(crate) proof fn ready_result(alphabet: h::Alphabet, lengths: Seq<u16>,
    original: Seq<Code>, codes: Seq<Code>, original_work: Seq<u16>, work: Seq<u16>,
    root: usize, used: usize)
    requires h::maximum_length(lengths) > 0, root == h::maximum_length(lengths),
        used == h::capacity(root as nat), codes.len() == original.len(),
        h::accepted_lengths(lengths, crate::table_preparation_specs::require_complete(alphabet)),
        crate::table_preparation_specs::root_capacity_allowed(alphabet, used as nat),
        crate::table_preparation_specs::sorted_workspace(lengths, original_work, work),
        model::table(alphabet, lengths, root as nat, codes),
        forall|index: int| used <= index < codes.len() ==>
            #[trigger] codes[index] == original[index],
    ensures model::result(alphabet, lengths, original, codes, original_work, work,
        InflateTable::Success { root, used }),
{
    reveal(model::result);
}

#[verifier::spinoff_prover]
pub(crate) proof fn legacy_codes(lengths: Seq<u16>, work: Seq<u16>,
    original: Seq<Code>, codes: Seq<Code>)
    requires lengths.len() <= 19,
        forall|symbol: int| 0 <= symbol < lengths.len() ==> lengths[symbol] <= 7,
        h::valid_histogram(lengths, h::histogram(lengths)),
        h::valid_prefix(h::histogram(lengths), 15),
        h::slots(h::histogram(lengths), 15) == 0,
        h::bucket_ordered(lengths, h::histogram(lengths), work),
        model::table(h::Alphabet::CodeLengths, lengths,
            h::maximum_length(lengths) as nat, codes),
        codes.len() == original.len(),
        forall|index: int| 0 <= index < codes.len()
            && h::capacity(h::maximum_length(lengths) as nat) <= index
            ==> #[trigger] codes[index] == original[index],
    ensures h::root_codes_table(lengths, work, h::before(h::histogram(lengths), 16),
        codes, original), h::root_decoding_table(lengths, codes),
{
    reveal(model::table);
    facts::metadata_bounds(lengths);
    crate::dynamic_header_proofs::maximum_bounded(lengths, 7);
    let counts = h::histogram(lengths);
    let total = h::before(counts, 16);
    let root = h::maximum_length(lengths) as nat;
    facts::depth_capacity(root);
    assert forall|index: int| 0 <= index < codes.len() implies
        #[trigger] codes[index] == h::root_codes_after(lengths, work,
            total, index, original[index]) by {
        if index < h::capacity(root) {
            assert(index as u32 as int == index);
            assert(model::entry(h::Alphabet::CodeLengths, lengths, codes[index], index as u32));
            decode::matching_symbol_exists(lengths, counts, work, index as u32);
            assert(exists|symbol: int| #[trigger] h::code_prefix_matches(lengths, symbol, index as u32)
                && emission::leaf(h::Alphabet::CodeLengths, symbol as nat,
                    lengths[symbol] as nat, codes[index])
                && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, index as u32)
                    ==> other == symbol));
            let symbol = choose|symbol: int|
                #[trigger] h::code_prefix_matches(lengths, symbol, index as u32)
                && emission::leaf(h::Alphabet::CodeLengths, symbol as nat,
                    lengths[symbol] as nat, codes[index])
                && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, index as u32)
                    ==> other == symbol);
            facts::sorted_symbol_position(lengths, counts, work, symbol);
            let position = (h::before(counts, lengths[symbol] as nat)
                + h::occurrences(lengths.take(symbol), lengths[symbol])) as nat;
            decode::root_written_symbol(lengths, work, total, index, symbol as u16,
                position, original[index]);
            assert(codes[index] == Code { op: 0, bits: lengths[symbol] as u8, val: symbol as u16 });
        } else {
            facts::root_codes_frame(lengths, work, total, index, original[index]);
        }
    }
    decode::root_table_decodes(lengths, work, codes, original);
}

pub(crate) open spec fn fixture_lengths() -> Seq<u16> {
    seq![1u16]
}

pub(crate) open spec fn fixture_codes() -> Seq<Code> {
    seq![Code { op: 16, bits: 1, val: 1 }, Code { op: 64, bits: 1, val: 0 }]
}

pub(crate) proof fn independent_one_bit_distance_fixture()
    ensures model::table(h::Alphabet::Distances, fixture_lengths(), 1, fixture_codes()),
        fixture_codes()[0].val == 1, fixture_codes()[1].op == 64,
{
    reveal(model::table);
    let lengths = fixture_lengths();
    let codes = fixture_codes();
    facts::zero_reversal();
    assert(lengths.drop_last() =~= Seq::<u16>::empty());
    assert(lengths.last() == 1);
    reveal_with_fuel(h::maximum_length, 2);
    assert(h::maximum_length(lengths) == 1);
    assert(h::canonical_code(lengths, 0) == 0);
    assert(0int * h::capacity(31) == 0) by (nonlinear_arith);
    assert(h::canonical_prefix(lengths, 0) == 0);
    assert(h::capacity(1) == 2) by (compute);
    assert(1int % 2 == 1) by (compute);
    assert(h::code_prefix_matches(lengths, 0, 0));
    assert forall|symbol: int| #[trigger] h::code_prefix_matches(lengths, symbol, 0)
        implies symbol == 0 by {
    }
    assert(model::entry(h::Alphabet::Distances, lengths, codes[0], 0));
    assert forall|symbol: int| !h::code_prefix_matches(lengths, symbol, 1) by {
        if h::code_prefix_matches(lengths, symbol, 1) {
            assert(symbol == 0);
        }
    }
    assert(model::entry(h::Alphabet::Distances, lengths, codes[1], 1));
    assert forall|index: int| 0 <= index < 2 implies
        #[trigger] model::entry(h::Alphabet::Distances, lengths, codes[index], index as u32) by {
        assert(index == 0 || index == 1);
    }
}

pub(crate) proof fn independent_one_bit_word_fixture()
    ensures model::entry(h::Alphabet::Distances, fixture_lengths(), fixture_codes()[0],
        0xffff_fffe),
        model::entry(h::Alphabet::Distances, fixture_lengths(), fixture_codes()[1],
            0xffff_ffff),
{
    independent_one_bit_distance_fixture();
    word_entry(h::Alphabet::Distances, fixture_lengths(), 1, fixture_codes(), 0xffff_fffe);
    word_entry(h::Alphabet::Distances, fixture_lengths(), 1, fixture_codes(), 0xffff_ffff);
    assert(h::capacity(1) == 2) by (compute);
}

}
