use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::linked_table_specs as model;
use crate::root_table_proofs as direct_facts;
use crate::root_table_specs as direct;
use crate::table_emission_specs as emission;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) proof fn zero_drop(alphabet: h::Alphabet, lengths: Seq<u16>,
    code: Code, word: u32)
    ensures model::leaf(alphabet, lengths, code, word, 0)
        <==> direct::entry(alphabet, lengths, code, word),
{
}

pub(crate) proof fn leaf_not_link(alphabet: h::Alphabet, symbol: nat, bits: nat,
    code: Code)
    requires emission::leaf(alphabet, symbol, bits, code),
    ensures !model::is_link(code),
{
    if model::is_link(code) {
        let op = code.op;
        assert(op & 64 == 0) by (bit_vector) requires op < 16;
    }
}

pub(crate) proof fn leaf_consumption(alphabet: h::Alphabet, lengths: Seq<u16>,
    code: Code, word: u32, dropped: nat, symbol: int)
    requires model::leaf(alphabet, lengths, code, word, dropped),
        h::code_prefix_matches(lengths, symbol, word),
    ensures dropped + code.bits == lengths[symbol],
        h::symbol_domain(alphabet, symbol as nat),
        h::entry_meaning(alphabet, symbol as nat, code.op, code.val),
{
    let selected = choose|selected: int|
        #[trigger] h::code_prefix_matches(lengths, selected, word)
        && dropped < lengths[selected]
        && emission::leaf(alphabet, selected as nat,
            (lengths[selected] as int - dropped) as nat, code)
        && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word)
            ==> other == selected);
    assert(selected == symbol);
}

pub(crate) proof fn direct_not_link(alphabet: h::Alphabet, lengths: Seq<u16>,
    code: Code, word: u32)
    requires direct::entry(alphabet, lengths, code, word),
    ensures !model::is_link(code),
{
    if exists|symbol: int| #[trigger] h::code_prefix_matches(lengths, symbol, word)
        && emission::leaf(alphabet, symbol as nat, lengths[symbol] as nat, code)
        && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word)
            ==> other == symbol) {
        let selected = choose|symbol: int|
            #[trigger] h::code_prefix_matches(lengths, symbol, word)
            && emission::leaf(alphabet, symbol as nat, lengths[symbol] as nat, code)
            && (forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word)
                ==> other == symbol);
        leaf_not_link(alphabet, selected as nat, lengths[selected] as nat, code);
    }
}

pub(crate) proof fn direct_table(alphabet: h::Alphabet, lengths: Seq<u16>,
    root: nat, codes: Seq<Code>)
    requires direct::table(alphabet, lengths, root, codes),
    ensures model::table(alphabet, lengths, root, h::capacity(root) as nat, codes),
{
    reveal(direct::table);
    reveal(model::table);
    facts::capacity_positive(root);
    facts::depth_capacity(root);
    assert forall|index: int| 0 <= index < h::capacity(root) implies
        !model::is_link(#[trigger] codes[index]) by {
        direct_not_link(alphabet, lengths, codes[index], index as u32);
    }
    assert forall|word: u64| {
        let first = #[trigger] codes[(word as u32 as int) % h::capacity(root)];
        if model::is_link(first) {
            model::leaf(alphabet, lengths, codes[h::subtable_index(first, word as nat)],
                word as u32, root)
        } else {
            model::leaf(alphabet, lengths, first, word as u32, 0)
        }
    } by {
        vstd::arithmetic::div_mod::lemma_mod_bound(word as u32 as int, h::capacity(root));
        direct_facts::word_entry(alphabet, lengths, root, codes, word as u32);
        zero_drop(alphabet, lengths, codes[(word as u32 as int) % h::capacity(root)],
            word as u32);
    }
}

pub(crate) proof fn child_selection(alphabet: h::Alphabet, lengths: Seq<u16>,
    root: nat, used: nat, codes: Seq<Code>, word: u64, link: Code, index: int)
    requires model::table(alphabet, lengths, root, used, codes),
        link == codes[(word as u32 as int) % h::capacity(root)],
        model::is_link(link),
        index == h::subtable_index(link, word as nat),
    ensures h::capacity(root) <= index < used <= codes.len(),
        link.bits == root && 1 <= link.op && root + link.op <= 15,
        model::leaf(alphabet, lengths, codes[index], word as u32, root),
{
    reveal(model::table);
    facts::capacity_positive(root);
    vstd::arithmetic::div_mod::lemma_mod_bound(word as u32 as int, h::capacity(root));
    assert(model::region(root, used, link));
    let end = (link.val as int + h::capacity(link.op as nat)) as nat;
    facts::subtable_link_bounds(link, root, link.val as nat, link.op as nat, end,
        word as nat);
}

pub(crate) proof fn empty_table(alphabet: h::Alphabet)
    ensures model::table(alphabet, Seq::<u16>::empty(), 1, 2,
        Seq::new(2, |index: int| direct::invalid_hole())),
{
    reveal(model::table);
    assert(h::capacity(1) == 2) by (compute);
}

pub(crate) proof fn independent_link_extent()
    ensures model::region(1, 4, Code { bits: 1, op: 1, val: 2 }),
        !model::region(1, 3, Code { bits: 1, op: 1, val: 2 }),
        !model::region(1, 4, Code { bits: 1, op: 1, val: 1 }),
        !model::region(2, 4, Code { bits: 1, op: 1, val: 2 }),
        h::subtable_index(Code { bits: 1, op: 1, val: 2 }, 1) == 2,
        h::subtable_index(Code { bits: 1, op: 1, val: 2 }, 3) == 3,
{
    assert(h::capacity(1) == 2) by (compute);
}

pub(crate) proof fn three_symbol_prefixes()
    ensures h::canonical_prefix(seq![1u16, 2u16, 2u16], 0) == 0,
        h::canonical_prefix(seq![1u16, 2u16, 2u16], 1) == 1,
        h::canonical_prefix(seq![1u16, 2u16, 2u16], 2) == 3,
{
    assert(h::canonical_code(seq![1u16, 2u16, 2u16], 0) == 0
        && h::canonical_code(seq![1u16, 2u16, 2u16], 1) == 2
        && h::canonical_code(seq![1u16, 2u16, 2u16], 2) == 3
        && h::capacity(30) == 0x4000_0000
        && h::capacity(31) == 0x8000_0000) by (compute);
    facts::zero_reversal();
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(1, bit)
            == h::word_bit(0x8000_0000, (31 - bit) as u32) by {
        assert((1u32 >> bit) & 1 == (0x8000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(3, bit)
            == h::word_bit(0xc000_0000, (31 - bit) as u32) by {
        assert((3u32 >> bit) & 1 == (0xc000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    facts::reversal_matches_model(0x8000_0000, 1);
    facts::reversal_matches_model(0xc000_0000, 3);
}

pub(crate) proof fn independent_two_level_table()
    ensures model::table(h::Alphabet::CodeLengths, seq![1u16, 2u16, 2u16], 1, 4,
        seq![
            Code { bits: 1, op: 0, val: 0 },
            Code { bits: 1, op: 1, val: 2 },
            Code { bits: 1, op: 0, val: 1 },
            Code { bits: 1, op: 0, val: 2 },
        ]),
{
    let lengths = seq![1u16, 2u16, 2u16];
    let codes = seq![
        Code { bits: 1, op: 0, val: 0 },
        Code { bits: 1, op: 1, val: 2 },
        Code { bits: 1, op: 0, val: 1 },
        Code { bits: 1, op: 0, val: 2 },
    ];
    three_symbol_prefixes();
    independent_link_extent();
    reveal(model::table);
    assert(h::capacity(1) == 2 && h::capacity(2) == 4) by (compute);
    assert(((1u64 << 1) - 1) as u64 == 1
        && ((1u64 << 2) - 1) as u64 == 3) by (compute);
    assert forall|word: u64| {
        let first = #[trigger] codes[(word as u32 as int) % h::capacity(1)];
        if model::is_link(first) {
            model::leaf(h::Alphabet::CodeLengths, lengths,
                codes[h::subtable_index(first, word as nat)], word as u32, 1)
        } else {
            model::leaf(h::Alphabet::CodeLengths, lengths, first, word as u32, 0)
        }
    } by {
        let tag = (word & 3) as u32;
        crate::huffman_lookahead::peek_root_index(word, 1, word & 1);
        crate::huffman_lookahead::peek_root_index(word, 2, word & 3);
        crate::huffman_lookahead::masked_subtable_index(word, 1, 1, word & 3);
        assert(tag <= 3 && word & 1 == (tag & 1) as u64
            && ((word & 3) >> 1) == (tag >> 1) as u64)
            by (bit_vector) requires tag == (word & 3) as u32;
        assert forall|symbol: int|
            #[trigger] h::code_prefix_matches(lengths, symbol, word as u32)
                <==> (symbol == 0 && (tag == 0 || tag == 2))
                    || (symbol == 1 && tag == 1) || (symbol == 2 && tag == 3) by {
        }
        if tag == 0 || tag == 2 {
            assert((tag & 1) == 0) by (bit_vector) requires tag == 0 || tag == 2;
            assert(h::code_prefix_matches(lengths, 0, word as u32));
            assert(model::leaf(h::Alphabet::CodeLengths, lengths, codes[0], word as u32, 0));
        } else if tag == 1 {
            assert(word & 1 == 1 && (word & 3) >> 1 == 0)
                by (bit_vector) requires tag == 1, tag == (word & 3) as u32;
            assert(h::code_prefix_matches(lengths, 1, word as u32));
            assert(model::leaf(h::Alphabet::CodeLengths, lengths, codes[2], word as u32, 1));
        } else {
            assert(tag == 3);
            assert(word & 1 == 1 && (word & 3) >> 1 == 1)
                by (bit_vector) requires tag == 3, tag == (word & 3) as u32;
            assert(h::code_prefix_matches(lengths, 2, word as u32));
            assert(model::leaf(h::Alphabet::CodeLengths, lengths, codes[3], word as u32, 1));
        }
    }
}

}
