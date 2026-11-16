use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::linked_table_specs as linked;
use crate::table_emission_specs as emission;
use crate::Code;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

pub(crate) proof fn prefix_split(word: nat, prefix: nat, root: nat, tail: nat)
    requires 1 <= root, 1 <= tail, root + tail <= 15,
        prefix < h::capacity(root + tail),
    ensures (word as int) % h::capacity(root + tail) == prefix
        <==> (word as int) % h::capacity(root) == (prefix as int) % h::capacity(root)
            && ((word as int) / h::capacity(root)) % h::capacity(tail)
                == (prefix as int) / h::capacity(root),
{
    facts::capacity_product(root, tail);
    facts::capacity_positive(root);
    facts::capacity_positive(tail);
    let r = h::capacity(root);
    let t = h::capacity(tail);
    lemma_mod_breakdown(word as int, r, t);
    lemma_mod_mod(word as int, r, t);
    lemma_fundamental_div_mod(prefix as int, r);
    lemma_mod_bound(prefix as int, r);
    if (word as int) % h::capacity(root + tail) == prefix {
        assert((word as int) % r == (prefix as int) % r);
        assert(((word as int) / r) % t == (prefix as int) / r)
            by (nonlinear_arith)
            requires r > 0,
                r * (((word as int) / r) % t) + (word as int) % r == prefix,
                prefix == r * ((prefix as int) / r) + (prefix as int) % r,
                (word as int) % r == (prefix as int) % r;
    }
}

pub(crate) proof fn selected_replica(word: nat, prefix: nat, root: nat,
    bits: nat, width: nat, base: nat)
    requires 1 <= root, 1 <= bits <= width, root + width <= 15,
        prefix < h::capacity(root + bits),
        (word as int) % h::capacity(root) == (prefix as int) % h::capacity(root),
    ensures h::table_replica(base, ((prefix as int) / h::capacity(root)) as nat,
        bits, width, base + ((word as int) / h::capacity(root)) % h::capacity(width))
            <==> (word as int) % h::capacity(root + bits) == prefix,
{
    facts::capacity_positive(root);
    facts::capacity_positive(bits);
    facts::capacity_positive(width);
    facts::capacity_positive((width - bits) as nat);
    facts::capacity_product(bits, (width - bits) as nat);
    let shifted = (word as int) / h::capacity(root);
    lemma_mod_bound(shifted, h::capacity(width));
    lemma_mod_mod(shifted, h::capacity(bits), h::capacity((width - bits) as nat));
    prefix_split(word, prefix, root, bits);
}

pub(crate) proof fn cached_word_projection(word: u64, width: u32)
    requires 1 <= width <= 15,
    ensures (word as int) % h::capacity(width as nat)
        == (word as u32 as int) % h::capacity(width as nat),
{
    facts::capacity_is_power(width as nat);
    vstd::bits::lemma_u64_pow2_no_overflow(width as nat);
    vstd::bits::lemma_u64_shl_is_mul(1, width as u64);
    vstd::bits::lemma_u64_low_bits_mask_is_mod(word, width as nat);
    let mask = ((1u64 << width) - 1) as u64;
    assert(mask as nat == vstd::bits::low_bits_mask(width as nat));
    crate::huffman_lookahead::peek_root_index(word, width, word & mask);
}

pub(crate) proof fn prefix_bound(prefix: nat, root: nat, tail: nat)
    requires 1 <= root, 1 <= tail, root + tail <= 15,
        (prefix as int) / h::capacity(root) < h::capacity(tail),
    ensures prefix < h::capacity(root + tail),
{
    facts::capacity_product(root, tail);
    facts::capacity_positive(root);
    let r = h::capacity(root);
    let t = h::capacity(tail);
    lemma_fundamental_div_mod(prefix as int, r);
    lemma_mod_bound(prefix as int, r);
    assert(prefix < r * t) by (nonlinear_arith)
        requires r > 0, (prefix as int) / r < t,
            prefix == r * ((prefix as int) / r) + (prefix as int) % r,
            0 <= (prefix as int) % r < r;
}

pub(crate) proof fn emitted_child_lookup(alphabet: h::Alphabet,
    lengths: Seq<u16>, counts: Seq<u16>, symbol: nat, length: nat, root: nat,
    prefix: nat, base: nat, width: nat, used: nat, link: Code, word: u64,
    before: Seq<Code>, after: Seq<Code>, code: Code, previous_size: nat)
    requires emission::child_context(lengths, counts, symbol, length, root, prefix,
        base, width, used, link, word),
        emission::result(alphabet, symbol, (length - root) as nat, base, width,
            prefix, before, after, code, previous_size),
    ensures after.len() == before.len(),
        base <= h::subtable_index(link, word as nat) < used <= after.len(),
        after[h::subtable_index(link, word as nat)]
            == if h::code_prefix_matches(lengths, symbol as int, word as u32) {
                code
            } else { before[h::subtable_index(link, word as nat)] },
        h::code_prefix_matches(lengths, symbol as int, word as u32) ==>
            linked::leaf(alphabet, lengths, after[h::subtable_index(link, word as nat)],
                word as u32, root),
{
    reveal(emission::result);
    let bits = (length - root) as nat;
    let whole = h::canonical_prefix(lengths, symbol as int) as nat;
    let index = h::subtable_index(link, word as nat);
    prefix_bound(whole, root, bits);
    cached_word_projection(word, root as u32);
    cached_word_projection(word, length as u32);
    selected_replica(word as nat, whole, root, bits, width, base);
    facts::subtable_link_bounds(link, root, base, width, used, word as nat);
    assert(h::table_replica(base, prefix, bits, width, index)
        <==> h::code_prefix_matches(lengths, symbol as int, word as u32));
    if h::code_prefix_matches(lengths, symbol as int, word as u32) {
        assert forall|other: int| #[trigger] h::code_prefix_matches(lengths, other, word as u32)
            implies other == symbol by {
            crate::huffman_decode::matching_symbol_unique(lengths, counts,
                symbol as int, other, word as u32);
        }
        assert(linked::leaf(alphabet, lengths, code, word as u32, root));
    }
}

pub(crate) open spec fn fixture_counts() -> Seq<u16> {
    Seq::new(16, |level: int| if level == 1 { 1u16 }
        else if level == 2 { 2u16 } else { 0u16 })
}

pub(crate) proof fn independent_child_context()
    ensures emission::child_context(seq![1u16, 2u16, 2u16], fixture_counts(),
            1, 2, 1, 0, 2, 1, 4, Code { bits: 1, op: 1, val: 2 }, 1),
        emission::child_context(seq![1u16, 2u16, 2u16], fixture_counts(),
            2, 2, 1, 1, 2, 1, 4, Code { bits: 1, op: 1, val: 2 }, 3),
        !emission::child_context(seq![1u16, 2u16, 2u16], fixture_counts(),
            1, 2, 1, 0, 2, 1, 4, Code { bits: 1, op: 1, val: 2 }, 0),
        emission::child_context(seq![1u16, 2u16, 2u16], fixture_counts(),
            1, 2, 1, 0, 2, 1, 4, Code { bits: 1, op: 1, val: 2 },
                (u64::MAX - 2) as u64),
{
    let lengths = seq![1u16, 2u16, 2u16];
    let counts = fixture_counts();
    crate::linked_table_proofs::three_symbol_prefixes();
    crate::linked_table_proofs::independent_link_extent();
    assert(h::capacity(1) == 2) by (compute);
    assert forall|level: int| 1 <= level <= 15 implies
        #[trigger] counts[level] == h::occurrences(lengths, level as u16) by {
        facts::histogram_prefix_step(lengths, 0, level as u16);
        facts::histogram_prefix_step(lengths, 1, level as u16);
        facts::histogram_prefix_step(lengths, 2, level as u16);
        assert(lengths.take(3) =~= lengths);
        assert(lengths.take(0) =~= Seq::<u16>::empty());
    }
    assert(h::slots(Seq::new(16, |level: int| if level == 1 { 1u16 }
        else if level == 2 { 2u16 } else { 0u16 }), 1) == 1
        && h::slots(Seq::new(16, |level: int| if level == 1 { 1u16 }
        else if level == 2 { 2u16 } else { 0u16 }), 2) == 0) by (compute);
    assert forall|depth: nat| depth <= 15 implies #[trigger] h::slots(counts, depth) >= 0 by {
        if depth > 2 {
            facts::slots_empty_tail(counts, 2, depth);
        }
    }
    assert(3int / 2 == 1 && 3int % 2 == 1
        && (0xffff_fffdu32 as int) % 2 == 1
        && (u64::MAX - 2) as u64 == 0xffff_ffff_ffff_fffdu64) by (compute);
    let word = 0xffff_ffff_ffff_fffdu64;
    let low = word as u32;
    assert(low == 0xffff_fffdu32) by (bit_vector)
        requires low == word as u32, word == 0xffff_ffff_ffff_fffdu64;
}

pub(crate) proof fn independent_child_effect()
    ensures linked::leaf(h::Alphabet::CodeLengths, seq![1u16, 2u16, 2u16],
        Code { bits: 1, op: 0, val: 1 }, 1, 1),
{
    let original = Seq::new(4, |index: int|
        if index == 1 { Code { bits: 1, op: 1, val: 2 } }
        else { Code { bits: 1, op: 64, val: 99 } });
    let code = Code { bits: 1, op: 0, val: 1 };
    let after = original.update(2, code);
    independent_child_context();
    reveal(emission::result);
    assert(h::capacity(1) == 2) by (compute);
    assert forall|index: int| 0 <= index < 4 implies
        h::table_replica(2, 0, 1, 1, index) == (index == 2) by {}
    assert(emission::result(h::Alphabet::CodeLengths, 1, 1, 2, 1, 0,
        original, after, code, 2));
    emitted_child_lookup(h::Alphabet::CodeLengths, seq![1u16, 2u16, 2u16],
        fixture_counts(), 1, 2, 1, 0, 2, 1, 4, Code { bits: 1, op: 1, val: 2 },
        1, original, after, code, 2);
}

}
