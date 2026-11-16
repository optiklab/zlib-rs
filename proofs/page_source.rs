use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::page_source_specs as model;
use crate::subtable_coverage_proofs as coverage;
use vstd::prelude::*;

verus! {

pub proof fn covered(lengths: Seq<u16>, original: Seq<u16>, root: nat,
    max: nat, key: int, width: nat, opening: model::Opening, symbol: int)
    requires model::valid_window(lengths, original, root, max, key, width, opening),
        0 <= symbol < lengths.len(), root < lengths[symbol] <= 15,
        (h::canonical_prefix(lengths, symbol) as int) % h::capacity(root) == key,
    ensures lengths[symbol] <= root + width,
{
    coverage::same_wire_root_covered(lengths, original, opening.remaining,
        opening.position, opening.length, root, max, width, opening.symbol, symbol);
}

pub proof fn opening_result(remaining: Seq<u16>, length: nat, root: nat,
    max: nat, width: nat, key: int)
    requires h::chosen_width(remaining, (length - root) as nat, root, max, width),
    ensures forall|lengths: Seq<u16>, original: Seq<u16>, position: nat, symbol: int|
        #[trigger] model::context(lengths, original, root, max, key,
            model::Opening { symbol, position, length, remaining })
        ==> model::valid_window(lengths, original, root, max, key, width,
            model::Opening { symbol, position, length, remaining }),
{
}

pub open spec fn fixture_remaining() -> Seq<u16> {
    Seq::new(16, |level: int| if level == 3 { 4u16 } else { 0u16 })
}

pub proof fn independent_opening()
    ensures model::valid_window(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            2, 3, 1, 1, model::Opening {
                symbol: 2, position: 2, length: 3, remaining: fixture_remaining(),
            }),
        !model::context(seq![2u16, 2, 3, 3, 3, 3], coverage::fixture_counts(),
            2, 3, 0, model::Opening {
                symbol: 2, position: 2, length: 3, remaining: fixture_remaining(),
            }),
        (h::canonical_prefix(seq![2u16, 2, 3, 3, 3, 3], 4) as int) % h::capacity(2) != 1,
{
    let lengths = seq![2u16, 2, 3, 3, 3, 3];
    let original = coverage::fixture_counts();
    let remaining = fixture_remaining();
    coverage::independent_root_coverage();
    assert(h::before(coverage::fixture_counts(), 3) == 2
        && h::before(coverage::fixture_counts(), 4) == 6
        && h::first_code(coverage::fixture_counts(), 3) == 4
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 2) == 4
        && h::canonical_code(seq![2u16, 2, 3, 3, 3, 3], 4) == 6
        && h::capacity(29) == 536870912 && h::capacity(2) == 4) by (compute);
    assert(h::slots(original, 0) == 1);
    assert(h::slots(original, 1) == 2);
    assert(h::slots(original, 2) == 2);
    assert(h::slots(original, 3) == 0);
    assert forall|depth: nat| depth <= 15 implies h::slots(original, depth) >= 0 by {
        if depth > 3 { facts::slots_empty_tail(original, 3, depth); }
    }
    assert forall|level: int| 1 <= level <= 15 implies
        remaining[level] == h::remaining_count(original, level as nat, 2) by {
        if level >= 4 {
            facts::before_monotone(original, 4, level as nat);
        }
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(1, bit) == h::word_bit(0x8000_0000, (31 - bit) as u32) by {
        assert((1u32 >> bit) & 1 == (0x8000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    assert forall|bit: u32| bit < 32 implies
        #[trigger] h::word_bit(3, bit) == h::word_bit(0xc000_0000, (31 - bit) as u32) by {
        assert((3u32 >> bit) & 1 == (0xc000_0000u32 >> ((31 - bit) as u32)) & 1)
            by (bit_vector) requires bit < 32;
    }
    facts::reversal_matches_model(0x8000_0000, 1);
    facts::reversal_matches_model(0xc000_0000, 3);
}

}
