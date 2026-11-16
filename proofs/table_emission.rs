use crate::huffman_specs::{self as h, Alphabet};
use crate::table_emission_specs as model;
use crate::Code;
use vstd::prelude::*;

verus! {

pub(crate) proof fn leaf_role_separation(alphabet: Alphabet, symbol: nat,
    bits: nat, entry: Code)
    requires model::leaf(alphabet, symbol, bits, entry),
    ensures 1 <= entry.bits <= 15,
        !(1 <= entry.op <= 15),
        entry.op & 32 != 0 ==> matches!(alphabet, Alphabet::LiteralLengths) && symbol == 256,
        entry.op & 16 != 0 ==> match alphabet {
            Alphabet::CodeLengths => false,
            Alphabet::LiteralLengths => 257 <= symbol <= 285,
            Alphabet::Distances => symbol <= 29,
        },
        h::invalid_operation(entry.op) ==> match alphabet {
            Alphabet::CodeLengths => false,
            Alphabet::LiteralLengths => 286 <= symbol <= 287,
            Alphabet::Distances => 30 <= symbol <= 31,
        },
{
    let op = entry.op;
    match alphabet {
        Alphabet::CodeLengths => {},
        Alphabet::LiteralLengths => {
            if 257 <= symbol <= 285 {
                assert(16 <= op <= 21);
            }
        },
        Alphabet::Distances => {
            if symbol <= 29 {
                assert(16 <= op <= 29);
            }
        },
    }
    if 16 <= op <= 29 {
        assert(op & 16 != 0 && op & 32 == 0 && op & 64 == 0) by (bit_vector)
            requires 16 <= op <= 29;
    } else if op == 0 {
        assert(op & 16 == 0 && op & 32 == 0 && op & 64 == 0) by (bit_vector)
            requires op == 0;
    } else if op == 96 {
        assert(op & 16 == 0 && op & 32 != 0 && op & 64 != 0) by (bit_vector)
            requires op == 96;
    } else {
        assert(h::invalid_operation(op));
        assert(!(1 <= op <= 15)) by (bit_vector) requires op & 64 != 0;
    }
}

pub(crate) open spec fn fixture_before() -> Seq<Code> {
    Seq::new(24, |index: int| if index == 1 {
        Code { bits: 2, op: 4, val: 4 }
    } else { Code { bits: 1, op: 64, val: 99 } })
}

pub(crate) open spec fn fixture_after() -> Seq<Code> {
    Seq::new(24, |index: int| if index == 9 || index == 17 {
        Code { bits: 3, op: 17, val: 11 }
    } else { fixture_before()[index] })
}

pub(crate) proof fn offset_and_completion_fixture()
    ensures model::result(Alphabet::LiteralLengths, 265, 3, 4, 4, 5,
            fixture_before(), fixture_after(), Code { bits: 3, op: 17, val: 11 }, 16),
        h::subtable_link(Code { bits: 2, op: 4, val: 4 }, 2, 4, 4, 20),
        h::subtable_index(Code { bits: 2, op: 4, val: 4 }, 21) == 9,
        h::subtable_index(Code { bits: 2, op: 4, val: 4 }, 53) == 17,
{
    reveal(model::result);
    assert(h::capacity(2) == 4 && h::capacity(3) == 8 && h::capacity(4) == 16)
        by (compute);
    assert(h::entry_meaning(Alphabet::LiteralLengths, 265, 17, 11)) by (compute);
    assert forall|index: int| 0 <= index < 24 implies
        h::table_replica(4, 5, 3, 4, index) == (index == 9 || index == 17) by {}
}

}
