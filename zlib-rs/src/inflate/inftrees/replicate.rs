use super::layout::TableLayout;
use crate::Code;

#[cfg(verus_keep_ghost)]
use super::layout::valid_layout;
#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_layout(layout), 1 <= code_bits <= layout.width,
        prefix < huffman_specs::capacity(code_bits as nat),
        layout.used <= table.len(),
    ensures result == huffman_specs::capacity(layout.width as nat),
        final(table)@.len() == old(table)@.len(),
        forall|index: int| #![trigger final(table)@[index]]
            0 <= index < old(table)@.len() ==>
            final(table)@[index] == if huffman_specs::table_replica(
                layout.next as nat, prefix as nat, code_bits as nat, layout.width as nat, index
            ) { entry } else { old(table)@[index] },
))]
pub(super) fn replicate_entry(
    table: &mut [Code],
    layout: &TableLayout,
    prefix: usize,
    code_bits: usize,
    entry: Code,
) -> usize {
    let base = layout.next;
    let table_bits = layout.width;
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original_table = table@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::usize_shift_capacity(code_bits);
        huffman_proofs::usize_shift_capacity(table_bits);
        huffman_proofs::capacity_positive(code_bits as nat);
        huffman_proofs::capacity_positive(table_bits as nat);
        huffman_proofs::capacity_multiple(code_bits as nat, table_bits as nat);
    }
    let incr = 1usize << code_bits;
    let size = 1usize << table_bits;
    let mut fill = size;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 0 < fill <= size, fill % incr == 0,
            table@.len() == original_table.len(),
            forall|index: int| #![trigger table@[index]]
                0 <= index < table@.len() ==>
                table@[index] == if huffman_specs::table_replica(
                    base as nat, prefix as nat, code_bits as nat, table_bits as nat, index
                ) && index - base >= fill { entry } else { original_table[index] },
        decreases fill,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof_decl! {
            let ghost previous_fill = fill;
            let ghost previous_table = table@;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if fill < incr {
                vstd::arithmetic::div_mod::lemma_small_mod(fill as nat, incr as nat);
            }
        }
        fill -= incr;
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish(
                previous_fill as int, incr as int);
            vstd::arithmetic::div_mod::lemma_small_mod(prefix as nat, incr as nat);
            vstd::arithmetic::div_mod::lemma_mod_adds(fill as int, prefix as int, incr as int);
        }
        table[base + prefix + fill] = entry;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|index: int| #![trigger table@[index]]
                0 <= index < table@.len() implies
                table@[index] == if huffman_specs::table_replica(
                    base as nat, prefix as nat, code_bits as nat, table_bits as nat, index
                ) && index - base >= fill { entry } else { original_table[index] } by {
                if index != base + prefix + fill {
                    if huffman_specs::table_replica(
                        base as nat, prefix as nat, code_bits as nat, table_bits as nat, index
                    ) && fill <= index - base < previous_fill {
                        huffman_proofs::replica_period(index - base, fill as int,
                            incr as int, prefix as int);
                    }
                    assert(table@[index] == previous_table[index]);
                }
            }
        }
        if fill == 0 {
            break;
        }
    }
    size
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn fills_only_matching_prefixes_and_preserves_surrounding_entries() {
        let untouched = Code {
            op: 64,
            bits: 1,
            val: 9,
        };
        let entry = Code {
            op: 16,
            bits: 2,
            val: 258,
        };
        let mut table = [untouched; 12];
        let layout = TableLayout {
            next: 2,
            width: 3,
            used: 10,
        };
        assert_eq!(replicate_entry(&mut table, &layout, 1, 2, entry), 8);
        assert_eq!(
            table,
            [
                untouched, untouched, untouched, entry, untouched, untouched, untouched, entry,
                untouched, untouched, untouched, untouched
            ]
        );
    }
}
