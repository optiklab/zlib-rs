use super::{entries, layout::TableLayout, replicate, CodeType};
use crate::Code;

#[cfg(verus_keep_ghost)]
use crate::{huffman_proofs, huffman_specs, table_emission_specs as model};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) struct EntryPosition {
    pub length: usize,
    pub drop: usize,
    pub prefix: usize,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verifier::spinoff_prover)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires super::layout::valid_layout(layout),
        position.drop < position.length <= 15,
        position.length - position.drop <= layout.width,
        position.prefix < huffman_specs::capacity((position.length - position.drop) as nat),
        layout.used <= table.len(),
        huffman_specs::symbol_domain(entries::alphabet(kind), symbol as nat),
        huffman_specs::tables_match(entries::alphabet(kind),
            parameters.0@, parameters.1@, parameters.2),
    ensures model::result(entries::alphabet(kind), symbol as nat,
        (position.length - position.drop) as nat, layout.next as nat,
        layout.width as nat, position.prefix as nat, old(table)@, final(table)@,
        result.0, result.1 as nat),
        result.0.bits == position.length - position.drop,
        huffman_specs::entry_meaning(entries::alphabet(kind),
            symbol as nat, result.0.op, result.0.val),
        result.1 == huffman_specs::capacity(layout.width as nat),
        final(table)@.len() == old(table)@.len(),
        layout.next == 0 ==> forall|index: int| #![trigger final(table)@[index]]
            0 <= index < old(table)@.len() ==>
            final(table)@[index] == if huffman_specs::table_replica(0,
                position.prefix as nat, (position.length - position.drop) as nat,
                layout.width as nat, index
            ) { result.0 } else { old(table)@[index] },
        forall|lengths: Seq<u16>, counts: Seq<u16>, link: Code, word: u64|
            #[trigger] model::child_context(lengths, counts, symbol as nat,
                position.length as nat, position.drop as nat, position.prefix as nat,
                layout.next as nat, layout.width as nat, layout.used as nat, link, word) ==>
                final(table)@[huffman_specs::subtable_index(link, word as nat)]
                    == (if huffman_specs::code_prefix_matches(lengths, symbol as int, word as u32) {
                        result.0
                    } else { old(table)@[huffman_specs::subtable_index(link, word as nat)] })
                && (huffman_specs::code_prefix_matches(lengths, symbol as int, word as u32) ==>
                    crate::linked_table_specs::leaf(entries::alphabet(kind), lengths,
                        final(table)@[huffman_specs::subtable_index(link, word as nat)],
                        word as u32, position.drop as nat)),
        forall|lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
                processed: nat, root: nat, max: nat, epoch: nat,
                pages: Seq<Option<crate::table_pages_specs::Page>>,
                openings: Seq<Option<crate::page_source_specs::Opening>>, original: Seq<Code>|
            crate::constructor_table_specs::progress(entries::alphabet(kind),
                lengths, work, processed, root, layout.used as int,
                pages, original, old(table)@)
                && crate::constructor_pages_specs::ownership(lengths, counts, work,
                    root, max, layout.used as int, epoch, pages, openings)
                && processed < work.len() && work[processed as int] == symbol
                && crate::constructor_pages_specs::emission_region(lengths, root,
                    pages, symbol as int, layout.next as nat, layout.width as nat,
                    (position.length - position.drop) as nat, position.prefix as nat)
            ==> crate::constructor_table_specs::progress(entries::alphabet(kind),
                lengths, work, processed + 1, root, layout.used as int,
                pages, original, final(table)@),
))]
pub(super) fn emit_entry(
    kind: &CodeType,
    symbol: u16,
    position: EntryPosition,
    parameters: (&[u16], &[u8], u16),
    table: &mut [Code],
    layout: &TableLayout,
) -> (Code, usize) {
    #[cfg(verus_keep_ghost)]
    proof_decl! { let ghost original = table@; }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(model::result);
        huffman_proofs::capacity_positive(layout.width as nat);
    }
    let entry = entries::make_entry(
        kind,
        symbol,
        position.length,
        position.drop,
        parameters.0,
        parameters.1,
        parameters.2,
    );
    let previous_size = replicate::replicate_entry(
        table,
        layout,
        position.prefix,
        position.length - position.drop,
        entry,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|lengths: Seq<u16>, counts: Seq<u16>, link: Code, word: u64|
            #[trigger] model::child_context(lengths, counts, symbol as nat,
                position.length as nat, position.drop as nat, position.prefix as nat,
                layout.next as nat, layout.width as nat, layout.used as nat, link, word) implies
                table@[huffman_specs::subtable_index(link, word as nat)]
                    == (if huffman_specs::code_prefix_matches(lengths, symbol as int, word as u32) {
                        entry
                    } else { original[huffman_specs::subtable_index(link, word as nat)] })
                && (huffman_specs::code_prefix_matches(lengths, symbol as int, word as u32) ==>
                    crate::linked_table_specs::leaf(entries::alphabet(kind), lengths,
                        table@[huffman_specs::subtable_index(link, word as nat)],
                        word as u32, position.drop as nat)) by {
            crate::child_emission_proofs::emitted_child_lookup(entries::alphabet(kind),
                lengths, counts, symbol as nat, position.length as nat, position.drop as nat,
                position.prefix as nat, layout.next as nat, layout.width as nat,
                layout.used as nat, link, word, original, table@, entry, previous_size as nat);
        }
        assert forall|lengths: Seq<u16>, counts: Seq<u16>, work: Seq<u16>,
                processed: nat, root: nat, max: nat, epoch: nat,
                pages: Seq<Option<crate::table_pages_specs::Page>>,
                openings: Seq<Option<crate::page_source_specs::Opening>>, original_table: Seq<Code>|
            crate::constructor_table_specs::progress(entries::alphabet(kind),
                lengths, work, processed, root, layout.used as int,
                pages, original_table, original)
                && crate::constructor_pages_specs::ownership(lengths, counts, work,
                    root, max, layout.used as int, epoch, pages, openings)
                && processed < work.len() && work[processed as int] == symbol
                && crate::constructor_pages_specs::emission_region(lengths, root,
                    pages, symbol as int, layout.next as nat, layout.width as nat,
                    (position.length - position.drop) as nat, position.prefix as nat)
            implies crate::constructor_table_specs::progress(entries::alphabet(kind),
                lengths, work, processed + 1, root, layout.used as int,
                pages, original_table, table@) by {
            crate::constructor_pages_proofs::emission_keeps_links(lengths, counts, work,
                root, max, layout.used as int, epoch, pages, openings, entries::alphabet(kind),
                symbol as int, layout.next as nat, layout.width as nat,
                (position.length - position.drop) as nat, position.prefix as nat,
                original, table@, entry);
            crate::constructor_table_proofs::emitted(entries::alphabet(kind), lengths,
                work, processed, root, layout.used as int, pages, original_table,
                original, table@, entry, layout.next as nat, layout.width as nat,
                (position.length - position.drop) as nat, position.prefix as nat);
        }
    }
    (entry, previous_size)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn emits_every_leaf_class_into_only_the_selected_subtable_replicas() {
        for (kind, symbol, operation, value) in [
            (CodeType::Codes, 18, 0, 18),
            (CodeType::Lens, 0, 0, 0),
            (CodeType::Lens, 255, 0, 255),
            (CodeType::Lens, 256, 96, 0),
            (CodeType::Lens, 257, 16, 3),
            (CodeType::Lens, 265, 17, 11),
            (CodeType::Lens, 285, 16, 258),
            (CodeType::Lens, 286, 77, 0),
            (CodeType::Lens, 287, 202, 0),
            (CodeType::Dists, 0, 16, 1),
            (CodeType::Dists, 4, 17, 5),
            (CodeType::Dists, 29, 29, 24577),
            (CodeType::Dists, 30, 64, 0),
            (CodeType::Dists, 31, 64, 0),
        ] {
            let mut table = [Code {
                bits: 1,
                op: 64,
                val: 99,
            }; 24];
            table[1] = Code {
                bits: 2,
                op: 4,
                val: 4,
            };
            let before = table;
            let layout = TableLayout {
                next: 4,
                width: 4,
                used: 20,
            };
            let expected = Code {
                bits: 3,
                op: operation,
                val: value,
            };
            assert_eq!(
                emit_entry(
                    &kind,
                    symbol,
                    EntryPosition {
                        length: 5,
                        drop: 2,
                        prefix: 5,
                    },
                    entries::table_parameters(&kind),
                    &mut table,
                    &layout,
                ),
                (expected, 16),
            );
            for (index, entry) in table.into_iter().enumerate() {
                assert_eq!(
                    entry,
                    if index == 9 || index == 17 {
                        expected
                    } else {
                        before[index]
                    },
                );
            }
        }
    }
}
