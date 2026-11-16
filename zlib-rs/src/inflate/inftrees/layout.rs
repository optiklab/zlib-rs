use super::{entries::CodeType, lookahead::subtable_width};
use crate::{Code, ENOUGH_DISTS, ENOUGH_LENS};

#[cfg(verus_keep_ghost)]
use crate::{
    huffman_proofs, huffman_specs, page_source_proofs, page_source_specs, subtable_coverage_specs,
    table_pages_proofs, table_pages_specs,
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) struct TableLayout {
    pub next: usize,
    pub width: usize,
    pub used: usize,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(super) open spec fn valid_layout(layout: &TableLayout) -> bool {
    1 <= layout.width <= 15 && layout.used > 0
        && layout.next + huffman_specs::capacity(layout.width as nat) == layout.used
}

pub(super) open spec fn fits_kind(kind: &CodeType, used: nat) -> bool {
    match kind {
        CodeType::Codes => true,
        CodeType::Lens => used <= ENOUGH_LENS,
        CodeType::Dists => used <= ENOUGH_DISTS,
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= root <= 15,
    ensures valid_layout(&result), result.next == 0, result.width == root,
        result.used == huffman_specs::capacity(root as nat),
))]
pub(super) fn root_layout(root: usize) -> TableLayout {
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::usize_shift_capacity(root);
        huffman_proofs::capacity_positive(root as nat);
    }
    TableLayout {
        next: 0,
        width: root,
        used: 1 << root,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_layout(layout), drop < length <= max <= 15,
        previous_size == huffman_specs::capacity(layout.width as nat),
        layout.used <= usize::MAX - 32768,
        layout.used <= u16::MAX,
    ensures valid_layout(final(layout)),
        final(layout).next == old(layout).used,
        final(layout).next <= u16::MAX,
        length - drop <= final(layout).width,
        final(layout).width + drop <= max,
        huffman_specs::chosen_width(counts@, (length - drop) as nat, drop as nat,
            max as nat, final(layout).width as nat),
        final(layout).used == old(layout).used
            + huffman_specs::capacity(final(layout).width as nat),
        result == fits_kind(kind, final(layout).used as nat),
        forall|lengths: Seq<u16>, original: Seq<u16>, position: nat|
            #[trigger] subtable_coverage_specs::source_context(lengths, original, counts@,
                position, length as nat, drop as nat, max as nat)
            ==> (forall|symbol: int| #[trigger] subtable_coverage_specs::in_root(lengths,
                    symbol, drop as nat,
                    huffman_specs::normalized_cursor(original, length as nat, position))
                ==> lengths[symbol] <= final(layout).width + drop),
))]
pub(super) fn advance_layout(
    layout: &mut TableLayout,
    counts: &[u16; 16],
    length: usize,
    drop: usize,
    max: usize,
    kind: &CodeType,
    previous_size: usize,
) -> bool {
    layout.next += previous_size;
    layout.width = subtable_width(counts, length, drop, max);
    #[cfg(verus_keep_ghost)]
    proof! {
        huffman_proofs::usize_shift_capacity(layout.width);
        huffman_proofs::depth_capacity(layout.width as nat);
    }
    layout.used += 1usize << layout.width;
    if matches!(kind, CodeType::Lens) && layout.used > ENOUGH_LENS {
        return false;
    }
    if matches!(kind, CodeType::Dists) && layout.used > ENOUGH_DISTS {
        return false;
    }
    true
}

#[inline(always)]
#[allow(clippy::too_many_arguments)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_layout(layout), 1 <= root == drop < length <= max <= 15,
        previous_size == huffman_specs::capacity(layout.width as nat),
        layout.used <= usize::MAX - 32768, layout.used <= u16::MAX,
        huffman_specs::capacity(root as nat) <= layout.used,
        prefix < huffman_specs::capacity(root as nat) <= table.len(),
    ensures valid_layout(final(layout)),
        final(layout).next == old(layout).used,
        final(layout).next <= u16::MAX,
        length - drop <= final(layout).width,
        final(layout).width + drop <= max,
        huffman_specs::chosen_width(counts@, (length - drop) as nat, drop as nat,
            max as nat, final(layout).width as nat),
        final(layout).used == old(layout).used
            + huffman_specs::capacity(final(layout).width as nat),
        result == fits_kind(kind, final(layout).used as nat),
        forall|lengths: Seq<u16>, original: Seq<u16>, position: nat|
            #[trigger] subtable_coverage_specs::source_context(lengths, original, counts@,
                position, length as nat, root as nat, max as nat)
            ==> (forall|symbol: int| #[trigger] subtable_coverage_specs::in_root(lengths,
                    symbol, root as nat,
                    huffman_specs::normalized_cursor(original, length as nat, position))
                ==> lengths[symbol] <= root + final(layout).width),
        huffman_specs::subtable_link_result(old(table)@, final(table)@,
            prefix as nat, root as nat, old(layout).used as nat,
            final(layout).next as nat, final(layout).width as nat,
            final(layout).used as nat, result),
        result ==> (forall|pages: Seq<Option<table_pages_specs::Page>>|
            #[trigger] table_pages_specs::valid(root as nat, max as nat,
                old(layout).used as int, pages) && pages[prefix as int] == None
            ==> table_pages_specs::valid(root as nat, max as nat,
                final(layout).used as int, pages.update(prefix as int,
                    Some(table_pages_specs::Page {
                        base: final(layout).next as int, width: final(layout).width as nat,
                    })))),
        result ==> (forall|lengths: Seq<u16>, original: Seq<u16>, position: nat, symbol: int|
            #[trigger] page_source_specs::context(lengths, original, root as nat, max as nat,
                prefix as int, page_source_specs::Opening {
                    symbol, position, length: length as nat, remaining: counts@,
                }) ==> page_source_specs::valid_window(lengths, original, root as nat,
                    max as nat, prefix as int, final(layout).width as nat,
                    page_source_specs::Opening {
                        symbol, position, length: length as nat, remaining: counts@,
                    })),
        result ==> (forall|alphabet: huffman_specs::Alphabet, lengths: Seq<u16>,
                work: Seq<u16>, processed: nat,
                pages: Seq<Option<table_pages_specs::Page>>, original: Seq<Code>|
            #[trigger] crate::constructor_table_specs::progress(alphabet, lengths,
                work, processed, root as nat, old(layout).used as int,
                pages, original, old(table)@)
                && pages[prefix as int] == None && final(layout).used <= old(table).len()
            ==> crate::constructor_table_specs::progress(alphabet, lengths, work,
                processed, root as nat, final(layout).used as int,
                pages.update(prefix as int, Some(table_pages_specs::Page {
                    base: (final(layout).next) as int, width: final(layout).width as nat,
                })), original, final(table)@)),
        result ==> (forall|lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
                epoch: nat, pages: Seq<Option<table_pages_specs::Page>>,
                openings: Seq<Option<page_source_specs::Opening>>, symbol: int|
            crate::constructor_pages_specs::ownership(lengths, original,
                work, root as nat, max as nat, old(layout).used as int, epoch, pages, openings)
                && pages[prefix as int] == None && epoch < work.len()
                && work[epoch as int] as int == symbol
                && page_source_specs::context(lengths, original, root as nat, max as nat,
                    prefix as int, page_source_specs::Opening {
                        symbol, position: epoch, length: length as nat, remaining: counts@,
                    })
            ==> crate::constructor_pages_specs::ownership(lengths, original, work,
                root as nat, max as nat, final(layout).used as int, epoch,
                pages.update(prefix as int, Some(table_pages_specs::Page {
                    base: (final(layout).next) as int, width: final(layout).width as nat,
                })), openings.update(prefix as int, Some(page_source_specs::Opening {
                    symbol, position: epoch, length: length as nat, remaining: counts@,
                })))),
))]
pub(super) fn advance_and_link(
    layout: &mut TableLayout,
    counts: &[u16; 16],
    length: usize,
    drop: usize,
    max: usize,
    kind: &CodeType,
    previous_size: usize,
    table: &mut [Code],
    root: usize,
    prefix: usize,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof_decl! {
        let ghost previous_used = layout.used;
        let ghost previous_table = table@;
    }
    if !advance_layout(layout, counts, length, drop, max, kind, previous_size) {
        return false;
    }
    table[prefix] = Code {
        op: layout.width as u8,
        bits: root as u8,
        val: layout.next as u16,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        table_pages_proofs::allocation_result(root as nat, max as nat,
            previous_used as int, layout.next as int, layout.width as nat,
            layout.used as int, prefix as int);
        page_source_proofs::opening_result(counts@, length as nat, root as nat,
            max as nat, layout.width as nat, prefix as int);
        assert(huffman_specs::subtable_link_result(previous_table, table@,
            prefix as nat, root as nat, previous_used as nat, layout.next as nat,
            layout.width as nat, layout.used as nat, true));
        assert forall|alphabet: huffman_specs::Alphabet, lengths: Seq<u16>,
                work: Seq<u16>, processed: nat,
                pages: Seq<Option<table_pages_specs::Page>>, original: Seq<Code>|
            #[trigger] crate::constructor_table_specs::progress(alphabet, lengths,
                work, processed, root as nat, previous_used as int,
                pages, original, previous_table)
                && pages[prefix as int] == None && layout.used <= previous_table.len()
            implies crate::constructor_table_specs::progress(alphabet, lengths, work,
                processed, root as nat, layout.used as int,
                pages.update(prefix as int, Some(table_pages_specs::Page {
                    base: layout.next as int, width: layout.width as nat,
                })), original, table@) by {
            reveal(crate::constructor_table_specs::progress);
            crate::constructor_table_proofs::allocated(alphabet, lengths, work, processed,
                root as nat, previous_used as int, pages, original, previous_table, table@,
                prefix as int, layout.width as nat);
        }
        assert forall|lengths: Seq<u16>, original: Seq<u16>, work: Seq<u16>,
                epoch: nat, pages: Seq<Option<table_pages_specs::Page>>,
                openings: Seq<Option<page_source_specs::Opening>>, symbol: int|
            crate::constructor_pages_specs::ownership(lengths, original,
                work, root as nat, max as nat, previous_used as int, epoch, pages, openings)
                && pages[prefix as int] == None && epoch < work.len()
                && work[epoch as int] as int == symbol
                && page_source_specs::context(lengths, original, root as nat, max as nat,
                    prefix as int, page_source_specs::Opening {
                        symbol, position: epoch, length: length as nat, remaining: counts@,
                    })
            implies crate::constructor_pages_specs::ownership(lengths, original, work,
                root as nat, max as nat, layout.used as int, epoch,
                pages.update(prefix as int, Some(table_pages_specs::Page {
                    base: layout.next as int, width: layout.width as nat,
                })), openings.update(prefix as int, Some(page_source_specs::Opening {
                    symbol, position: epoch, length: length as nat, remaining: counts@,
                }))) by {
            let opening = page_source_specs::Opening {
                symbol, position: epoch, length: length as nat, remaining: counts@,
            };
            assert(page_source_specs::valid_window(lengths, original, root as nat,
                max as nat, prefix as int, layout.width as nat, opening));
            crate::constructor_pages_proofs::allocated(lengths, original, work,
                root as nat, max as nat, previous_used as int, epoch, pages, openings,
                prefix as int, layout.width as nat, opening);
        }
    }
    true
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn source_opening_fixture_constructs_both_owned_pages() {
        let sentinel = Code {
            op: 255,
            bits: 15,
            val: u16::MAX,
        };
        let mut table = [sentinel; 12];
        let mut work = [u16::MAX; 6];
        let result = super::super::inflate_table(
            CodeType::Lens,
            &[2, 2, 3, 3, 3, 3],
            &mut table,
            2,
            &mut work,
        );
        assert!(matches!(
            result,
            super::super::InflateTable::Success { root: 2, used: 8 }
        ));
        assert_eq!(work, [0, 1, 2, 3, 4, 5]);
        let expected = [
            (0, 2, 0),
            (1, 2, 4),
            (0, 2, 1),
            (1, 2, 6),
            (0, 1, 2),
            (0, 1, 3),
            (0, 1, 4),
            (0, 1, 5),
        ];
        for (index, (op, bits, val)) in expected.into_iter().enumerate() {
            assert_eq!(table[index], Code { op, bits, val });
        }
        assert_eq!(table[8..], [sentinel; 4]);
    }

    #[test]
    fn capacity_checks_preserve_the_exact_new_region_at_the_boundary() {
        for (kind, limit) in [
            (CodeType::Lens, ENOUGH_LENS),
            (CodeType::Dists, ENOUGH_DISTS),
        ] {
            for excess in [0, 1] {
                let mut layout = TableLayout {
                    next: limit - 12 + excess,
                    width: 2,
                    used: limit - 8 + excess,
                };
                let old_used = layout.used;
                let accepted = advance_layout(&mut layout, &[0; 16], 4, 1, 4, &kind, 4);
                assert_eq!(accepted, excess == 0);
                assert_eq!(
                    (layout.next, layout.width, layout.used),
                    (old_used, 3, limit + excess)
                );
            }
        }
    }

    #[test]
    fn code_length_tables_preserve_the_existing_uncapped_policy() {
        for kind in [CodeType::Codes, CodeType::Lens, CodeType::Dists] {
            let mut layout = root_layout(1);
            let accepted = advance_layout(&mut layout, &[0; 16], 15, 0, 15, &kind, 2);
            assert_eq!(accepted, matches!(kind, CodeType::Codes));
            assert_eq!((layout.next, layout.width, layout.used), (2, 15, 32770));
        }
    }

    #[test]
    fn successive_links_use_absolute_adjacent_regions_and_preserve_other_cells() {
        let sentinel = Code {
            op: 64,
            bits: 1,
            val: 99,
        };
        let mut table = [sentinel; 16];
        let mut layout = root_layout(2);
        assert!(advance_and_link(
            &mut layout,
            &[0; 16],
            3,
            2,
            3,
            &CodeType::Lens,
            4,
            &mut table,
            2,
            1
        ));
        assert_eq!((layout.next, layout.width, layout.used), (4, 1, 6));
        assert_eq!(
            table[1],
            Code {
                op: 1,
                bits: 2,
                val: 4
            }
        );
        assert!(advance_and_link(
            &mut layout,
            &[0; 16],
            4,
            2,
            4,
            &CodeType::Lens,
            2,
            &mut table,
            2,
            3
        ));
        assert_eq!((layout.next, layout.width, layout.used), (6, 2, 10));
        assert_eq!(
            table[3],
            Code {
                op: 2,
                bits: 2,
                val: 6
            }
        );
        for (index, entry) in table.iter().enumerate() {
            if index != 1 && index != 3 {
                assert_eq!(*entry, sentinel);
            }
        }
    }

    #[test]
    fn link_capacity_rejection_keeps_the_entire_table_untouched() {
        for (kind, limit) in [
            (CodeType::Lens, ENOUGH_LENS),
            (CodeType::Dists, ENOUGH_DISTS),
        ] {
            for excess in [0, 1] {
                let sentinel = Code {
                    op: 64,
                    bits: 1,
                    val: 99,
                };
                let mut table = vec![sentinel; limit + 1];
                let original = table.clone();
                let mut layout = TableLayout {
                    next: limit - 12 + excess,
                    width: 2,
                    used: limit - 8 + excess,
                };
                let accepted =
                    advance_and_link(&mut layout, &[0; 16], 4, 1, 4, &kind, 4, &mut table, 1, 1);
                assert_eq!(accepted, excess == 0);
                assert_eq!(
                    (layout.next, layout.width, layout.used),
                    (limit - 8 + excess, 3, limit + excess)
                );
                if accepted {
                    assert_eq!(
                        table[1],
                        Code {
                            op: 3,
                            bits: 1,
                            val: (limit - 8) as u16
                        }
                    );
                    for (index, entry) in table.iter().enumerate() {
                        if index != 1 {
                            assert_eq!(*entry, sentinel);
                        }
                    }
                } else {
                    assert_eq!(table, original);
                }
            }
        }
    }
}
