use crate::huffman_proofs as facts;
use crate::huffman_specs as h;
use crate::table_pages_specs::{cells, cost, disjoint, valid, Page};
use vstd::prelude::*;

verus! {

pub proof fn uniform_cells(pages: Seq<Option<Page>>, value: int)
    requires forall|index: int| 0 <= index < pages.len() ==> cost(#[trigger] pages[index]) == value,
    ensures cells(pages) == pages.len() * value,
    decreases pages.len(),
{
    reveal(cells);
    if pages.len() > 0 {
        uniform_cells(pages.drop_last(), value);
        assert(cost(pages.last()) == value);
        assert((pages.len() - 1) * value + value == pages.len() * value) by (nonlinear_arith);
    }
}

pub proof fn bounded_cells(pages: Seq<Option<Page>>, width: nat)
    requires forall|index: int| 0 <= index < pages.len() ==>
        match #[trigger] pages[index] { None => true, Some(page) => page.width <= width },
    ensures 0 <= cells(pages) <= pages.len() * h::capacity(width),
    decreases pages.len(),
{
    reveal(cells);
    facts::capacity_positive(width);
    if pages.len() > 0 {
        bounded_cells(pages.drop_last(), width);
        match pages.last() {
            Some(page) => {
                facts::capacity_positive(page.width);
                facts::capacity_monotone(page.width, width);
            },
            None => {},
        }
        assert(0 <= cost(pages.last()) <= h::capacity(width));
        assert(cells(pages.drop_last()) + cost(pages.last()) <= pages.len() * h::capacity(width))
            by (nonlinear_arith)
            requires cells(pages.drop_last()) <= (pages.len() - 1) * h::capacity(width),
                cost(pages.last()) <= h::capacity(width);
    }
}

pub proof fn updated_cells(pages: Seq<Option<Page>>, key: int, page: Option<Page>)
    requires 0 <= key < pages.len(),
    ensures cells(pages.update(key, page)) == cells(pages) - cost(pages[key]) + cost(page),
    decreases pages.len(),
{
    reveal(cells);
    let updated = pages.update(key, page);
    if key < pages.len() - 1 {
        assert(updated.drop_last() =~= pages.drop_last().update(key, page));
        assert(updated.last() == pages.last());
        updated_cells(pages.drop_last(), key, page);
    } else {
        assert(key == pages.len() - 1);
        assert(updated.drop_last() =~= pages.drop_last());
        assert(updated.last() == page && pages[key] == pages.last());
    }
}

pub proof fn budget(root: nat, max: nat, used: int, pages: Seq<Option<Page>>)
    requires valid(root, max, used, pages),
    ensures h::capacity(root) <= used <= 49152, used <= u16::MAX,
        root == max ==> used == h::capacity(root),
{
    bounded_cells(pages, (max - root) as nat);
    if root == max {
        assert forall|index: int| 0 <= index < pages.len() implies
            cost(#[trigger] pages[index]) == 0 by {
            match pages[index] {
                Some(page) => { assert(1 <= page.width && page.width + root <= max); },
                None => {},
            }
        }
        uniform_cells(pages, 0);
        facts::capacity_monotone(root, 15);
        assert(h::capacity(15) == 32768) by (compute);
    } else {
        facts::capacity_product(root, (max - root) as nat);
        facts::capacity_monotone(root, 14);
        facts::capacity_monotone(max, 15);
        assert(h::capacity(14) == 16384 && h::capacity(15) == 32768) by (compute);
    }
}

pub proof fn initial(root: nat, max: nat)
    requires 1 <= root <= max <= 15,
    ensures valid(root, max, h::capacity(root),
        Seq::new(h::capacity(root) as nat, |index: int| None)),
{
    facts::capacity_positive(root);
    let pages = Seq::<Option<Page>>::new(h::capacity(root) as nat, |index: int| None);
    uniform_cells(pages, 0);
}

pub proof fn allocated(root: nat, max: nat, used: int, pages: Seq<Option<Page>>,
    key: int, width: nat)
    requires valid(root, max, used, pages), 0 <= key < pages.len(), pages[key] == None,
        1 <= width && width + root <= max,
    ensures valid(root, max, used + h::capacity(width),
        pages.update(key, Some(Page { base: used, width }))),
{
    budget(root, max, used, pages);
    facts::capacity_positive(width);
    let page = Page { base: used, width };
    let updated = pages.update(key, Some(page));
    updated_cells(pages, key, Some(page));
    assert forall|index: int| 0 <= index < updated.len() implies
        match #[trigger] updated[index] {
            None => true,
            Some(entry) => 1 <= entry.width && entry.width + root <= max
                && h::capacity(root) <= entry.base
                && entry.base + h::capacity(entry.width) <= used + h::capacity(width),
        } by {
        if index != key { assert(updated[index] == pages[index]); }
    }
    assert forall|first: int, second: int| 0 <= first < second < updated.len() implies
        match (#[trigger] updated[first], #[trigger] updated[second]) {
            (Some(left), Some(right)) => disjoint(left, right),
            _ => true,
        } by {
        if first == key {
            assert(updated[second] == pages[second]);
            match pages[second] {
                Some(other) => { assert(other.base + h::capacity(other.width) <= used); },
                None => {},
            }
        } else if second == key {
            assert(updated[first] == pages[first]);
            match pages[first] {
                Some(other) => { assert(other.base + h::capacity(other.width) <= used); },
                None => {},
            }
        } else {
            assert(updated[first] == pages[first] && updated[second] == pages[second]);
        }
    }
}

pub proof fn allocation_result(root: nat, max: nat, before: int, next: int,
    width: nat, after: int, key: int)
    requires 1 <= root < max <= 15, 1 <= width, width + root <= max,
        next == before, after == before + h::capacity(width),
        0 <= key < h::capacity(root),
    ensures forall|pages: Seq<Option<Page>>|
        #[trigger] valid(root, max, before, pages) && pages[key] == None
        ==> valid(root, max, after, pages.update(key, Some(Page { base: next, width }))),
{
    assert forall|pages: Seq<Option<Page>>|
        #[trigger] valid(root, max, before, pages) && pages[key] == None
        implies valid(root, max, after, pages.update(key, Some(Page { base: next, width }))) by {
        allocated(root, max, before, pages, key, width);
    }
}

pub proof fn independent_page_order()
    ensures valid(2, 3, 12, seq![
        Some(Page { base: 4, width: 1 }), Some(Page { base: 8, width: 1 }),
        Some(Page { base: 6, width: 1 }), Some(Page { base: 10, width: 1 })]),
{
    assert(h::capacity(2) == 4 && h::capacity(1) == 2) by (compute);
    initial(2, 3);
    let zero = Seq::<Option<Page>>::new(4, |index: int| None);
    allocated(2, 3, 4, zero, 0, 1);
    let one = zero.update(0, Some(Page { base: 4, width: 1 }));
    allocated(2, 3, 6, one, 2, 1);
    let two = one.update(2, Some(Page { base: 6, width: 1 }));
    allocated(2, 3, 8, two, 1, 1);
    let three = two.update(1, Some(Page { base: 8, width: 1 }));
    allocated(2, 3, 10, three, 3, 1);
    assert(three.update(3, Some(Page { base: 10, width: 1 })) =~= seq![
        Some(Page { base: 4, width: 1 }), Some(Page { base: 8, width: 1 }),
        Some(Page { base: 6, width: 1 }), Some(Page { base: 10, width: 1 })]);
}

pub proof fn independent_maximum_budget()
    ensures valid(14, 15, 49152,
        Seq::new(16384, |index: int| Some(Page { base: 16384 + 2 * index, width: 1 }))),
        valid(15, 15, 32768, Seq::new(32768, |index: int| None)),
{
    assert(h::capacity(14) == 16384 && h::capacity(15) == 32768
        && h::capacity(1) == 2) by (compute);
    let pages = Seq::new(16384, |index: int| Some(Page { base: 16384 + 2 * index, width: 1 }));
    uniform_cells(pages, 2);
    initial(15, 15);
}

}
