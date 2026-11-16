use crate::huffman_specs as h;
use vstd::prelude::*;

verus! {

// Physical Code-cell ownership by root slot, not numeric allocation order.
pub struct Page {
    pub base: int,
    pub width: nat,
}

pub open spec fn cost(page: Option<Page>) -> int {
    match page { None => 0, Some(page) => h::capacity(page.width) }
}

#[verifier::opaque]
pub open spec fn cells(pages: Seq<Option<Page>>) -> int
    decreases pages.len(),
{
    if pages.len() == 0 { 0 }
    else { cells(pages.drop_last()) + cost(pages.last()) }
}

pub open spec fn disjoint(first: Page, second: Page) -> bool {
    first.base + h::capacity(first.width) <= second.base
        || second.base + h::capacity(second.width) <= first.base
}

pub open spec fn valid(root: nat, max: nat, used: int, pages: Seq<Option<Page>>) -> bool {
    1 <= root <= max <= 15 && pages.len() == h::capacity(root)
        && used == h::capacity(root) + cells(pages)
        && (forall|index: int| 0 <= index < pages.len() ==>
            match #[trigger] pages[index] {
                None => true,
                Some(page) => 1 <= page.width && page.width + root <= max
                    && h::capacity(root) <= page.base
                    && page.base + h::capacity(page.width) <= used,
            })
        && (forall|first: int, second: int| 0 <= first < second < pages.len() ==>
            match (#[trigger] pages[first], #[trigger] pages[second]) {
                (Some(left), Some(right)) => disjoint(left, right),
                _ => true,
            })
}

}
