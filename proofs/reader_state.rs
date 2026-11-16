use crate::{bit_proofs, bit_specs as bits, header_loop_specs as registers};
use vstd::prelude::*;

verus! {

pub(crate) proof fn clean_cache_bound(word: u64, count: u8, width: u8)
    requires count <= width < 64, bits::cached_suffix(word, count, Seq::empty()),
    ensures word < (1u64 << width),
    decreases 63 - width,
{
    reveal(bits::cached_suffix);
    assert(!bits::word_bit(word, width as nat));
    if width == 63 {
        assert(word < (1u64 << width)) by (bit_vector)
            requires width == 63, (word >> width) & 1 != 1;
    } else {
        clean_cache_bound(word, count, (width + 1) as u8);
        assert(word < (1u64 << width)) by (bit_vector)
            requires width < 63, word < (1u64 << ((width + 1) as u8)),
                (word >> width) & 1 != 1;
    }
}

pub(crate) proof fn unused_byte_rewind_budget(initial_count: nat, advanced: nat,
    consumed: nat, final_count: nat)
    requires initial_count < 8,
        final_count + consumed == initial_count + 8 * advanced,
    ensures final_count / 8 <= advanced,
{
    assert(final_count < 8 * (advanced + 1));
}

pub(crate) proof fn clean_cache_retarget(word: u64, count: u8, pending: Seq<bool>)
    requires count <= 64, bits::cached_suffix(word, count, Seq::empty()),
    ensures bits::cached_suffix(word, count, pending),
{
    reveal(bits::cached_suffix);
    assert forall|index: nat| count <= index < 64
        && #[trigger] bits::word_bit(word, index) implies
        index - count < pending.len() && pending[(index - count) as int] by {
        assert(index - count < Seq::<bool>::empty().len());
    }
}

pub(crate) proof fn exact_fill_clean(before: u64, count: u8, after: u64, added: Seq<bool>)
    requires count <= 64, count as int + added.len() <= 64,
        bits::cached_suffix(before, count, Seq::empty()),
        bits::filled_word(before, count, after, added),
    ensures bits::cached_suffix(after, (count as int + added.len()) as u8, Seq::empty()),
{
    reveal(bits::cached_suffix);
    let total = (count as int + added.len()) as u8;
    assert forall|index: nat| total <= index < 64 implies
        !(#[trigger] bits::word_bit(after, index)) by {
        assert(index >= count);
        assert(!bits::word_bit(before, index));
        assert(index - count >= added.len());
    }
}

pub(crate) proof fn bounded_read_clean(before: u64, count: u8, after: u64,
    final_count: u8, added: Seq<bool>, dropped: u8)
    requires count <= 64, count as int + added.len() <= 64,
        dropped < 64, dropped <= count as int + added.len(),
        final_count as int == count as int + added.len() - dropped,
        bits::cached_suffix(before, count, Seq::empty()),
        exists|loaded: u64| #[trigger] bits::filled_word(before, count, loaded, added)
            && after == loaded >> dropped,
    ensures final_count <= 64, bits::cached_suffix(after, final_count, Seq::empty()),
{
    let loaded = choose|loaded: u64| #[trigger] bits::filled_word(before, count, loaded, added)
        && after == loaded >> dropped;
    let total = (count as int + added.len()) as u8;
    exact_fill_clean(before, count, loaded, added);
    bit_proofs::cached_consume(loaded, total, dropped, Seq::empty());
}

pub(crate) proof fn register_step_clean(before: registers::State, after: registers::State,
    pending: Seq<bool>)
    requires before.count <= 64, registers::register_step(before, after, pending),
        bits::cached_suffix(before.word, before.count, Seq::empty()),
    ensures after.count <= 64, bits::cached_suffix(after.word, after.count, Seq::empty()),
{
    reveal(registers::register_step);
    let added = pending.subrange(8 * before.advanced as int, 8 * after.advanced as int);
    let dropped = (after.dropped - before.dropped) as u8;
    bounded_read_clean(before.word, before.count, after.word, after.count, added, dropped);
}

pub(crate) proof fn register_path_clean(path: Seq<registers::State>, pending: Seq<bool>,
    position: nat)
    requires path.len() > 0, registers::register_path(path, pending),
        position < path.len(), path[0].count <= 64,
        bits::cached_suffix(path[0].word, path[0].count, Seq::empty()),
    ensures path[position as int].count <= 64,
        bits::cached_suffix(path[position as int].word, path[position as int].count, Seq::empty()),
    decreases position,
{
    reveal(registers::register_path);
    if position > 0 {
        register_path_clean(path, pending, (position - 1) as nat);
        let previous = (position - 1) as int;
        assert(0 <= previous < path.len() - 1);
        assert(registers::register_step(path[previous], path[previous + 1], pending));
        register_step_clean(path[(position - 1) as int], path[position as int], pending);
    }
}

pub(crate) proof fn register_path_retarget(path: Seq<registers::State>, pending: Seq<bool>,
    next_pending: Seq<bool>)
    requires path.len() > 0, registers::register_path(path, pending),
        path[0].count <= 64,
        bits::cached_suffix(path[0].word, path[0].count, Seq::empty()),
    ensures path.last().count <= 64,
        bits::cached_suffix(path.last().word, path.last().count, next_pending),
{
    register_path_clean(path, pending, (path.len() - 1) as nat);
    clean_cache_retarget(path.last().word, path.last().count, next_pending);
}

}
