use crate::bit_specs as model;
use vstd::prelude::*;

verus! {

pub proof fn alignment(count: u8)
    ensures count & 7 == count as int % 8,
        count & 7 <= count,
        count & 7 < 8,
        count as int - (count & 7) as int == 8 * (count as int / 8),
{
    assert(count & 7 == (count % 8) as u8
        && count & 7 <= count && count & 7 < 8) by (bit_vector);
}

pub proof fn shift_compose(word: u64, first: u64, second: u64)
    requires (first as int + second as int) < 64,
    ensures ((word >> first) >> second == word >> ((first + second) as u64)),
{
    assert((word >> first) >> second == word >> ((first + second) as u64))
        by (bit_vector) requires (first as int + second as int) < 64;
}

pub proof fn shifted_buffer(word: u64, count: u8, take: u8)
    requires count <= 64, take <= count, take < 64,
    ensures model::buffered_bits(word >> take, (count - take) as u8)
        == model::buffered_bits(word, count).subrange(take as int, count as int),
{
    let remaining = (count - take) as u8;
    let after = model::buffered_bits(word >> take, remaining);
    let expected = model::buffered_bits(word, count).subrange(take as int, count as int);
    assert forall|index: int| 0 <= index < remaining implies
        #[trigger] after[index] == expected[index] by {
        shift_compose(word, take as u64, index as u64);
    }
    assert(after =~= expected);
}

pub proof fn appended_buffer(word: u64, count: u8, read: u64, added: u8)
    requires count < 64, count as int + added as int <= 64,
    ensures model::append_compatible(word, count, read, added) ==>
        model::buffered_bits(word | (read << count), (count + added) as u8)
            == model::buffered_bits(word, count) + model::buffered_bits(read, added),
{
    if model::append_compatible(word, count, read, added) {
        let combined = word | (read << count);
        let after = model::buffered_bits(combined, (count + added) as u8);
        let expected = model::buffered_bits(word, count) + model::buffered_bits(read, added);
        let width = count as u64;
        assert(after.len() == count as int + added as int);
        assert(expected.len() == count as int + added as int);
        assert forall|index: int| 0 <= index < count as int + added as int implies
            #[trigger] after[index] == expected[index] by {
            let position = index as u64;
            if index < count {
                assert(((combined >> position) & 1) == ((word >> position) & 1))
                    by (bit_vector) requires position < width < 64,
                        combined == word | (read << width);
            } else {
                let offset = (index - count as int) as u64;
                assert(offset < added);
                assert(index as nat == count as nat + offset as nat);
                assert(model::word_bit(word, count as nat + offset as nat)
                    ==> model::word_bit(read, offset as nat));
                assert(model::word_bit(word, index as nat)
                    ==> model::word_bit(read, offset as nat));
                assert(((combined >> position) & 1) == ((read >> offset) & 1))
                    by (bit_vector) requires width < 64, position < 64, offset < 64,
                        position == (width + offset) as u64,
                        combined == word | (read << width),
                        ((word >> position) & 1 == 1) ==> ((read >> offset) & 1 == 1);
            }
        }
        assert(after =~= expected);
    }
}

pub proof fn zero_cache_compatible(count: u8, read: u64, added: u8)
    requires count as int + added as int <= 64,
    ensures model::append_compatible(0, count, read, added),
{
    assert forall|index: nat| index < added
        && #[trigger] model::word_bit(0, count as nat + index) implies model::word_bit(read, index) by {
        let position = (count as nat + index) as u64;
        assert((0u64 >> position) & 1 == 0) by (bit_vector);
    }
}

pub proof fn cached_append(word: u64, count: u8, read: u64, added: u8, pending: Seq<bool>)
    requires count < 64, count as int + added as int <= 64,
        added <= pending.len(),
        model::cached_suffix(word, count, pending),
        model::read_agrees(read, pending),
        model::buffered_bits(read, added) == pending.take(added as int),
    ensures model::append_compatible(word, count, read, added),
        model::buffered_bits(word | (read << count), (count + added) as u8)
            == model::buffered_bits(word, count) + pending.take(added as int),
        model::cached_suffix(word | (read << count), (count + added) as u8,
            pending.skip(added as int)),
{
    reveal(model::cached_suffix);
    assert forall|index: nat| index < added
        && #[trigger] model::word_bit(word, count as nat + index) implies
        model::word_bit(read, index) by {
        assert(count as nat + index < 64);
        assert(model::word_bit(word, count as nat + index) ==> pending[index as int]);
        assert(model::buffered_bits(read, added)[index as int] == pending[index as int]);
    }
    appended_buffer(word, count, read, added);
    let combined = word | (read << count);
    let new_count = (count + added) as u8;
    assert forall|index: nat| new_count <= index < 64
        && #[trigger] model::word_bit(combined, index) implies
        index - new_count < pending.skip(added as int).len()
            && pending.skip(added as int)[(index - new_count) as int] by {
        let position = index as u64;
        let width = count as u64;
        let offset = (index - count) as u64;
        assert(((combined >> position) & 1 == 1) == (
            ((word >> position) & 1 == 1) || ((read >> offset) & 1 == 1)))
            by (bit_vector) requires width <= position < 64, width < 64,
                offset == (position - width) as u64, combined == word | (read << width);
        assert(model::word_bit(word, index) || model::word_bit(read, (index - count) as nat));
        if model::word_bit(word, index) {
            assert(index - count < pending.len() && pending[(index - count) as int]);
        } else {
            assert(model::word_bit(read, (index - count) as nat));
            assert(index - count < pending.len() && pending[(index - count) as int]);
        }
    }
}

pub proof fn byte_read_agrees(byte: u8, pending: Seq<bool>)
    requires pending.len() >= 8,
        model::buffered_bits(byte as u64, 8) == pending.take(8),
    ensures model::read_agrees(byte as u64, pending),
{
    assert forall|index: nat| index < 64
        && #[trigger] model::word_bit(byte as u64, index) implies
        index < pending.len() && pending[index as int] by {
        if index < 8 {
            assert(model::buffered_bits(byte as u64, 8)[index as int] == pending[index as int]);
        } else {
            let position = index as u64;
            assert(((byte as u64) >> position) & 1 == 0) by (bit_vector)
                requires 8 <= position < 64;
        }
    }
}

pub proof fn full_read_agrees(read: u64, pending: Seq<bool>, added: u8)
    requires pending.len() >= 64, added <= 64,
        model::buffered_bits(read, 64) == pending.take(64),
    ensures model::read_agrees(read, pending),
        model::buffered_bits(read, added) == pending.take(added as int),
{
    assert forall|index: nat| index < 64
        && #[trigger] model::word_bit(read, index) implies
        index < pending.len() && pending[index as int] by {
        assert(model::buffered_bits(read, 64)[index as int] == pending[index as int]);
    }
    assert(model::buffered_bits(read, added) =~= pending.take(added as int));
}

pub proof fn cached_consume(word: u64, count: u8, take: u8, pending: Seq<bool>)
    requires count <= 64, take <= count, take < 64,
        model::cached_suffix(word, count, pending),
    ensures model::cached_suffix(word >> take, (count - take) as u8, pending),
{
    reveal(model::cached_suffix);
    assert forall|index: nat| (count - take) <= index < 64
        && #[trigger] model::word_bit(word >> take, index) implies
        index - (count - take) < pending.len()
            && pending[(index - (count - take)) as int] by {
        let position = index as u64;
        let shift = take as u64;
        if index + take < 64 {
            shift_compose(word, shift, position);
            assert(model::word_bit(word, (index + take) as nat));
        } else {
            assert(((word >> shift) >> position) & 1 == 0) by (bit_vector)
                requires shift < 64, position < 64, shift as int + position as int >= 64;
        }
    }
}

pub proof fn empty_cache(count: u8, pending: Seq<bool>)
    requires count <= 64,
    ensures model::cached_suffix(0, count, pending),
{
    reveal(model::cached_suffix);
    assert forall|index: nat| count <= index < 64
        && #[trigger] model::word_bit(0, index) implies
        index - count < pending.len() && pending[(index - count) as int] by {
        let position = index as u64;
        assert((0u64 >> position) & 1 == 0) by (bit_vector);
    }
}

pub proof fn needed_bytes_bounds(count: u8, target: usize)
    requires count <= 64, target <= 64,
    ensures model::needed_bytes(count, target) <= 8,
        (model::needed_bytes(count, target) == 0) == (target <= count),
        count as int + 8 * model::needed_bytes(count, target) >= target,
        model::needed_bytes(count, target) > 0 ==>
            count as int + 8 * (model::needed_bytes(count, target) - 1) < target,
{
}

pub proof fn filled_word_composes(before: u64, count: u8, middle: u64, after: u64,
    first: Seq<bool>, second: Seq<bool>)
    requires count as nat + first.len() + second.len() <= 64,
        model::filled_word(before, count, middle, first),
        model::filled_word(middle, (count as nat + first.len()) as u8, after, second),
    ensures model::filled_word(before, count, after, first + second),
{
    let boundary = (count as nat + first.len()) as u8;
    let combined = first + second;
    assert forall|index: nat| index < 64 implies #[trigger] model::word_bit(after, index)
        == (model::word_bit(before, index)
            || (count <= index && index - count < combined.len()
                && combined[(index - count) as int])) by {
        assert(model::word_bit(middle, index)
            == (model::word_bit(before, index)
                || (count <= index && index - count < first.len()
                    && first[(index - count) as int])));
        assert(model::word_bit(after, index)
            == (model::word_bit(middle, index)
                || (boundary <= index && index - boundary < second.len()
                    && second[(index - boundary) as int])));
        if index < count {
        } else if index < boundary {
            assert(combined[(index - count) as int] == first[(index - count) as int]);
        } else if index - boundary < second.len() {
            assert(combined[(index - count) as int] == second[(index - boundary) as int]);
        }
    }
}

pub proof fn needed_bytes_after_prefix(count: u8, target: usize, first: nat)
    requires count <= 64, target <= 64,
        count as nat + 8 * first <= 64,
        first <= model::needed_bytes(count, target),
    ensures first + model::needed_bytes((count as nat + 8 * first) as u8, target)
        == model::needed_bytes(count, target),
{
    needed_bytes_bounds(count, target);
    needed_bytes_bounds((count as nat + 8 * first) as u8, target);
}

pub proof fn capped_fill_after_prefix(count: u8, target: usize, first: nat, available: nat)
    requires count <= 64, target <= 64,
        count as nat + 8 * first <= 64,
        first <= model::needed_bytes(count, target), first <= available,
    ensures first + (if model::needed_bytes((count as nat + 8 * first) as u8, target)
                <= available - first {
            model::needed_bytes((count as nat + 8 * first) as u8, target)
        } else { (available - first) as nat })
        == if model::needed_bytes(count, target) <= available {
            model::needed_bytes(count, target)
        } else { available },
{
    needed_bytes_after_prefix(count, target, first);
}

pub proof fn header_fill_bounds(count: u8, target: usize)
    requires count <= 64, target <= 57,
    ensures count as int + 8 * model::needed_bytes(count, target) <= 64,
{
    needed_bytes_bounds(count, target);
}

pub proof fn filled_word_empty(before: u64, count: u8, after: u64)
    requires model::filled_word(before, count, after, Seq::empty()),
    ensures after == before,
{
    assert forall|index: u64| index < 64 implies
        #[trigger] ((after >> index) & 1) == ((before >> index) & 1) by {
        assert(model::word_bit(after, index as nat) == model::word_bit(before, index as nat));
        assert(((after >> index) & 1) == ((before >> index) & 1)) by (bit_vector)
            requires (((after >> index) & 1) == 1) == (((before >> index) & 1) == 1);
    }
    assert(after == before) by (bit_vector)
        requires forall|index: u64| index < 64 ==>
            #[trigger] ((after >> index) & 1) == ((before >> index) & 1);
}

pub proof fn input_suffix(bytes: Seq<u8>, start: int)
    requires 0 <= start <= bytes.len(),
    ensures model::input_bits(bytes.skip(start)) == model::input_bits(bytes).skip(8 * start),
{
    assert(model::input_bits(bytes.skip(start)) =~= model::input_bits(bytes).skip(8 * start));
}

pub proof fn low_first_octet_fixture()
    ensures model::input_bits(seq![0xb6u8, 0x1du8]).take(12)
        == seq![false, true, true, false, true, true, false, true, true, false, true, true],
{
    let bits = model::input_bits(seq![0xb6u8, 0x1du8]).take(12);
    let expected = seq![false, true, true, false, true, true, false, true, true, false, true, true];
    assert forall|index: int| 0 <= index < 12 implies
        #[trigger] bits[index] == expected[index] by {
        let position = index as u64;
        let octet = if position < 8 { 0xb6u64 } else { 0x1du64 };
        assert((((octet >> (position % 8)) & 1) == 1) ==
            (position == 1 || position == 2 || position == 4 || position == 5
                || position == 7 || position == 8 || position == 10 || position == 11))
            by (bit_vector) requires position < 12,
                octet == if position < 8 { 0xb6u64 } else { 0x1du64 };
        assert(index == 0 || index == 1 || index == 2 || index == 3 || index == 4 || index == 5
            || index == 6 || index == 7 || index == 8 || index == 9 || index == 10 || index == 11);
        assert(bits[index] == (((octet >> (position % 8)) & 1) == 1));
    }
    assert(bits =~= expected);
}

pub proof fn input_byte_step(bytes: Seq<u8>, index: int)
    requires 0 <= index < bytes.len(),
    ensures model::input_bits(bytes).skip(8 * index).take(8)
            == model::buffered_bits(bytes[index] as u64, 8),
        model::input_bits(bytes).take(8 * (index + 1))
            == model::input_bits(bytes).take(8 * index)
                + model::buffered_bits(bytes[index] as u64, 8),
        model::input_bits(bytes).skip(8 * index).skip(8)
            == model::input_bits(bytes).skip(8 * (index + 1)),
{
    let bits = model::input_bits(bytes);
    let byte = model::buffered_bits(bytes[index] as u64, 8);
    assert(bits.skip(8 * index).take(8) =~= byte);
    assert(bits.take(8 * (index + 1)) =~= bits.take(8 * index) + byte);
    assert(bits.skip(8 * index).skip(8) =~= bits.skip(8 * (index + 1)));
}

pub proof fn filled_word_step(before: u64, start: u8, word: u64, count: u8,
    prefix: Seq<bool>, byte: u8)
    requires count as int == start as int + prefix.len(),
        count <= 56, model::filled_word(before, start, word, prefix),
    ensures model::filled_word(before, start, word | ((byte as u64) << count),
        prefix + model::buffered_bits(byte as u64, 8)),
{
    let after = word | ((byte as u64) << count);
    let added = prefix + model::buffered_bits(byte as u64, 8);
    assert forall|index: nat| index < 64 implies #[trigger] model::word_bit(after, index)
        == (model::word_bit(before, index)
            || (start <= index && index - start < added.len() && added[(index - start) as int])) by {
        let position = index as u64;
        let width = count as u64;
        if index < count {
            assert(((after >> position) & 1) == ((word >> position) & 1))
                by (bit_vector) requires position < width < 64,
                    after == word | ((byte as u64) << width);
        } else if index < count as nat + 8 {
            let offset = (index - count) as u64;
            assert(((after >> position) & 1 == 1) == (((word >> position) & 1 == 1)
                || (((byte as u64) >> offset) & 1 == 1))) by (bit_vector)
                requires width <= position < 64, width < 64, offset == (position - width) as u64,
                    after == word | ((byte as u64) << width);
        } else {
            assert(((after >> position) & 1) == ((word >> position) & 1))
                by (bit_vector) requires width < 64, position < 64,
                    position as int >= width as int + 8,
                    after == word | ((byte as u64) << width);
        }
        assert(model::word_bit(word, index)
            == (model::word_bit(before, index)
                || (start <= index && index - start < prefix.len()
                    && prefix[(index - start) as int])));
    }
}

pub proof fn three_bit_word(word: u64, count: u8)
    requires 3 <= count <= 64,
    ensures (word & 7) as u16 == model::three_bit_value(model::buffered_bits(word, count)),
{
    assert(word >> 0u64 == word && word & 7 <= 7) by (bit_vector);
    let bits = model::buffered_bits(word, count);
    assert(bits[0] == (word & 1 == 1));
    assert(bits[1] == ((word >> 1u64) & 1 == 1));
    assert(bits[2] == ((word >> 2u64) & 1 == 1));
    assert(word & 7 == (if word & 1 == 1 { 1u64 } else { 0u64 })
        + (if (word >> 1) & 1 == 1 { 2u64 } else { 0u64 })
        + (if (word >> 2) & 1 == 1 { 4u64 } else { 0u64 })) by (bit_vector);
}

pub proof fn low_field_step(word: u64, width: u8)
    requires 1 <= width < 64,
    ensures (word & (((1u64 << width) - 1) as u64)) as nat
        == (word & 1) as nat
            + 2 * (((word >> 1u64) & (((1u64 << ((width - 1) as u8)) - 1) as u64)) as nat),
{
    let low = word & 1;
    let rest = (word >> 1u64) & (((1u64 << ((width - 1) as u8)) - 1) as u64);
    let result = word & (((1u64 << width) - 1) as u64);
    assert(result as u128 == low as u128 + 2u128 * rest as u128) by (bit_vector)
        requires 1 <= width < 64, low == word & 1,
            rest == (word >> 1u64) & (((1u64 << ((width - 1) as u8)) - 1) as u64),
            result == word & (((1u64 << width) - 1) as u64);
}

pub proof fn buffered_value(word: u64, width: u8)
    requires width < 64,
    ensures model::low_first_value(model::buffered_bits(word, width))
        == (word & (((1u64 << width) - 1) as u64)) as nat,
    decreases width,
{
    if width == 0 {
        assert(word & (((1u64 << 0u8) - 1) as u64) == 0) by (bit_vector);
    } else {
        shifted_buffer(word, width, 1);
        buffered_value(word >> 1u8, (width - 1) as u8);
        low_field_step(word, width);
        assert(model::buffered_bits(word, width).skip(1)
            =~= model::buffered_bits(word >> 1u8, (width - 1) as u8));
        assert(word >> 0u64 == word && word & 1 <= 1) by (bit_vector);
    }
}

pub proof fn numeric_field(word: u64, count: u8, width: u8,
    source: Seq<bool>, pending: Seq<bool>)
    requires width < 64, width <= count <= 64,
        model::buffered_bits(word, count) + pending == source,
    ensures model::low_first_value(source.take(width as int))
        == (word & (((1u64 << width) - 1) as u64)) as nat,
{
    buffered_value(word, width);
    assert(model::buffered_bits(word, width) =~= source.take(width as int));
}

pub proof fn refill_accounting(count: u8)
    requires count < 64,
    ensures ((63u8 ^ count) >> 3) as int == (63 - count as int) / 8,
        ((63u8 ^ count) >> 3) <= 7,
        56 <= count | 56 <= 63,
        (count | 56) as int == count as int + 8 * (((63u8 ^ count) >> 3) as int),
{
    let increment = (63u8 ^ count) >> 3;
    assert(increment == ((63 - count) as u8) / 8 && increment <= 7
        && 56 <= count | 56 <= 63
        && (count | 56) as u16 == count as u16 + 8u16 * increment as u16)
        by (bit_vector) requires count < 64, increment == (63u8 ^ count) >> 3;
}

}
