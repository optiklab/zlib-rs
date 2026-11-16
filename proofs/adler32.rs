use crate::specs;
use vstd::arithmetic::div_mod::*;
use vstd::prelude::*;

verus! {

pub proof fn pack(a: u32, b: u32)
    requires a < 65521, b < 65521,
    ensures (a | (b << 16)) as int == b as int * 65536 + a as int,
{
    assert(a | (b << 16) == b * 65536 + a) by (bit_vector)
        requires a < 65521, b < 65521;
}

pub proof fn single_byte(bytes: Seq<u8>)
    requires bytes.len() == 1,
    ensures specs::byte_sum(bytes) == bytes[0] as int,
        specs::weighted_sum(bytes) == bytes[0] as int,
{
    assert(bytes.drop_last() == Seq::<u8>::empty());
    assert(bytes.last() == bytes[0]);
    reveal_with_fuel(specs::byte_sum, 2);
    reveal_with_fuel(specs::weighted_sum, 2);
}

pub proof fn split(value: u32)
    ensures
        ((value as u64) & 0xffff) as int == specs::low(value),
        (((value as u64) >> 16) & 0xffff) as int == specs::high(value),
{
    assert(((value as u64) & 0xffff) == (value & 0xffff) as u64) by (bit_vector);
    assert((((value as u64) >> 16) & 0xffff) == ((value >> 16) & 0xffff) as u64)
        by (bit_vector);
}

pub proof fn mod_add(a: int, b: int)
    ensures (a + b % 65521) % 65521 == (a + b) % 65521,
{
    lemma_add_mod_noop_right(a, b, 65521);
}

pub proof fn prefix_step(bytes: Seq<u8>, i: int)
    requires 0 <= i < bytes.len(),
    ensures
        specs::byte_sum(bytes.take(i + 1))
            == specs::byte_sum(bytes.take(i)) + bytes[i] as int,
        specs::weighted_sum(bytes.take(i + 1))
            == specs::weighted_sum(bytes.take(i)) + specs::byte_sum(bytes.take(i + 1)),
{
    assert(bytes.take(i + 1).drop_last() == bytes.take(i));
    assert(bytes.take(i + 1).last() == bytes[i]);
}

pub proof fn prefix_bounds(bytes: Seq<u8>, i: int)
    requires 0 <= i <= bytes.len(),
    ensures
        0 <= specs::byte_sum(bytes.take(i)) <= specs::byte_sum(bytes),
        0 <= specs::weighted_sum(bytes.take(i)) <= specs::weighted_sum(bytes),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        if i < bytes.len() {
            prefix_bounds(bytes.drop_last(), i);
            prefix_bounds(bytes.drop_last(), bytes.len() as int - 1);
            assert(bytes.drop_last().take(i) == bytes.take(i));
        } else {
            prefix_bounds(bytes.drop_last(), bytes.len() as int - 1);
            assert(bytes.take(i) == bytes);
        }
    }
}

pub proof fn sum_bounds(bytes: Seq<u8>)
    ensures
        0 <= specs::byte_sum(bytes) <= 255 * bytes.len(),
        0 <= 2 * specs::weighted_sum(bytes) <= 255 * bytes.len() * (bytes.len() + 1),
    decreases bytes.len(),
{
    if bytes.len() > 0 {
        sum_bounds(bytes.drop_last());
        assert(bytes.len() == bytes.drop_last().len() + 1);
        assert(255int * bytes.len() * (bytes.len() + 1)
            == 255int * (bytes.len() - 1) * bytes.len() + 510 * bytes.len())
            by (nonlinear_arith);
    }
}

// RFC 1950 section 8.2 permits delaying reduction for NMAX = 5552 bytes.
// The stronger 65535 initial bound also covers noncanonical API seeds.
pub proof fn delayed_bounds(a: int, b: int, bytes: Seq<u8>)
    requires 0 <= a <= 65535, 0 <= b <= 65535, bytes.len() <= 5552,
    ensures a + specs::byte_sum(bytes) <= u32::MAX,
        b + bytes.len() as int * a + specs::weighted_sum(bytes) <= u32::MAX,
{
    sum_bounds(bytes);
    let n = bytes.len() as int;
    assert(n * a <= 5552int * 65535) by (nonlinear_arith)
        requires 0 <= n <= 5552, 0 <= a <= 65535;
    assert(n * (n + 1) <= 5552int * 5553) by (nonlinear_arith)
        requires 0 <= n <= 5552;
    assert(255int * n * (n + 1) <= 7861715280int) by (nonlinear_arith)
        requires 0 <= n <= 5552;
}

pub proof fn concatenated_sums(left: Seq<u8>, right: Seq<u8>)
    ensures
        specs::byte_sum(left + right) == specs::byte_sum(left) + specs::byte_sum(right),
        specs::weighted_sum(left + right) == specs::weighted_sum(left)
            + right.len() as int * specs::byte_sum(left) + specs::weighted_sum(right),
    decreases right.len(),
{
    if right.len() == 0 {
        assert(left + right == left);
    } else {
        concatenated_sums(left, right.drop_last());
        assert((left + right).drop_last() == left + right.drop_last());
        assert((left + right).last() == right.last());
        assert(right.len() as int * specs::byte_sum(left)
            == right.drop_last().len() as int * specs::byte_sum(left)
                + specs::byte_sum(left)) by (nonlinear_arith)
            requires right.len() == right.drop_last().len() + 1;
    }
}

pub proof fn prefix_chunk(bytes: Seq<u8>, offset: int, count: int)
    requires 0 <= offset, 0 <= count, offset + count <= bytes.len(),
    ensures
        specs::byte_sum(bytes.take(offset + count)) == specs::byte_sum(bytes.take(offset))
            + specs::byte_sum(bytes.subrange(offset, offset + count)),
        specs::weighted_sum(bytes.take(offset + count))
            == specs::weighted_sum(bytes.take(offset))
                + count * specs::byte_sum(bytes.take(offset))
                + specs::weighted_sum(bytes.subrange(offset, offset + count)),
{
    assert(bytes.take(offset) + bytes.subrange(offset, offset + count)
        == bytes.take(offset + count));
    concatenated_sums(bytes.take(offset), bytes.subrange(offset, offset + count));
}

pub proof fn update_components(a: int, b: int, bytes: Seq<u8>)
    ensures
        0 <= specs::update(a, b, bytes) <= u32::MAX,
        specs::canonical(specs::update(a, b, bytes) as u32),
        specs::low(specs::update(a, b, bytes) as u32)
            == (a + specs::byte_sum(bytes)) % 65521,
        specs::high(specs::update(a, b, bytes) as u32)
            == (b + bytes.len() as int * a + specs::weighted_sum(bytes)) % 65521,
{
    let low = (a + specs::byte_sum(bytes)) % 65521;
    let high = (b + bytes.len() as int * a + specs::weighted_sum(bytes)) % 65521;
    lemma_mod_bound(a + specs::byte_sum(bytes), 65521);
    lemma_mod_bound(b + bytes.len() as int * a + specs::weighted_sum(bytes), 65521);
    let x = low as u32;
    let y = high as u32;
    pack(x, y);
    assert((x | (y << 16)) & 0xffff == x) by (bit_vector)
        requires x < 65521, y < 65521;
    assert(((x | (y << 16)) >> 16) & 0xffff == y) by (bit_vector)
        requires x < 65521, y < 65521;
}

pub proof fn update_modular(a: int, b: int, bytes: Seq<u8>)
    ensures specs::update(a % 65521, b % 65521, bytes) == specs::update(a, b, bytes),
{
    lemma_add_mod_noop_right(specs::byte_sum(bytes), a, 65521);
    lemma_mul_mod_noop_left(a, bytes.len() as int, 65521);
    assert(a % 65521 * bytes.len() as int == bytes.len() as int * (a % 65521))
        by (nonlinear_arith);
    assert(a * bytes.len() as int == bytes.len() as int * a) by (nonlinear_arith);
    lemma_add_mod_noop(b, bytes.len() as int * a, 65521);
    lemma_add_mod_noop(b % 65521, bytes.len() as int * (a % 65521), 65521);
    lemma_add_mod_noop_right(specs::weighted_sum(bytes), b + bytes.len() as int * a, 65521);
    lemma_add_mod_noop_right(specs::weighted_sum(bytes),
        b % 65521 + bytes.len() as int * (a % 65521), 65521);
}

pub proof fn update_concatenation(a: int, b: int, left: Seq<u8>, right: Seq<u8>)
    ensures specs::update(
        specs::low(specs::update(a, b, left) as u32),
        specs::high(specs::update(a, b, left) as u32), right)
        == specs::update(a, b, left + right),
{
    concatenated_sums(left, right);
    update_components(a, b, left);
    update_modular(a + specs::byte_sum(left),
        b + left.len() as int * a + specs::weighted_sum(left), right);
    assert((left.len() as int + right.len() as int) * a
        == left.len() as int * a + right.len() as int * a) by (nonlinear_arith);
    assert(right.len() as int * (a + specs::byte_sum(left))
        == right.len() as int * a + right.len() as int * specs::byte_sum(left))
        by (nonlinear_arith);
}

// Independent requirement-facing properties: initial value and one RFC byte step.
pub proof fn rfc_initial_value()
    ensures specs::checksum(Seq::empty()) == 1,
{}

pub proof fn rfc_byte_step(a: int, b: int, bytes: Seq<u8>, byte: u8)
    ensures specs::update(a, b, bytes.push(byte)) == specs::update(
        specs::low(specs::update(a, b, bytes) as u32),
        specs::high(specs::update(a, b, bytes) as u32), seq![byte]),
{
    update_concatenation(a, b, bytes, seq![byte]);
    assert(bytes + seq![byte] == bytes.push(byte));
}

pub proof fn rfc_three_byte_weighting(a: u8, b: u8, c: u8)
    ensures specs::checksum(seq![a, b, c])
        == ((3 + 3 * a as int + 2 * b as int + c as int) % 65521) * 65536
            + (1 + a as int + b as int + c as int) % 65521,
{
    reveal_with_fuel(specs::byte_sum, 4);
    reveal_with_fuel(specs::weighted_sum, 4);
}

pub proof fn checksum_concatenation(left: Seq<u8>, right: Seq<u8>)
    ensures specs::combine(specs::checksum(left) as u32, specs::checksum(right) as u32,
        right.len() as int) == specs::checksum(left + right),
{
    update_components(1, 0, left);
    update_components(1, 0, right);
    concatenated_sums(left, right);
    let a = specs::low(specs::checksum(left) as u32);
    let b = specs::high(specs::checksum(left) as u32);
    let c = specs::low(specs::checksum(right) as u32);
    let d = specs::high(specs::checksum(right) as u32);
    let sl = specs::byte_sum(left);
    let sr = specs::byte_sum(right);
    let bl = left.len() as int + specs::weighted_sum(left);
    let br = right.len() as int + specs::weighted_sum(right);
    let n = right.len() as int;
    lemma_add_mod_noop(1 + sl, 1 + sr, 65521);
    lemma_sub_mod_noop(a + c, 1, 65521);
    lemma_sub_mod_noop(2 + sl + sr, 1, 65521);
    lemma_sub_mod_noop(1 + sl, 1, 65521);
    lemma_mul_mod_noop_right(n, a - 1, 65521);
    lemma_mul_mod_noop_right(n, sl, 65521);
    lemma_add_mod_noop(bl, br, 65521);
    lemma_add_mod_noop(b + d, n * (a - 1), 65521);
    lemma_add_mod_noop(bl + br, n * sl, 65521);
}

pub proof fn combine_reductions(a: int, b: int, reduced_a: u64, reduced_b: u64)
    requires
        0 <= a < 3 * 65521, 0 <= b < 4 * 65521,
        reduced_a as int == if a >= 2 * 65521 { a - 2 * 65521 }
            else if a >= 65521 { a - 65521 } else { a },
        reduced_b as int == if b >= 3 * 65521 { b - 3 * 65521 }
            else if b >= 2 * 65521 { b - 2 * 65521 }
            else if b >= 65521 { b - 65521 } else { b },
    ensures reduced_a < 65521, reduced_b < 65521,
        reduced_a as int == a % 65521, reduced_b as int == b % 65521,
{
    lemma_fundamental_div_mod(a, 65521);
    lemma_fundamental_div_mod(b, 65521);
}

pub proof fn combine_formula(first: u32, second: u32, len: u64, rem: u64, a: u64, b: u64)
    requires specs::canonical(first), specs::canonical(second),
        rem as int == len as int % 65521,
        a as int == (specs::low(first) + specs::low(second) + 65521 - 1) % 65521,
        b as int == ((rem as int * specs::low(first)) % 65521
            + specs::high(first) + specs::high(second) + 65521 - rem as int) % 65521,
    ensures b as int * 65536 + a as int == specs::combine(first, second, len as int),
{
    lemma_mod_add_multiples_vanish(specs::low(first) + specs::low(second) - 1, 65521);
    lemma_add_mod_noop_right(
        specs::high(first) + specs::high(second) + 65521 - rem as int,
        rem as int * specs::low(first), 65521);
    lemma_mod_add_multiples_vanish(
        specs::high(first) + specs::high(second) + rem as int * (specs::low(first) - 1), 65521);
    assert(rem as int * specs::low(first) - rem as int
        == rem as int * (specs::low(first) - 1)) by (nonlinear_arith);
    lemma_mul_mod_noop_left(len as int, specs::low(first) - 1, 65521);
    lemma_add_mod_noop_right(specs::high(first) + specs::high(second),
        len as int * (specs::low(first) - 1), 65521);
}

}
