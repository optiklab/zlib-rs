use crate::crc_specs as model;
use vstd::prelude::*;

verus! {

pub proof fn bit_identities(value: u32)
    ensures value ^ 0 == value, 0 ^ value == value,
        value & 0 == 0, 0 & value == 0, value & u32::MAX == value,
{
    assert(value ^ 0 == value && 0 ^ value == value
        && value & 0 == 0 && 0 & value == 0 && value & u32::MAX == value)
        by (bit_vector);
}

pub open spec fn multiplication_at(a: u32, initial_b: u32, mask: u32,
    partial: u32, current_b: u32, index: nat) -> bool
{
    index <= 32 && mask == model::coefficient_mask(index)
        && current_b == model::shift_bits(initial_b, index)
        && model::product(a, initial_b) == partial ^ model::product_terms(a, initial_b, index)
}

pub open spec fn multiplication_state(a: u32, initial_b: u32, mask: u32,
    partial: u32, current_b: u32) -> bool
{
    exists|index: nat| multiplication_at(a, initial_b, mask, partial, current_b, index)
}

pub proof fn xor_reassociate(a: u32, b: u32, c: u32)
    ensures a ^ (b ^ c) == (a ^ b) ^ c,
{
    assert(a ^ (b ^ c) == (a ^ b) ^ c) by (bit_vector);
}

pub proof fn xor_commutes(a: u32, b: u32)
    ensures a ^ b == b ^ a,
{
    assert(a ^ b == b ^ a) by (bit_vector);
}

pub proof fn finish_multiplication(a: u32, initial_b: u32, mask: u32,
    partial: u32, current_b: u32)
    requires multiplication_state(a, initial_b, mask, partial, current_b), mask == 0,
    ensures model::product(a, initial_b) == partial,
{
    let index = choose|i: nat| multiplication_at(a, initial_b, mask, partial, current_b, i);
    if index < 32 {
        lower_mask(index as u32);
    }
    bit_identities(partial);
}

pub proof fn next_mask(index: u32)
    requires index < 32,
    ensures model::coefficient_mask(index as nat) >> 1
        == model::coefficient_mask(index as nat + 1),
{
    if index < 31 {
        assert((0x8000_0000u32 >> index) >> 1 == 0x8000_0000u32 >> (index + 1))
            by (bit_vector) requires index < 31;
    } else {
        assert(0x8000_0000u32 >> 31 == 1) by (bit_vector);
        assert(1u32 >> 1 == 0) by (bit_vector);
    }
}

pub proof fn lower_mask(index: u32)
    requires index < 32,
    ensures model::coefficient_mask(index as nat) > 0,
        model::coefficient_mask(index as nat) - 1
            == model::remaining_mask(index as nat + 1),
{
    assert(0x8000_0000u32 >> index > 0) by (bit_vector) requires index < 32;
    if index < 31 {
        assert((0x8000_0000u32 >> index) - 1 == 0xffff_ffffu32 >> (index + 1))
            by (bit_vector) requires index < 31;
    } else {
        assert((0x8000_0000u32 >> index) - 1 == 0) by (bit_vector) requires index == 31;
    }
}

pub proof fn shift_step(value: u32, index: nat)
    ensures model::shift_bits(value, index + 1)
        == model::times_x(model::shift_bits(value, index)),
{}

pub proof fn unfold_term(a: u32, b: u32, index: nat)
    requires index < 32,
    ensures model::product_terms(a, b, index)
        == (if a & model::coefficient_mask(index) != 0 {
            model::shift_bits(b, index)
        } else { 0 }) ^ model::product_terms(a, b, index + 1),
        model::coefficient_mask(index) > 0,
{
    lower_mask(index as u32);
}

pub proof fn zero_terms(a: u32, b: u32, index: nat)
    requires a & model::remaining_mask(index) == 0,
    ensures model::product_terms(a, b, index) == 0,
    decreases 32 - index,
{
    bit_identities(a);
    bit_identities(0);
    if index < 32 {
        let i = index as u32;
        if i < 31 {
            assert(a & (0x8000_0000u32 >> i) == 0
                && a & (u32::MAX >> (i + 1)) == 0) by (bit_vector)
                requires i < 31, a & (u32::MAX >> i) == 0;
        } else {
            assert(a & (0x8000_0000u32 >> i) == 0) by (bit_vector)
                requires i == 31, a & (u32::MAX >> i) == 0;
        }
        zero_terms(a, b, index + 1);
    }
}

pub proof fn rfc_crc_initial_value()
    ensures model::checksum_update(0, Seq::empty()) == 0,
{
    assert(!(!0u32) == 0u32) by (bit_vector);
}

pub proof fn crc_check_vector()
    ensures model::checksum_update(0, seq![49u8, 50, 51, 52, 53, 54, 55, 56, 57])
        == 0xcbf4_3926,
{
    assert(model::checksum_update(0, seq![49u8, 50, 51, 52, 53, 54, 55, 56, 57])
        == 0xcbf4_3926) by (compute);
}

pub proof fn product_left_identity(value: u32)
    ensures model::product(model::ONE, value) == value,
{
    assert(model::ONE & model::remaining_mask(1) == 0) by (compute);
    assert(model::ONE & model::coefficient_mask(0) == model::ONE) by (compute);
    zero_terms(model::ONE, value, 1);
    bit_identities(value);
}

pub proof fn times_x_linear(a: u32, b: u32)
    ensures model::times_x(a ^ b) == model::times_x(a) ^ model::times_x(b),
{
    assert((if (a ^ b) & 1 != 0 { ((a ^ b) >> 1) ^ 0xedb8_8320u32 }
        else { (a ^ b) >> 1 })
        == (if a & 1 != 0 { (a >> 1) ^ 0xedb8_8320u32 } else { a >> 1 })
            ^ (if b & 1 != 0 { (b >> 1) ^ 0xedb8_8320u32 } else { b >> 1 }))
        by (bit_vector);
}

pub proof fn shift_linear(a: u32, b: u32, count: nat)
    ensures model::shift_bits(a ^ b, count)
        == model::shift_bits(a, count) ^ model::shift_bits(b, count),
    decreases count,
{
    if count > 0 {
        shift_linear(a, b, (count - 1) as nat);
        times_x_linear(model::shift_bits(a, (count - 1) as nat),
            model::shift_bits(b, (count - 1) as nat));
    }
}

pub proof fn shift_without_reduction(value: u32, count: u32)
    requires count <= 8, value & (((1u32 << count) - 1) as u32) == 0,
    ensures model::shift_bits(value, count as nat) == value >> count,
    decreases count,
{
    if count == 0 {
        assert(value >> 0 == value) by (bit_vector);
    } else {
        assert(value & (((1u32 << ((count - 1) as u32)) - 1) as u32) == 0) by (bit_vector)
            requires 0 < count <= 8, value & (((1u32 << count) - 1) as u32) == 0;
        shift_without_reduction(value, (count - 1) as u32);
        assert((value >> ((count - 1) as u32)) & 1 == 0
            && (value >> ((count - 1) as u32)) >> 1 == value >> count) by (bit_vector)
            requires 0 < count <= 8, value & (((1u32 << count) - 1) as u32) == 0;
    }
}

pub proof fn byte_table_rule(crc: u32, byte: u8)
    ensures model::byte_step(crc, byte)
        == model::shift_bits(((crc as u8) ^ byte) as u32, 8) ^ (crc >> 8),
{
    let low = ((crc as u8) ^ byte) as u32;
    let high = crc & 0xffff_ff00u32;
    assert(crc ^ byte as u32 == low ^ high) by (bit_vector)
        requires low == ((crc as u8) ^ byte) as u32, high == crc & 0xffff_ff00u32;
    assert(high & (((1u32 << 8) - 1) as u32) == 0) by (bit_vector)
        requires high == crc & 0xffff_ff00u32;
    assert(high >> 8 == crc >> 8) by (bit_vector)
        requires high == crc & 0xffff_ff00u32;
    shift_linear(low, high, 8);
    shift_without_reduction(high, 8);
}

pub proof fn raw_prefix_step(start: u32, bytes: Seq<u8>, index: int)
    requires 0 <= index < bytes.len(),
    ensures model::raw_update(start, bytes.take(index + 1))
        == model::byte_step(model::raw_update(start, bytes.take(index)), bytes[index]),
{
    assert(bytes.take(index + 1).drop_last() == bytes.take(index));
    assert(bytes.take(index + 1).last() == bytes[index]);
}

}
