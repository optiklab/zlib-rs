use core::marker::PhantomData;

use crate::{Code, ReturnCode};

pub(super) mod buffer;
mod sync_buffer;

#[derive(Debug, Clone, Copy)]
pub(crate) struct BitReader<'a> {
    ptr: *const u8,
    end: *const u8,
    bit_buffer: u64,
    bits_used: u8,
    _marker: PhantomData<&'a [u8]>,
}

impl<'a> BitReader<'a> {
    pub fn new(slice: &'a [u8]) -> Self {
        let range = slice.as_ptr_range();

        Self {
            ptr: range.start,
            end: range.end,
            bit_buffer: 0,
            bits_used: 0,
            _marker: PhantomData,
        }
    }

    /// # Safety
    ///
    /// For nonempty input, ptr and len must satisfy the requirements of
    /// [`core::slice::from_raw_parts`]. Empty input may use a null pointer.
    #[inline(always)]
    pub unsafe fn update_slice(&mut self, ptr: *const u8, len: usize) {
        let end = ptr.wrapping_add(len);

        *self = Self {
            ptr,
            end,
            bit_buffer: self.bit_buffer,
            bits_used: self.bits_used,
            _marker: PhantomData,
        };
    }

    #[inline(always)]
    pub fn advance(&mut self, bytes: usize) {
        self.ptr = Ord::min(self.ptr.wrapping_add(bytes), self.end);
    }

    #[inline(always)]
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr
    }

    #[inline(always)]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr as *mut u8
    }

    #[inline(always)]
    pub fn as_slice(&self) -> &[u8] {
        let len = self.bytes_remaining();
        if len == 0 {
            return &[];
        }
        // SAFETY: condition of constructing this struct.
        unsafe { core::slice::from_raw_parts(self.ptr, len) }
    }

    #[inline(always)]
    pub fn bits_in_buffer(&self) -> u8 {
        self.bits_used
    }

    #[inline(always)]
    pub fn hold(&self) -> u64 {
        self.bit_buffer
    }

    #[inline(always)]
    pub fn bytes_remaining(&self) -> usize {
        self.end as usize - self.ptr as usize
    }

    #[inline(always)]
    pub fn bytes_remaining_including_buffer(&self) -> usize {
        (self.end as usize - self.ptr as usize) + (self.bits_used as usize >> 3)
    }

    #[inline(always)]
    pub fn need_bits(&mut self, n: usize) -> Result<(), ReturnCode> {
        if self.bits_used as usize >= n {
            return Ok(());
        }
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, complete) =
            buffer::fill_from_slice(&mut self.bit_buffer, &mut self.bits_used, input, n);
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        if complete {
            Ok(())
        } else {
            Err(ReturnCode::Ok)
        }
    }

    #[inline]
    #[cfg(test)]
    pub fn read_header_counts(&mut self) -> Result<(usize, usize, usize), ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, counts) =
            super::header_lengths::read_counts(&mut self.bit_buffer, &mut self.bits_used, input);
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        counts.ok_or(ReturnCode::Ok)
    }

    #[cfg(test)]
    #[inline]
    pub fn read_header_lengths(
        &mut self,
        lengths: &mut [u16],
        have: &mut usize,
        target: usize,
    ) -> Result<(), ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, complete) = super::header_lengths::read_lengths(
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            lengths,
            have,
            target,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        if complete {
            Ok(())
        } else {
            Err(ReturnCode::Ok)
        }
    }

    #[inline]
    #[cfg(test)]
    pub fn read_code_length(&mut self, table: &[Code], root: usize) -> Result<Code, ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, entry) = super::inftrees::read_code_length(
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            table,
            root,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        entry.ok_or(ReturnCode::Ok)
    }

    #[inline]
    #[cfg(test)]
    pub fn read_repeat_extra(
        &mut self,
        code_bits: u8,
        symbol: u16,
        have: usize,
    ) -> Result<u16, ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, outcome) = super::header_lengths::read_repeat_extra(
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            code_bits,
            symbol,
            have,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        match outcome {
            super::header_lengths::RepeatExtra::NeedInput => Err(ReturnCode::Ok),
            super::header_lengths::RepeatExtra::MissingPrevious => Err(ReturnCode::DataError),
            super::header_lengths::RepeatExtra::Value(extra) => Ok(extra),
        }
    }

    #[inline]
    #[cfg(test)]
    pub fn read_repeat_lengths(
        &mut self,
        code_bits: u8,
        symbol: u16,
        lengths: &mut [u16],
        have: &mut usize,
        total: usize,
    ) -> Result<(), ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, outcome) = super::header_lengths::read_repeat_lengths(
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            code_bits,
            symbol,
            lengths,
            have,
            total,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        match outcome {
            None => Err(ReturnCode::Ok),
            Some(false) => Err(ReturnCode::DataError),
            Some(true) => Ok(()),
        }
    }

    #[inline]
    #[cfg(test)]
    pub fn read_length_symbol(
        &mut self,
        table: &[Code],
        root: usize,
        lengths: &mut [u16],
        have: &mut usize,
        total: usize,
    ) -> Result<(), ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, outcome) = super::inftrees::read_length_symbol(
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            table,
            root,
            lengths,
            have,
            total,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        match outcome {
            None => Err(ReturnCode::Ok),
            Some(false) => Err(ReturnCode::DataError),
            Some(true) => Ok(()),
        }
    }

    #[inline]
    #[allow(clippy::too_many_arguments)]
    pub fn read_header_state(
        &mut self,
        mode: &mut super::Mode,
        nlen: &mut usize,
        ndist: &mut usize,
        ncode: &mut usize,
        len_table: &mut super::Table,
        next: &mut usize,
        lengths: &mut [u16],
        have: &mut usize,
        table: &mut [Code],
        work: &mut [u16],
    ) -> super::header_state::HeaderAction {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, outcome) = super::header_state::read_header_state(
            mode,
            nlen,
            ndist,
            ncode,
            len_table,
            next,
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            lengths,
            have,
            table,
            work,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        outcome
    }

    #[inline]
    #[cfg(test)]
    pub fn read_code_length_table(
        &mut self,
        lengths: &mut [u16],
        have: &mut usize,
        target: usize,
        table: &mut [Code],
        work: &mut [u16],
    ) -> Result<super::inftrees::InflateTable, ReturnCode> {
        let input = if self.ptr == self.end {
            &[]
        } else {
            // SAFETY: the reader's construction/update invariant covers its nonempty slice.
            unsafe { core::slice::from_raw_parts(self.ptr, self.bytes_remaining()) }
        };
        let (consumed, outcome) = super::inftrees::read_code_length_table(
            &mut self.bit_buffer,
            &mut self.bits_used,
            input,
            lengths,
            have,
            target,
            table,
            work,
        );
        // SAFETY: the kernel advances no further than the supplied slice.
        self.ptr = unsafe { self.ptr.add(consumed) };
        outcome.ok_or(ReturnCode::Ok)
    }

    /// Remove zero to seven bits as needed to go to a byte boundary
    #[inline(always)]
    pub fn next_byte_boundary(&mut self) {
        buffer::align_to_byte(&mut self.bit_buffer, &mut self.bits_used);
    }

    #[inline(always)]
    pub fn pull_byte(&mut self) -> Result<u8, ReturnCode> {
        // SAFETY: bounds checking.
        if self.ptr == self.end {
            return Err(ReturnCode::Ok);
        }
        let byte = unsafe { *self.ptr };
        self.ptr = unsafe { self.ptr.add(1) };

        buffer::append_byte(&mut self.bit_buffer, &mut self.bits_used, byte);

        Ok(byte)
    }

    #[inline(always)]
    /// Copy enough bytes from the BitReader's underlying slice to fill the internal
    /// bit buffer with 7 bytes of data.
    ///
    /// Safety:
    ///
    /// `self.ptr` must point to at least 8 readable bytes, as indicated by `bytes_remaining()`
    pub unsafe fn refill(&mut self) {
        debug_assert!(self.bytes_remaining() >= 8);

        // SAFETY: the caller ensures eight readable bytes.
        let input = unsafe { core::slice::from_raw_parts(self.ptr, 8) };
        let increment = buffer::refill_from_slice(&mut self.bit_buffer, &mut self.bits_used, input);
        self.ptr = self.ptr.wrapping_add(increment as usize);
    }

    #[inline(always)]
    pub fn bits(&mut self, n: usize) -> u64 {
        // debug_assert!( n <= self.bits_used, "{n} bits requested, but only {} avaliable", self.bits_used);

        buffer::peek_bits(self.bit_buffer, n)
    }

    #[inline(always)]
    pub fn drop_bits(&mut self, n: u8) {
        buffer::consume_bits(&mut self.bit_buffer, &mut self.bits_used, n);
    }

    #[inline(always)]
    pub fn start_sync_search(&mut self) -> ([u8; 4], usize) {
        sync_buffer::drain_sync_buffer(&mut self.bit_buffer, &mut self.bits_used)
    }

    #[inline(always)]
    pub fn init_bits(&mut self) {
        buffer::reset_bits(&mut self.bit_buffer, &mut self.bits_used);
    }

    #[inline(always)]
    pub fn prime(&mut self, bits: u8, value: u64) {
        buffer::prime_bits(&mut self.bit_buffer, &mut self.bits_used, bits, value);
    }

    #[inline(always)]
    pub fn return_unused_bytes(&mut self) {
        let len = buffer::return_unused_bits(&mut self.bit_buffer, &mut self.bits_used);
        // SAFETY: ptr is advanced whenever bits_used is incremented by 8, so this sub is always
        // in bounds.
        self.ptr = unsafe { self.ptr.sub(len as usize) };
        assert!(self.bits_used <= 32);
    }
}

#[cfg(feature = "std")]
impl std::io::Read for BitReader<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        assert_eq!(self.bits_used, 0, "bit buffer not cleared before read");

        let number_of_bytes = Ord::min(buf.len(), self.bytes_remaining());

        // SAFETY: `buf` is a mutable (exclusive) reference, so it cannot overlap the memory that
        // the reader contains
        unsafe { core::ptr::copy_nonoverlapping(self.ptr, buf.as_mut_ptr(), number_of_bytes) }

        self.ptr = unsafe { self.ptr.add(number_of_bytes) };
        Ok(number_of_bytes)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn priming_masks_values_and_preserves_the_existing_low_first_prefix() {
        let input = [0xa5];
        let mut reader = BitReader::new(&input);
        for (bits, value, expected_word, expected_count) in [
            (0, u64::MAX, 0, 0),
            (16, 0x12345, 0x2345, 16),
            (16, u64::MAX, 0xffff2345, 32),
            (0, u64::MAX, 0xffff2345, 32),
        ] {
            reader.prime(bits, value);
            assert_eq!(
                (reader.hold(), reader.bits_in_buffer()),
                (expected_word, expected_count)
            );
            assert_eq!(reader.as_ptr(), input.as_ptr());
            assert_eq!(reader.bytes_remaining(), input.len());
        }
        let mut full = BitReader::new(&input);
        full.prime(63, u64::MAX);
        full.prime(1, u64::MAX);
        assert_eq!((full.hold(), full.bits_in_buffer()), (u64::MAX, 64));
    }

    #[test]
    fn low_first_fields_cross_bytes_and_align_before_more_input() {
        let mut reader = BitReader::new(&[0xb6, 0x1d, 0xd2]);
        assert_eq!(reader.pull_byte(), Ok(0xb6));
        assert_eq!(reader.bits(3), 6);
        reader.drop_bits(3);
        assert_eq!(reader.bits_in_buffer(), 5);
        assert_eq!(reader.bits(7), 22);
        assert_eq!(reader.need_bits(10), Ok(()));
        assert_eq!(reader.bits(9), 438);
        reader.drop_bits(9);
        assert_eq!(reader.bits_in_buffer(), 4);
        reader.next_byte_boundary();
        assert_eq!(reader.bits_in_buffer(), 0);
        assert_eq!(reader.need_bits(8), Ok(()));
        assert_eq!(reader.bits(8), 0xd2);
        reader.drop_bits(8);
        assert_eq!(reader.need_bits(1), Err(ReturnCode::Ok));
        assert_eq!((reader.hold(), reader.bits_in_buffer()), (0, 0));
    }

    #[test]
    fn cached_lookahead_is_not_required_to_be_zero_above_available_bits() {
        let input = [1, 2, 3, 4, 5, 6, 7, 0xa5, 0x5a];
        let mut reader = BitReader::new(&input);
        // SAFETY: the input contains nine readable bytes.
        unsafe { reader.refill() };
        assert_eq!((reader.bits_in_buffer(), reader.bytes_remaining()), (56, 2));
        reader.drop_bits(56);
        assert_eq!((reader.hold(), reader.bits_in_buffer()), (0xa5, 0));
        let mut exhausted = reader;
        assert_eq!(exhausted.need_bits(24), Err(ReturnCode::Ok));
        assert_eq!(
            (exhausted.bits(16), exhausted.bits_in_buffer()),
            (0x5aa5, 16)
        );
        assert_eq!(exhausted.bytes_remaining(), 0);
        let mut field = reader;
        let mut lengths = [u16::MAX; 19];
        let mut have = 0;
        assert_eq!(
            field.read_header_lengths(&mut lengths, &mut have, 1),
            Ok(())
        );
        assert_eq!((have, lengths[16]), (1, 5));
        assert_eq!((field.hold(), field.bits_in_buffer()), (0x14, 5));
        assert_eq!(field.bytes_remaining(), 1);
        reader.next_byte_boundary();
        reader.drop_bits(0);
        assert_eq!((reader.hold(), reader.bits_in_buffer()), (0xa5, 0));
        assert_eq!(reader.bits(0), 0);
        assert_eq!(reader.pull_byte(), Ok(0xa5));
        assert_eq!((reader.bits(8), reader.bits_in_buffer()), (0xa5, 8));
        reader.drop_bits(8);
        assert_eq!(reader.pull_byte(), Ok(0x5a));
        assert_eq!(reader.bits(8), 0x5a);
    }

    #[test]
    fn full_word_is_consumed_without_a_word_sized_shift() {
        let mut reader = BitReader::new(&[0, 0, 0, 0, 0, 0, 0, 0x80]);
        assert_eq!(reader.need_bits(64), Ok(()));
        assert_eq!(reader.bits_in_buffer(), 64);
        reader.drop_bits(63);
        assert_eq!((reader.bits(1), reader.bits_in_buffer()), (1, 1));
        reader.drop_bits(1);
        assert_eq!((reader.hold(), reader.bits_in_buffer()), (0, 0));
    }

    #[test]
    fn refill_preserves_buffered_prefix_and_tracks_every_count_and_cached_suffix() {
        let input = [0xb6, 0x1d, 0xd2, 0x8f, 4, 0xa9, 0xc3, 0x75, 0x6a];
        for count in 0..64 {
            let mut reader = BitReader::new(&input);
            reader.prime(count, 0);
            // SAFETY: all nine input bytes remain readable after priming.
            unsafe { reader.refill() };
            let advanced = usize::from((63 - count) / 8);
            assert_eq!(reader.bytes_remaining(), input.len() - advanced);
            assert_eq!(
                usize::from(reader.bits_in_buffer()),
                usize::from(count) + 8 * advanced
            );
            reader.drop_bits(count);
            for byte in &input[..advanced] {
                assert_eq!(reader.bits(8), u64::from(*byte));
                reader.drop_bits(8);
            }
            assert_eq!(reader.bits_in_buffer(), 0);
            assert_eq!(reader.pull_byte(), Ok(input[advanced]));
            assert_eq!(reader.bits(8), u64::from(input[advanced]));
        }
    }

    #[test]
    fn consecutive_refills_preserve_unread_cache_across_every_consumption_boundary() {
        let input = [
            0xb6, 0x1d, 0xd2, 0x8f, 4, 0xa9, 0xc3, 0x75, 0x6a, 0xe7, 0x13, 0x92, 0xfd, 0x51, 0x38,
            0x80, 0x5b, 0xc6, 0x29, 0x7d, 0x03, 0xa4, 0xee, 0x19, 0x62, 0xd8, 0x47, 0xb1, 0x95,
            0x2c, 0x70, 0xfa,
        ];
        for remaining in 0..64 {
            for consumed in 0..64 {
                let mut reader = BitReader::new(&input);
                assert_eq!(reader.need_bits(64), Ok(()));
                let mut position = 64 - usize::from(remaining);
                if remaining == 0 {
                    reader.drop_bits(63);
                    reader.drop_bits(1);
                } else {
                    reader.drop_bits(64 - remaining);
                }
                // SAFETY: eight bytes were pulled from a 32-byte input.
                unsafe { reader.refill() };
                if consumed > reader.bits_in_buffer() {
                    continue;
                }
                reader.drop_bits(consumed);
                position += usize::from(consumed);
                // SAFETY: the previous refill advanced by at most seven bytes.
                unsafe { reader.refill() };
                let end = reader.as_ptr() as usize - input.as_ptr() as usize;
                assert_eq!(usize::from(reader.bits_in_buffer()), end * 8 - position);
                while reader.bits_in_buffer() != 0 {
                    assert_eq!(
                        reader.bits(1),
                        u64::from((input[position / 8] >> (position % 8)) & 1)
                    );
                    reader.drop_bits(1);
                    position += 1;
                }
                assert_eq!(position, end * 8);
                assert_eq!(reader.pull_byte(), Ok(input[end]));
                assert_eq!(reader.bits(8), u64::from(input[end]));
            }
        }
    }

    #[test]
    fn returning_unused_bytes_preserves_the_unread_stream_with_and_without_cached_lookahead() {
        let input = [
            0xb6, 0x1d, 0xd2, 0x8f, 4, 0xa9, 0xc3, 0x75, 0x6a, 0xe7, 0x13, 0x92, 0xfd, 0x51, 0x38,
            0x80, 0x5b, 0xc6, 0x29, 0x7d, 0x03, 0xa4, 0xee, 0x19,
        ];
        for cached in [false, true] {
            for consumed in 0..=64 {
                let mut reader = BitReader::new(&input);
                assert_eq!(reader.need_bits(64), Ok(()));
                if consumed == 64 {
                    reader.drop_bits(63);
                    reader.drop_bits(1);
                } else {
                    reader.drop_bits(consumed);
                }
                if cached && reader.bits_in_buffer() < 64 {
                    // SAFETY: only eight bytes have been advanced in the 24-byte input.
                    unsafe { reader.refill() };
                }
                let mut position = usize::from(consumed);
                reader.return_unused_bytes();
                let count = usize::from(reader.bits_in_buffer());
                assert!(count < 8);
                assert_eq!(reader.hold() >> count, 0);
                let offset = reader.as_ptr() as usize - input.as_ptr() as usize;
                assert_eq!(offset * 8, position + count);
                while position < input.len() * 8 {
                    assert_eq!(reader.need_bits(1), Ok(()));
                    assert_eq!(
                        reader.bits(1),
                        u64::from((input[position / 8] >> (position % 8)) & 1)
                    );
                    reader.drop_bits(1);
                    position += 1;
                }
                assert_eq!(reader.need_bits(1), Err(ReturnCode::Ok));
            }
        }
    }

    #[test]
    fn dynamic_header_fields_resume_at_each_octet_and_preserve_unwritten_lengths() {
        let input = [0xb6u8, 0x1d, 0xd2];
        let expected = [
            (16, 6),
            (17, 6),
            (18, 6),
            (0, 6),
            (8, 1),
            (7, 4),
            (9, 4),
            (6, 6),
        ];
        let mut lengths = [u16::MAX; 23];
        let mut have = 0;
        let mut reader = BitReader::new(&[]);
        for (index, byte) in input.iter().enumerate() {
            // SAFETY: this octet remains alive throughout the reader's use.
            unsafe { reader.update_slice(byte, 1) };
            let before = lengths;
            let previous_have = have;
            assert_eq!(
                reader.read_header_lengths(&mut lengths, &mut have, expected.len()),
                if index == 2 {
                    Ok(())
                } else {
                    Err(ReturnCode::Ok)
                }
            );
            for slot in 0..lengths.len() {
                let expected_value = expected[previous_have..have]
                    .iter()
                    .find(|&&(symbol, _)| symbol == slot)
                    .map_or(before[slot], |&(_, value)| value);
                assert_eq!(lengths[slot], expected_value);
            }
            assert_eq!(have, [2, 5, 8][index]);
            assert_eq!(reader.bits_in_buffer(), [2, 1, 0][index]);
            assert_eq!(reader.bytes_remaining(), 0);
        }
        for (symbol, value) in expected {
            assert_eq!(lengths[symbol], value);
        }
    }

    #[test]
    fn header_symbol_steps_preserve_source_errors_lengths_and_raw_cached_state() {
        use crate::inflate::inftrees::{inflate_table, CodeType, InflateTable};

        let mut alphabet = [0; 19];
        for symbol in [0, 5, 16] {
            alphabet[symbol] = 2;
        }
        alphabet[17] = 3;
        alphabet[18] = 3;
        let mut table = [Code::default(); 128];
        let mut work = [0; 19];
        assert_eq!(
            inflate_table(CodeType::Codes, &alphabet, &mut table, 3, &mut work),
            InflateTable::Success { root: 3, used: 8 }
        );
        // Canonical codes 00/01/10/110/111, packed in low-first wire positions.
        for (symbol, code, bits, width, base) in [
            (0u16, 0u128, 2usize, 0usize, 1usize),
            (5, 2, 2, 0, 1),
            (16, 1, 2, 2, 3),
            (17, 3, 3, 3, 3),
            (18, 7, 3, 7, 11),
        ] {
            for extra in [0usize, ((1 << width) - 1) / 2, (1 << width) - 1] {
                let target = bits + width;
                let repeats = base + extra;
                let stream = code
                    | ((extra as u128) << bits)
                    | (0xda35_b69c_27e1_f048_519a_6c3e_82d7_b405u128 << target);
                for count in 0..=64u8 {
                    for len in 0..=3usize {
                        let input = [
                            (stream >> count) as u8,
                            (stream >> (u32::from(count) + 8)) as u8,
                            (stream >> (u32::from(count) + 16)) as u8,
                        ];
                        for cached in [false, true] {
                            let held = if cached {
                                (usize::from(count) + 8 * len).min(64)
                            } else {
                                usize::from(count)
                            };
                            let word = (stream & ((1u128 << held) - 1)) as u64;
                            for have in [0usize, 2] {
                                for capacity in [1, repeats.saturating_sub(1).max(1), repeats] {
                                    let total = have + capacity;
                                    let mut lengths = [9u16; 144];
                                    lengths[..have].fill(7);
                                    let mut expected_lengths = lengths;
                                    let mut next = have;
                                    let available = usize::from(count) + 8 * len;
                                    let complete = available >= target;
                                    let missing = symbol == 16 && have == 0;
                                    let fits = complete && !missing && repeats <= capacity;
                                    let expected = if !complete {
                                        Err(ReturnCode::Ok)
                                    } else if fits {
                                        let value = if symbol < 16 {
                                            symbol
                                        } else if symbol == 16 {
                                            7
                                        } else {
                                            0
                                        };
                                        expected_lengths[have..have + repeats].fill(value);
                                        Ok(())
                                    } else {
                                        Err(ReturnCode::DataError)
                                    };
                                    let dropped = if !complete {
                                        0
                                    } else if missing {
                                        bits
                                    } else {
                                        target
                                    };
                                    let advanced = target
                                        .saturating_sub(usize::from(count))
                                        .div_ceil(8)
                                        .min(len);
                                    let incoming =
                                        (stream >> count) & ((1u128 << (8 * advanced)) - 1);
                                    let loaded = (u128::from(word) | (incoming << count)) as u64;
                                    let mut reader = BitReader::new(&input[..len]);
                                    if len == 0 {
                                        // SAFETY: empty input admits a null pointer.
                                        unsafe { reader.update_slice(core::ptr::null(), 0) };
                                    }
                                    reader.bit_buffer = word;
                                    reader.bits_used = count;
                                    assert_eq!(
                                        reader.read_length_symbol(
                                            &table,
                                            3,
                                            &mut lengths,
                                            &mut next,
                                            total
                                        ),
                                        expected
                                    );
                                    assert_eq!(lengths, expected_lengths);
                                    assert_eq!(next, have + if fits { repeats } else { 0 });
                                    assert_eq!(reader.hold(), loaded >> dropped);
                                    assert_eq!(
                                        usize::from(reader.bits_in_buffer()),
                                        usize::from(count) + 8 * advanced - dropped
                                    );
                                    assert_eq!(reader.bytes_remaining(), len - advanced);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn repeat_input_expansion_preserves_lengths_and_bits_on_every_error_boundary() {
        let input = [0xb6u8, 0x1d];
        for code_bits in [1u8, 3, 7] {
            for (symbol, width, base) in [(16, 2usize, 3usize), (17, 3, 3), (18, 7, 11)] {
                for have in [0usize, 2] {
                    for count in 0..=64u8 {
                        let available = if count == 64 {
                            0xd31a_f6c5_87b9_42e7u64
                        } else {
                            0xd31a_f6c5_87b9_42e7u64 & ((1u64 << count) - 1)
                        };
                        for len in 0..=input.len() {
                            let pending = input[..len]
                                .iter()
                                .enumerate()
                                .fold(0u64, |bits, (index, &byte)| {
                                    bits | (u64::from(byte) << (8 * index))
                                });
                            let source = u128::from(available) | (u128::from(pending) << count);
                            let extra = ((source >> code_bits) & ((1u128 << width) - 1)) as usize;
                            let repeats = base + extra;
                            for total in [have, have + repeats - 1, have + repeats] {
                                for cached in [false, true] {
                                    let word = if cached { source as u64 } else { available };
                                    let mut reader = BitReader::new(&input[..len]);
                                    if len == 0 {
                                        // SAFETY: empty input admits a null pointer.
                                        unsafe { reader.update_slice(core::ptr::null(), 0) };
                                    }
                                    reader.bit_buffer = word;
                                    reader.bits_used = count;
                                    let mut lengths = [0xa55au16; 144];
                                    if have != 0 {
                                        lengths[..have].copy_from_slice(&[5, 7]);
                                    }
                                    let mut expected_lengths = lengths;
                                    let mut next = have;
                                    let target = usize::from(code_bits) + width;
                                    let complete = usize::from(count) + 8 * len >= target;
                                    let missing = symbol == 16 && have == 0;
                                    let fits = complete && !missing && have + repeats <= total;
                                    let expected = if !complete {
                                        Err(ReturnCode::Ok)
                                    } else if fits {
                                        expected_lengths[have..have + repeats]
                                            .fill(if symbol == 16 { 7 } else { 0 });
                                        Ok(())
                                    } else {
                                        Err(ReturnCode::DataError)
                                    };
                                    assert_eq!(
                                        reader.read_repeat_lengths(
                                            code_bits,
                                            symbol,
                                            &mut lengths,
                                            &mut next,
                                            total,
                                        ),
                                        expected
                                    );
                                    assert_eq!(lengths, expected_lengths);
                                    assert_eq!(next, have + if fits { repeats } else { 0 });
                                    let advanced = target
                                        .saturating_sub(usize::from(count))
                                        .div_ceil(8)
                                        .min(len);
                                    let dropped = if !complete {
                                        0
                                    } else if missing {
                                        usize::from(code_bits)
                                    } else {
                                        target
                                    };
                                    let prefix =
                                        u128::from(pending) & ((1u128 << (8 * advanced)) - 1);
                                    let loaded = (u128::from(word) | (prefix << count)) as u64;
                                    assert_eq!(reader.hold(), loaded >> dropped);
                                    assert_eq!(
                                        usize::from(reader.bits_in_buffer()),
                                        usize::from(count) + 8 * advanced - dropped
                                    );
                                    assert_eq!(reader.bytes_remaining(), len - advanced);
                                    if !complete {
                                        let before = (reader.hold(), reader.bits_in_buffer());
                                        assert_eq!(
                                            reader.read_repeat_lengths(
                                                code_bits,
                                                symbol,
                                                &mut lengths,
                                                &mut next,
                                                total,
                                            ),
                                            Err(ReturnCode::Ok)
                                        );
                                        assert_eq!(lengths, expected_lengths);
                                        assert_eq!(next, have);
                                        assert_eq!(
                                            (reader.hold(), reader.bits_in_buffer()),
                                            before
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn repeat_extra_parsing_preserves_error_precedence_raw_state_and_cached_input() {
        let input = [0xb6u8, 0x1d, 0xd2];
        for code_bits in 1..=7u8 {
            for (symbol, width) in [(16, 2usize), (17, 3), (18, 7)] {
                for have in [0, 1] {
                    for count in 0..=64u8 {
                        let available = if count == 64 {
                            0xd31a_f6c5_87b9_42e7u64
                        } else {
                            0xd31a_f6c5_87b9_42e7u64 & ((1u64 << count) - 1)
                        };
                        for len in 0..=input.len() {
                            let pending = input[..len]
                                .iter()
                                .enumerate()
                                .fold(0u64, |bits, (index, &byte)| {
                                    bits | (u64::from(byte) << (8 * index))
                                });
                            let source = u128::from(available) | (u128::from(pending) << count);
                            for cached in [false, true] {
                                let word = if cached { source as u64 } else { available };
                                let mut reader = BitReader::new(&input[..len]);
                                if len == 0 {
                                    // SAFETY: empty input admits a null pointer.
                                    unsafe { reader.update_slice(core::ptr::null(), 0) };
                                }
                                reader.bit_buffer = word;
                                reader.bits_used = count;
                                let target = usize::from(code_bits) + width;
                                let complete = usize::from(count) + 8 * len >= target;
                                let missing_previous = complete && symbol == 16 && have == 0;
                                let expected = if !complete {
                                    Err(ReturnCode::Ok)
                                } else if missing_previous {
                                    Err(ReturnCode::DataError)
                                } else {
                                    Ok(((source >> code_bits) & ((1u128 << width) - 1)) as u16)
                                };
                                assert_eq!(
                                    reader.read_repeat_extra(code_bits, symbol, have),
                                    expected
                                );
                                let consumed = target
                                    .saturating_sub(usize::from(count))
                                    .div_ceil(8)
                                    .min(len);
                                let discarded = if !complete {
                                    0
                                } else if missing_previous {
                                    usize::from(code_bits)
                                } else {
                                    target
                                };
                                let prefix = pending & ((1u64 << (8 * consumed)) - 1);
                                let loaded =
                                    (u128::from(word) | (u128::from(prefix) << count)) as u64;
                                assert_eq!(
                                    (reader.hold(), usize::from(reader.bits_in_buffer())),
                                    (
                                        loaded >> discarded,
                                        usize::from(count) + 8 * consumed - discarded
                                    )
                                );
                                assert_eq!(reader.bytes_remaining(), len - consumed);
                                if !complete {
                                    let before = (reader.hold(), reader.bits_in_buffer());
                                    assert_eq!(
                                        reader.read_repeat_extra(code_bits, symbol, have),
                                        Err(ReturnCode::Ok)
                                    );
                                    assert_eq!((reader.hold(), reader.bits_in_buffer()), before);
                                }
                            }
                        }
                    }
                }
            }
        }
        for (symbol, expected) in [(16, 1), (17, 5), (18, 101)] {
            assert_eq!(
                BitReader::new(&[0x2d, 0x03]).read_repeat_extra(3, symbol, 1),
                Ok(expected)
            );
        }
    }

    #[test]
    fn code_length_lookup_matches_rfc_canonical_example_and_wire_order() {
        use crate::inflate::inftrees::{inflate_table, CodeType, InflateTable};

        let lengths = [3u16, 3, 3, 3, 3, 2, 4, 4];
        let mut table = [Code::default(); 16];
        let mut work = [0; 8];
        assert_eq!(
            inflate_table(CodeType::Codes, &lengths, &mut table, 4, &mut work),
            InflateTable::Success { root: 4, used: 16 }
        );
        // Literal RFC 1951 3.2.2 codes, packed with the first wire bit lowest.
        for (symbol, (word, width)) in [
            (2u64, 3u8),
            (6, 3),
            (1, 3),
            (5, 3),
            (3, 3),
            (0, 2),
            (7, 4),
            (15, 4),
        ]
        .into_iter()
        .enumerate()
        {
            let expected = Code {
                op: 0,
                bits: width,
                val: symbol as u16,
            };
            let unread = [0x5au8];
            let mut reader = BitReader::new(&unread);
            reader.bit_buffer = word;
            reader.bits_used = width;
            assert_eq!(reader.read_code_length(&table, 4), Ok(expected));
            assert_eq!((reader.hold(), reader.bits_in_buffer()), (word, width));
            assert_eq!(reader.bytes_remaining(), 1);
            for count in 0..width {
                // SAFETY: empty input admits a null pointer.
                unsafe { reader.update_slice(core::ptr::null(), 0) };
                reader.bit_buffer = word & ((1u64 << count) - 1);
                reader.bits_used = count;
                let before = reader.hold();
                assert_eq!(reader.read_code_length(&table, 4), Err(ReturnCode::Ok));
                assert_eq!((reader.hold(), reader.bits_in_buffer()), (before, count));
                assert_eq!(reader.bytes_remaining(), 0);
            }
            let encoded = [word as u8];
            let mut reader = BitReader::new(&encoded);
            assert_eq!(reader.read_code_length(&table, 4), Ok(expected));
            assert_eq!((reader.hold(), reader.bits_in_buffer()), (word, 8));
            assert_eq!(reader.bytes_remaining(), 0);
        }
    }

    #[test]
    fn lazy_code_length_lookup_preserves_short_codes_cache_input_and_raw_registers() {
        use crate::inflate::inftrees::{inflate_table, CodeType, InflateTable};

        let input = [0xb6u8, 0x1d];
        for root in 1..=7usize {
            let mut lengths = [0u16; 19];
            for (index, length) in lengths[..root].iter_mut().enumerate() {
                *length = (index + 1) as u16;
            }
            lengths[root] = root as u16;
            let mut table = [Code::default(); 128];
            let mut work = [0; 19];
            assert_eq!(
                inflate_table(CodeType::Codes, &lengths, &mut table, root, &mut work),
                InflateTable::Success {
                    root,
                    used: 1 << root
                }
            );
            for pattern in 0..(1u64 << root) {
                for count in 0..=64u8 {
                    let seed = 0xa591_3ce7_42d8_b600 | pattern;
                    let available = if count == 64 {
                        seed
                    } else {
                        seed & ((1u64 << count) - 1)
                    };
                    let prefix_length =
                        ((available.trailing_ones() as usize).min(root) + 1).min(root);
                    for len in 0..=input.len() {
                        let pending = input[..len]
                            .iter()
                            .enumerate()
                            .fold(0u64, |bits, (index, &byte)| {
                                bits | (u64::from(byte) << (8 * index))
                            });
                        let source = u128::from(available) | (u128::from(pending) << count);
                        for cached in [false, true] {
                            let word = if cached { source as u64 } else { available };
                            let mut reader = BitReader::new(&input[..len]);
                            if len == 0 {
                                // SAFETY: empty input admits a null pointer.
                                unsafe { reader.update_slice(core::ptr::null(), 0) };
                            }
                            reader.bit_buffer = word;
                            reader.bits_used = count;
                            let advanced =
                                usize::from(usize::from(count) < prefix_length && len != 0);
                            let symbol = (source as u64).trailing_ones() as usize;
                            let symbol = symbol.min(root);
                            let expected = if usize::from(count) >= prefix_length || len != 0 {
                                Ok(Code {
                                    op: 0,
                                    bits: (symbol + 1).min(root) as u8,
                                    val: symbol as u16,
                                })
                            } else {
                                Err(ReturnCode::Ok)
                            };
                            assert_eq!(reader.read_code_length(&table, root), expected);
                            let prefix = if advanced == 0 { 0 } else { pending & 255 };
                            let loaded = (u128::from(word) | (u128::from(prefix) << count)) as u64;
                            assert_eq!(
                                (reader.hold(), usize::from(reader.bits_in_buffer())),
                                (loaded, usize::from(count) + 8 * advanced)
                            );
                            assert_eq!(reader.bytes_remaining(), len - advanced);
                            let before = (
                                reader.hold(),
                                reader.bits_in_buffer(),
                                reader.bytes_remaining(),
                            );
                            assert_eq!(reader.read_code_length(&table, root), expected);
                            assert_eq!(
                                (
                                    reader.hold(),
                                    reader.bits_in_buffer(),
                                    reader.bytes_remaining()
                                ),
                                before
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn null_empty_input_preserves_buffered_state_across_input_adapters() {
        for count in 0..=64u8 {
            let word = if count == 64 {
                u64::MAX
            } else {
                (1u64 << count) - 1
            };
            let mut reader = BitReader::new(&[]);
            // SAFETY: empty input admits a null pointer.
            unsafe { reader.update_slice(core::ptr::null(), 0) };
            reader.bit_buffer = word;
            reader.bits_used = count;
            assert!(reader.as_slice().is_empty());
            for target in 0..=64usize {
                let mut filled = reader;
                assert_eq!(
                    filled.need_bits(target),
                    if usize::from(count) >= target {
                        Ok(())
                    } else {
                        Err(ReturnCode::Ok)
                    }
                );
                assert_eq!((filled.hold(), filled.bits_in_buffer()), (word, count));
                assert!(filled.as_ptr().is_null());
            }
            let mut counts = reader;
            assert_eq!(
                counts.read_header_counts(),
                if count >= 14 {
                    Ok((288, 32, 19))
                } else {
                    Err(ReturnCode::Ok)
                }
            );
            let discarded = if count >= 14 { 14 } else { 0 };
            assert_eq!(
                (counts.hold(), counts.bits_in_buffer()),
                (word >> discarded, count - discarded)
            );
            assert!(counts.as_ptr().is_null());

            let mut lengths = [u16::MAX; 19];
            let mut have = 0;
            let mut fields = reader;
            assert_eq!(
                fields.read_header_lengths(&mut lengths, &mut have, 1),
                if count >= 3 {
                    Ok(())
                } else {
                    Err(ReturnCode::Ok)
                }
            );
            let discarded = if count >= 3 { 3 } else { 0 };
            assert_eq!(
                (fields.hold(), fields.bits_in_buffer()),
                (word >> discarded, count - discarded)
            );
            assert!(fields.as_ptr().is_null());

            let mut table = [Code {
                op: 0,
                bits: 0,
                val: 0,
            }; 128];
            let mut work = [u16::MAX; 19];
            lengths.fill(u16::MAX);
            have = 0;
            let mut constructed = reader;
            assert_eq!(
                constructed.read_code_length_table(
                    &mut lengths,
                    &mut have,
                    1,
                    &mut table,
                    &mut work
                ),
                if count >= 3 {
                    Ok(crate::inflate::inftrees::InflateTable::InvalidCode)
                } else {
                    Err(ReturnCode::Ok)
                }
            );
            assert_eq!(
                (constructed.hold(), constructed.bits_in_buffer()),
                (word >> discarded, count - discarded)
            );
            assert!(constructed.as_ptr().is_null());
        }
    }

    #[test]
    fn dynamic_header_counts_cover_all_counts_cache_states_and_partial_input() {
        let input = [0xb6u8, 0x1d, 0xd2];
        for initial_count in 0..=64u8 {
            let available = if initial_count == 64 {
                0xa591_3ce7_42d8_b60fu64
            } else {
                0xa591_3ce7_42d8_b60fu64 & ((1u64 << initial_count) - 1)
            };
            for len in 0..=input.len() {
                let pending = input[..len]
                    .iter()
                    .enumerate()
                    .fold(0u64, |bits, (index, &byte)| {
                        bits | (u64::from(byte) << (8 * index))
                    });
                let source = u128::from(available) | (u128::from(pending) << initial_count);
                for cached in [false, true] {
                    let initial_word = if cached { source as u64 } else { available };
                    let mut reader = BitReader::new(&input[..len]);
                    reader.bit_buffer = initial_word;
                    reader.bits_used = initial_count;
                    let complete = usize::from(initial_count) + 8 * len >= 14;
                    assert_eq!(
                        reader.read_header_counts(),
                        if complete {
                            Ok((
                                (source & 31) as usize + 257,
                                ((source >> 5) & 31) as usize + 1,
                                ((source >> 10) & 15) as usize + 4,
                            ))
                        } else {
                            Err(ReturnCode::Ok)
                        }
                    );
                    let consumed = 14usize
                        .saturating_sub(usize::from(initial_count))
                        .div_ceil(8)
                        .min(len);
                    let discarded = if complete { 14 } else { 0 };
                    let prefix = pending & ((1u64 << (8 * consumed)) - 1);
                    let loaded =
                        (u128::from(initial_word) | (u128::from(prefix) << initial_count)) as u64;
                    assert_eq!(reader.hold(), loaded >> discarded);
                    assert_eq!(
                        usize::from(reader.bits_in_buffer()),
                        usize::from(initial_count) + 8 * consumed - discarded
                    );
                    assert_eq!(reader.bytes_remaining(), len - consumed);
                    if !complete {
                        let before = (reader.hold(), reader.bits_in_buffer());
                        assert_eq!(reader.read_header_counts(), Err(ReturnCode::Ok));
                        assert_eq!((reader.hold(), reader.bits_in_buffer()), before);
                    }
                }
            }
        }
        for (input, expected) in [
            ([0xb6u8, 0x1d], (279, 14, 11)),
            ([0xff, 0xff], (288, 32, 19)),
            ([0, 0], (257, 1, 4)),
        ] {
            assert_eq!(BitReader::new(&input).read_header_counts(), Ok(expected));
        }
    }

    #[test]
    fn complete_header_reader_covers_cached_input_all_counts_and_partial_headers() {
        let input = [0xb6u8, 0x1d, 0xd2, 0x8f, 4, 0xa9, 0xc3, 0x75];
        let order = [
            16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,
        ];
        for initial_count in 0..=64u8 {
            let available = if initial_count == 64 {
                0xa591_3ce7_42d8_b60fu64
            } else {
                0xa591_3ce7_42d8_b60fu64 & ((1u64 << initial_count) - 1)
            };
            for len in 0..=input.len() {
                let pending = input[..len]
                    .iter()
                    .enumerate()
                    .fold(0u64, |bits, (index, &byte)| {
                        bits | (u64::from(byte) << (8 * index))
                    });
                let source = u128::from(available) | (u128::from(pending) << initial_count);
                for cached in [false, true] {
                    let initial_word = if cached { source as u64 } else { available };
                    for target in 0..=19 {
                        for start in 0..=target {
                            let mut lengths = [u16::MAX; 23];
                            for &symbol in &order[..start] {
                                lengths[symbol] = 5;
                            }
                            let before = lengths;
                            let mut have = start;
                            let mut count = initial_count;
                            let mut word = initial_word;
                            let (consumed, complete) = super::super::header_lengths::read_lengths(
                                &mut word,
                                &mut count,
                                &input[..len],
                                &mut lengths,
                                &mut have,
                                target,
                            );
                            let required = (3 * (target - start))
                                .saturating_sub(usize::from(initial_count))
                                .div_ceil(8);
                            let fields =
                                (target - start).min((usize::from(initial_count) + 8 * len) / 3);
                            assert_eq!(consumed, required.min(len));
                            assert_eq!(complete, have == target);
                            assert_eq!(have, start + fields);
                            assert_eq!(
                                usize::from(count),
                                usize::from(initial_count) + 8 * consumed - 3 * fields
                            );
                            let prefix = if consumed == 8 {
                                pending
                            } else {
                                pending & ((1u64 << (8 * consumed)) - 1)
                            };
                            let loaded = (u128::from(initial_word)
                                | (u128::from(prefix) << initial_count))
                                as u64;
                            assert_eq!(word, loaded >> (3 * fields));
                            for slot in 0..lengths.len() {
                                let position = order.iter().position(|&symbol| symbol == slot);
                                assert_eq!(
                                    lengths[slot],
                                    match position {
                                        Some(position) if start <= position && position < have =>
                                            ((source >> (3 * (position - start))) & 7) as u16,
                                        _ => before[slot],
                                    }
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn slice_fill_preserves_partial_exhaustion_and_exact_input_accounting() {
        let input = [0xb6, 0x1d, 0xd2, 0x8f, 4, 0xa9, 0xc3, 0x75, 0x6a];
        for len in 0..=input.len() {
            for discarded in 0..=8 {
                if len == 0 && discarded != 0 {
                    continue;
                }
                let mut initial = BitReader::new(&input[..len]);
                if len != 0 {
                    assert_eq!(initial.pull_byte(), Ok(input[0]));
                    initial.drop_bits(discarded);
                }
                for target in 0..=56 {
                    let mut reader = initial;
                    let position = usize::from(discarded);
                    let loaded = usize::from(len != 0);
                    let end = len.min(loaded.max((position + target).div_ceil(8)));
                    let expected_count = end * 8 - position;
                    let expected = if expected_count >= target {
                        Ok(())
                    } else {
                        Err(ReturnCode::Ok)
                    };
                    assert_eq!(reader.need_bits(target), expected);
                    assert_eq!(reader.bytes_remaining(), len - end);
                    assert_eq!(usize::from(reader.bits_in_buffer()), expected_count);
                    for offset in position..end * 8 {
                        assert_eq!(
                            reader.bits(1),
                            u64::from((input[offset / 8] >> (offset % 8)) & 1)
                        );
                        reader.drop_bits(1);
                    }
                    assert_eq!(reader.bits_in_buffer(), 0);
                }
            }
        }
    }
}
