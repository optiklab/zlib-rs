use libz_rs_sys::{
    inflate, inflateEnd, inflateInit2_, z_stream, zlibVersion, Z_BUF_ERROR, Z_DATA_ERROR,
    Z_NO_FLUSH, Z_OK, Z_STREAM_END,
};

// RFC 1951 3.2.7: code-length symbols 18/0/1 have lengths 1/2/2.
// Two symbol-18 runs encode 256 zeros, followed by EOB/distance lengths 1/1.
// The only data symbol is EOB. Independently accepted by zlib 1.3.1.
const EMPTY_DYNAMIC: [u8; 12] = [
    0x05, 0xc0, 0x81, 0x08, 0x00, 0x00, 0x00, 0x00, 0x20, 0x7f, 0xeb, 0x07,
];

// Repeat 16 crosses literal 255 / EOB 256 / distance 0 and 1.
// Independently accepted by C-zlib 1.3.1 for all twelve input chunk sizes.
const CROSS_ALPHABET_REPEAT: [u8; 12] = [
    0x05, 0xc1, 0x85, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20, 0x7f, 0xea, 0x26,
];

#[test]
fn empty_code_length_alphabet_preserves_suspension_and_missing_eob_error_timing() {
    // Pinned C-zlib 1.3.1: 29 header bits, then 258 one-bit zero lengths.
    for schedule in [&[35usize][..], &[4, 31], &[4, 8, 23]] {
        let mut input = [0u8; 36];
        input[0] = 0x05;
        let mut output = [0xa5u8];
        let mut stream = z_stream::default();
        unsafe {
            assert_eq!(
                inflateInit2_(
                    &mut stream,
                    -15,
                    zlibVersion(),
                    core::mem::size_of::<z_stream>() as i32,
                ),
                Z_OK
            );
            stream.next_out = output.as_mut_ptr();
            stream.avail_out = 1;
            let mut supplied = 0;
            for &size in schedule {
                stream.next_in = input[supplied..].as_mut_ptr();
                stream.avail_in = size as _;
                supplied += size;
                assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_OK);
                assert_eq!((stream.total_in as usize, stream.avail_in), (supplied, 0));
                assert!(stream.msg.is_null());
                assert_eq!((stream.avail_out, stream.total_out, output), (1, 0, [0xa5]));
                stream.next_in = core::ptr::null_mut();
                assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_BUF_ERROR);
                assert_eq!(stream.total_in as usize, supplied);
            }
            assert_eq!(supplied, 35);
            assert_eq!(stream.data_type & 63, 0);
            stream.next_in = input[35..].as_mut_ptr();
            stream.avail_in = 1;
            assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_DATA_ERROR);
            assert_eq!(
                (stream.total_in, stream.avail_in, stream.data_type & 63),
                (36, 0, 1)
            );
            assert_eq!((stream.avail_out, stream.total_out, output), (1, 0, [0xa5]));
            assert_eq!(
                core::ffi::CStr::from_ptr(stream.msg).to_bytes(),
                b"invalid code -- missing end-of-block"
            );
            assert_eq!(inflateEnd(&mut stream), Z_OK);
        }
    }
}

#[test]
fn dynamic_header_resumes_at_every_input_chunk_size_without_losing_partial_fields() {
    for fixture in [EMPTY_DYNAMIC, CROSS_ALPHABET_REPEAT] {
        for chunk_size in 1..=fixture.len() {
            let mut input = fixture;
            let mut output = [0xa5u8];
            let mut stream = z_stream::default();
            unsafe {
                assert_eq!(
                    inflateInit2_(
                        &mut stream,
                        -15,
                        zlibVersion(),
                        core::mem::size_of::<z_stream>() as i32,
                    ),
                    Z_OK
                );
                stream.next_out = output.as_mut_ptr();
                stream.avail_out = 1;
                let mut supplied = 0;
                let mut result = Z_OK;
                for chunk in input.chunks_mut(chunk_size) {
                    supplied += chunk.len();
                    stream.next_in = chunk.as_mut_ptr();
                    stream.avail_in = chunk.len() as _;
                    result = inflate(&mut stream, Z_NO_FLUSH);
                    assert_eq!(
                        result,
                        if supplied == fixture.len() {
                            Z_STREAM_END
                        } else {
                            Z_OK
                        },
                        "chunk size {chunk_size}, supplied {supplied}"
                    );
                    assert_eq!(stream.avail_in, 0);
                    assert_eq!(stream.total_in as usize, supplied);
                    assert_eq!((stream.avail_out, stream.total_out, output), (1, 0, [0xa5]));
                    if result != Z_STREAM_END {
                        stream.next_in = core::ptr::null_mut();
                        assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_BUF_ERROR);
                        assert_eq!(stream.total_in as usize, supplied);
                        assert_eq!((stream.avail_out, stream.total_out, output), (1, 0, [0xa5]));
                    }
                }
                assert_eq!(result, Z_STREAM_END);
                assert_eq!(inflateEnd(&mut stream), Z_OK);
            }
        }
    }
}

#[test]
fn repeat_without_a_previous_length_reports_data_error_without_output() {
    // Complete code-length tree for 16/18; its first decoded symbol is 16.
    // Independently rejected as "invalid bit length repeat" by zlib 1.3.1.
    let mut input = [0x05u8, 0x00, 0x82, 0x00];
    let mut output = [0xa5u8];
    let mut stream = z_stream::default();
    unsafe {
        assert_eq!(
            inflateInit2_(
                &mut stream,
                -15,
                zlibVersion(),
                core::mem::size_of::<z_stream>() as i32,
            ),
            Z_OK
        );
        stream.next_in = input.as_mut_ptr();
        stream.avail_in = input.len() as _;
        stream.next_out = output.as_mut_ptr();
        stream.avail_out = 1;
        let result = inflate(&mut stream, Z_NO_FLUSH);
        assert_eq!(result, Z_DATA_ERROR);
        assert_eq!(stream.total_in as usize, input.len());
        assert_eq!((stream.avail_out, stream.total_out, output), (1, 0, [0xa5]));
        assert_eq!(
            core::ffi::CStr::from_ptr(stream.msg).to_bytes(),
            b"invalid bit length repeat"
        );
        assert_eq!(inflateEnd(&mut stream), Z_OK);
    }
}

#[test]
fn repeat_without_previous_waits_for_the_complete_extra_field() {
    // Seven header fields end at bit 38; only code 16 and one extra bit remain.
    let mut input = [0x05u8, 0x60, 0x82, 0x00, 0x00];
    let mut continuation = [0u8];
    let mut output = [0xa5u8];
    let mut stream = z_stream::default();
    unsafe {
        assert_eq!(
            inflateInit2_(
                &mut stream,
                -15,
                zlibVersion(),
                core::mem::size_of::<z_stream>() as i32,
            ),
            Z_OK
        );
        stream.next_in = input.as_mut_ptr();
        stream.avail_in = input.len() as _;
        stream.next_out = output.as_mut_ptr();
        stream.avail_out = 1;
        assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_OK);
        assert_eq!((stream.total_in, stream.avail_in), (5, 0));
        assert_eq!(stream.data_type & 63, 2);
        assert!(stream.msg.is_null());

        stream.next_in = core::ptr::null_mut();
        assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_BUF_ERROR);
        assert_eq!((stream.total_in, stream.data_type & 63), (5, 2));
        assert!(stream.msg.is_null());

        stream.next_in = continuation.as_mut_ptr();
        stream.avail_in = 1;
        assert_eq!(inflate(&mut stream, Z_NO_FLUSH), Z_DATA_ERROR);
        assert_eq!((stream.total_in, stream.avail_in), (6, 0));
        assert_eq!(stream.data_type & 63, 9);
        assert_eq!((stream.avail_out, stream.total_out, output), (1, 0, [0xa5]));
        assert_eq!(
            core::ffi::CStr::from_ptr(stream.msg).to_bytes(),
            b"invalid bit length repeat"
        );
        assert_eq!(inflateEnd(&mut stream), Z_OK);
    }
}
