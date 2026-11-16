use libz_rs_sys::{
    inflate, inflateEnd, inflateInit2_, inflatePrime, inflateSync, z_stream, zlibVersion,
    Z_DATA_ERROR, Z_NO_FLUSH, Z_OK, Z_STREAM_END,
};

#[test]
fn prime_does_not_rewind_unconsumed_input() {
    let mut stream = z_stream::default();
    let mut input = [0u8; 32];
    let mut output = [0u8; 512];
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
        assert_eq!(inflatePrime(&mut stream, 16, 3), Z_OK);
        assert_eq!(inflatePrime(&mut stream, 2, 0), Z_OK);
        stream.next_in = input.as_mut_ptr();
        stream.avail_in = input.len() as u32;
        stream.next_out = output.as_mut_ptr();
        stream.avail_out = output.len() as u32;
        let result = inflate(&mut stream, Z_NO_FLUSH);
        assert_eq!(inflateEnd(&mut stream), Z_OK);
        assert_eq!(result, Z_STREAM_END);
        assert_eq!(stream.next_in, input.as_mut_ptr());
        assert_eq!(stream.avail_in, input.len() as u32);
        assert_eq!((stream.total_in, stream.total_out), (0, 0));
    }
}

#[test]
fn sync_handles_empty_input_with_buffered_marker() {
    for complete in [false, true] {
        for null_input in [false, true] {
            let mut stream = z_stream::default();
            let mut backing = [0u8];

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
                if complete {
                    assert_eq!(inflatePrime(&mut stream, 16, 0), Z_OK);
                    assert_eq!(inflatePrime(&mut stream, 16, 0xffff), Z_OK);
                } else {
                    assert_eq!(inflatePrime(&mut stream, 8, 0), Z_OK);
                }
                stream.next_in = if null_input {
                    core::ptr::null_mut()
                } else {
                    backing.as_mut_ptr()
                };
                let next_in = stream.next_in;
                let result = inflateSync(&mut stream);
                assert_eq!(inflateEnd(&mut stream), Z_OK);
                assert_eq!(result, if complete { Z_OK } else { Z_DATA_ERROR });
                assert_eq!(stream.next_in, next_in);
                assert_eq!(stream.avail_in, 0);
                assert_eq!((stream.total_in, stream.total_out), (0, 0));
            }
        }
    }
}

#[test]
fn sync_preserves_buffered_bytes_after_bit_alignment() {
    for padding in 0..8 {
        let mut stream = z_stream::default();
        let buffered = (0x00ff_0000u32 << padding) | ((1u32 << padding) - 1);
        let mut tail = [0xffu8];

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
            assert_eq!(
                inflatePrime(&mut stream, 16, (buffered & 0xffff) as i32),
                Z_OK
            );
            assert_eq!(
                inflatePrime(&mut stream, 8 + padding, (buffered >> 16) as i32),
                Z_OK
            );
            stream.next_in = tail.as_mut_ptr();
            stream.avail_in = 1;
            let result = inflateSync(&mut stream);
            assert_eq!(inflateEnd(&mut stream), Z_OK);
            assert_eq!(result, Z_OK, "alignment padding: {padding}");
            assert_eq!(stream.avail_in, 0);
            assert_eq!(stream.total_in, 1);
        }
    }
}
