#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Reflected representation of the RFC 1952 section 2.3.1 CRC polynomial.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const CRC32_LSB_POLY: usize = 0xedb8_8320;
