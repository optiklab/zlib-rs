#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Code {
    /// operation, extra bits, table bits
    pub op: u8,
    /// bits in this part of the code
    pub bits: u8,
    /// offset in table or code value
    pub val: u16,
}
