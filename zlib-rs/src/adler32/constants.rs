#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) const BASE: u32 = 65521;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) const NMAX: u32 = 5552;
