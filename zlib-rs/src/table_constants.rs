#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const ENOUGH_LENS: usize = 1332;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const ENOUGH_DISTS: usize = 592;
