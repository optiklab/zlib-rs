use crate::huffman_specs::Alphabet;
use crate::table_preparation_specs as model;
use vstd::prelude::*;

verus! {

pub(crate) proof fn root_policy_boundaries()
    ensures model::root_capacity_allowed(Alphabet::LiteralLengths, 1024),
        !model::root_capacity_allowed(Alphabet::LiteralLengths, 2048),
        model::root_capacity_allowed(Alphabet::Distances, 512),
        !model::root_capacity_allowed(Alphabet::Distances, 1024),
        model::root_capacity_allowed(Alphabet::CodeLengths, 32768),
        model::require_complete(Alphabet::CodeLengths),
        !model::require_complete(Alphabet::LiteralLengths),
        !model::require_complete(Alphabet::Distances),
{
    reveal(model::root_capacity_allowed);
}

pub(crate) proof fn code_lengths_capacity()
    ensures forall|used: nat| model::root_capacity_allowed(Alphabet::CodeLengths, used),
{
    reveal(model::root_capacity_allowed);
}

pub(crate) proof fn requested_root_boundaries()
    ensures model::clamped_root(0, 1, 11) == 1,
        model::clamped_root(usize::MAX as nat, 1, 11) == 11,
        model::clamped_root(10, 1, 11) == 10,
        model::clamped_root(0, 4, 4) == 4,
        model::clamped_root(usize::MAX as nat, 4, 4) == 4,
{
    reveal(model::clamped_root);
}

pub(crate) proof fn clamped_root_at_upper_bound(requested: nat, minimum: nat, maximum: nat)
    requires minimum <= maximum <= requested,
    ensures model::clamped_root(requested, minimum, maximum) == maximum,
{
    reveal(model::clamped_root);
}

}
