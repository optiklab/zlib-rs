//! Same-source proof root. Only the modules explicitly imported here are covered.
#![feature(proc_macro_hygiene)]
#![feature(cfg_eval)]

#[path = "../zlib-rs/src/code.rs"]
mod code;
pub(crate) use code::Code;
#[path = "../zlib-rs/src/table_constants.rs"]
mod table_constants;
pub(crate) use table_constants::{ENOUGH_DISTS, ENOUGH_LENS};

#[path = "../zlib-rs/src/adler32/constants.rs"]
mod constants;
#[path = "../proofs/adler32.rs"]
mod proofs;
#[path = "../specs/adler32.rs"]
mod specs;
use constants::NMAX;
#[path = "../zlib-rs/src/adler32/combine.rs"]
mod combine;
#[path = "../zlib-rs/src/adler32/generic.rs"]
mod generic;
#[path = "../zlib-rs/src/adler32/short.rs"]
mod short;

mod crc32;
#[path = "../proofs/crc32.rs"]
mod crc_proofs;
#[path = "../specs/crc32.rs"]
mod crc_specs;

#[path = "../proofs/bitreader.rs"]
mod bit_proofs;
#[path = "../specs/bitreader.rs"]
mod bit_specs;
#[path = "../zlib-rs/src/inflate/bitreader/sync_buffer.rs"]
mod bitreader;
#[path = "../zlib-rs/src/inflate/bitreader/buffer.rs"]
mod buffer;
#[path = "../proofs/canonical_intervals.rs"]
mod canonical_intervals;
#[path = "../proofs/capacity_bound.rs"]
mod capacity_bound_proofs;
#[path = "../specs/capacity_bound.rs"]
mod capacity_bound_specs;
#[path = "../proofs/child_emission.rs"]
mod child_emission_proofs;
#[path = "../proofs/closing_cost.rs"]
mod closing_cost_proofs;
#[path = "../specs/closing_cost.rs"]
mod closing_cost_specs;
#[path = "../proofs/constructor_cost.rs"]
mod constructor_cost_proofs;
#[path = "../specs/constructor_cost.rs"]
mod constructor_cost_specs;
#[path = "../proofs/constructor_pages.rs"]
mod constructor_pages_proofs;
#[path = "../specs/constructor_pages.rs"]
mod constructor_pages_specs;
#[path = "../proofs/constructor_table.rs"]
mod constructor_table_proofs;
#[path = "../specs/constructor_table.rs"]
mod constructor_table_specs;
#[path = "../proofs/dynamic_header.rs"]
mod dynamic_header_proofs;
#[path = "../specs/dynamic_header.rs"]
mod dynamic_header_specs;
#[path = "../proofs/dynamic_start.rs"]
mod dynamic_start_proofs;
#[path = "../specs/dynamic_start.rs"]
mod dynamic_start_specs;
#[path = "../zlib-rs/src/inflate/inffixed_tbl.rs"]
mod fixed_tables;
#[path = "../proofs/fixed_trees.rs"]
mod fixed_tree_proofs;
#[path = "../specs/fixed_trees.rs"]
mod fixed_tree_specs;
#[path = "../proofs/group_closing.rs"]
mod group_closing_proofs;
#[path = "../specs/group_closing.rs"]
mod group_closing_specs;
#[path = "../zlib-rs/src/inflate/header_lengths.rs"]
mod header_lengths;
#[path = "../proofs/header_loop.rs"]
mod header_loop_proofs;
#[path = "../specs/header_loop.rs"]
mod header_loop_specs;
#[path = "../proofs/header_producer.rs"]
mod header_producer_proofs;
#[path = "../specs/header_producer.rs"]
mod header_producer_specs;
#[path = "../zlib-rs/src/inflate/header_state.rs"]
mod header_state;
#[path = "../proofs/histogram_cost.rs"]
mod histogram_cost_proofs;
#[path = "../specs/histogram_cost.rs"]
mod histogram_cost_specs;
#[path = "../zlib-rs/src/inflate/inftrees.rs"]
mod huffman;
#[path = "../proofs/huffman_decode.rs"]
mod huffman_decode;
#[path = "../proofs/huffman_lookahead.rs"]
mod huffman_lookahead;
#[path = "../proofs/huffman.rs"]
mod huffman_proofs;
#[path = "../specs/huffman.rs"]
mod huffman_specs;
#[path = "../proofs/linked_table.rs"]
mod linked_table_proofs;
#[path = "../specs/linked_table.rs"]
mod linked_table_specs;
#[path = "../proofs/page_source.rs"]
mod page_source_proofs;
#[path = "../specs/page_source.rs"]
mod page_source_specs;
#[path = "../proofs/reader_state.rs"]
mod reader_state_proofs;
#[path = "../proofs/root_table.rs"]
mod root_table_proofs;
#[path = "../specs/root_table.rs"]
mod root_table_specs;
#[path = "../proofs/subtable_coverage.rs"]
mod subtable_coverage_proofs;
#[path = "../specs/subtable_coverage.rs"]
mod subtable_coverage_specs;
#[path = "../proofs/table_emission.rs"]
mod table_emission_proofs;
#[path = "../specs/table_emission.rs"]
mod table_emission_specs;
#[path = "../proofs/table_pages.rs"]
mod table_pages_proofs;
#[path = "../specs/table_pages.rs"]
mod table_pages_specs;
#[path = "../proofs/table_preparation.rs"]
mod table_preparation_proofs;
#[path = "../specs/table_preparation.rs"]
mod table_preparation_specs;
