param(
    [string]$EvidenceDirectory
)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$root = Split-Path $PSScriptRoot -Parent
if (-not $EvidenceDirectory) {
    $EvidenceDirectory = Join-Path $PSScriptRoot ("target\acceptance-" + [guid]::NewGuid().ToString('N'))
}
$EvidenceDirectory = [IO.Path]::GetFullPath($EvidenceDirectory)
if (Test-Path -LiteralPath $EvidenceDirectory) {
    throw "Acceptance requires a new evidence directory: $EvidenceDirectory"
}
New-Item -ItemType Directory -Path $EvidenceDirectory | Out-Null
$version = (& verus --version | Out-String)
if ($LASTEXITCODE -ne 0 -or $version -notmatch '0\.2026\.11\.02\.8bf68ee') {
    throw 'Select the pinned official Verus release on PATH'
}
if (-not $env:VERUS_Z3_PATH) { throw 'Set VERUS_Z3_PATH to the pinned release solver' }
$solver = (& $env:VERUS_Z3_PATH --version | Out-String)
if ($LASTEXITCODE -ne 0 -or $solver -notmatch 'Z3 version 4\.16\.0') {
    throw 'Select Z3 4.16.0 from the pinned release'
}
$bindings = [ordered]@{
    'fixed_tables::code' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_distance_table' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::build_fixed_distance_table' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_table' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::build_fixed_literal_table' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_000' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_016' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_032' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_048' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_064' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_080' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_096' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_112' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_128' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_144' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_160' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_176' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_192' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_208' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_224' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_240' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_256' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_272' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_288' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_304' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_320' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_336' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_352' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_368' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_384' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_400' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_416' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_432' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_448' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_464' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_480' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'fixed_tables::fixed_literal_496' = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    'huffman::lookup_root_entry' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::emission::emit_entry' = 'zlib-rs\src\inflate\inftrees\emission.rs'
    'huffman::preparation::clamped_root' = 'zlib-rs\src\inflate\inftrees\preparation.rs'
    'huffman::preparation::root_capacity_allowed' = 'zlib-rs\src\inflate\inftrees\preparation.rs'
    'huffman::preparation::prepare_table' = 'zlib-rs\src\inflate\inftrees\preparation.rs'
    'huffman::dynamic_start::read_dynamic_header' = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
    'generic::adler32_rust' = 'zlib-rs\src\adler32\generic.rs'
    'generic::adler32_len_64' = 'zlib-rs\src\adler32\generic.rs'
    'generic::adler32_chunk' = 'zlib-rs\src\adler32\generic.rs'
    'generic::adler32_chunk8' = 'zlib-rs\src\adler32\generic.rs'
    'short::adler32_len_1' = 'zlib-rs\src\adler32\short.rs'
    'short::adler32_len_16' = 'zlib-rs\src\adler32\short.rs'
    'combine::adler32_combine' = 'zlib-rs\src\adler32\combine.rs'
    'crc32::combine::multmodp' = 'zlib-rs\src\crc32\combine.rs'
    'crc32::combine::crc32_combine_op' = 'zlib-rs\src\crc32\combine.rs'
    'crc32::tables::build_crc32_table' = 'zlib-rs\src\crc32\tables.rs'
    'crc32::byte::crc32_table_update' = 'zlib-rs\src\crc32\byte.rs'
    'crc32::byte::get_crc_table' = 'zlib-rs\src\crc32\byte.rs'
    'crc32::byte::crc32_naive_inner' = 'zlib-rs\src\crc32\byte.rs'
    'bitreader::drain_sync_buffer' = 'zlib-rs\src\inflate\bitreader\sync_buffer.rs'
    'buffer::reset_bits' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::prime_bits' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::peek_bits' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::consume_bits' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::align_to_byte' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::append_byte' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::refill_bits' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::return_unused_bits' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::fill_from_slice' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::read_word' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'buffer::refill_from_slice' = 'zlib-rs\src\inflate\bitreader\buffer.rs'
    'huffman::slots::remaining_code_space' = 'zlib-rs\src\inflate\inftrees\slots.rs'
    'huffman::histogram::length_histogram' = 'zlib-rs\src\inflate\inftrees\histogram.rs'
    'huffman::analysis::analyze_lengths' = 'zlib-rs\src\inflate\inftrees\analysis.rs'
    'huffman::sorting::build_offsets' = 'zlib-rs\src\inflate\inftrees\sorting.rs'
    'huffman::sorting::sort_symbols' = 'zlib-rs\src\inflate\inftrees\sorting.rs'
    'huffman::analysis::analyze_and_sort_lengths' = 'zlib-rs\src\inflate\inftrees\analysis.rs'
    'huffman::codes::advance_reversed_code' = 'zlib-rs\src\inflate\inftrees\codes.rs'
    'huffman::codes::reverse_word' = 'zlib-rs\src\inflate\inftrees\codes.rs'
    'huffman::codes::next_code' = 'zlib-rs\src\inflate\inftrees\codes.rs'
    'huffman::replicate::replicate_entry' = 'zlib-rs\src\inflate\inftrees\replicate.rs'
    'huffman::progress::advance_symbol' = 'zlib-rs\src\inflate\inftrees\progress.rs'
    'huffman::entries::table_parameters' = 'zlib-rs\src\inflate\inftrees\entries.rs'
    'huffman::entries::make_entry' = 'zlib-rs\src\inflate\inftrees\entries.rs'
    'huffman::lookahead::subtable_width' = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
    'huffman::layout::root_layout' = 'zlib-rs\src\inflate\inftrees\layout.rs'
    'huffman::layout::advance_layout' = 'zlib-rs\src\inflate\inftrees\layout.rs'
    'huffman::layout::advance_and_link' = 'zlib-rs\src\inflate\inftrees\layout.rs'
    'huffman::inflate_table' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::dynamic_tables::inflate_literal_table' = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
    'huffman::dynamic_tables::inflate_distance_table' = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
    'huffman::dynamic_tables::inflate_completed_literal_table' = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
    'huffman::dynamic_tables::inflate_completed_distance_table' = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
    'huffman::lookup_code_length' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::lookup_subtable_index' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::read_code_length' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::read_length_symbol' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::header_loop::read_length_symbols' = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
    'huffman::header_loop::read_length_header' = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
    'huffman::dynamic_resume::resume_dynamic_header' = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
    'huffman::header_phase::read_header_phase' = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
    'header_state::resume_phase' = 'zlib-rs\src\inflate\header_state.rs'
    'header_state::apply_header_step' = 'zlib-rs\src\inflate\header_state.rs'
    'header_state::read_header_state' = 'zlib-rs\src\inflate\header_state.rs'
    'header_state::HeaderAction::error_message' = 'zlib-rs\src\inflate\header_state.rs'
    'huffman::header_start::read_alphabet_header' = 'zlib-rs\src\inflate\inftrees\header_start.rs'
    'huffman::header_loop::HeaderOutcome::error_message' = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
    'huffman::finish_code_length_table' = 'zlib-rs\src\inflate\inftrees.rs'
    'huffman::read_code_length_table' = 'zlib-rs\src\inflate\inftrees.rs'
    'header_lengths::write_length' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::read_length' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::read_counts' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::read_repeat_extra' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::read_repeat_lengths' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::read_selected_length_symbol' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::read_lengths' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::finish_length_header' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::push_decoded_length' = 'zlib-rs\src\inflate\header_lengths.rs'
    'header_lengths::repeat_decoded_length' = 'zlib-rs\src\inflate\header_lengths.rs'
}
$requirements = [ordered]@{
    'reader_state_proofs::clean_cache_bound' = 'proofs\reader_state.rs'
    'reader_state_proofs::unused_byte_rewind_budget' = 'proofs\reader_state.rs'
    'reader_state_proofs::clean_cache_retarget' = 'proofs\reader_state.rs'
    'reader_state_proofs::exact_fill_clean' = 'proofs\reader_state.rs'
    'reader_state_proofs::bounded_read_clean' = 'proofs\reader_state.rs'
    'reader_state_proofs::register_step_clean' = 'proofs\reader_state.rs'
    'reader_state_proofs::register_path_clean' = 'proofs\reader_state.rs'
    'reader_state_proofs::register_path_retarget' = 'proofs\reader_state.rs'
    'capacity_bound_proofs::slack_bounds' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::slack_double' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::capacity_linear_gap' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::upper_nonnegative' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::closing_slack' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::analytic_certificate' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::tail_bound' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::capacity_remove' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::active_frontier' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::minimum_short_leaves' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::closing_even' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::forest_even' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::skip_root' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::concrete_histogram_bounds' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::occurrences_bound' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::histogram_faithful' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::dynamic_histogram_budget' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::dynamic_no_capacity_error' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::dynamic_candidate_bound' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::root_storage' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::finite_offsets' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::candidate_storage' = 'proofs\capacity_bound.rs'
    'capacity_bound_proofs::independent_sharp_bounds' = 'proofs\capacity_bound.rs'
    'group_closing_proofs::weighted_step' = 'proofs\group_closing.rs'
    'group_closing_proofs::weighted_zero' = 'proofs\group_closing.rs'
    'group_closing_proofs::sum_weighted' = 'proofs\group_closing.rs'
    'group_closing_proofs::count_ordered_window' = 'proofs\group_closing.rs'
    'group_closing_proofs::boundary_quotient_window' = 'proofs\group_closing.rs'
    'group_closing_proofs::deepest_bucket_closes_group' = 'proofs\group_closing.rs'
    'group_closing_proofs::opening_in_closing_window' = 'proofs\group_closing.rs'
    'group_closing_proofs::depth_count_bound' = 'proofs\group_closing.rs'
    'group_closing_proofs::weighted_forest_bound' = 'proofs\group_closing.rs'
    'group_closing_proofs::histogram_forest_bound' = 'proofs\group_closing.rs'
    'group_closing_proofs::certificate_histogram_budget' = 'proofs\group_closing.rs'
    'group_closing_proofs::no_capacity_error_from_certificate' = 'proofs\group_closing.rs'
    'group_closing_proofs::forest_empty_tail' = 'proofs\group_closing.rs'
    'group_closing_proofs::independent_two_page_forest' = 'proofs\group_closing.rs'
    'closing_cost_proofs::canonical_frontier_partition' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::quotient_from_interval' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::closing_zero' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::complement_quotient' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::closing_from_quotients' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::closing_counts_boundaries' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::aligned_leaf_step' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::scaled_unit_gap' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::first_group_aligned' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::complete_suffix_boundary' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::aligned_strict_gap' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::opening_width_attained' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::bounds_path' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::bounds_complete_histogram' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::independent_certificate' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::independent_two_leaf_bound' = 'proofs\closing_cost.rs'
    'closing_cost_proofs::independent_maximizing_closed_costs' = 'proofs\closing_cost.rs'
    'histogram_cost_proofs::bucket_unique' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::width_search' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::normalized_width_exists' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::source_length_join' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::root_key_join' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::first_group_join' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::charge_join' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::sum_join' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::sum_zero_at_max' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::root_key_monotone' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::adjacent_group' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::histogram_budget_excludes_refusal' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::no_capacity_error' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::independent_histogram_cost' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::completion_needs_leaves' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::frontier' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::complete_path' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::slots_from_frontiers' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::path_from_frontiers' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::complete_histogram_path' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::path_suffix_sound' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::path_sound' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::path_leaf_capacity' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::minimum_leaf_budget' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::root_not_raised' = 'proofs\histogram_cost.rs'
    'histogram_cost_proofs::independent_complete_path' = 'proofs\histogram_cost.rs'
    'constructor_cost_proofs::window_cost' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::before_fresh' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::certificate_from_ownership' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::prefix_monotone' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::remove_last_source' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::skip_last_source' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::cells_prefix' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::refusal_cost' = 'proofs\constructor_cost.rs'
    'constructor_cost_proofs::independent_two_page_cost' = 'proofs\constructor_cost.rs'
    'constructor_table_proofs::no_capacity_error' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::first_opening' = 'proofs\constructor_table.rs'
    'constructor_pages_proofs::first_openings_updated' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::opening_ledger_frame' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::independent_first_openings' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::canonical_population' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::remaining_unique' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::chosen_width_unique' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::first_opening_unique' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::window_unique' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::normalized_window' = 'proofs\constructor_pages.rs'
    'huffman_proofs::canonical_prefix_at_cursor' = 'proofs\huffman.rs'
    'constructor_table_proofs::finished' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::refused_result' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::ready_result' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::native_code_parts' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::selected_target' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::written_lookup_leaf' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::lookup_written' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::decoded_word' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::complete' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::initial' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::emission_target' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::emitted' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::past_targets_after_allocation' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::allocated' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::target_bounds' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::tail_frame' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::root_target' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::root_corollary' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::independent_complete_progress' = 'proofs\constructor_table.rs'
    'constructor_table_proofs::independent_complete_table' = 'proofs\constructor_table.rs'
    'constructor_pages_proofs::ordered_positions' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::initial' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::advanced' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::current_opening' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::active_page' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::canonical_self' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::short_root_free' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::storage_bound' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::candidate_storage' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::emission_parameters' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::emission_keeps_links' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::emission_keeps_other_pages' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::allocated' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::fresh_key' = 'proofs\constructor_pages.rs'
    'constructor_pages_proofs::independent_two_pages' = 'proofs\constructor_pages.rs'
    'page_source_proofs::covered' = 'proofs\page_source.rs'
    'page_source_proofs::opening_result' = 'proofs\page_source.rs'
    'page_source_proofs::independent_opening' = 'proofs\page_source.rs'
    'table_pages_proofs::uniform_cells' = 'proofs\table_pages.rs'
    'table_pages_proofs::bounded_cells' = 'proofs\table_pages.rs'
    'table_pages_proofs::updated_cells' = 'proofs\table_pages.rs'
    'table_pages_proofs::budget' = 'proofs\table_pages.rs'
    'table_pages_proofs::initial' = 'proofs\table_pages.rs'
    'table_pages_proofs::allocated' = 'proofs\table_pages.rs'
    'table_pages_proofs::allocation_result' = 'proofs\table_pages.rs'
    'table_pages_proofs::independent_page_order' = 'proofs\table_pages.rs'
    'table_pages_proofs::independent_maximum_budget' = 'proofs\table_pages.rs'
    'subtable_coverage_proofs::lookahead_boundary' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::chosen_width_covers_symbol' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::width_result' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::ordered_quotients' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::canonical_root_order' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::no_root_revisit' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::wire_root_equivalence' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::same_wire_root_covered' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::wire_root_no_revisit' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::independent_root_coverage' = 'proofs\subtable_coverage.rs'
    'subtable_coverage_proofs::independent_wire_order' = 'proofs\subtable_coverage.rs'
    'fixed_tree_proofs::literal_prefix_population' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::distance_prefix_population' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::literal_start' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::distance_start' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::literal_assignment' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::distance_assignment' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::independent_rfc_boundaries' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::fixed_histograms' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::literal_slots' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::distance_slots' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::complete_fixed_distributions' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::five_bit_reversal' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::distance_prefix' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::distance_table' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::independent_distance_cells' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::nine_bit_prefix' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::literal_selected_prefix' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::literal_table' = 'proofs\fixed_trees.rs'
    'fixed_tree_proofs::independent_literal_cells' = 'proofs\fixed_trees.rs'
    'child_emission_proofs::prefix_split' = 'proofs\child_emission.rs'
    'child_emission_proofs::selected_replica' = 'proofs\child_emission.rs'
    'child_emission_proofs::cached_word_projection' = 'proofs\child_emission.rs'
    'child_emission_proofs::prefix_bound' = 'proofs\child_emission.rs'
    'child_emission_proofs::emitted_child_lookup' = 'proofs\child_emission.rs'
    'child_emission_proofs::independent_child_context' = 'proofs\child_emission.rs'
    'child_emission_proofs::independent_child_effect' = 'proofs\child_emission.rs'
    'linked_table_proofs::zero_drop' = 'proofs\linked_table.rs'
    'linked_table_proofs::leaf_not_link' = 'proofs\linked_table.rs'
    'linked_table_proofs::leaf_consumption' = 'proofs\linked_table.rs'
    'linked_table_proofs::direct_not_link' = 'proofs\linked_table.rs'
    'linked_table_proofs::direct_table' = 'proofs\linked_table.rs'
    'linked_table_proofs::child_selection' = 'proofs\linked_table.rs'
    'linked_table_proofs::empty_table' = 'proofs\linked_table.rs'
    'linked_table_proofs::independent_link_extent' = 'proofs\linked_table.rs'
    'linked_table_proofs::three_symbol_prefixes' = 'proofs\linked_table.rs'
    'linked_table_proofs::independent_two_level_table' = 'proofs\linked_table.rs'
    'root_table_proofs::word_entry' = 'proofs\root_table.rs'
    'root_table_proofs::independent_one_bit_word_fixture' = 'proofs\root_table.rs'
    'root_table_proofs::initial' = 'proofs\root_table.rs'
    'root_table_proofs::emitted' = 'proofs\root_table.rs'
    'root_table_proofs::complete' = 'proofs\root_table.rs'
    'root_table_proofs::incomplete_one_bit_shape' = 'proofs\root_table.rs'
    'root_table_proofs::single_symbol_prefix' = 'proofs\root_table.rs'
    'root_table_proofs::incomplete_cursor_code' = 'proofs\root_table.rs'
    'root_table_proofs::incomplete' = 'proofs\root_table.rs'
    'root_table_proofs::finished' = 'proofs\root_table.rs'
    'root_table_proofs::ready_result' = 'proofs\root_table.rs'
    'root_table_proofs::legacy_codes' = 'proofs\root_table.rs'
    'root_table_proofs::independent_one_bit_distance_fixture' = 'proofs\root_table.rs'
    'table_emission_proofs::leaf_role_separation' = 'proofs\table_emission.rs'
    'table_emission_proofs::offset_and_completion_fixture' = 'proofs\table_emission.rs'
    'table_preparation_proofs::root_policy_boundaries' = 'proofs\table_preparation.rs'
    'table_preparation_proofs::code_lengths_capacity' = 'proofs\table_preparation.rs'
    'table_preparation_proofs::requested_root_boundaries' = 'proofs\table_preparation.rs'
    'table_preparation_proofs::clamped_root_at_upper_bound' = 'proofs\table_preparation.rs'
    'dynamic_start_proofs::finish' = 'proofs\dynamic_start.rs'
    'dynamic_start_proofs::compatibility_boundaries' = 'proofs\dynamic_start.rs'
    'dynamic_start_proofs::buffered_count_phase_fixture' = 'proofs\dynamic_start.rs'
    'huffman_proofs::remaining_symbols_decreases' = 'proofs\huffman.rs'
    'huffman_proofs::subtable_link_bounds' = 'proofs\huffman.rs'
    'huffman_proofs::subtable_link_fixture' = 'proofs\huffman.rs'
    'huffman_proofs::distance_subtable_index_fixture' = 'proofs\huffman.rs'
    'huffman_lookahead::masked_subtable_index' = 'proofs\huffman_lookahead.rs'
    'header_producer_proofs::suspend' = 'proofs\header_producer.rs'
    'header_producer_proofs::finish' = 'proofs\header_producer.rs'
    'header_producer_proofs::no_input_empty_header' = 'proofs\header_producer.rs'
    'header_producer_proofs::empty_alphabet_fixture' = 'proofs\header_producer.rs'
    'dynamic_header_proofs::two_symbol_header_codes' = 'proofs\dynamic_header.rs'
    'header_loop_proofs::start' = 'proofs\header_loop.rs'
    'header_loop_proofs::header_completion_fixture' = 'proofs\header_loop.rs'
    'header_loop_proofs::stopped_header_fixture' = 'proofs\header_loop.rs'
    'header_loop_proofs::empty_header_rejected' = 'proofs\header_loop.rs'
    'header_loop_proofs::append_register' = 'proofs\header_loop.rs'
    'header_loop_proofs::register_from_fill' = 'proofs\header_loop.rs'
    'header_loop_proofs::append_symbol' = 'proofs\header_loop.rs'
    'header_loop_proofs::finish' = 'proofs\header_loop.rs'
    'header_loop_proofs::prefix' = 'proofs\header_loop.rs'
    'header_loop_proofs::empty_path_zero' = 'proofs\header_loop.rs'
    'header_loop_proofs::empty_result_missing_eob' = 'proofs\header_loop.rs'
    'header_loop_proofs::completed_repeat_fixture' = 'proofs\header_loop.rs'
    'header_loop_proofs::partial_prefix_fixture' = 'proofs\header_loop.rs'
    'canonical_intervals::canonical_intervals_partition' = 'proofs\canonical_intervals.rs'
    'huffman_decode::root_table_decodes' = 'proofs\huffman_decode.rs'
    'huffman_decode::root_word_decodes' = 'proofs\huffman_decode.rs'
    'dynamic_header_proofs::wire_roundtrip' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::wire_inverse' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::rfc_wire_order' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::header_counts_bounds' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::header_counts_fixture' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::header_from_wire' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::pad_read_header' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::repeat_count_bounds' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::repeat_extra_bounds' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::repeat_extra_fixture' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::repeat_input_fixture' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::symbol_transition_from_effect' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::symbol_transition_without_code' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::symbol_effect_after_prefix' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::repeat_input_frames' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::symbol_input_fixture' = 'proofs\dynamic_header.rs'
    'dynamic_header_proofs::empty_symbol_input_fixture' = 'proofs\dynamic_header.rs'
    'huffman_lookahead::root_lookahead_stable' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::available_source_prefix' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::filled_u32_prefix' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::root_entry_source' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::root_source_ready' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::rfc_canonical_example' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::root_entry_bounds' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::root_entry_symbol' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::constructed_header_table' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::header_entry_symbol' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::constructed_root_bounds' = 'proofs\huffman_lookahead.rs'
    'huffman_lookahead::peek_root_index' = 'proofs\huffman_lookahead.rs'
    'bit_proofs::shifted_buffer' = 'proofs\bitreader.rs'
    'bit_proofs::appended_buffer' = 'proofs\bitreader.rs'
    'bit_proofs::filled_word_composes' = 'proofs\bitreader.rs'
    'bit_proofs::needed_bytes_after_prefix' = 'proofs\bitreader.rs'
    'bit_proofs::capped_fill_after_prefix' = 'proofs\bitreader.rs'
    'bit_proofs::refill_accounting' = 'proofs\bitreader.rs'
    'bit_proofs::zero_cache_compatible' = 'proofs\bitreader.rs'
    'bit_proofs::cached_append' = 'proofs\bitreader.rs'
    'bit_proofs::cached_consume' = 'proofs\bitreader.rs'
    'bit_proofs::empty_cache' = 'proofs\bitreader.rs'
    'bit_proofs::needed_bytes_bounds' = 'proofs\bitreader.rs'
    'bit_proofs::header_fill_bounds' = 'proofs\bitreader.rs'
    'bit_proofs::input_byte_step' = 'proofs\bitreader.rs'
    'bit_proofs::low_first_octet_fixture' = 'proofs\bitreader.rs'
    'bit_proofs::three_bit_word' = 'proofs\bitreader.rs'
    'bit_proofs::buffered_value' = 'proofs\bitreader.rs'
}
$files = @(
    'proofs\reader_state.rs',
    'specs\capacity_bound.rs', 'proofs\capacity_bound.rs',
    'specs\group_closing.rs', 'proofs\group_closing.rs',
    'specs\closing_cost.rs', 'proofs\closing_cost.rs',
    'specs\histogram_cost.rs', 'proofs\histogram_cost.rs',
    'specs\constructor_cost.rs', 'proofs\constructor_cost.rs',
    'specs\constructor_table.rs', 'proofs\constructor_table.rs',
    'specs\constructor_pages.rs', 'proofs\constructor_pages.rs',
    'specs\page_source.rs', 'proofs\page_source.rs',
    'specs\table_pages.rs', 'proofs\table_pages.rs',
    'specs\subtable_coverage.rs', 'proofs\subtable_coverage.rs',
    'proofs\child_emission.rs',
    'specs\linked_table.rs', 'proofs\linked_table.rs',
    'specs\root_table.rs', 'proofs\root_table.rs',
    'specs\table_emission.rs', 'proofs\table_emission.rs',
    'zlib-rs\src\inflate\inftrees\emission.rs',
    'specs\table_preparation.rs', 'proofs\table_preparation.rs',
    'zlib-rs\src\inflate\inftrees\preparation.rs',
    'specs\dynamic_start.rs', 'proofs\dynamic_start.rs',
    'zlib-rs\src\inflate\inftrees\dynamic_start.rs',
    'verus\Cargo.toml', 'verus\Cargo.lock', 'verus\rust-toolchain.toml', 'verus\lib.rs',
    'specs\adler32.rs', 'proofs\adler32.rs', 'zlib-rs\src\adler32\constants.rs',
    'verus\crc32.rs', 'specs\crc32.rs', 'proofs\crc32.rs', 'zlib-rs\src\crc32\constants.rs',
    'specs\bitreader.rs', 'proofs\bitreader.rs', 'specs\huffman.rs', 'proofs\huffman.rs',
    'proofs\canonical_intervals.rs',
    'specs\fixed_trees.rs', 'proofs\fixed_trees.rs',
    'proofs\huffman_decode.rs',
    'proofs\huffman_lookahead.rs',
    'specs\dynamic_header.rs', 'proofs\dynamic_header.rs',
    'specs\header_loop.rs', 'proofs\header_loop.rs',
    'specs\header_producer.rs', 'proofs\header_producer.rs',
    'zlib-rs\src\lib.rs', 'zlib-rs\src\code.rs',
    'zlib-rs\src\table_constants.rs',
    'zlib-rs\src\inflate.rs', 'zlib-rs\src\inflate\bitreader.rs',
    'zlib-rs\src\inflate\inftrees.rs',
    'libz-rs-sys\tests\inflate_sync.rs', 'libz-rs-sys\tests\dynamic_header.rs',
    'Cargo.toml', 'zlib-rs\Cargo.toml',
    'verus\verify.ps1', 'verus\check-negative-controls.ps1'
) + @($bindings.Values | Select-Object -Unique)
$hashes = [ordered]@{}
$sourceRoot = Join-Path $EvidenceDirectory 'source'
foreach ($file in $files) {
    $destination = Join-Path $sourceRoot $file
    New-Item -ItemType Directory -Force -Path (Split-Path $destination) | Out-Null
    Copy-Item -LiteralPath (Join-Path $root $file) -Destination $destination
    $hashes[$file] = (Get-FileHash -LiteralPath $destination -Algorithm SHA256).Hash
}
$stdout = Join-Path $EvidenceDirectory 'stdout.log'
$stderr = Join-Path $EvidenceDirectory 'stderr.log'
& cargo +1.99.1 verus verify --manifest-path (Join-Path $sourceRoot 'verus\Cargo.toml') `
    --locked --target-dir (Join-Path $EvidenceDirectory 'build') `
    --fwd-verus-args-to roots -- --no-cheating --output-json 1> $stdout 2> $stderr
if ($LASTEXITCODE -ne 0) { throw "Verification failed; see $stderr" }

$output = [IO.File]::ReadAllText($stdout)
# The pinned Cargo mode may print successful dependency summaries before root JSON.
$json = [regex]::Replace($output, '\A(?:verification results:: \d+ verified, 0 errors\r?\n)*', '')
$result = $json | ConvertFrom-Json
$summary = $result.'verification-results'
if (-not $summary.success -or $summary.errors -ne 0 -or $summary.verified -le 0 `
    -or -not $summary.'is-verifying-entire-crate') {
    throw 'Missing unrestricted successful application proof summary'
}
$observed = @($result.'func-details'.PSObject.Properties.Name)
foreach ($name in @($bindings.Keys) + @($requirements.Keys)) {
    if ($observed -notcontains "zlib_rs_verification::$name") {
        throw "Missing application function binding: $name"
    }
}
foreach ($file in $hashes.Keys) {
    if ((Get-FileHash -LiteralPath (Join-Path $root $file) -Algorithm SHA256).Hash -ne $hashes[$file]) {
        throw "Live source changed during frozen-source acceptance: $file"
    }
}
[ordered]@{
    command = 'cargo +1.99.1 verus verify --manifest-path <frozen-source>\verus\Cargo.toml --locked --target-dir <fresh> --fwd-verus-args-to roots -- --no-cheating --output-json'
    verifier = $version.Trim()
    solver = $solver.Trim()
    lifetime_checking = $true
    erasure_checking = $true
    result = $summary
    production_bindings = $bindings
    requirement_bindings = $requirements
    source_sha256 = $hashes
} | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath (Join-Path $EvidenceDirectory 'evidence.json')
Write-Output "$($summary.verified) verified, 0 errors; $($bindings.Count) production bindings present."
Write-Output "Retained acceptance evidence: $EvidenceDirectory"
exit 0
