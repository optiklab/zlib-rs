param(
    [string]$EvidenceDirectory,
    [string[]]$Controls = @()
)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false
$root = Split-Path $PSScriptRoot -Parent
if (-not $EvidenceDirectory) {
    $EvidenceDirectory = Join-Path $PSScriptRoot ("target\controls-" + [guid]::NewGuid().ToString('N'))
}
$EvidenceDirectory = [IO.Path]::GetFullPath($EvidenceDirectory)
if (Test-Path -LiteralPath $EvidenceDirectory) {
    throw "Controls require a new evidence directory: $EvidenceDirectory"
}
New-Item -ItemType Directory -Path $EvidenceDirectory | Out-Null
$build = Join-Path $EvidenceDirectory 'dependency-build'

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
    'zlib-rs\src\inflate\inffixed_tbl.rs',
    'specs\fixed_trees.rs', 'proofs\fixed_trees.rs',
    'specs\root_table.rs', 'proofs\root_table.rs',
    'specs\table_emission.rs', 'proofs\table_emission.rs',
    'zlib-rs\src\inflate\inftrees\emission.rs',
    'specs\table_preparation.rs', 'proofs\table_preparation.rs',
    'zlib-rs\src\inflate\inftrees\preparation.rs',
    'specs\dynamic_start.rs', 'proofs\dynamic_start.rs',
    'zlib-rs\src\inflate\inftrees\dynamic_resume.rs',
    'zlib-rs\src\inflate\inftrees\header_phase.rs',
    'zlib-rs\src\inflate\header_state.rs',
    'zlib-rs\src\inflate\inftrees\dynamic_start.rs',
    'zlib-rs\src\inflate\inftrees\dynamic_tables.rs',
    'verus\Cargo.toml', 'verus\Cargo.lock', 'verus\rust-toolchain.toml', 'verus\lib.rs',
    'zlib-rs\src\code.rs', 'zlib-rs\src\table_constants.rs',
    'specs\adler32.rs', 'proofs\adler32.rs',
    'zlib-rs\src\adler32\constants.rs', 'zlib-rs\src\adler32\short.rs',
    'zlib-rs\src\adler32\combine.rs', 'zlib-rs\src\adler32\generic.rs',
    'verus\crc32.rs', 'specs\crc32.rs', 'proofs\crc32.rs',
    'zlib-rs\src\crc32\constants.rs', 'zlib-rs\src\crc32\combine.rs',
    'zlib-rs\src\crc32\tables.rs', 'zlib-rs\src\crc32\byte.rs',
    'specs\bitreader.rs', 'proofs\bitreader.rs', 'specs\huffman.rs', 'proofs\huffman.rs',
    'proofs\canonical_intervals.rs',
    'proofs\huffman_decode.rs',
    'proofs\huffman_lookahead.rs',
    'specs\dynamic_header.rs', 'proofs\dynamic_header.rs',
    'specs\header_loop.rs', 'proofs\header_loop.rs',
    'specs\header_producer.rs', 'proofs\header_producer.rs',
    'zlib-rs\src\inflate\inftrees\header_start.rs',
    'zlib-rs\src\inflate\inftrees\header_loop.rs',
    'zlib-rs\src\inflate\header_lengths.rs',
    'zlib-rs\src\inflate\bitreader\sync_buffer.rs', 'zlib-rs\src\inflate\inftrees\slots.rs',
    'zlib-rs\src\inflate\bitreader\buffer.rs',
    'zlib-rs\src\inflate\inftrees.rs', 'zlib-rs\src\inflate\inftrees\histogram.rs',
    'zlib-rs\src\inflate\inftrees\analysis.rs', 'zlib-rs\src\inflate\inftrees\sorting.rs',
    'zlib-rs\src\inflate\inftrees\codes.rs', 'zlib-rs\src\inflate\inftrees\replicate.rs',
    'zlib-rs\src\inflate\inftrees\progress.rs', 'zlib-rs\src\inflate\inftrees\entries.rs',
    'zlib-rs\src\inflate\inftrees\lookahead.rs', 'zlib-rs\src\inflate\inftrees\layout.rs',
    'zlib-rs\src\lib.rs', 'zlib-rs\src\inflate.rs', 'zlib-rs\src\inflate\bitreader.rs',
    'libz-rs-sys\tests\inflate_sync.rs', 'libz-rs-sys\tests\dynamic_header.rs',
    'Cargo.toml', 'zlib-rs\Cargo.toml',
    'verus\verify.ps1', 'verus\check-negative-controls.ps1'
)
$cases = @(
    @{
        Name = 'equivalent-state-lengths-entry'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = 'if !matches!(*mode, Mode::CodeLens) {'
        New = 'if matches!(*mode, Mode::Table | Mode::LenLens) {'
        Failure = $null
    },
    @{
        Name = 'equivalent-state-table-metadata'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = '&& final(table).bits == root && *final(next) == used'
        New = '&& *final(next) == used && final(table).bits == root'
        Failure = $null
    },
    @{
        Name = 'wrong-state-table-selector'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = 'table.codes = Codes::Codes;'
        New = 'table.codes = Codes::Len;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-state-table-root'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = 'table.bits = root;'
        New = 'table.bits = used;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-state-alphabet-suspend'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = '*mode = Mode::LenLens;'
        New = '*mode = Mode::Table;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-state-counts-action'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = 'HeaderStep::NeedCounts => return HeaderAction::NeedInput,'
        New = 'HeaderStep::NeedCounts => return HeaderAction::Complete,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-state-missing-eob-message'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = 'Self::MissingEob => HeaderOutcome::MissingEob.error_message(),'
        New = 'Self::MissingEob => HeaderOutcome::InvalidRepeat.error_message(),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-state-completion-eob'
        File = 'zlib-rs\src\inflate\header_state.rs'
        Old = '&& final(lens)@[256] != 0,'
        New = '&& final(lens)@[256] == 0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-phase-alphabet-bound'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = '&& have < counts.2,'
        New = '&& have + 0 < counts.2,'
        Failure = $null
    },
    @{
        Name = 'false-phase-alphabet-bound'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = '&& have < counts.2,'
        New = '&& have > counts.2,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-phase-lengths-metadata'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = 'actual == counts && r == root && u == used,'
        New = 'r == root && u == used && actual == counts,'
        Failure = $null
    },
    @{
        Name = 'false-phase-lengths-metadata'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = 'actual == counts && r == root && u == used,'
        New = 'actual == counts && r == root && u != used,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-phase-stable-alphabet'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = 'huffman_specs::header_decoding_table(alphabet, table, root)),'
        New = 'huffman_specs::header_decoding_table(alphabet, table, (root + 1) as usize)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-phase-alphabet-target'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = '                counts.2,'
        New = '                counts.1,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-phase-counts-error'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = 'return (advanced, HeaderStep::InvalidCounts { counts });'
        New = 'return (advanced, HeaderStep::NeedAlphabet { counts });'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-phase-untouched-tail'
        File = 'zlib-rs\src\inflate\inftrees\header_phase.rs'
        Old = '19 <= index < old(lens)@.len() && *final(have) <= index'
        New = '19 <= index < old(lens)@.len()'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-resume-count-sum'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
        Old = 'let total = nlen + ndist;'
        New = 'let total = ndist + nlen;'
        Failure = $null
    },
    @{
        Name = 'wrong-resume-count-sum'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
        Old = 'let total = nlen + ndist;'
        New = 'let total = nlen;'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'equivalent-resume-completion-bound'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
        Old = '*old(have) <= *final(have) <= nlen + ndist <= 316,'
        New = '*old(have) <= *final(have) <= ndist + nlen <= 316,'
        Failure = $null
    },
    @{
        Name = 'false-resume-completion-bound'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
        Old = '*old(have) <= *final(have) <= nlen + ndist <= 316,'
        New = '*old(have) <= *final(have) <= nlen + ndist < 316,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-resume-complete-eob'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
        Old = '<==> *final(have) == nlen + ndist && final(lens)@[256] != 0,'
        New = '<==> *final(have) == nlen + ndist && final(lens)@[256] == 0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-resume-prefix-frame'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_resume.rs'
        Old = '(index < *old(have) || *final(have) <= index)'
        New = '(index <= *old(have) || *final(have) <= index)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-alphabet-stable-table-witness'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'huffman_specs::header_decoding_table(alphabet, final(table)@, root))'
        New = 'huffman_specs::header_decoding_table(alphabet, final(table)@, (root + 0) as usize))'
        Failure = $null
    },
    @{
        Name = 'false-alphabet-stable-table-witness'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'huffman_specs::header_decoding_table(alphabet, final(table)@, root))'
        New = 'huffman_specs::header_decoding_table(alphabet, final(table)@, (root + 1) as usize))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-dynamic-stable-table-witness'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'crate::huffman_specs::header_decoding_table(alphabet, final(table)@, root))'
        New = 'crate::huffman_specs::header_decoding_table(alphabet, final(table)@, (root + 0) as usize))'
        Failure = $null
    },
    @{
        Name = 'false-dynamic-stable-table-witness'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'crate::huffman_specs::header_decoding_table(alphabet, final(table)@, root))'
        New = 'crate::huffman_specs::header_decoding_table(alphabet, final(table)@, (root + 1) as usize))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-completed-literal-entry-result'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'lengths@.subrange(0, nlen as int), 10,'
        New = 'lengths@.subrange(0, nlen as int), 10 + 0,'
        Failure = $null
    },
    @{
        Name = 'false-completed-literal-entry-result'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'lengths@.subrange(0, nlen as int), 10,'
        New = 'lengths@.subrange(0, nlen as int), 9,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-completed-distance-entry-result'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'lengths@.subrange(nlen as int, (nlen + ndist) as int), 9,'
        New = 'lengths@.subrange(nlen as int, (nlen + ndist) as int), 9 + 0,'
        Failure = $null
    },
    @{
        Name = 'false-completed-distance-entry-result'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'lengths@.subrange(nlen as int, (nlen + ndist) as int), 9,'
        New = 'lengths@.subrange(nlen as int, (nlen + ndist) as int), 8,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-completed-literal-entry-extent'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'let literals = &combined[..nlen];'
        New = 'let literals = &combined[..ndist];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-completed-distance-entry-offset'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'let distances = &combined[nlen..];'
        New = 'let distances = &combined[..ndist];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-reset-empty-register'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'ensures *final(word) == 0, *final(count) == 0,'
        New = 'ensures *final(word) == 0 + 0, *final(count) == 0 + 0,'
        Failure = $null
    },
    @{
        Name = 'false-reset-empty-register'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'ensures *final(word) == 0, *final(count) == 0,'
        New = 'ensures *final(word) == 1, *final(count) == 0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-reset-empty-cache'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*word = 0;'
        New = '*word = 1;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-reader-clean-cache-bound'
        File = 'proofs\reader_state.rs'
        Old = 'ensures word < (1u64 << width),'
        New = 'ensures word < (1u64 << (width + 0)),'
        Failure = $null
    },
    @{
        Name = 'false-reader-clean-cache-bound'
        File = 'proofs\reader_state.rs'
        Old = 'ensures word < (1u64 << width),'
        New = 'ensures word == 0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-prime-count-append'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'ensures *final(count) as int == *old(count) as int + bits as int,'
        New = 'ensures *final(count) as int == *old(count) as int + bits as int + 0,'
        Failure = $null
    },
    @{
        Name = 'false-prime-count-append'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'ensures *final(count) as int == *old(count) as int + bits as int,'
        New = 'ensures *final(count) as int == *old(count) as int + bits as int + 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-prime-low-first-value'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '+ bit_specs::buffered_bits(value, bits),'
        New = '+ bit_specs::buffered_bits(value >> 1u8, bits),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-prime-append-direction'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*word += value << *count;'
        New = '*word += value >> *count;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-counts-clean-cache-export'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '#[trigger] bit_specs::cached_suffix(*final(word), *final(count), next_pending),'
        New = '#[trigger] bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, next_pending),'
        Failure = $null
    },
    @{
        Name = 'false-counts-clean-cache-export'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '#[trigger] bit_specs::cached_suffix(*final(word), *final(count), next_pending),'
        New = '#[trigger] bit_specs::cached_suffix(*final(word), 0, next_pending),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-wire-lengths-clean-cache-export'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'false-wire-lengths-clean-cache-export'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), 0, Seq::empty()),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-alphabet-table-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'false-alphabet-table-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), 0, Seq::empty()),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-alphabet-header-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'false-alphabet-header-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), 0, Seq::empty()),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-dynamic-header-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'false-dynamic-header-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), 0, Seq::empty()),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-reader-state-rewind-budget'
        File = 'proofs\reader_state.rs'
        Old = 'ensures final_count / 8 <= advanced,'
        New = 'ensures final_count / 8 <= advanced + 0,'
        Failure = $null
    },
    @{
        Name = 'missing-reader-state-rewind-entry-bound'
        File = 'proofs\reader_state.rs'
        Old = 'requires initial_count < 8,'
        New = 'requires initial_count <= 8,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-reader-state-rewind-budget'
        File = 'proofs\reader_state.rs'
        Old = 'ensures final_count / 8 <= advanced,'
        New = 'ensures final_count / 8 < advanced,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-slice-fill-clean-cache'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = '            bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'false-slice-fill-clean-cache'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '            bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = '            bit_specs::cached_suffix(*final(word), 0, Seq::empty()),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'false-header-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'bit_specs::cached_suffix(*final(word), *final(count), Seq::empty()),'
        New = 'bit_specs::cached_suffix(*final(word), 0, Seq::empty()),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-symbol-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = '#[trigger] bit_specs::cached_suffix(*final(word), *final(count), next_pending),'
        New = '#[trigger] bit_specs::cached_suffix(*final(word), (*final(count) as int + 0) as u8, next_pending),'
        Failure = $null
    },
    @{
        Name = 'false-symbol-clean-cache-export'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = '#[trigger] bit_specs::cached_suffix(*final(word), *final(count), next_pending),'
        New = '#[trigger] bit_specs::cached_suffix(*final(word), 0, next_pending),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-reader-state-register-drop'
        File = 'specs\header_loop.rs'
        Old = 'after.word == loaded >> ((after.dropped - before.dropped) as u8)'
        New = 'after.word == (loaded >> ((after.dropped - before.dropped) as u8))'
        Failure = $null
    },
    @{
        Name = 'wrong-reader-state-register-drop'
        File = 'specs\header_loop.rs'
        Old = 'after.word == loaded >> ((after.dropped - before.dropped) as u8)'
        New = 'after.word == loaded'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'proofs\reader_state.rs'
    },
    @{
        Name = 'equivalent-reader-state-fill-count'
        File = 'proofs\reader_state.rs'
        Old = 'ensures bits::cached_suffix(after, (count as int + added.len()) as u8, Seq::empty()),'
        New = 'ensures bits::cached_suffix(after, (count as int + added.len() + 0) as u8, Seq::empty()),'
        Failure = $null
    },
    @{
        Name = 'missing-reader-state-exact-fill'
        File = 'proofs\reader_state.rs'
        Old = 'bits::filled_word(before, count, after, added),'
        New = 'true,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-alphabet-resume-wire-prefix'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat)'
        New = 'dynamic_header_specs::prefix_fits(final(lens)@, (*final(have) as nat + 0))'
        Failure = $null
    },
    @{
        Name = 'false-alphabet-resume-wire-prefix'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat)'
        New = 'dynamic_header_specs::prefix_fits(final(lens)@, (*final(have) as nat + 1))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-dynamic-resume-wire-prefix'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'crate::dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat)'
        New = 'crate::dynamic_header_specs::prefix_fits(final(lens)@, (*final(have) as nat + 0))'
        Failure = $null
    },
    @{
        Name = 'false-dynamic-resume-wire-prefix'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'crate::dynamic_header_specs::prefix_fits(final(lens)@, *final(have) as nat)'
        New = 'crate::dynamic_header_specs::prefix_fits(final(lens)@, (*final(have) as nat + 1))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-alphabet-resume-root-width'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = '==> 1 <= (#[trigger] final(table)@[index]).bits <= root)'
        New = '==> 1 <= (#[trigger] final(table)@[index]).bits <= root + 0)'
        Failure = $null
    },
    @{
        Name = 'false-alphabet-resume-root-width'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = '==> 1 <= (#[trigger] final(table)@[index]).bits <= root)'
        New = '==> 1 <= (#[trigger] final(table)@[index]).bits < root)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-dynamic-resume-prefix'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'crate::dynamic_header_specs::decoded_prefix(final(lens)@, *final(have) as nat)'
        New = 'crate::dynamic_header_specs::decoded_prefix(final(lens)@, (*final(have) as nat + 0))'
        Failure = $null
    },
    @{
        Name = 'false-dynamic-resume-prefix'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'crate::dynamic_header_specs::decoded_prefix(final(lens)@, *final(have) as nat)'
        New = 'crate::dynamic_header_specs::decoded_prefix(final(lens)@, (*final(have) as nat + 1))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-literal-caller-root'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'CodeType::Lens, lengths, &mut table[..], 10,'
        New = 'CodeType::Lens, lengths, &mut table[..], 10 + 0,'
        Failure = $null
    },
    @{
        Name = 'wrong-literal-caller-root'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'CodeType::Lens, lengths, &mut table[..], 10,'
        New = 'CodeType::Lens, lengths, &mut table[..], 9,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'equivalent-distance-caller-root'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'CodeType::Dists, lengths, &mut table[..], 9,'
        New = 'CodeType::Dists, lengths, &mut table[..], 9 + 0,'
        Failure = $null
    },
    @{
        Name = 'wrong-distance-caller-root'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'CodeType::Dists, lengths, &mut table[..], 9,'
        New = 'CodeType::Dists, lengths, &mut table[..], 10,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-literal-caller-alphabet'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'CodeType::Lens, lengths,'
        New = 'CodeType::Dists, lengths,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-distance-caller-alphabet'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'CodeType::Dists, lengths,'
        New = 'CodeType::Lens, lengths,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'weak-literal-caller-cardinality'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'requires lengths.len() <= 286,'
        New = 'requires lengths.len() <= 288,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'weak-distance-caller-cardinality'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
        Old = 'requires lengths.len() <= 30,'
        New = 'requires lengths.len() <= 32,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'missing-native-dynamic-capacity-guarantee'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '==> !matches!(result, InflateTable::EnoughIsNotEnough),'
        New = '==> true,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees\dynamic_tables.rs'
    },
    @{
        Name = 'equivalent-tight-literal-extent'
        File = 'specs\capacity_bound.rs'
        Old = 'extent >= 1332'
        New = 'extent >= 1332 + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-tight-literal-extent'
        File = 'specs\capacity_bound.rs'
        Old = 'extent >= 1332'
        New = 'extent >= 1331'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'equivalent-tight-distance-extent'
        File = 'specs\capacity_bound.rs'
        Old = 'extent >= 592'
        New = 'extent >= 592 + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-tight-distance-extent'
        File = 'specs\capacity_bound.rs'
        Old = 'extent >= 592'
        New = 'extent >= 591'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'equivalent-tight-literal-cardinality'
        File = 'specs\capacity_bound.rs'
        Old = 'lengths.len() <= 286'
        New = 'lengths.len() < 287'
        Failure = $null
    },
    @{
        Name = 'weak-tight-literal-cardinality'
        File = 'specs\capacity_bound.rs'
        Old = 'lengths.len() <= 286'
        New = 'lengths.len() <= 288'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'equivalent-tight-distance-cardinality'
        File = 'specs\capacity_bound.rs'
        Old = 'lengths.len() <= 30'
        New = 'lengths.len() < 31'
        Failure = $null
    },
    @{
        Name = 'weak-tight-distance-cardinality'
        File = 'specs\capacity_bound.rs'
        Old = 'lengths.len() <= 30'
        New = 'lengths.len() <= 32'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'wrong-tight-literal-root'
        File = 'specs\capacity_bound.rs'
        Old = 'requested == 10'
        New = 'requested == 11'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'wrong-tight-distance-root'
        File = 'specs\capacity_bound.rs'
        Old = 'requested == 9'
        New = 'requested == 10'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'false-native-literal-root-guarantee'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '((matches!(codetype, CodeType::Lens) && bits == 10 && lens.len() <= 286)'
        New = '((matches!(codetype, CodeType::Lens) && bits == 11 && lens.len() <= 286)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-native-distance-root-guarantee'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '|| (matches!(codetype, CodeType::Dists) && bits == 9 && lens.len() <= 30))'
        New = '|| (matches!(codetype, CodeType::Dists) && bits == 10 && lens.len() <= 30))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-bound-rounding'
        File = 'specs\capacity_bound.rs'
        Old = '(available + size - 1) / size'
        New = '(available + size - 1 + 0) / size'
        Failure = $null
    },
    @{
        Name = 'wrong-bound-rounding-offset'
        File = 'specs\capacity_bound.rs'
        Old = '(available + size - 1) / size'
        New = '(available + size - 2) / size'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'equivalent-bound-slack'
        File = 'specs\capacity_bound.rs'
        Old = 'rounded(available, size) * size - available'
        New = 'rounded(available, size) * size - available + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-bound-slack-debit'
        File = 'specs\capacity_bound.rs'
        Old = 'rounded(available, size) * size - available'
        New = 'rounded(available, size) * size - available - 1'
        Failure = 'requires not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'equivalent-bound-tail-domain'
        File = 'specs\capacity_bound.rs'
        Old = 'if 1 <= root < depth <= 15 {'
        New = 'if 1 <= root && root + 1 <= depth <= 15 {'
        Failure = $null
    },
    @{
        Name = 'missing-bound-terminal-state'
        File = 'specs\capacity_bound.rs'
        Old = 'if 1 <= root < depth <= 15 {'
        New = 'if 1 <= root < depth < 15 {'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'equivalent-bound-terminal-gap'
        File = 'specs\capacity_bound.rs'
        Old = '- size - (15 - depth)) as nat)'
        New = '- size - (15 - depth) + 0) as nat)'
        Failure = $null
    },
    @{
        Name = 'wrong-bound-tail-ceiling'
        File = 'specs\capacity_bound.rs'
        Old = 'h::capacity((15 - root) as nat)'
        New = 'h::capacity((14 - root) as nat)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'wrong-bound-depth-gap'
        File = 'specs\capacity_bound.rs'
        Old = '- size - (15 - depth)) as nat)'
        New = '- size - (16 - depth)) as nat)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
    },
    @{
        Name = 'weak-bound-even-frontier'
        File = 'proofs\capacity_bound.rs'
        Old = 'requires 1 <= root <= 14, available % 2 == 0,'
        New = 'requires 1 <= root <= 14,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'weak-bound-short-leaf-budget'
        File = 'proofs\capacity_bound.rs'
        Old = 'h::before(counts, 16) <= bound, 1 <= root <= 14,'
        New = 'h::before(counts, 16) <= bound + 1, 1 <= root <= 14,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-bound-literal-maximum'
        File = 'proofs\capacity_bound.rs'
        Old = 'ensures cost::forest(counts, root, 1, 2) <= if root == 10 { 308int } else { 80int },'
        New = 'ensures cost::forest(counts, root, 1, 2) <= if root == 10 { 307int } else { 80int },'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-bound-distance-maximum'
        File = 'proofs\capacity_bound.rs'
        Old = 'ensures cost::forest(counts, root, 1, 2) <= if root == 10 { 308int } else { 80int },'
        New = 'ensures cost::forest(counts, root, 1, 2) <= if root == 10 { 308int } else { 79int },'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'weak-bound-literal-cardinality'
        File = 'proofs\capacity_bound.rs'
        Old = "(requested == 10 && lengths.len() <= 286) || (requested == 9 && lengths.len() <= 30),`n    ensures ({"
        New = "(requested == 10 && lengths.len() <= 287) || (requested == 9 && lengths.len() <= 30),`n    ensures ({"
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'weak-bound-distance-cardinality'
        File = 'proofs\capacity_bound.rs'
        Old = "(requested == 10 && lengths.len() <= 286) || (requested == 9 && lengths.len() <= 30),`n    ensures ({"
        New = "(requested == 10 && lengths.len() <= 286) || (requested == 9 && lengths.len() <= 31),`n    ensures ({"
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'weak-bound-candidate-freshness'
        File = 'proofs\capacity_bound.rs'
        Old = "regions[key] == None, opening.position == processed,`n        crate::constructor_pages_specs::first_opening(lengths, work, root, key, opening),`n        crate::page_source_specs::valid_window(lengths, counts, root, max, key, width, opening),`n    ensures used + h::capacity(width) <= if requested == 10"
        New = "regions[key] == None, opening.position <= processed,`n        crate::constructor_pages_specs::first_opening(lengths, work, root, key, opening),`n        crate::page_source_specs::valid_window(lengths, counts, root, max, key, width, opening),`n    ensures used + h::capacity(width) <= if requested == 10"
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'paired-bound-ceiling-translation'
        File = 'specs\capacity_bound.rs'
        Old = '(available + size - 1) / size'
        New = '(available + size) / size'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
        Additional = @(@{
            File = 'specs\closing_cost.rs'
            Old = '(((available + capacity - 1) / capacity'
            New = '(((available + capacity) / capacity'
        }, @{
            File = 'specs\closing_cost.rs'
            Old = '(((available - leaves) as nat + capacity - 1) / capacity)'
            New = '(((available - leaves) as nat + capacity) / capacity)'
        })
    },
    @{
        Name = 'paired-bound-short-horizon'
        File = 'specs\capacity_bound.rs'
        Old = 'h::capacity((15 - root) as nat)'
        New = 'h::capacity((14 - root) as nat)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\capacity_bound.rs'
        Additional = @(@{
            File = 'specs\closing_cost.rs'
            Old = 'available * h::capacity((15 - depth) as nat)'
            New = 'available * h::capacity((14 - depth) as nat)'
        })
    },
    @{
        Name = 'equivalent-group-selected-depth'
        File = 'specs\group_closing.rs'
        Old = '&& depth == root + pages::opening_width('
        New = '&& depth == 0 + root + pages::opening_width('
        Failure = $null
    },
    @{
        Name = 'wrong-group-selected-depth'
        File = 'specs\group_closing.rs'
        Old = '&& depth == root + pages::opening_width('
        New = '&& depth == 1 + root + pages::opening_width('
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'missing-group-first-source'
        File = 'specs\group_closing.rs'
        Old = 'histogram::first_group(counts, root, max, position)'
        New = 'true'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'equivalent-group-count-base'
        File = 'specs\group_closing.rs'
        Old = 'if processed == 0 { 0 }'
        New = 'if processed < 1 { 0 }'
        Failure = $null
    },
    @{
        Name = 'wrong-group-count-base'
        File = 'specs\group_closing.rs'
        Old = 'if processed == 0 { 0 }'
        New = 'if processed == 0 { 1 }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'equivalent-group-count-increment'
        File = 'specs\group_closing.rs'
        Old = '{ 1nat } else { 0nat }'
        New = '{ 0nat + 1nat } else { 0nat }'
        Failure = $null
    },
    @{
        Name = 'wrong-group-count-increment'
        File = 'specs\group_closing.rs'
        Old = '{ 1nat } else { 0nat }'
        New = '{ 2nat } else { 0nat }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'equivalent-group-weight-threshold'
        File = 'specs\group_closing.rs'
        Old = 'if depth > root {'
        New = 'if depth >= root + 1 {'
        Failure = $null
    },
    @{
        Name = 'wrong-group-weight-threshold'
        File = 'specs\group_closing.rs'
        Old = 'if depth > root {'
        New = 'if depth > root + 1 {'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'wrong-group-weight-shift'
        File = 'specs\group_closing.rs'
        Old = 'h::capacity((depth - root) as nat)'
        New = 'h::capacity((depth + 1 - root) as nat)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'equivalent-group-weight-suffix'
        File = 'specs\group_closing.rs'
        Old = 'depth == 0 || depth >= 16'
        New = 'depth == 0 || depth > 15'
        Failure = $null
    },
    @{
        Name = 'wrong-group-weight-terminal'
        File = 'specs\group_closing.rs'
        Old = 'depth == 0 || depth >= 16'
        New = 'depth == 0 || depth >= 15'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
    },
    @{
        Name = 'equivalent-group-window-nonstrict'
        File = 'proofs\group_closing.rs'
        Old = '==> histogram::root_key(counts, root, first) < histogram::root_key(counts, root, second),'
        New = '==> histogram::root_key(counts, root, first) <= histogram::root_key(counts, root, second),'
        Failure = $null
    },
    @{
        Name = 'closed-group-window-upper'
        File = 'proofs\group_closing.rs'
        Old = '==> lower <= histogram::root_key(counts, root, position) < upper,'
        New = '==> lower <= histogram::root_key(counts, root, position) <= upper,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'missing-group-certificate-initial-budget'
        File = 'proofs\group_closing.rs'
        Old = '&& upper(1, 2, remaining).unwrap() <= child_limit,'
        New = '&& true,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'missing-group-root-budget'
        File = 'proofs\group_closing.rs'
        Old = 'h::capacity(root) + child_limit <= limit,'
        New = 'child_limit <= limit,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'equivalent-paired-group-histogram-weight'
        File = 'specs\group_closing.rs'
        Old = '* h::capacity((depth - root) as nat)'
        New = '* (h::capacity((depth - root) as nat) + 0)'
        Failure = $null
        Additional = @(@{
            File = 'specs\histogram_cost.rs'
            Old = 'source_length(counts, position), root, max)) as nat'
            New = 'source_length(counts, position), root, max)) as nat + 0'
        })
    },
    @{
        Name = 'paired-wrong-group-histogram-weight'
        File = 'specs\group_closing.rs'
        Old = '* h::capacity((depth - root) as nat)'
        New = '* (h::capacity((depth - root) as nat) + 1)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\group_closing.rs'
        Additional = @(@{
            File = 'specs\histogram_cost.rs'
            Old = 'source_length(counts, position), root, max)) as nat'
            New = 'source_length(counts, position), root, max)) as nat + 1'
        })
    },
    @{
        Name = 'equivalent-closing-state-budget'
        File = 'specs\closing_cost.rs'
        Old = 'available <= remaining <= bound'
        New = 'available <= remaining && remaining < bound + 1'
        Failure = $null
    },
    @{
        Name = 'wrong-closing-state-frontier'
        File = 'specs\closing_cost.rs'
        Old = 'available <= remaining <= bound'
        New = 'available < remaining <= bound'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'equivalent-closing-edge-consumption'
        File = 'specs\closing_cost.rs'
        Old = '&& state(bound, depth + 1, 2 * (available - leaves) as nat, (remaining - leaves) as nat)'
        New = '&& state(bound, depth + 1, 2 * (available - leaves) as nat, (remaining + 0 - leaves) as nat)'
        Failure = $null
    },
    @{
        Name = 'wrong-closing-edge-consumption'
        File = 'specs\closing_cost.rs'
        Old = '&& state(bound, depth + 1, 2 * (available - leaves) as nat, (remaining - leaves) as nat)'
        New = '&& state(bound, depth + 1, 2 * (available - leaves) as nat, remaining)'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'wrong-closing-edge-doubling'
        File = 'specs\closing_cost.rs'
        Old = '&& state(bound, depth + 1, 2 * (available - leaves) as nat, (remaining - leaves) as nat)'
        New = '&& state(bound, depth + 1, 1 * (available - leaves) as nat, (remaining - leaves) as nat)'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'equivalent-closing-rounding'
        File = 'specs\closing_cost.rs'
        Old = 'available + capacity - 1'
        New = 'available - 1 + capacity'
        Failure = $null
    },
    @{
        Name = 'wrong-closing-rounding'
        File = 'specs\closing_cost.rs'
        Old = 'available + capacity - 1'
        New = 'available + capacity'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'equivalent-closing-cell-weight'
        File = 'specs\closing_cost.rs'
        Old = ')) * capacity) as nat'
        New = ')) * (capacity + 0)) as nat'
        Failure = $null
    },
    @{
        Name = 'wrong-closing-cell-weight'
        File = 'specs\closing_cost.rs'
        Old = ')) * capacity) as nat'
        New = ')) * (capacity + 1)) as nat'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'equivalent-bellman-edge-budget'
        File = 'specs\closing_cost.rs'
        Old = 'closing(root, depth, available, leaves) + next <= value'
        New = 'closing(root, depth, available, leaves) + next < value + 1'
        Failure = $null
    },
    @{
        Name = 'weak-bellman-missing-child'
        File = 'specs\closing_cost.rs'
        Old = 'None => false,'
        New = 'None => true,'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'missing-bellman-edge-charge'
        File = 'specs\closing_cost.rs'
        Old = 'closing(root, depth, available, leaves) + next <= value'
        New = 'next <= value'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'missing-bellman-terminal-charge'
        File = 'specs\closing_cost.rs'
        Old = 'closing(root, depth, available, available) <= value'
        New = '0 <= value'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\closing_cost.rs'
    },
    @{
        Name = 'equivalent-paired-closing-histogram-weight'
        File = 'specs\closing_cost.rs'
        Old = ')) * capacity) as nat'
        New = ')) * (capacity + 0)) as nat'
        Failure = $null
        Additional = @(@{
            File = 'specs\histogram_cost.rs'
            Old = 'source_length(counts, position), root, max)) as nat'
            New = 'source_length(counts, position), root, max)) as nat + 0'
        })
    },
    @{
        Name = 'paired-wrong-closing-histogram-weight'
        File = 'specs\closing_cost.rs'
        Old = ')) * capacity) as nat'
        New = ')) * (capacity + 1)) as nat'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\closing_cost.rs'
        Additional = @(@{
            File = 'specs\histogram_cost.rs'
            Old = 'source_length(counts, position), root, max)) as nat'
            New = 'source_length(counts, position), root, max)) as nat + 1'
        })
    },
    @{
        Name = 'equivalent-histogram-bucket-end'
        File = 'specs\histogram_cost.rs'
        Old = 'h::before(counts, level) <= position < h::before(counts, level + 1)'
        New = 'h::before(counts, level) <= position && position + 1 <= h::before(counts, level + 1)'
        Failure = $null
    },
    @{
        Name = 'shifted-histogram-bucket-start'
        File = 'specs\histogram_cost.rs'
        Old = 'h::before(counts, level) <= position < h::before(counts, level + 1)'
        New = 'h::before(counts, level) <= position + 1 <= h::before(counts, level + 1)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'overlapping-histogram-buckets'
        File = 'specs\histogram_cost.rs'
        Old = 'position < h::before(counts, level + 1)'
        New = 'position <= h::before(counts, level + 1)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'equivalent-histogram-root-key'
        File = 'specs\histogram_cost.rs'
        Old = 'h::capacity((32 - root) as nat)'
        New = 'h::capacity((32 + 0 - root) as nat)'
        Failure = $null
    },
    @{
        Name = 'wrong-histogram-root-key'
        File = 'specs\histogram_cost.rs'
        Old = 'h::capacity((32 - root) as nat)'
        New = 'h::capacity((33 - root) as nat)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'equivalent-histogram-first-group'
        File = 'specs\histogram_cost.rs'
        Old = 'earlier < position && root < source_length'
        New = 'earlier + 1 <= position && root < source_length'
        Failure = $null
    },
    @{
        Name = 'wrong-histogram-first-group'
        File = 'specs\histogram_cost.rs'
        Old = 'earlier < position && root < source_length'
        New = 'earlier <= position && root < source_length'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'missing-histogram-first-group'
        File = 'specs\histogram_cost.rs'
        Old = '!= root_key(counts, root, position)'
        New = '!= root_key(counts, root, position) || true'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'equivalent-histogram-cell-charge'
        File = 'specs\histogram_cost.rs'
        Old = 'source_length(counts, position), root, max)) as nat'
        New = 'source_length(counts, position), root, max)) as nat + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-histogram-cell-charge'
        File = 'specs\histogram_cost.rs'
        Old = 'source_length(counts, position), root, max)) as nat'
        New = 'source_length(counts, position), root, max)) as nat + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'equivalent-histogram-sum-base'
        File = 'specs\histogram_cost.rs'
        Old = 'if processed == 0 { 0 }'
        New = 'if processed < 1 { 0 }'
        Failure = $null
    },
    @{
        Name = 'wrong-histogram-sum-base'
        File = 'specs\histogram_cost.rs'
        Old = 'if processed == 0 { 0 }'
        New = 'if processed == 0 { 1 }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'equivalent-histogram-enumeration-frontier'
        File = 'specs\histogram_cost.rs'
        Old = 'available <= remaining'
        New = 'available < remaining + 1'
        Failure = $null
    },
    @{
        Name = 'wrong-histogram-enumeration-frontier'
        File = 'specs\histogram_cost.rs'
        Old = 'available <= remaining'
        New = 'available < remaining'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'wrong-histogram-enumeration-consumption'
        File = 'specs\histogram_cost.rs'
        Old = '(remaining - counts[depth as int]) as nat'
        New = 'remaining'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'wrong-histogram-enumeration-doubling'
        File = 'specs\histogram_cost.rs'
        Old = '2 * (available - counts[depth as int]) as nat'
        New = '1 * (available - counts[depth as int]) as nat'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'weak-histogram-enumeration-terminal'
        File = 'specs\histogram_cost.rs'
        Old = 'remaining == counts[depth as int]'
        New = 'remaining >= counts[depth as int]'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\histogram_cost.rs'
    },
    @{
        Name = 'equivalent-histogram-root-cardinality'
        File = 'proofs\histogram_cost.rs'
        Old = 'lengths.len() <= bound < h::capacity(requested)'
        New = 'lengths.len() <= bound && bound + 1 <= h::capacity(requested)'
        Failure = $null
    },
    @{
        Name = 'missing-histogram-root-cardinality'
        File = 'proofs\histogram_cost.rs'
        Old = 'lengths.len() <= bound < h::capacity(requested)'
        New = 'lengths.len() <= bound'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-paired-histogram-source-cost'
        File = 'specs\histogram_cost.rs'
        Old = 'source_length(counts, position), root, max)) as nat'
        New = 'source_length(counts, position), root, max)) as nat + 0'
        Failure = $null
        Additional = @(@{
            File = 'specs\constructor_cost.rs'
            Old = 'as nat, root, max)) as nat'
            New = 'as nat, root, max)) as nat + 0'
        })
    },
    @{
        Name = 'paired-wrong-histogram-source-cost'
        File = 'specs\histogram_cost.rs'
        Old = 'source_length(counts, position), root, max)) as nat'
        New = 'source_length(counts, position), root, max)) as nat + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
        Additional = @(@{
            File = 'specs\constructor_cost.rs'
            Old = 'as nat, root, max)) as nat'
            New = 'as nat, root, max)) as nat + 1'
        })
    },
    @{
        Name = 'equivalent-canonical-source-cell-cost'
        File = 'specs\constructor_cost.rs'
        Old = 'as nat, root, max)) as nat'
        New = 'as nat, root, max)) as nat + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-canonical-source-cell-cost'
        File = 'specs\constructor_cost.rs'
        Old = 'as nat, root, max)) as nat'
        New = 'as nat, root, max)) as nat + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
    },
    @{
        Name = 'equivalent-canonical-prefix-base'
        File = 'specs\constructor_cost.rs'
        Old = 'if processed == 0 { 0 }'
        New = 'if processed < 1 { 0 }'
        Failure = $null
    },
    @{
        Name = 'wrong-canonical-prefix-base'
        File = 'specs\constructor_cost.rs'
        Old = 'if processed == 0 { 0 }'
        New = 'if processed == 0 { 1 }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
    },
    @{
        Name = 'equivalent-canonical-candidate-boundary'
        File = 'specs\constructor_cost.rs'
        Old = 'root, max, position + 1)'
        New = 'root, max, 1 + position)'
        Failure = $null
    },
    @{
        Name = 'missing-canonical-rejected-candidate'
        File = 'specs\constructor_cost.rs'
        Old = 'root, max, position + 1)'
        New = 'root, max, position)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
    },
    @{
        Name = 'missing-canonical-root-cost'
        File = 'specs\constructor_cost.rs'
        Old = 'h::capacity(root) as nat + prefix_cost'
        New = '0nat + prefix_cost'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
    },
    @{
        Name = 'missing-canonical-cost-firstness'
        File = 'specs\constructor_cost.rs'
        Old = 'if first_source(lengths, original, work, root, max, position) {'
        New = 'if position < work.len() && work[position as int] < lengths.len() && root < lengths[work[position as int] as int] {'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
    },
    @{
        Name = 'equivalent-canonical-cost-frontier'
        File = 'specs\constructor_cost.rs'
        Old = '&& opening.position < processed,'
        New = '&& opening.position + 1 <= processed,'
        Failure = $null
    },
    @{
        Name = 'weak-canonical-cost-frontier'
        File = 'specs\constructor_cost.rs'
        Old = '&& opening.position < processed,'
        New = '&& opening.position <= processed,'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_cost.rs'
    },
    @{
        Name = 'equivalent-paired-physical-source-cost'
        File = 'specs\constructor_cost.rs'
        Old = 'as nat, root, max)) as nat'
        New = 'as nat, root, max)) as nat + 0'
        Failure = $null
        Additional = @(@{
            File = 'specs\table_pages.rs'
            Old = 'Some(page) => h::capacity(page.width)'
            New = 'Some(page) => h::capacity(page.width) + 0'
        })
    },
    @{
        Name = 'paired-wrong-physical-source-cost'
        File = 'specs\constructor_cost.rs'
        Old = 'as nat, root, max)) as nat'
        New = 'as nat, root, max)) as nat + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_cost.rs'
        Additional = @(@{
            File = 'specs\table_pages.rs'
            Old = 'Some(page) => h::capacity(page.width)'
            New = 'Some(page) => h::capacity(page.width) + 1'
        })
    },
    @{
        Name = 'equivalent-canonical-opening-population'
        File = 'specs\constructor_pages.rs'
        Old = 'if level == 0 { 0u16 }'
        New = 'if level < 1 { 0u16 }'
        Failure = $null
    },
    @{
        Name = 'wrong-canonical-opening-population'
        File = 'specs\constructor_pages.rs'
        Old = 'if level == 0 { 0u16 }'
        New = 'if level == 0 { 1u16 }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-canonical-opening-start'
        File = 'specs\constructor_pages.rs'
        Old = '(length - root) as nat'
        New = '((length - root) as nat + 0)'
        Failure = $null
    },
    @{
        Name = 'wrong-canonical-opening-start'
        File = 'specs\constructor_pages.rs'
        Old = '(length - root) as nat'
        New = '((length - root) as nat + 1)'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-canonical-opening-width'
        File = 'specs\constructor_pages.rs'
        Old = 'as nat, root, max, width)'
        New = 'as nat, root, max, width + 0)'
        Failure = $null
    },
    @{
        Name = 'wrong-canonical-opening-width'
        File = 'specs\constructor_pages.rs'
        Old = 'as nat, root, max, width)'
        New = 'as nat, root, max, width + 1)'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-first-opening-bound'
        File = 'specs\constructor_pages.rs'
        Old = '0 <= position < opening.position'
        New = '0 <= position && position + 1 <= opening.position'
        Failure = $null
    },
    @{
        Name = 'wrong-first-opening-bound'
        File = 'specs\constructor_pages.rs'
        Old = '0 <= position < opening.position'
        New = '0 <= position <= opening.position'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'missing-first-opening-predecessor'
        File = 'specs\constructor_pages.rs'
        Old = '                    % h::capacity(root) != key'
        New = '                    % h::capacity(root) != key || true'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-first-opening-ledger'
        File = 'specs\constructor_pages.rs'
        Old = 'Some(opening) => first_opening(lengths, work, root, key, opening),'
        New = 'Some(opening) => true && first_opening(lengths, work, root, key, opening),'
        Failure = $null
    },
    @{
        Name = 'missing-first-opening-ledger'
        File = 'specs\constructor_pages.rs'
        Old = 'Some(opening) => first_opening(lengths, work, root, key, opening),'
        New = 'Some(opening) => true,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'wrong-first-opening-root-key'
        File = 'specs\constructor_pages.rs'
        Old = '% h::capacity(root) == key'
        New = '% h::capacity(root) == key + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-general-opening-ledger-key'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let next_openings = openings.update(key, Some(opening));'
        New = 'let next_openings = openings.update(key + 0, Some(opening));'
        Failure = $null
    },
    @{
        Name = 'wrong-general-opening-ledger-key'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let next_openings = openings.update(key, Some(opening));'
        New = 'let next_openings = openings.update(0, Some(opening));'
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees.rs'
    },
    @{
        Name = 'equivalent-general-constructor-return'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '/* set return parameters */'
        New = 'let root = root + 0; /* set return parameters */'
        Failure = $null
    },
    @{
        Name = 'false-general-constructor-capacity-refusal'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '/* set return parameters */'
        New = 'if root < max { return InflateTable::EnoughIsNotEnough; } /* set return parameters */'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-paired-general-capacity-result'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '/* set return parameters */'
        New = 'let root = root + 0; /* set return parameters */'
        Failure = $null
        Additional = @(@{
            File = 'specs\constructor_table.rs'
            Old = '|| exists|witness: Refusal| #[trigger] refused(alphabet, lengths,'
            New = '|| false || exists|witness: Refusal| #[trigger] refused(alphabet, lengths,'
        })
    },
    @{
        Name = 'paired-false-general-capacity-result'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '/* set return parameters */'
        New = 'if root < max { return InflateTable::EnoughIsNotEnough; } /* set return parameters */'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_table.rs'
        Additional = @(@{
            File = 'specs\constructor_table.rs'
            Old = '|| exists|witness: Refusal| #[trigger] refused(alphabet, lengths,'
            New = '|| true || exists|witness: Refusal| #[trigger] refused(alphabet, lengths,'
        })
    },
    @{
        Name = 'missing-general-refusal-candidate-extent'
        File = 'specs\constructor_table.rs'
        Old = '&& witness.used + h::capacity(witness.width) <= original.len()'
        New = '&& true'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-general-constructor-link-key'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '                huff & mask,'
        New = '                (huff & mask) + 0,'
        Failure = $null
    },
    @{
        Name = 'wrong-general-constructor-link-key'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '                huff & mask,'
        New = '                0,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-general-constructor-drop'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'drop_ = root;'
        New = 'drop_ = root + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-general-constructor-drop'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'drop_ = root;'
        New = 'drop_ = 0;'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'omitted-general-constructor-page'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'if len > root && (huff & mask) != low {'
        New = 'if false && len > root && (huff & mask) != low {'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'equivalent-general-constructor-active-key'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'low = huff & mask;'
        New = 'low = (huff & mask) + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-general-constructor-active-key'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'low = huff & mask;'
        New = 'low = 0;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-general-constructor-root-mask'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let mask = layout.used - 1;'
        New = 'let mask = layout.used - 2;'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'equivalent-constructor-progress-root-base'
        File = 'specs\constructor_table.rs'
        Old = 'Some(pages::Page { base: 0, width: root })'
        New = 'Some(pages::Page { base: 0int + 0, width: root })'
        Failure = $null
    },
    @{
        Name = 'wrong-constructor-progress-root-base'
        File = 'specs\constructor_table.rs'
        Old = 'Some(pages::Page { base: 0, width: root })'
        New = 'Some(pages::Page { base: 1, width: root })'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-constructor-progress-residual-bits'
        File = 'specs\constructor_table.rs'
        Old = 'else { (lengths[symbol] - root) as nat }'
        New = 'else { (lengths[symbol] - root + 0) as nat }'
        Failure = $null
    },
    @{
        Name = 'wrong-constructor-progress-residual-bits'
        File = 'specs\constructor_table.rs'
        Old = 'else { (lengths[symbol] - root) as nat }'
        New = 'else { lengths[symbol] as nat }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-constructor-progress-child-lookup'
        File = 'specs\constructor_table.rs'
        Old = 'Some(page) => page.base + ((word as int) / h::capacity(root)) % h::capacity(page.width),'
        New = 'Some(page) => page.base + (((word as int) / h::capacity(root)) % h::capacity(page.width)) + 0,'
        Failure = $null
    },
    @{
        Name = 'wrong-constructor-progress-child-lookup'
        File = 'specs\constructor_table.rs'
        Old = 'Some(page) => page.base + ((word as int) / h::capacity(root)) % h::capacity(page.width),'
        New = 'Some(page) => page.base + (word as int) % h::capacity(page.width),'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-constructor-progress-lookup-drop'
        File = 'specs\constructor_table.rs'
        Old = 'match lookup_page(root, regions, word) { Some(_) => root, None => 0 }'
        New = 'match lookup_page(root, regions, word) { Some(_) => root + 0, None => 0 }'
        Failure = $null
    },
    @{
        Name = 'wrong-constructor-progress-lookup-drop'
        File = 'specs\constructor_table.rs'
        Old = 'match lookup_page(root, regions, word) { Some(_) => root, None => 0 }'
        New = 'match lookup_page(root, regions, word) { Some(_) => 0, None => 0 }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-constructor-progress-frame'
        File = 'specs\constructor_table.rs'
        Old = '} else { codes[index] == original[index] }'
        New = '} else { original[index] == codes[index] }'
        Failure = $null
    },
    @{
        Name = 'missing-constructor-progress-frame'
        File = 'specs\constructor_table.rs'
        Old = '} else { codes[index] == original[index] }'
        New = '} else { true }'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'missing-constructor-progress-leaf'
        File = 'specs\constructor_table.rs'
        Old = 'written(alphabet, lengths, work, processed, root, regions, index, codes[index])'
        New = 'true'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'wrong-constructor-progress-link-width'
        File = 'specs\constructor_table.rs'
        Old = 'page.base as nat, page.width,'
        New = 'page.base as nat, page.width + 1,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_table.rs'
    },
    @{
        Name = 'equivalent-constructor-opening-epoch'
        File = 'specs\constructor_pages.rs'
        Old = 'opening.position <= epoch'
        New = 'epoch >= opening.position'
        Failure = $null
    },
    @{
        Name = 'missing-constructor-opening-epoch'
        File = 'specs\constructor_pages.rs'
        Old = '&& opening.position <= epoch'
        New = '&& true'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'missing-constructor-opening-work-join'
        File = 'specs\constructor_pages.rs'
        Old = '&& work[opening.position as int] as int == opening.symbol'
        New = '&& true'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'undersized-constructor-linked-backing'
        File = 'specs\constructor_pages.rs'
        Old = 'else { h::capacity(root) + h::capacity(max) }'
        New = 'else { h::capacity(max) }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-constructor-root-region'
        File = 'specs\constructor_pages.rs'
        Old = 'base == 0 && width == root && bits == lengths[symbol]'
        New = 'base == 0 && width == root && bits + 0 == lengths[symbol]'
        Failure = $null
    },
    @{
        Name = 'wrong-constructor-root-region'
        File = 'specs\constructor_pages.rs'
        Old = 'base == 0 && width == root && bits == lengths[symbol]'
        New = 'base == 1 && width == root && bits == lengths[symbol]'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-constructor-child-region'
        File = 'specs\constructor_pages.rs'
        Old = 'Some(page) => base == page.base && width == page.width,'
        New = 'Some(page) => base == page.base + 0 && width == page.width,'
        Failure = $null
    },
    @{
        Name = 'wrong-constructor-child-region'
        File = 'specs\constructor_pages.rs'
        Old = 'Some(page) => base == page.base && width == page.width,'
        New = 'Some(page) => base == page.base + 1 && width == page.width,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\constructor_pages.rs'
    },
    @{
        Name = 'equivalent-opening-wire-key'
        File = 'specs\page_source.rs'
        Old = '&& key == (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root)'
        New = '&& key == (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root) + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-opening-wire-key'
        File = 'specs\page_source.rs'
        Old = '&& key == (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root)'
        New = '&& key == (h::canonical_prefix(lengths, opening.symbol) as int) % h::capacity(root) + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\page_source.rs'
    },
    @{
        Name = 'wrong-opening-cursor-position'
        File = 'specs\page_source.rs'
        Old = '== h::normalized_cursor(original, opening.length, opening.position)'
        New = '== h::normalized_cursor(original, opening.length, opening.position + 1)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\page_source.rs'
    },
    @{
        Name = 'wrong-opening-population'
        File = 'specs\page_source.rs'
        Old = 'coverage::source_context(lengths, original, opening.remaining,'
        New = 'coverage::source_context(lengths, original, original,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\page_source.rs'
    },
    @{
        Name = 'false-opening-coverage-width'
        File = 'proofs\page_source.rs'
        Old = 'ensures lengths[symbol] <= root + width,'
        New = 'ensures lengths[symbol] <= width,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-opening-key'
        File = 'proofs\page_source.rs'
        Old = '            2, 3, 1, 1, model::Opening {'
        New = '            2, 3, 0, 1, model::Opening {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-opening-chosen-width'
        File = 'specs\page_source.rs'
        Old = 'root, max, width)'
        New = 'root, max, width + 0)'
        Failure = $null
    },
    @{
        Name = 'equivalent-native-opening-width'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'max as nat, prefix as int, final(layout).width as nat,'
        New = 'max as nat, prefix as int, final(layout).width as nat + 0,'
        Failure = $null
    },
    @{
        Name = 'false-native-opening-width'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'max as nat, prefix as int, final(layout).width as nat,'
        New = 'max as nat, prefix as int, final(layout).width as nat + 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-allocation-source-coverage'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = '==> lengths[symbol] <= final(layout).width + drop),'
        New = '==> lengths[symbol] <= drop + final(layout).width),'
        Failure = $null
    },
    @{
        Name = 'false-allocation-source-coverage'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = '==> lengths[symbol] <= final(layout).width + drop),'
        New = '==> lengths[symbol] <= final(layout).width),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-link-source-coverage'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = '==> lengths[symbol] <= root + final(layout).width),'
        New = '==> lengths[symbol] <= root + final(layout).width + 0),'
        Failure = $null
    },
    @{
        Name = 'false-link-source-coverage'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = '==> lengths[symbol] <= root + final(layout).width),'
        New = '==> lengths[symbol] <= final(layout).width),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-page-cell-cost'
        File = 'specs\table_pages.rs'
        Old = 'Some(page) => h::capacity(page.width)'
        New = 'Some(page) => h::capacity(page.width) + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-page-cell-units'
        File = 'specs\table_pages.rs'
        Old = 'Some(page) => h::capacity(page.width)'
        New = 'Some(page) => 4 * h::capacity(page.width)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\table_pages.rs'
    },
    @{
        Name = 'wrong-adjacent-page-disjointness'
        File = 'specs\table_pages.rs'
        Old = 'first.base + h::capacity(first.width) <= second.base'
        New = 'first.base + h::capacity(first.width) < second.base'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\table_pages.rs'
    },
    @{
        Name = 'wrong-page-root-slot-count'
        File = 'specs\table_pages.rs'
        Old = 'pages.len() == h::capacity(root)'
        New = 'pages.len() == h::capacity(root) + 1'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\table_pages.rs'
    },
    @{
        Name = 'false-page-global-budget'
        File = 'proofs\table_pages.rs'
        Old = 'h::capacity(root) <= used <= 49152,'
        New = 'h::capacity(root) <= used <= 32768,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-page-update-total'
        File = 'proofs\table_pages.rs'
        Old = '== cells(pages) - cost(pages[key]) + cost(page),'
        New = '== cells(pages) + cost(page),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-page-update-total'
        File = 'proofs\table_pages.rs'
        Old = '== cells(pages) - cost(pages[key]) + cost(page),'
        New = '== cells(pages) + cost(page) - cost(pages[key]),'
        Failure = $null
    },
    @{
        Name = 'equivalent-native-page-base'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'base: final(layout).next as int, width: final(layout).width as nat,'
        New = 'base: final(layout).next as int + 0, width: final(layout).width as nat,'
        Failure = $null
    },
    @{
        Name = 'false-native-page-base'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'base: final(layout).next as int, width: final(layout).width as nat,'
        New = 'base: final(layout).next as int + 1, width: final(layout).width as nat,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-page-total'
        File = 'proofs\table_pages.rs'
        Old = 'ensures valid(2, 3, 12, seq!['
        New = 'ensures valid(2, 3, 14, seq!['
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-normalized-root-prefix'
        File = 'specs\subtable_coverage.rs'
        Old = '        / h::capacity((32 - root) as nat)'
        New = '        / h::capacity((32 - root) as nat) + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-normalized-root-scale'
        File = 'specs\subtable_coverage.rs'
        Old = '        / h::capacity((32 - root) as nat)'
        New = '        / h::capacity(root)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\subtable_coverage.rs'
    },
    @{
        Name = 'wrong-source-current-population'
        File = 'specs\subtable_coverage.rs'
        Old = '&& h::remaining_histogram(original, remaining, position)'
        New = '&& h::remaining_histogram(original, remaining, position + 1)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\subtable_coverage.rs'
    },
    @{
        Name = 'false-lookahead-boundary'
        File = 'proofs\subtable_coverage.rs'
        Old = '+ h::capacity((32 - root) as nat)'
        New = '- h::capacity((32 - root) as nat)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-root-quotient-order'
        File = 'proofs\subtable_coverage.rs'
        Old = 'ensures first / size <= second / size,'
        New = 'ensures first / size < second / size,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-canonical-root-order'
        File = 'proofs\subtable_coverage.rs'
        Old = 'ensures model::root_prefix(lengths, first, root) <= model::root_prefix(lengths, second, root),'
        New = 'ensures model::root_prefix(lengths, first, root) < model::root_prefix(lengths, second, root),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-wire-root-equivalence'
        File = 'proofs\subtable_coverage.rs'
        Old = '(model::root_prefix(lengths, first, root) == model::root_prefix(lengths, second, root)),'
        New = '(model::root_prefix(lengths, first, root) != model::root_prefix(lengths, second, root)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-root-revisit'
        File = 'proofs\subtable_coverage.rs'
        Old = 'ensures model::root_prefix(lengths, first, root) != model::root_prefix(lengths, third, root),'
        New = 'ensures model::root_prefix(lengths, first, root) == model::root_prefix(lengths, third, root),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-wire-order'
        File = 'proofs\subtable_coverage.rs'
        Old = '(h::canonical_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 4) as int) % h::capacity(2) == 1,'
        New = '(h::canonical_prefix(seq![3u16, 3, 3, 3, 3, 3, 3, 3], 4) as int) % h::capacity(2) == 2,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-native-root-coverage'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = '==> lengths[symbol] <= result + drop),'
        New = '==> lengths[symbol] <= result + drop + 0),'
        Failure = $null
    },
    @{
        Name = 'false-native-root-coverage'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = '==> lengths[symbol] <= result + drop),'
        New = '==> lengths[symbol] <= result),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-paired-lookahead-population'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = 'left -= counts[curr + drop] as i32;'
        New = 'left -= counts[curr + drop + 0] as i32;'
        Additional = @(
            @{
                File = 'specs\huffman.rs'
                Old = 'counts[(depth + drop - 1) as int] as int)'
                New = 'counts[(depth + drop - 1 + 0) as int] as int)'
            }
        )
        Failure = $null
    },
    @{
        Name = 'paired-wrong-lookahead-population'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = 'left -= counts[curr + drop] as i32;'
        New = 'left -= counts[curr] as i32;'
        Additional = @(
            @{
                File = 'specs\huffman.rs'
                Old = 'counts[(depth + drop - 1) as int] as int)'
                New = 'counts[(depth - 1) as int] as int)'
            },
            @{
                File = 'specs\huffman.rs'
                Old = '- counts[(depth + drop) as int] > 0)'
                New = '- counts[depth as int] > 0)'
            },
            @{
                File = 'specs\huffman.rs'
                Old = 'lookahead_space(counts, start, drop, width) - counts[(width + drop) as int] <= 0)'
                New = 'lookahead_space(counts, start, drop, width) - counts[width as int] <= 0)'
            },
            @{
                File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
                Old = 'drop as nat, depth) - counts@[(depth + drop) as int] > 0,'
                New = 'drop as nat, depth) - counts@[depth as int] > 0,'
            },
            @{
                File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
                Old = 'drop as nat, depth) - counts@[(depth + drop) as int] > 0 by {'
                New = 'drop as nat, depth) - counts@[depth as int] > 0 by {'
            },
            @{
                File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
                Old = '- counts@[(depth + drop) as int]);'
                New = '- counts@[depth as int]);'
            }
        )
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\subtable_coverage.rs'
    },
    @{
        Name = 'equivalent-child-source-prefix'
        File = 'specs\table_emission.rs'
        Old = '&& prefix == (h::canonical_prefix(lengths, symbol as int) as int) / h::capacity(root)'
        New = '&& prefix == (h::canonical_prefix(lengths, symbol as int) as int) / h::capacity(root) + 0'
        Failure = $null
    },
    @{
        Name = 'wrong-child-source-root'
        File = 'specs\table_emission.rs'
        Old = '== (h::canonical_prefix(lengths, symbol as int) as int) % h::capacity(root)'
        New = '!= (h::canonical_prefix(lengths, symbol as int) as int) % h::capacity(root)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\child_emission.rs'
    },
    @{
        Name = 'wrong-child-source-prefix'
        File = 'specs\table_emission.rs'
        Old = '&& prefix == (h::canonical_prefix(lengths, symbol as int) as int) / h::capacity(root)'
        New = '&& prefix == (h::canonical_prefix(lengths, symbol as int) as int) % h::capacity(root)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\child_emission.rs'
    },
    @{
        Name = 'wrong-child-prefix-split'
        File = 'proofs\child_emission.rs'
        Old = '== (prefix as int) / h::capacity(root),'
        New = '== (prefix as int) % h::capacity(root),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'narrow-child-cache-projection'
        File = 'proofs\child_emission.rs'
        Old = '== (word as u32 as int) % h::capacity(width as nat),'
        New = '== (word as u8 as int) % h::capacity(width as nat),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-child-prefix-bound'
        File = 'proofs\child_emission.rs'
        Old = 'ensures prefix < h::capacity(root + tail),'
        New = 'ensures prefix < h::capacity(root),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-native-child-emission-cell'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = 'final(table)@[huffman_specs::subtable_index(link, word as nat)],'
        New = 'final(table)@[layout.next as int],'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-native-child-emission-cell'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = 'final(table)@[huffman_specs::subtable_index(link, word as nat)],'
        New = 'final(table)@[huffman_specs::subtable_index(link, word as nat) + 0],'
        Failure = $null
    },
    @{
        Name = 'false-independent-child-leaf'
        File = 'proofs\child_emission.rs'
        Old = 'Code { bits: 1, op: 0, val: 1 }, 1, 1),'
        New = 'Code { bits: 1, op: 0, val: 2 }, 1, 1),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-child-untouched-frame'
        File = 'proofs\child_emission.rs'
        Old = '} else { before[h::subtable_index(link, word as nat)] },'
        New = '} else { code },'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-linked-leaf-width'
        File = 'specs\linked_table.rs'
        Old = '(lengths[symbol] as int - dropped) as nat, code)'
        New = '(lengths[symbol] as int - dropped + 0) as nat, code)'
        Failure = $null
    },
    @{
        Name = 'wrong-linked-leaf-width'
        File = 'specs\linked_table.rs'
        Old = '(lengths[symbol] as int - dropped) as nat, code)'
        New = 'lengths[symbol] as nat, code)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\linked_table.rs'
    },
    @{
        Name = 'wrong-linked-child-drop'
        File = 'specs\linked_table.rs'
        Old = 'word as u32, root)'
        New = 'word as u32, 0)'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\linked_table.rs'
    },
    @{
        Name = 'wrong-linked-region-limit'
        File = 'specs\linked_table.rs'
        Old = 'code.val as int + h::capacity(code.op as nat) <= used'
        New = 'code.val as int + h::capacity(code.op as nat) < used'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\linked_table.rs'
    },
    @{
        Name = 'wrong-linked-region-base'
        File = 'specs\linked_table.rs'
        Old = 'h::subtable_link(code, root, code.val as nat, code.op as nat,'
        New = 'h::subtable_link(code, root, code.val as nat + 1, code.op as nat,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\linked_table.rs'
    },
    @{
        Name = 'wrong-linked-link-classification'
        File = 'specs\linked_table.rs'
        Old = '1 <= code.op < 16'
        New = '2 <= code.op < 16'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\linked_table.rs'
    },
    @{
        Name = 'false-independent-linked-consumption'
        File = 'proofs\linked_table.rs'
        Old = 'ensures dropped + code.bits == lengths[symbol],'
        New = 'ensures code.bits == lengths[symbol],'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-linked-root-extent'
        File = 'proofs\linked_table.rs'
        Old = 'ensures model::table(alphabet, lengths, root, h::capacity(root) as nat, codes),'
        New = 'ensures model::table(alphabet, lengths, root, h::capacity(root) as nat + 1, codes),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-native-linked-selection'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'codes[result as int],'
        New = 'codes[link.val as int],'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-native-linked-selection'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'codes[result as int],'
        New = 'codes[result as int + 0],'
        Failure = $null
    },
    @{
        Name = 'equivalent-fixed-literal-flattening'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = 'table[index] = rows[index / 16][index % 16];'
        New = 'table[index] = rows[index / 16 + 0][index % 16];'
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-literal-flattening'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = 'table[index] = rows[index / 16][index % 16];'
        New = 'table[index] = rows[index / 16][0];'
        Failure = 'invariant not satisfied at end of loop body'
    },
    @{
        Name = 'wrong-fixed-literal-block-order'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '        fixed_literal_032(),'
        New = '        fixed_literal_016(),'
        Failure = 'invariant not satisfied before loop'
    },
    @{
        Name = 'wrong-fixed-literal-block-base'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "    fixed_literal_016,`n    16,"
        New = "    fixed_literal_016,`n    17,"
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-fixed-literal-actual-eob'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "    fixed_literal_000,`n    0,`n    [`n        code(96, 7, 0),"
        New = "    fixed_literal_000,`n    0,`n    [`n        code(96 + 0, 7, 0),"
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-literal-actual-eob'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "    fixed_literal_000,`n    0,`n    [`n        code(96, 7, 0),"
        New = "    fixed_literal_000,`n    0,`n    [`n        code(0, 7, 0),"
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-literal-actual-literal'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "    fixed_literal_000,`n    0,`n    [`n        code(96, 7, 0),`n        code(0, 8, 80),"
        New = "    fixed_literal_000,`n    0,`n    [`n        code(96, 7, 0),`n        code(0, 8, 81),"
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-literal-seven-bit-replica'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "    fixed_literal_384,`n    384,`n    [`n        code(96, 7, 0),"
        New = "    fixed_literal_384,`n    384,`n    [`n        code(96, 8, 0),"
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-literal-eight-bit-replica'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 205),"
        New = "        code(0, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 205),"
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-literal-getter-source'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '    let table = &LENFIX;'
        New = '    let table = &[Code { op: 0, bits: 9, val: 0 }; 512];'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-literal-reversal'
        File = 'specs\fixed_trees.rs'
        Old = '((word & 1) << 8)'
        New = '((word & 1) << 7)'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-fixed-literal-reversal'
        File = 'specs\fixed_trees.rs'
        Old = '((word & 1) << 8)'
        New = '((word & 1) << (8 + 0))'
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-literal-middle-range'
        File = 'specs\fixed_trees.rs'
        Old = 'else if reversed < 384 { reversed / 2 - 48 }'
        New = 'else if reversed < 382 { reversed / 2 - 48 }'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-fixed-literal-model-eob'
        File = 'specs\fixed_trees.rs'
        Old = 'Code { op: if symbol < 256 { 0 } else if symbol == 256 { 96 }'
        New = 'Code { op: if symbol < 256 { 0 } else if symbol == 256 { 32 }'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-fixed-literal-model-reserved'
        File = 'specs\fixed_trees.rs'
        Old = '            else { 64 },'
        New = '            else { 192 },'
        Failure = 'assertion failed'
    },
    @{
        Name = 'paired-wrong-fixed-literal-reserved'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 204),"
        New = "        code(192, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 204),"
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\fixed_trees.rs'
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 206),"
                New = "        code(192, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 206),"
            },
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 205),"
                New = "        code(192, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 205),"
            },
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 207),"
                New = "        code(192, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 207),"
            },
            @{
                File = 'specs\fixed_trees.rs'
                Old = '            else { 64 },'
                New = '            else { 192 },'
            }
        )
    },
    @{
        Name = 'equivalent-paired-fixed-literal-reserved'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 204),"
        New = "        code(64 + 0, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 204),"
        Failure = $null
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 206),"
                New = "        code(64 + 0, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 206),"
            },
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 205),"
                New = "        code(64 + 0, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 118),`n        code(0, 8, 54),`n        code(0, 9, 205),"
            },
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(64, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 207),"
                New = "        code(64 + 0, 8, 0),`n        code(19, 7, 51),`n        code(0, 8, 119),`n        code(0, 8, 55),`n        code(0, 9, 207),"
            },
            @{
                File = 'specs\fixed_trees.rs'
                Old = '            else { 64 },'
                New = '            else { (64u8 + 0u8) as u8 },'
            }
        )
    },
    @{
        Name = 'false-independent-fixed-literal-eob'
        File = 'proofs\fixed_trees.rs'
        Old = 'ensures model::literal_entry(0) == (crate::Code { op: 96, bits: 7, val: 0 }),'
        New = 'ensures model::literal_entry(0) == (crate::Code { op: 32, bits: 7, val: 0 }),'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\fixed_trees.rs'
    },
    @{
        Name = 'equivalent-fixed-cell-constructor'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '    Code { op, bits, val }'
        New = '    Code { op: op + 0, bits, val }'
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-cell-constructor'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '    Code { op, bits, val }'
        New = '    Code { op, bits: 0, val }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'equivalent-fixed-distance-actual-base'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '        code(16, 5, 1),'
        New = '        code(16, 5, 1 + 0),'
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-distance-actual-base'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '        code(16, 5, 1),'
        New = '        code(16, 5, 2),'
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-distance-actual-order'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(16, 5, 1),`n        code(23, 5, 257),"
        New = "        code(23, 5, 257),`n        code(16, 5, 1),"
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-distance-actual-reserved'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(22, 5, 129),`n        code(64, 5, 0),"
        New = "        code(22, 5, 129),`n        code(0, 5, 0),"
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-distance-actual-largest-base'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '        code(29, 5, 24577),'
        New = '        code(29, 5, 24578),'
        Failure = 'assertion failed'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-distance-getter-source'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = '    let table = &DISTFIX;'
        New = '    let table = &[Code { op: 16, bits: 5, val: 1 }; 32];'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'zlib-rs\src\inflate\inffixed_tbl.rs'
    },
    @{
        Name = 'wrong-fixed-distance-reversal'
        File = 'specs\fixed_trees.rs'
        Old = '((word & 1) << 4)'
        New = '((word & 1) << 3)'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-fixed-distance-reversal'
        File = 'specs\fixed_trees.rs'
        Old = '((word & 1) << 4)'
        New = '((word & 1) << (4 + 0))'
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-distance-model-reserved'
        File = 'specs\fixed_trees.rs'
        Old = 'h::distance_extra(symbol)) as u8 } else { 64 },'
        New = 'h::distance_extra(symbol)) as u8 } else { 192 },'
        Failure = 'assertion failed'
    },
    @{
        Name = 'paired-wrong-fixed-distance-reserved'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(22, 5, 129),`n        code(64, 5, 0),"
        New = "        code(22, 5, 129),`n        code(192, 5, 0),"
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\fixed_trees.rs'
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(22, 5, 193),`n        code(64, 5, 0),"
                New = "        code(22, 5, 193),`n        code(192, 5, 0),"
            },
            @{
                File = 'specs\fixed_trees.rs'
                Old = 'h::distance_extra(symbol)) as u8 } else { 64 },'
                New = 'h::distance_extra(symbol)) as u8 } else { 192 },'
            }
        )
    },
    @{
        Name = 'equivalent-paired-fixed-distance-reserved'
        File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
        Old = "        code(22, 5, 129),`n        code(64, 5, 0),"
        New = "        code(22, 5, 129),`n        code(64 + 0, 5, 0),"
        Failure = $null
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inffixed_tbl.rs'
                Old = "        code(22, 5, 193),`n        code(64, 5, 0),"
                New = "        code(22, 5, 193),`n        code(64 + 0, 5, 0),"
            },
            @{
                File = 'specs\fixed_trees.rs'
                Old = 'h::distance_extra(symbol)) as u8 } else { 64 },'
                New = 'h::distance_extra(symbol)) as u8 } else { (64u8 + 0u8) as u8 },'
            }
        )
    },
    @{
        Name = 'false-independent-fixed-distance-cell'
        File = 'proofs\fixed_trees.rs'
        Old = 'ensures model::distance_entry(0) == (crate::Code { op: 16, bits: 5, val: 1 }),'
        New = 'ensures model::distance_entry(0) == (crate::Code { op: 16, bits: 5, val: 2 }),'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\fixed_trees.rs'
    },
    @{
        Name = 'equivalent-fixed-literal-first-code'
        File = 'specs\fixed_trees.rs'
        Old = 'if symbol < 144 { (symbol + 48) as nat }'
        New = 'if symbol < 144 { (symbol + 48 + 0) as nat }'
        Failure = $null
    },
    @{
        Name = 'wrong-fixed-literal-first-width'
        File = 'specs\fixed_trees.rs'
        Old = 'if symbol < 144 { 8 } else if symbol < 256 { 9 }'
        New = 'if symbol < 144 { 7 } else if symbol < 256 { 9 }'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-fixed-literal-first-code'
        File = 'specs\fixed_trees.rs'
        Old = 'if symbol < 144 { (symbol + 48) as nat }'
        New = 'if symbol < 144 { (symbol + 49) as nat }'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-fixed-literal-nine-bit-start'
        File = 'specs\fixed_trees.rs'
        Old = 'else if symbol < 256 { (symbol + 256) as nat }'
        New = 'else if symbol < 256 { (symbol + 255) as nat }'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-fixed-distance-source-width'
        File = 'specs\fixed_trees.rs'
        Old = 'Seq::new(32, |symbol: int| 5u16)'
        New = 'Seq::new(32, |symbol: int| 4u16)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-fixed-literal-source-boundary'
        File = 'specs\fixed_trees.rs'
        Old = 'else if symbol < 280 { 7 } else { 8 }'
        New = 'else if symbol < 279 { 7 } else { 8 }'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-fixed-prefix-population'
        File = 'proofs\fixed_trees.rs'
        Old = 'range_population(prefix, 256, 280)'
        New = 'range_population(prefix, 256, 279)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-fixed-population-induction'
        File = 'proofs\fixed_trees.rs'
        Old = 'literal_prefix_population(prefix - 1, length);'
        New = 'literal_prefix_population(prefix, length);'
        Failure = 'could not prove termination'
    },
    @{
        Name = 'false-independent-fixed-eob-code'
        File = 'proofs\fixed_trees.rs'
        Old = 'h::canonical_code(model::literal_lengths(), 256) == 0,'
        New = 'h::canonical_code(model::literal_lengths(), 256) == 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-fixed-distance-endpoint'
        File = 'proofs\fixed_trees.rs'
        Old = 'h::canonical_code(model::distance_lengths(), 31) == 31,'
        New = 'h::canonical_code(model::distance_lengths(), 31) == 30,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-fixed-completeness'
        File = 'proofs\fixed_trees.rs'
        Old = 'ensures h::accepted_lengths(model::literal_lengths(), true),'
        New = 'ensures !h::accepted_lengths(model::literal_lengths(), true),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-general-root-lookup-width'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let index = buffer::peek_bits(word, root);'
        New = 'let index = buffer::peek_bits(word, root + 0);'
        Failure = $null
    },
    @{
        Name = 'narrowed-general-root-lookup-index'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[index as usize]'
        New = 'table[index as u8 as usize]'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'shifted-general-root-lookup-cache'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let index = buffer::peek_bits(word, root);'
        New = 'let index = buffer::peek_bits(word >> 32, root);'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'false-independent-general-root-projection'
        File = 'proofs\root_table.rs'
        Old = '        codes[(word as int) % h::capacity(root)], word),'
        New = '        codes[0], word),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-root-word-hole'
        File = 'proofs\root_table.rs'
        Old = 'model::entry(h::Alphabet::Distances, fixture_lengths(), fixture_codes()[1],'
        New = 'model::entry(h::Alphabet::Distances, fixture_lengths(), fixture_codes()[0],'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-root-invalid-hole-write'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][huff + 0] = here;'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-root-invalid-hole'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][huff] = Code { op: here.op + 0, ..here };'
        Failure = $null
        Additional = @(@{
            File = 'specs\root_table.rs'
            Old = '    Code { op: 64, bits: 1, val: 0 }'
            New = '    Code { op: (64u8 + 0u8) as u8, bits: 1, val: 0 }'
        })
    },
    @{
        Name = 'wrong-root-invalid-hole-opcode'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][huff] = Code { op: 0, ..here };'
        Failure = 'precondition not satisfied'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees.rs'
    },
    @{
        Name = 'paired-wrong-root-invalid-hole'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][huff] = Code { op: 0, ..here };'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\root_table.rs'
        Additional = @(@{
            File = 'specs\root_table.rs'
            Old = '    Code { op: 64, bits: 1, val: 0 }'
            New = '    Code { op: 0, bits: 1, val: 0 }'
        })
    },
    @{
        Name = 'wrong-root-invalid-hole-index'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][0] = here;'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'omitted-root-invalid-hole'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'let _ = here;'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-root-invalid-hole-width'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][huff] = Code { bits: 0, ..here };'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-root-invalid-hole-value'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[layout.next..][huff] = here;'
        New = 'table[layout.next..][huff] = Code { val: 1, ..here };'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-root-model-invalid-hole'
        File = 'specs\root_table.rs'
        Old = '    Code { op: 64, bits: 1, val: 0 }'
        New = '    Code { op: 0, bits: 1, val: 0 }'
        Failure = 'assertion failed'
        DiagnosticFile = 'proofs\root_table.rs'
    },
    @{
        Name = 'false-independent-root-distance-leaf'
        File = 'proofs\root_table.rs'
        Old = 'fixture_codes()[0].val == 1, fixture_codes()[1].op == 64,'
        New = 'fixture_codes()[0].val == 2, fixture_codes()[1].op == 64,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-root-hole-index'
        File = 'proofs\root_table.rs'
        Old = 'assert(model::entry(h::Alphabet::Distances, lengths, codes[1], 1));'
        New = 'assert(model::entry(h::Alphabet::Distances, lengths, codes[1], 0));'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-byte-addition'
        File = 'zlib-rs\src\adler32\short.rs'
        Old = 'adler += buf[0] as u32;'
        New = 'adler += (buf[0] as u32) + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-executable-byte'
        File = 'zlib-rs\src\adler32\short.rs'
        Old = 'adler += buf[0] as u32;'
        New = 'adler += 0;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-production-loop'
        File = 'zlib-rs\src\adler32\short.rs'
        Old = 'decreases buf.len() - i,'
        New = 'decreases buf.len(),'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'false-independent-rfc-property'
        File = 'proofs\adler32.rs'
        Old = 'ensures specs::checksum(Seq::empty()) == 1,'
        New = 'ensures specs::checksum(Seq::empty()) == 2,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-zero-crc-product'
        File = 'zlib-rs\src\crc32\combine.rs'
        Old = 'return 0;'
        New = 'return 1;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-crc-loop'
        File = 'zlib-rs\src\crc32\combine.rs'
        Old = 'decreases m,'
        New = 'decreases a,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'wrong-crc-table-polynomial'
        File = 'zlib-rs\src\crc32\tables.rs'
        Old = 'c = CRC32_LSB_POLY as u32 ^ (c >> 1);'
        New = 'c = 0u32 ^ (c >> 1);'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'wrong-crc-byte-update'
        File = 'zlib-rs\src\crc32\byte.rs'
        Old = 'crc = table[usize::from(crc32_lsb ^ data[index])] ^ (crc >> 8);'
        New = 'crc = table[usize::from(crc32_lsb ^ data[index])] ^ (crc >> 7);'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'false-independent-crc-property'
        File = 'proofs\crc32.rs'
        Old = 'ensures model::checksum_update(0, Seq::empty()) == 0,'
        New = 'ensures model::checksum_update(0, Seq::empty()) == 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-sync-alignment-direction'
        File = 'zlib-rs\src\inflate\bitreader\sync_buffer.rs'
        Old = '*word >>= skip;'
        New = '*word <<= skip;'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'nondecreasing-sync-loop'
        File = 'zlib-rs\src\inflate\bitreader\sync_buffer.rs'
        Old = 'decreases *count,'
        New = 'decreases initial_count,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'wrong-huffman-success-on-oversubscription'
        File = 'zlib-rs\src\inflate\inftrees\slots.rs'
        Old = 'return None;'
        New = 'return Some(0);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-huffman-histogram'
        File = 'zlib-rs\src\inflate\inftrees\histogram.rs'
        Old = 'count[len as usize] += 1;'
        New = 'count[len as usize] += 0;'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'reject-valid-huffman-lengths'
        File = 'zlib-rs\src\inflate\inftrees\analysis.rs'
        Old = 'if left > 0 && (require_complete || max != 1) {'
        New = 'if left > 0 || require_complete {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-huffman-symbol-write'
        File = 'zlib-rs\src\inflate\inftrees\sorting.rs'
        Old = 'work[offset as usize] = symbol as u16;'
        New = 'work[offset as usize] = (symbol as u16) + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-huffman-bucket-offset'
        File = 'zlib-rs\src\inflate\inftrees\sorting.rs'
        Old = 'offsets[level + 1] = offsets[level] + counts[level];'
        New = 'offsets[level + 1] = offsets[level] + 0;'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'wrong-huffman-symbol'
        File = 'zlib-rs\src\inflate\inftrees\sorting.rs'
        Old = 'work[offset as usize] = symbol as u16;'
        New = 'work[offset as usize] = 0;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'nondecreasing-huffman-sort-loop'
        File = 'zlib-rs\src\inflate\inftrees\sorting.rs'
        Old = 'decreases lengths.len() - symbol,'
        New = 'decreases lengths.len(),'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'omit-huffman-sorting-caller'
        File = 'zlib-rs\src\inflate\inftrees\analysis.rs'
        Old = 'sort_symbols(lengths, &count, work);'
        New = 'let _ = &count;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-huffman-stability'
        File = 'proofs\huffman.rs'
        Old = 'ensures work[model::before(counts, level as nat) as int + first] <'
        New = 'ensures work[model::before(counts, level as nat) as int + first] >'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-huffman-code-step'
        File = 'zlib-rs\src\inflate\inftrees\codes.rs'
        Old = 'let step = 0x80000000u32 >> (length - 1);'
        New = 'let step = 0x40000000u32 >> (length - 1);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'omit-huffman-bit-reversal'
        File = 'zlib-rs\src\inflate\inftrees\codes.rs'
        Old = '(next, huff)'
        New = '(next, next)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-canonical-code-width'
        File = 'proofs\huffman.rs'
        Old = 'ensures model::canonical_code(lengths, symbol) < model::capacity(lengths[symbol] as nat),'
        New = 'ensures model::canonical_code(lengths, symbol) >= model::capacity(lengths[symbol] as nat),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-huffman-table-entry'
        File = 'zlib-rs\src\inflate\inftrees\replicate.rs'
        Old = 'table[base + prefix + fill] = entry;'
        New = 'table[base + prefix + fill] = Code { op: entry.op, bits: entry.bits, val: entry.val };'
        Failure = $null
    },
    @{
        Name = 'wrong-huffman-table-entry'
        File = 'zlib-rs\src\inflate\inftrees\replicate.rs'
        Old = 'table[base + prefix + fill] = entry;'
        New = 'table[base + prefix + fill] = Code { op: 0, bits: 0, val: 0 };'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-huffman-table-prefix'
        File = 'zlib-rs\src\inflate\inftrees\replicate.rs'
        Old = 'table[base + prefix + fill] = entry;'
        New = 'table[base + fill] = entry;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'nondecreasing-huffman-table-fill'
        File = 'zlib-rs\src\inflate\inftrees\replicate.rs'
        Old = 'decreases fill,'
        New = 'decreases size,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'clobber-unrelated-huffman-table-cell'
        File = 'zlib-rs\src\inflate\inftrees\replicate.rs'
        Old = 'if fill == 0 {'
        New = 'if fill == 0 { table[base] = entry;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-huffman-symbol-increment'
        File = 'zlib-rs\src\inflate\inftrees\progress.rs'
        Old = '*symbol += 1;'
        New = '*symbol = *symbol + 1;'
        Failure = $null
    },
    @{
        Name = 'skipped-huffman-symbol'
        File = 'zlib-rs\src\inflate\inftrees\progress.rs'
        Old = '*symbol += 1;'
        New = '*symbol += 2;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'discarded-huffman-bucket-count'
        File = 'zlib-rs\src\inflate\inftrees\progress.rs'
        Old = 'counts[current] -= 1;'
        New = 'counts[current] = 0;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'premature-huffman-symbol-termination'
        File = 'zlib-rs\src\inflate\inftrees\progress.rs'
        Old = 'if current == max {'
        New = 'if current <= max {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-huffman-cursor-caller-length'
        File = 'zlib-rs\src\inflate\inftrees\progress.rs'
        Old = 'super::codes::next_code(cursor, current)'
        New = 'super::codes::next_code(cursor, max)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-huffman-end-marker'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = 'op: 0b01100000,'
        New = 'op: 96,'
        Failure = $null
    },
    @{
        Name = 'wrong-rfc-length-base'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = '163, 195, 227, 258,'
        New = '163, 195, 228, 258,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-rfc-distance-base'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = '24577, 0, 0,'
        New = '24576, 0, 0,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'reserved-length-marked-valid'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = '16, 77, 202,'
        New = '16, 16, 202,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-huffman-literal-entry'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = 'val: symbol,'
        New = 'val: 0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-huffman-end-marker'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = 'op: 0b01100000,'
        New = 'op: 0b01000000,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-huffman-entry-bit-consumption'
        File = 'zlib-rs\src\inflate\inftrees\entries.rs'
        Old = 'if symbol >= threshold {'
        New = 'if symbol >= threshold { let drop = 0usize;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-huffman-lookahead-increment'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = 'curr += 1;'
        New = 'curr = curr + 1;'
        Failure = $null
    },
    @{
        Name = 'omitted-huffman-lookahead-population'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = 'left -= counts[curr + drop] as i32;'
        New = 'left -= 0;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'missed-exact-huffman-lookahead-fill'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = 'if left <= 0 {'
        New = 'if left < 0 {'
        Failure = 'assertion failed'
    },
    @{
        Name = 'nondecreasing-huffman-lookahead'
        File = 'zlib-rs\src\inflate\inftrees\lookahead.rs'
        Old = 'decreases max - curr - drop,'
        New = 'decreases max - drop,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'equivalent-huffman-region-increment'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'layout.next += previous_size;'
        New = 'layout.next = layout.next + previous_size;'
        Failure = $null
    },
    @{
        Name = 'overlapping-huffman-region'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'layout.next += previous_size;'
        New = 'layout.next += 1;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'omitted-huffman-lookahead-caller'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'layout.width = subtable_width(counts, length, drop, max);'
        New = 'layout.width = length - drop;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'reject-fitting-huffman-region'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'matches!(kind, CodeType::Lens) && layout.used > ENOUGH_LENS'
        New = 'matches!(kind, CodeType::Lens) && layout.used >= ENOUGH_LENS'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'accept-oversized-huffman-distance-region'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'if matches!(kind, CodeType::Dists) && layout.used > ENOUGH_DISTS {'
        New = 'if false {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'underreported-huffman-region-space'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'layout.used += 1usize << layout.width;'
        New = 'layout.used += 1usize << (layout.width - 1);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-root-constructor-clamp'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'Ord::min(Ord::max(requested, min), max)'
        New = 'Ord::min(Ord::max(requested + 0, min), max)'
        Failure = $null
    },
    @{
        Name = 'wrong-root-constructor-replication-prefix'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'huff >> drop_,'
        New = '0,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'lost-root-constructor-successor'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'huff = advanced.code as usize;'
        New = 'huff = if advanced.code == 1 { 0 } else { advanced.code as usize };'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'wrong-root-constructor-invalid-outcome'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'return TablePreparation::Finished(InflateTable::InvalidCode)'
        New = 'return TablePreparation::Finished(InflateTable::EnoughIsNotEnough)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'clobbered-root-constructor-result'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '/* set return parameters */'
        New = 'table[0] = Code { op: 64, bits: 1, val: 0 }; /* set return parameters */'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-independent-rfc-bit-order'
        File = 'proofs\huffman.rs'
        Old = 'model::canonical_prefix(lengths, 0) == 2'
        New = 'model::canonical_prefix(lengths, 0) == 1'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-root-constructor-loop'
        File = 'proofs\huffman.rs'
        Old = '(total - processed) as nat'
        New = 'total'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-root-constructor-remaining-symbols'
        File = 'proofs\huffman.rs'
        Old = '(total - processed) as nat'
        New = '(total - processed + 0) as nat'
        Failure = $null
    },
    @{
        Name = 'equivalent-canonical-partition-word'
        File = 'proofs\canonical_intervals.rs'
        Old = 'complete_canonical_intervals_cover(lengths, counts, work, index);'
        New = 'complete_canonical_intervals_cover(lengths, counts, work, index + 0);'
        Failure = $null
    },
    @{
        Name = 'false-canonical-bucket-gap'
        File = 'proofs\canonical_intervals.rs'
        Old = 'ensures (model::first_code(counts, low) + counts[low as int] as nat)'
        New = 'ensures (model::first_code(counts, low) + counts[low as int] as nat + 1)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'omitted-first-canonical-symbol-coverage'
        File = 'proofs\canonical_intervals.rs'
        Old = 'ensures exists|symbol: int| 0 <= symbol < lengths.len() && 1 <= lengths[symbol] <= 15'
        New = 'ensures exists|symbol: int| 0 < symbol < lengths.len() && 1 <= lengths[symbol] <= 15'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-relational-reversal-witness'
        File = 'proofs\huffman_decode.rs'
        Old = 'let result = previous | (bit << position);'
        New = 'let result = previous | (bit << ((position + 0) as u32));'
        Failure = $null
    },
    @{
        Name = 'lost-relational-reversal-bit'
        File = 'proofs\huffman_decode.rs'
        Old = 'let bit = (word >> ((31 - position) as u32)) & 1;'
        New = 'let bit = (word >> ((31 - position) as u32)) & 0;'
        Failure = 'requires not satisfied'
    },
    @{
        Name = 'nondecreasing-relational-reversal-witness'
        File = 'proofs\huffman_decode.rs'
        Old = 'decreases width,'
        New = 'decreases 32u32,'
        Failure = 'could not prove termination'
    },
    @{
        Name = 'shifted-canonical-word-meaning'
        File = 'proofs\huffman_decode.rs'
        Old = 'model::reversed_word(word) as int),'
        New = '(model::reversed_word(word) as int) + 1),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'lost-matching-root-last-writer'
        File = 'proofs\huffman_decode.rs'
        Old = 'if model::code_prefix_matches(lengths, last, index as u32) {'
        New = 'if false {'
        Failure = 'assertion failed'
    },
    @{
        Name = 'divided-root-word-projection'
        File = 'proofs\huffman_decode.rs'
        Old = '((word as int) % model::capacity(root)) as u32),'
        New = '((word as int) / model::capacity(root)) as u32),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-length-write'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'lengths[usize::from(ORDER[position])] = value;'
        New = 'lengths[usize::from(ORDER[position])] = value + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-header-wire-permutation'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,'
        New = '17, 16, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'lost-header-length-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'lengths[usize::from(ORDER[position])] = value;'
        New = 'lengths[usize::from(ORDER[position])] = 0;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nonzero-header-padding'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'write_length(lengths, position, 0);'
        New = 'write_length(lengths, position, 1);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'nondecreasing-header-padding'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'decreases 19 - *have,'
        New = 'decreases 19 - initial_have,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'omitted-header-padding-caller'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'super::header_lengths::finish_length_header(lens, have);'
        New = 'let _ = ();'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'truncated-header-table-alphabet'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let lengths = &lens[..19];'
        New = 'let lengths = &lens[..18];'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-wire-inverse'
        File = 'proofs\dynamic_header.rs'
        Old = 'model::wire_position(model::wire_symbol(position)) == position,'
        New = 'model::wire_position(model::wire_symbol(position)) == position + 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-decoded-repeat-count'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let count = usize::from(extra) + if symbol == 18 { 11 } else { 3 };'
        New = 'let count = usize::from(extra) + 0 + if symbol == 18 { 11 } else { 3 };'
        Failure = $null
    },
    @{
        Name = 'wrong-short-decoded-repeat-count'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let count = usize::from(extra) + if symbol == 18 { 11 } else { 3 };'
        New = 'let count = usize::from(extra) + if symbol == 18 { 11 } else { 2 };'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-long-decoded-repeat-count'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let count = usize::from(extra) + if symbol == 18 { 11 } else { 3 };'
        New = 'let count = usize::from(extra) + if symbol == 18 { 10 } else { 3 };'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'lost-previous-decoded-repeat-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let value = if symbol == 16 { lengths[*have - 1] } else { 0 };'
        New = 'let value = 0u16;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'accepted-decoded-repeat-overrun'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'if *have + count > total {'
        New = 'if false {'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'rejected-exact-decoded-repeat-fit'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'if *have + count > total {'
        New = 'if *have + count >= total {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-decoded-repeat-fill'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'decreases remaining,'
        New = 'decreases count,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'omitted-decoded-repeat-write-caller'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'push_decoded_length(lengths, have, value);'
        New = 'let _ = value;'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'lost-direct-decoded-length'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'lengths[*have] = value;'
        New = 'lengths[*have] = 0;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-decoded-repeat-range'
        File = 'proofs\dynamic_header.rs'
        Old = 'symbol == 18 ==> 11 <= model::repeat_count(symbol, extra) <= 138,'
        New = 'symbol == 18 ==> 11 <= model::repeat_count(symbol, extra) <= 137,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'premature-root-lookahead'
        File = 'proofs\huffman_lookahead.rs'
        Old = '            <= available,'
        New = '            >= available,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'false-independent-root-lookahead-equality'
        File = 'proofs\huffman_lookahead.rs'
        Old = '== table[(second as int) % model::capacity(model::maximum_length(lengths) as nat)],'
        New = '!= table[(second as int) % model::capacity(model::maximum_length(lengths) as nat)],'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-bit-buffer-mask'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let mask = (1u64 << n) - 1;'
        New = 'let mask = (1u64 << n) - 1 + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-bit-buffer-peek-width'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let mask = (1u64 << n) - 1;'
        New = 'let mask = 1u64 << n;'
        Failure = 'requires not satisfied'
    },
    @{
        Name = 'wrong-bit-buffer-consume-direction'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*word >>= n;'
        New = '*word <<= n;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-bit-buffer-count'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*count -= n;'
        New = '*count -= 0;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-bit-buffer-alignment'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let skip = *count & 7;'
        New = 'let skip = 0u8;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'omitted-bit-buffer-consume-caller'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'consume_bits(word, count, skip);'
        New = 'let _ = skip;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-buffer-prefix'
        File = 'proofs\bitreader.rs'
        Old = 'ensures model::buffered_bits(word >> take, (count - take) as u8)'
        New = 'ensures model::buffered_bits(word >> take, count)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-root-lookup-peek-width'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let index = buffer::peek_bits(word, root);'
        New = 'let index = buffer::peek_bits(word, root - 1);'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-root-lookup-table-index'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'table[index as usize]'
        New = 'table[0]'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-root-peek-index'
        File = 'proofs\huffman_lookahead.rs'
        Old = 'ensures value as int == (word as u32 as int) % model::capacity(root as nat),'
        New = 'ensures value as int == 1 + (word as u32 as int) % model::capacity(root as nat),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-byte-append-count'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*count += 8;'
        New = '*count += 8 + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-byte-append-offset'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*word |= (byte as u64) << *count;'
        New = '*word |= byte as u64;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-byte-append-count'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*count += 8;'
        New = '*count += 7;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-bulk-refill-offset'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*word |= read << *count;'
        New = '*word |= read;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-bulk-refill-byte-increment'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let increment = (63 ^ *count) >> 3;'
        New = 'let increment = (55 ^ *count) >> 3;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-bulk-refill-final-count'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*count |= 56;'
        New = '*count |= 48;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-independent-refill-accounting'
        File = 'proofs\bitreader.rs'
        Old = 'ensures ((63u8 ^ count) >> 3) as int == (63 - count as int) / 8,'
        New = 'ensures ((63u8 ^ count) >> 3) as int == (63 - count as int) / 7,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-cache-compatibility'
        File = 'proofs\bitreader.rs'
        Old = 'ensures model::append_compatible(0, count, read, added),'
        New = 'ensures model::append_compatible(u64::MAX, count, read, added),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-cache-consumption'
        File = 'proofs\bitreader.rs'
        Old = 'ensures model::cached_suffix(word >> take, (count - take) as u8, pending),'
        New = 'ensures model::cached_suffix(word >> take, (count - take) as u8, pending.skip(1)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-cache-initialization'
        File = 'proofs\bitreader.rs'
        Old = 'ensures model::cached_suffix(0, count, pending),'
        New = 'ensures model::cached_suffix(u64::MAX, count, pending),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-cache-append'
        File = 'proofs\bitreader.rs'
        Old = 'pending.skip(added as int)),'
        New = 'pending.skip(added as int + 1)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-unused-byte-count'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let bytes = *count >> 3;'
        New = 'let bytes = *count / 8;'
        Failure = $null
    },
    @{
        Name = 'wrong-unused-byte-count'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '    bytes'
        New = '    bytes + 1'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-unused-buffer-prefix'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '*word = peek_bits(*word, *count as usize);'
        New = '*word = peek_bits(0, *count as usize);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-slice-fill-progress'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'consumed += 1;'
        New = 'consumed += 1 + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-slice-fill-input-byte'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'append_byte(word, count, input[consumed]);'
        New = 'append_byte(word, count, input[0]);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'omitted-slice-fill-append'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'append_byte(word, count, input[consumed]);'
        New = 'let _ = input[consumed];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'accepted-slice-fill-exhaustion'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'return (consumed, false);'
        New = 'return (consumed, true);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'rejected-slice-fill-success'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '    (consumed, true)'
        New = '    (consumed, false)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-slice-fill'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'decreases wanted - consumed,'
        New = 'decreases wanted,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'false-independent-input-octet-order'
        File = 'specs\bitreader.rs'
        Old = '(index % 8) as nat'
        New = '(7 - index % 8) as nat'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-independent-slice-byte-limit'
        File = 'proofs\bitreader.rs'
        Old = 'ensures model::needed_bytes(count, target) <= 8,'
        New = 'ensures model::needed_bytes(count, target) <= 7,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-field-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let value = buffer::peek_bits(*word, 3) as u16;'
        New = 'let value = (buffer::peek_bits(*word, 3) as u16) + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-header-field-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let value = buffer::peek_bits(*word, 3) as u16;'
        New = 'let value = buffer::peek_bits(*word, 2) as u16;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'omitted-header-field-write'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'write_length(lengths, *have, value);'
        New = 'let _ = value;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-field-consumption'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'buffer::consume_bits(word, count, 3);'
        New = 'buffer::consume_bits(word, count, 2);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'accepted-header-field-exhaustion'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'return (consumed, false);'
        New = 'return (consumed, true);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-three-bit-value'
        File = 'proofs\bitreader.rs'
        Old = 'ensures (word & 7) as u16 == model::three_bit_value(model::buffered_bits(word, count)),'
        New = 'ensures (word & 7) as u16 == 1 + model::three_bit_value(model::buffered_bits(word, count)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-bulk-input-low-octet'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let result = u64::from(input[0])'
        New = 'let result = (u64::from(input[0]) + 0)'
        Failure = $null
    },
    @{
        Name = 'wrong-bulk-input-low-octet'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let result = u64::from(input[0])'
        New = 'let result = u64::from(input[7])'
        Failure = 'requires not satisfied'
    },
    @{
        Name = 'wrong-bulk-input-high-octet'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '| (u64::from(input[7]) << 56);'
        New = '| (u64::from(input[6]) << 56);'
        Failure = 'requires not satisfied'
    },
    @{
        Name = 'omitted-bulk-input-read'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = 'let read = read_word(input);'
        New = 'let read = 0u64;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-bulk-input-advance'
        File = 'zlib-rs\src\inflate\bitreader\buffer.rs'
        Old = '    refill_bits(word, count, read)'
        New = '    refill_bits(word, count, read) + 1'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-loop-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let needed = 3 * (target - start);'
        New = 'let needed = (target - start) * 3;'
        Failure = $null
    },
    @{
        Name = 'wrong-header-loop-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let needed = 3 * (target - start);'
        New = 'let needed = 2 * (target - start);'
        Failure = 'invariant not satisfied'
    },
    @{
        Name = 'premature-header-loop-termination'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'while *have < target {'
        New = 'while *have + 1 < target {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'nondecreasing-header-read-loop'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'decreases target - *have,'
        New = 'decreases target - start,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'accepted-header-loop-exhaustion'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'return (consumed, complete);'
        New = 'return (consumed, true);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-loop-input-suffix'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let pending = &input[consumed..];'
        New = 'let pending = input;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-independent-header-fill-capacity'
        File = 'proofs\bitreader.rs'
        Old = 'ensures count as int + 8 * model::needed_bytes(count, target) <= 64,'
        New = 'ensures count as int + 8 * model::needed_bytes(count, target) <= 63,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-constructor-readiness'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'if !complete {'
        New = 'if complete == false {'
        Failure = $null
    },
    @{
        Name = 'premature-header-table-construction'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'if !complete {'
        New = 'if false {'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'omitted-header-table-construction'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let outcome = finish_code_length_table(lens, have, table, work);'
        New = 'let outcome = InflateTable::InvalidCode;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'rejected-valid-header-table-outcome'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '(consumed, Some(outcome))'
        New = '(consumed, Some(InflateTable::InvalidCode))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-table-byte-accounting'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '(consumed, Some(outcome))'
        New = '(consumed + 1, Some(outcome))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-padding-policy'
        File = 'specs\dynamic_header.rs'
        Old = 'padded && index < 19 && end <= wire_position(index as nat)'
        New = '!padded && index < 19 && end <= wire_position(index as nat)'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-paired-header-wire-order'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,'
        New = '(16 + 0), 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'if position < 3 { 16 + position }'
                New = 'if position < 3 { 16 + position + 0 }'
            },
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'if symbol >= 16 { (symbol - 16) as nat }'
                New = 'if symbol >= 16 { ((symbol - 16) as nat) + 0 }'
            }
        )
        Failure = $null
    },
    @{
        Name = 'paired-wrong-header-wire-order'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,'
        New = '17, 16, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15,'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'if position < 3 { 16 + position }'
                New = 'if position < 3 { if position < 2 { (17 - position) as nat } else { 18 } }'
            },
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'if symbol >= 16 { (symbol - 16) as nat }'
                New = 'if symbol >= 16 { if symbol == 16 { 1 } else if symbol == 17 { 0 } else { (symbol - 16) as nat } }'
            }
        )
        DiagnosticFile = 'proofs\dynamic_header.rs'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-header-count-offset'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let nlen = buffer::peek_bits(*word, 5) as usize + 257;'
        New = 'let nlen = buffer::peek_bits(*word, 5) as usize + 257 + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-header-nlen-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let nlen = buffer::peek_bits(*word, 5) as usize + 257;'
        New = 'let nlen = buffer::peek_bits(*word, 4) as usize + 257;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-ndist-offset'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let ndist = buffer::peek_bits(*word, 5) as usize + 1;'
        New = 'let ndist = buffer::peek_bits(*word, 5) as usize + 0;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-ncode-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let ncode = buffer::peek_bits(*word, 4) as usize + 4;'
        New = 'let ncode = buffer::peek_bits(*word, 3) as usize + 4;'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-count-consumption'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'buffer::consume_bits(word, count, 4);'
        New = 'buffer::consume_bits(word, count, 3);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'accepted-header-count-exhaustion'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'return (consumed, None);'
        New = 'return (consumed, Some((257, 1, 4)));'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-count-bound'
        File = 'proofs\dynamic_header.rs'
        Old = '4 <= model::header_counts(source).2 <= 19,'
        New = '4 <= model::header_counts(source).2 <= 18,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-count-fixture'
        File = 'proofs\dynamic_header.rs'
        Old = '== (279nat, 14nat, 11nat),'
        New = '== (278nat, 14nat, 11nat),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-header-count-offset'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let ncode = buffer::peek_bits(*word, 4) as usize + 4;'
        New = 'let ncode = buffer::peek_bits(*word, 4) as usize + 5;'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = '4 + bit_specs::low_first_value(source.subrange(10, 14))'
                New = '5 + bit_specs::low_first_value(source.subrange(10, 14))'
            }
        )
        DiagnosticFile = 'proofs\dynamic_header.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-ready-code-length-entry'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '(consumed, Some(entry))'
        New = '(consumed + 0, Some(entry))'
        Failure = $null
    },
    @{
        Name = 'missed-exact-code-length-readiness'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'if here.bits <= *count {'
        New = 'if here.bits < *count {'
        Failure = 'assertion failed'
    },
    @{
        Name = 'accepted-code-length-input-exhaustion'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'return (0, None);'
        New = 'return (0, Some(here));'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'unreported-code-length-input-advance'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '(consumed, Some(entry))'
        New = '(0, Some(entry))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'stale-code-length-entry-after-input'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let entry = lookup_code_length(table, root, *word);'
        New = 'let entry = here;'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'overread-code-length-input'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'buffer::fill_from_slice(word, count, input, root);'
        New = 'buffer::fill_from_slice(word, count, input, root + 8);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-root-entry-minimum'
        File = 'proofs\huffman_lookahead.rs'
        Old = '==> 1 <= (#[trigger] table[index]).bits <= model::maximum_length(lengths),'
        New = '==> 2 <= (#[trigger] table[index]).bits <= model::maximum_length(lengths),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-constructed-root-bound'
        File = 'proofs\huffman_lookahead.rs'
        Old = '==> 1 <= (#[trigger] table[index]).bits <= root,'
        New = '==> 1 <= (#[trigger] table[index]).bits < root,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-repeat-extra-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let extra = buffer::peek_bits(*word, extra_bits) as u16;'
        New = 'let extra = buffer::peek_bits(*word, extra_bits) as u16 + 0;'
        Failure = $null
    },
    @{
        Name = 'wrong-repeat-extra-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '2usize'
        New = '3usize'
        Failure = 'assertion failed'
    },
    @{
        Name = 'omitted-repeat-code-consumption'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'buffer::consume_bits(word, count, code_bits);'
        New = 'buffer::consume_bits(word, count, 0);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'omitted-repeat-extra-consumption'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'buffer::consume_bits(word, count, extra_bits as u8);'
        New = 'buffer::consume_bits(word, count, 0);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'accepted-repeat-extra-exhaustion'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'return (consumed, RepeatExtra::NeedInput);'
        New = 'return (consumed, RepeatExtra::Value(0));'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'premature-repeat-missing-previous'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'return (consumed, RepeatExtra::NeedInput);'
        New = 'return (consumed, RepeatExtra::MissingPrevious);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'lost-repeat-missing-previous'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'return (consumed, RepeatExtra::MissingPrevious);'
        New = 'return (consumed, RepeatExtra::Value(0));'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-repeat-extra-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let extra = buffer::peek_bits(*word, extra_bits) as u16;'
        New = 'let extra = buffer::peek_bits(*word, extra_bits) as u16 + 1;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'unreported-repeat-extra-input-advance'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '(consumed, RepeatExtra::Value(extra))'
        New = '(0, RepeatExtra::Value(extra))'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-independent-repeat-extra-bound'
        File = 'proofs\dynamic_header.rs'
        Old = 'ensures model::repeat_extra_value(source, code_bits, symbol) < model::repeat_extra_limit(symbol),'
        New = 'ensures model::repeat_extra_value(source, code_bits, symbol) + 1 < model::repeat_extra_limit(symbol),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-repeat-extra-fixture'
        File = 'proofs\dynamic_header.rs'
        Old = 'seq![true, false, true, true, false, true, false, false, true, true], 3, 18) == 101,'
        New = 'seq![true, false, true, true, false, true, false, false, true, true], 3, 18) == 100,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-paired-repeat-extra-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '2usize'
        New = '(2usize + 0)'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'if symbol == 16 { 2 } else if symbol == 17 { 3 } else { 7 }'
                New = 'if symbol == 16 { 2 + 0 } else if symbol == 17 { 3 } else { 7 }'
            }
        )
        Failure = $null
    },
    @{
        Name = 'paired-wrong-repeat-extra-width'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = '2usize'
        New = '3usize'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'if symbol == 16 { 2 } else if symbol == 17 { 3 } else { 7 }'
                New = 'if symbol == 16 { 3 } else if symbol == 17 { 3 } else { 7 }'
            }
        )
        DiagnosticFile = 'proofs\dynamic_header.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-repeat-input-expansion'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'Some(repeat_decoded_length(lengths, have, total, symbol, extra))'
        New = 'Some(repeat_decoded_length(lengths, have, total, symbol, extra) && true)'
        Failure = $null
    },
    @{
        Name = 'skipped-repeat-input-expansion'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'Some(repeat_decoded_length(lengths, have, total, symbol, extra))'
        New = 'Some(true)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'masked-repeat-input-overrun'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'Some(repeat_decoded_length(lengths, have, total, symbol, extra))'
        New = 'Some({ let _result = repeat_decoded_length(lengths, have, total, symbol, extra); true })'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'inverted-repeat-input-result'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'Some(repeat_decoded_length(lengths, have, total, symbol, extra))'
        New = 'Some(!repeat_decoded_length(lengths, have, total, symbol, extra))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'premature-repeat-input-error'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'RepeatExtra::NeedInput => (consumed, None),'
        New = 'RepeatExtra::NeedInput => (consumed, Some(false)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'lost-repeat-input-missing-previous'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'RepeatExtra::MissingPrevious => (consumed, Some(false)),'
        New = 'RepeatExtra::MissingPrevious => (consumed, None),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'unreported-repeat-input-advance'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let (consumed, outcome) = read_repeat_extra(word, count, input, code_bits, symbol, *have);'
        New = 'let (_consumed, outcome) = read_repeat_extra(word, count, input, code_bits, symbol, *have); let consumed = 0usize;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-repeat-input-progress'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'Some(repeat_decoded_length(lengths, have, total, symbol, extra))'
        New = 'Some({ let result = repeat_decoded_length(lengths, have, total, symbol, extra); *have += 1; result })'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'lost-repeat-input-truncation-frame'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'RepeatExtra::NeedInput => (consumed, None),'
        New = 'RepeatExtra::NeedInput => { if !lengths.is_empty() { lengths[0] = 0; } (consumed, None) },'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-repeat-input-fixture'
        File = 'proofs\dynamic_header.rs'
        Old = 'seq![7u16, 4, 4, 4, 4, 4]'
        New = 'seq![7u16, 4, 4, 4, 4, 5]'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-paired-repeat-input-error'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'RepeatExtra::MissingPrevious => (consumed, Some(false)),'
        New = 'RepeatExtra::MissingPrevious => (consumed, Some(false && true)),'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'None => false,'
                New = 'None => false || false,'
            }
        )
        Failure = $null
    },
    @{
        Name = 'paired-lost-repeat-input-error'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'RepeatExtra::MissingPrevious => (consumed, Some(false)),'
        New = 'RepeatExtra::MissingPrevious => (consumed, None),'
        Additional = @(
            @{
                File = 'specs\dynamic_header.rs'
                Old = 'None => false,'
                New = 'None => symbol == 16 && processed == 0 && after == before && final_processed == processed,'
            }
        )
        DiagnosticFile = 'proofs\dynamic_header.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-source-prefix-number'
        File = 'specs\huffman.rs'
        Old = 'crate::bit_specs::low_first_value(source.take(lengths[symbol] as int))'
        New = '(crate::bit_specs::low_first_value(source.take(lengths[symbol] as int)) + 0)'
        Failure = $null
    },
    @{
        Name = 'wrong-source-prefix-offset'
        File = 'specs\huffman.rs'
        Old = 'crate::bit_specs::low_first_value(source.take(lengths[symbol] as int))'
        New = 'crate::bit_specs::low_first_value(source.skip(1).take(lengths[symbol] as int))'
        DiagnosticFile = 'proofs\huffman_lookahead.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'rejected-exact-source-prefix'
        File = 'specs\huffman.rs'
        Old = 'lengths[symbol] <= source.len()'
        New = 'lengths[symbol] < source.len()'
        DiagnosticFile = 'proofs\huffman_lookahead.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-rfc-canonical-assignment'
        File = 'proofs\huffman_lookahead.rs'
        Old = 'model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 7) == 15,'
        New = 'model::canonical_code(seq![3u16, 3, 3, 3, 3, 2, 4, 4], 7) == 14,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-rfc-canonical-wire'
        File = 'proofs\huffman_lookahead.rs'
        Old = 'seq![false, true, true]),'
        New = 'seq![true, true, false]),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-source-prefix-readiness'
        File = 'proofs\huffman_lookahead.rs'
        Old = 'crate::bit_specs::buffered_bits(word, count))) == (entry.bits <= count),'
        New = 'crate::bit_specs::buffered_bits(word, count))) == (entry.bits < count),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-huffman-reversal-prefix-width'
        File = 'zlib-rs\src\inflate\inftrees\codes.rs'
        Old = 'result < huffman_specs::capacity(length as nat),'
        New = 'result < huffman_specs::capacity((length - 1) as nat),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-prefix-byte-accounting'
        File = 'proofs\bitreader.rs'
        Old = 'ensures first + model::needed_bytes((count as nat + 8 * first) as u8, target)'
        New = 'ensures (first + 0) + model::needed_bytes((count as nat + 8 * first) as u8, target)'
        Failure = $null
    },
    @{
        Name = 'reversed-raw-fill-composition'
        File = 'proofs\bitreader.rs'
        Old = 'ensures model::filled_word(before, count, after, first + second),'
        New = 'ensures model::filled_word(before, count, after, second + first),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'unreported-prefix-fill-bytes'
        File = 'proofs\bitreader.rs'
        Old = 'ensures first + model::needed_bytes((count as nat + 8 * first) as u8, target)'
        New = 'ensures model::needed_bytes((count as nat + 8 * first) as u8, target)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'overreported-capped-fill-bytes'
        File = 'proofs\bitreader.rs'
        Old = '} else { (available - first) as nat })'
        New = '} else { (available - first + 1) as nat })'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-selected-code-minimal-input'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '&& result.0 == bit_specs::needed_bytes(*old(count), entry.bits as usize),'
        New = '&& result.0 == bit_specs::needed_bytes(*old(count), entry.bits as usize) + 0,'
        Failure = $null
    },
    @{
        Name = 'false-one-bit-code-minimal-input'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = '(root == 1 ==> result.0 == bit_specs::needed_bytes(*old(count), entry.bits as usize))'
        New = '(root == 1 ==> result.0 == bit_specs::needed_bytes(*old(count), entry.bits as usize) + 1)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-filled-low-prefix-projection'
        File = 'proofs\huffman_lookahead.rs'
        Old = '== (after as u32 as int) % model::capacity(available as nat),'
        New = '== ((after as u32 as int) + 1) % model::capacity(available as nat),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-symbol-step-byte-sum'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let result = (first + second, outcome);'
        New = 'let result = (second + first, outcome);'
        Failure = $null
    },
    @{
        Name = 'unreported-symbol-step-input'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let result = (first + second, outcome);'
        New = 'let result = (second, outcome);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-direct-symbol-consumption'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'buffer::consume_bits(word, count, bits);'
        New = 'buffer::consume_bits(word, count, bits - 1);'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-direct-symbol-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'push_decoded_length(lengths, have, symbol);'
        New = 'push_decoded_length(lengths, have, if symbol == 0 { 1 } else { symbol });'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-direct-symbol-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        DiagnosticFile = 'proofs\dynamic_header.rs'
        Old = 'push_decoded_length(lengths, have, symbol);'
        New = 'push_decoded_length(lengths, have, if symbol == 0 { 1 } else { symbol });'
        Additional = @(@{
            File = 'specs\dynamic_header.rs'
            Old = 'if index == processed { value } else { before[index] }'
            New = 'if index == processed { if value == 0 { 1 } else { value } } else { before[index] }'
        })
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-paired-direct-symbol-value'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'push_decoded_length(lengths, have, symbol);'
        New = 'push_decoded_length(lengths, have, symbol + 0);'
        Additional = @(@{
            File = 'specs\dynamic_header.rs'
            Old = 'if index == processed { value } else { before[index] }'
            New = 'if index == processed { (value + 0) as u16 } else { before[index] }'
        })
        Failure = $null
    },
    @{
        Name = 'false-independent-symbol-step-fixture'
        File = 'proofs\dynamic_header.rs'
        Old = 'seq![7u16,0,9,9,9], 1, 2, 5,'
        New = 'seq![7u16,1,9,9,9], 1, 2, 5,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-empty-symbol-fixture'
        File = 'proofs\dynamic_header.rs'
        Old = 'seq![0u16,9], 0, 1, 2,'
        New = 'seq![1u16,9], 0, 1, 2,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-symbol-step-input-suffix'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let remaining = &input[first..];'
        New = 'let remaining = &input[..input.len() - first];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-selected-repeat-symbol'
        File = 'zlib-rs\src\inflate\header_lengths.rs'
        Old = 'let result = read_repeat_lengths(word, count, input, bits, symbol, lengths, have, total);'
        New = 'let result = read_repeat_lengths(word, count, input, bits, 18, lengths, have, total);'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'equivalent-header-loop-advance'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'advanced += consumed;'
        New = 'advanced = advanced + consumed;'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-header-loop-advance'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'advanced += consumed;'
        New = 'advanced += consumed + 0;'
        Additional = @(
            @{
                File = 'specs\header_loop.rs'
                Old = 'before.advanced <= after.advanced <= pending.len() / 8'
                New = 'before.advanced + 0 <= after.advanced <= pending.len() / 8'
            }
        )
        Failure = $null
    },
    @{
        Name = 'unreported-header-loop-input'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = '(advanced, Some(true))'
        New = '(0, Some(true))'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-symbol-length-loop-input-suffix'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'let remaining = &input[advanced..];'
        New = 'let remaining = &input[..input.len() - advanced];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'premature-header-loop-completion'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if outcome != Some(true) {'
        New = 'if outcome != Some(true) || *have < total {'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'ignored-header-loop-data-error'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if outcome != Some(true) {'
        New = 'if outcome.is_none() {'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'nondecreasing-header-loop'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'decreases total - *have,'
        New = 'decreases total,'
        Failure = 'decreases not satisfied'
    },
    @{
        Name = 'wrong-header-loop-stop-policy'
        File = 'specs\header_loop.rs'
        Old = 'if outcome == Some(true) {'
        New = 'if outcome.is_some() {'
        DiagnosticFile = 'proofs\header_loop.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-loop-completion'
        File = 'proofs\header_loop.rs'
        Old = 'model::state(seq![7u16,0,0,0,0], 5, 0, 4, 1, 4), Some(true)),'
        New = 'model::state(seq![7u16,1,0,0,0], 5, 0, 4, 1, 4), Some(true)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-loop-suspension'
        File = 'proofs\header_loop.rs'
        Old = 'model::state(seq![7u16,0,9,9,9], 2, 1, 1, 0, 1), None),'
        New = 'model::state(seq![7u16,0,9,9,9], 2, 1, 1, 0, 1), Some(false)),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-empty-header-eob'
        File = 'proofs\header_loop.rs'
        Old = 'ensures after.lengths[256] == 0,'
        New = 'ensures after.lengths[256] == 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-eob-check'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if lengths[256] == 0 {'
        New = 'if 0 == lengths[256] {'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-header-eob-check'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if lengths[256] == 0 {'
        New = 'if lengths[256] < 1 {'
        Additional = @(
            @{
                File = 'specs\header_loop.rs'
                Old = '&& after.lengths[256] == 0,'
                New = '&& after.lengths[256] < 1,'
            }
        )
        Failure = $null
    },
    @{
        Name = 'wrong-header-eob-index'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if lengths[256] == 0 {'
        New = 'if lengths[255] == 0 {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'skipped-header-eob-check'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if lengths[256] == 0 {'
        New = 'if false {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'premature-header-eob-error'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'None => HeaderOutcome::NeedInput,'
        New = 'None => HeaderOutcome::MissingEob,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'lost-header-repeat-error'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'Some(false) => HeaderOutcome::InvalidRepeat,'
        New = 'Some(false) => HeaderOutcome::NeedInput,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-header-eob-message'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'Self::MissingEob => Some("invalid code -- missing end-of-block\0"),'
        New = 'Self::MissingEob => Some("invalid bit length repeat\0"),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-repeat-message'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'Self::InvalidRepeat => Some("invalid bit length repeat\0"),'
        New = 'Self::InvalidRepeat => Some("invalid code -- missing end-of-block\0"),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-completion'
        File = 'proofs\header_loop.rs'
        Old = 'crate::huffman::HeaderOutcome::Complete),'
        New = 'crate::huffman::HeaderOutcome::MissingEob),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-suspension'
        File = 'proofs\header_loop.rs'
        Old = 'crate::huffman::HeaderOutcome::NeedInput),'
        New = 'crate::huffman::HeaderOutcome::MissingEob),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-repeat'
        File = 'proofs\header_loop.rs'
        Old = 'crate::huffman::HeaderOutcome::InvalidRepeat),'
        New = 'crate::huffman::HeaderOutcome::MissingEob),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-header-eob-value'
        File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
        Old = 'if lengths[256] == 0 {'
        New = 'if lengths[256] == 1 {'
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
                Old = '<==> *final(have) == total && final(lengths)@[256] == 0,'
                New = '<==> *final(have) == total && final(lengths)@[256] == 1,'
            },
            @{
                File = 'zlib-rs\src\inflate\inftrees\header_loop.rs'
                Old = '<==> *final(have) == total && final(lengths)@[256] != 0,'
                New = '<==> *final(have) == total && final(lengths)@[256] != 1,'
            },
            @{
                File = 'specs\header_loop.rs'
                Old = '&& after.lengths[256] == 0,'
                New = '&& after.lengths[256] == 1,'
            },
            @{
                File = 'specs\header_loop.rs'
                Old = '&& after.lengths[256] != 0,'
                New = '&& after.lengths[256] != 1,'
            }
        )
        DiagnosticFile = 'proofs\header_loop.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-header-constructor-advance'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'let advanced = first + second;'
        New = 'let advanced = second + first;'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-header-constructor-reset'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = '*have = 0;'
        New = '*have = 0 + 0;'
        Additional = @(
            @{
                File = 'specs\header_producer.rs'
                Old = 'lengths::state(middle.lengths, 0, middle.word, middle.count, 0, 0)'
                New = 'lengths::state(middle.lengths, 0 + 0, middle.word, middle.count, 0, 0)'
            }
        )
        Failure = $null
    },
    @{
        Name = 'missing-header-constructor-reset'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = '*have = 0;'
        New = '*have = 19;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'unreported-header-constructor-input'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'let advanced = first + second;'
        New = 'let advanced = second;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-header-constructor-input-suffix'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'let remaining = &input[first..];'
        New = 'let remaining = &input[..input.len() - first];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-header-constructor-root'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'super::read_length_header(word, count, remaining, table, root, lens, have, total);'
        New = 'super::read_length_header(word, count, remaining, table, 7, lens, have, total);'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-header-constructor-error-stage'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'return (first, HeaderReadOutcome::NeedAlphabet);'
        New = 'return (first, HeaderReadOutcome::InvalidAlphabet);'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-constructor-used-count'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = 'Some(InflateTable::Success { root, used }) => (root, used),'
        New = 'Some(InflateTable::Success { root, used: _ }) => (root, 0),'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'false-independent-header-producer-progress'
        File = 'proofs\header_producer.rs'
        Old = '0, 0, 0, 0, 12), Seq::empty(), 4, 257,'
        New = '1, 0, 0, 0, 12), Seq::empty(), 4, 257,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-header-producer-metadata'
        File = 'proofs\header_producer.rs'
        Old = 'root: 1, used: 2, outcome: crate::huffman::HeaderOutcome::NeedInput }),'
        New = 'root: 1, used: 3, outcome: crate::huffman::HeaderOutcome::NeedInput }),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-header-producer-drop-coordinate'
        File = 'specs\header_producer.rs'
        Old = '(after.dropped - middle.dropped) as nat), decoded)'
        New = 'after.dropped as nat), decoded)'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Failure = 'assertion failed'
    },
    @{
        Name = 'paired-wrong-header-constructor-reset'
        File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
        Old = '*have = 0;'
        New = '*have = 19;'
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inftrees\header_start.rs'
                Old = 'lengths::state(middle.lengths, 0, middle.word, middle.count, 0, 0),'
                New = 'lengths::state(middle.lengths, 19, middle.word, middle.count, 0, 0),'
            },
            @{
                File = 'specs\header_producer.rs'
                Old = 'lengths::state(middle.lengths, 0, middle.word, middle.count, 0, 0)'
                New = 'lengths::state(middle.lengths, 19, middle.word, middle.count, 0, 0)'
            }
        )
        DiagnosticFile = 'proofs\header_producer.rs'
        Failure = 'assertion failed'
    },
    @{
        Name = 'equivalent-dynamic-count-advance'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'let advanced = first + second;'
        New = 'let advanced = second + first;'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-dynamic-count-profile'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'if nlen > 286 || ndist > 30 {'
        New = 'if 286 < nlen || 30 < ndist {'
        Additional = @(
            @{
                File = 'specs\dynamic_start.rs'
                Old = 'nlen <= 286 && ndist <= 30'
                New = '286 >= nlen && 30 >= ndist'
            }
        )
        Failure = $null
    },
    @{
        Name = 'wrong-dynamic-count-profile'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'if nlen > 286 || ndist > 30 {'
        New = 'if nlen > 285 || ndist > 30 {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-dynamic-count-profile'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'if nlen > 286 || ndist > 30 {'
        New = 'if nlen > 285 || ndist > 30 {'
        Additional = @(
            @{
                File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
                Old = '(counts.0 > 286 || counts.1 > 30),'
                New = '(counts.0 > 285 || counts.1 > 30),'
            },
            @{
                File = 'specs\dynamic_start.rs'
                Old = 'nlen <= 286 && ndist <= 30'
                New = 'nlen <= 285 && ndist <= 30'
            }
        )
        DiagnosticFile = 'proofs\dynamic_start.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-dynamic-count-progress-reset'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = '*have = 0;'
        New = '*have = 1;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-dynamic-count-alphabet-target'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = '        ncode,'
        New = '        4,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'unreported-dynamic-count-input'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'let advanced = first + second;'
        New = 'let advanced = second;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-dynamic-count-input-suffix'
        File = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Old = 'let remaining = &input[first..];'
        New = 'let remaining = &input[..];'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-dynamic-count-bit-width'
        File = 'specs\dynamic_start.rs'
        Old = '&& after.dropped == if counts.is_some() { 14nat } else { 0nat }'
        New = '&& after.dropped == if counts.is_some() { 13nat } else { 0nat }'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-dynamic-count-drop-coordinate'
        File = 'specs\dynamic_start.rs'
        Old = '(after.dropped - middle.dropped) as nat),'
        New = 'after.dropped as nat),'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees\dynamic_start.rs'
        Failure = 'assertion failed'
    },
    @{
        Name = 'false-independent-dynamic-count-progress'
        File = 'proofs\dynamic_start.rs'
        Old = '0, 0, 0, 0, 14),'
        New = '1, 0, 0, 0, 14),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-dynamic-count-metadata'
        File = 'proofs\dynamic_start.rs'
        Old = 'counts: (257, 1, 4), outcome: crate::huffman::HeaderReadOutcome::NeedAlphabet }),'
        New = 'counts: (257, 1, 5), outcome: crate::huffman::HeaderReadOutcome::NeedAlphabet }),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-subtable-link-cell'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'table[prefix] = Code {'
        New = 'table[prefix + 0] = Code {'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-subtable-link-offset'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'val: layout.next as u16,'
        New = 'val: (layout.next + 0) as u16,'
        Failure = $null
        Additional = @(@{
            File = 'specs\huffman.rs'
            Old = '&& entry.bits == root && entry.op == width && entry.val == next'
            New = '&& entry.bits == root && entry.op == width && entry.val == next + 0'
        })
    },
    @{
        Name = 'wrong-subtable-link-offset'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'val: layout.next as u16,'
        New = 'val: (layout.next - 1) as u16,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'paired-wrong-subtable-link-offset'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'val: layout.next as u16,'
        New = 'val: (layout.next - 1) as u16,'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\huffman.rs'
        Additional = @(@{
            File = 'specs\huffman.rs'
            Old = '&& entry.bits == root && entry.op == width && entry.val == next'
            New = '&& entry.bits == root && entry.op == width && entry.val as int == next - 1'
        })
    },
    @{
        Name = 'wrong-subtable-link-width'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'op: layout.width as u8,'
        New = 'op: root as u8,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-subtable-link-root-bits'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'bits: root as u8,'
        New = 'bits: (root + 1) as u8,'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-subtable-link-prefix'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'table[prefix] = Code {'
        New = 'table[0] = Code {'
        Failure = 'assertion failed'
    },
    @{
        Name = 'subtable-link-write-after-rejection'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'if !advance_layout(layout, counts, length, drop, max, kind, previous_size) {'
        New = 'if !advance_layout(layout, counts, length, drop, max, kind, previous_size) { table[prefix] = Code { op: 0, bits: 0, val: 0 };'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'reversed-subtable-link-rejection'
        File = 'zlib-rs\src\inflate\inftrees\layout.rs'
        Old = 'if !advance_layout(layout, counts, length, drop, max, kind, previous_size) {'
        New = 'if advance_layout(layout, counts, length, drop, max, kind, previous_size) {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-subtable-index-coordinate'
        File = 'specs\huffman.rs'
        Old = '((word as int) / capacity(entry.bits as nat))'
        New = '((word as int) / capacity(entry.bits as nat + 1))'
        DiagnosticFile = 'proofs\huffman.rs'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-subtable-link-fixture'
        File = 'proofs\huffman.rs'
        Old = 'model::subtable_index(Code { bits: 2, op: 2, val: 6 }, 15) == 9,'
        New = 'model::subtable_index(Code { bits: 2, op: 2, val: 6 }, 15) == 8,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-distance-subtable-width-sum'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'buffer::peek_bits(word, (root + width) as usize)'
        New = 'buffer::peek_bits(word, (width + root) as usize)'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-distance-subtable-base'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'link.val as usize + selected'
        New = 'selected + link.val as usize'
        Failure = $null
        Additional = @(@{
            File = 'specs\huffman.rs'
            Old = 'entry.val as int + ((word as int) / capacity(entry.bits as nat)) % capacity(entry.op as nat)'
            New = '((word as int) / capacity(entry.bits as nat)) % capacity(entry.op as nat) + entry.val as int'
        })
    },
    @{
        Name = 'wrong-distance-subtable-base'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'link.val as usize + selected'
        New = 'selected'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-distance-subtable-base'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'link.val as usize + selected'
        New = 'selected'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\huffman.rs'
        Additional = @(
            @{
                File = 'specs\huffman.rs'
                Old = 'entry.val as int + ((word as int) / capacity(entry.bits as nat)) % capacity(entry.op as nat)'
                New = '((word as int) / capacity(entry.bits as nat)) % capacity(entry.op as nat)'
            },
            @{
                File = 'zlib-rs\src\inflate\inftrees.rs'
                Old = 'link.val <= result < link.val as int + huffman_specs::capacity(link.op as nat),'
                New = '0 <= result < huffman_specs::capacity(link.op as nat),'
            },
            @{
                File = 'zlib-rs\src\inflate\inftrees.rs'
                Old = 'next <= (link.val as int + selected as int) < used by {'
                New = 'next <= selected < used by {'
            }
        )
    },
    @{
        Name = 'wrong-distance-subtable-shift'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'let shifted = masked >> root;'
        New = 'let shifted = masked >> width;'
        Failure = 'assertion failed'
    },
    @{
        Name = 'wrong-distance-subtable-peek-width'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'buffer::peek_bits(word, (root + width) as usize)'
        New = 'buffer::peek_bits(word, width as usize)'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'truncated-distance-subtable-result'
        File = 'zlib-rs\src\inflate\inftrees.rs'
        Old = 'link.val as usize + selected'
        New = '((link.val as usize + selected) as u16) as usize'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-distance-subtable-model-quotient'
        File = 'specs\huffman.rs'
        Old = '((word as int) / capacity(entry.bits as nat))'
        New = '((word as int) / capacity(entry.op as nat))'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'zlib-rs\src\inflate\inftrees.rs'
    },
    @{
        Name = 'false-independent-distance-subtable-boundary'
        File = 'proofs\huffman.rs'
        Old = 'model::subtable_index(Code { bits: 1, op: 14, val: 65535 }, u64::MAX as nat) == 81918,'
        New = 'model::subtable_index(Code { bits: 1, op: 14, val: 65535 }, u64::MAX as nat) == 81917,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-distance-subtable-bitorder'
        File = 'proofs\huffman.rs'
        Old = 'model::subtable_index(Code { bits: 2, op: 1, val: 4 }, 13) == 5,'
        New = 'model::subtable_index(Code { bits: 2, op: 1, val: 4 }, 13) == 4,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-preparation-root-clamp'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'Ord::min(Ord::max(requested, min), max)'
        New = 'Ord::max(Ord::min(requested, max), min)'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-preparation-literal-capacity'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'used > ENOUGH_LENS'
        New = 'used > ENOUGH_LENS + 0'
        Failure = $null
        Additional = @(@{
            File = 'specs\table_preparation.rs'
            Old = 'h::Alphabet::LiteralLengths => used <= 1332,'
            New = 'h::Alphabet::LiteralLengths => used <= 1332 + 0,'
        })
    },
    @{
        Name = 'wrong-preparation-root-clamp'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'Ord::min(Ord::max(requested, min), max)'
        New = 'max'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-preparation-root-clamp'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'Ord::min(Ord::max(requested, min), max)'
        New = 'if requested < min { min } else { max }'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\table_preparation.rs'
        Additional = @(@{
            File = 'specs\table_preparation.rs'
            Old = 'else { requested }'
            New = 'else { maximum }'
        })
    },
    @{
        Name = 'wrong-preparation-completeness-policy'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'analysis::analyze_and_sort_lengths(lens, matches!(kind, CodeType::Codes), work)'
        New = 'analysis::analyze_and_sort_lengths(lens, false, work)'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-preparation-invalid-result'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'return TablePreparation::Finished(InflateTable::InvalidCode)'
        New = 'return TablePreparation::Finished(InflateTable::Success { root: 1, used: 2 })'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-preparation-empty-code'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'table[1] = code;'
        New = 'table[1] = Code { op: 0, bits: 0, val: 0 };'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'modified-preparation-empty-workspace'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'table[0] = code;'
        New = 'table[0] = code; if !work.is_empty() { work[0] = 0; }'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-preparation-literal-capacity'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'used > ENOUGH_LENS'
        New = 'used > 1023'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-preparation-literal-capacity'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'used > ENOUGH_LENS'
        New = 'used > 1023'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\table_preparation.rs'
        Additional = @(@{
            File = 'specs\table_preparation.rs'
            Old = 'h::Alphabet::LiteralLengths => used <= 1332,'
            New = 'h::Alphabet::LiteralLengths => used <= 1023,'
        })
    },
    @{
        Name = 'omitted-preparation-distance-capacity'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'if matches!(kind, CodeType::Dists) && used > ENOUGH_DISTS {'
        New = 'if false {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-preparation-root-used'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = 'used: layout.used,'
        New = 'used: layout.used - 1,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-preparation-entry-threshold'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = '        threshold,'
        New = '        threshold: 0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'corrupted-preparation-histogram'
        File = 'zlib-rs\src\inflate\inftrees\preparation.rs'
        Old = '        count,'
        New = '        count: [0; 16],'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-preparation-profile-boundary'
        File = 'proofs\table_preparation.rs'
        Old = 'ensures model::root_capacity_allowed(Alphabet::LiteralLengths, 1024),'
        New = 'ensures model::root_capacity_allowed(Alphabet::LiteralLengths, 1333),'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-preparation-root-boundary'
        File = 'proofs\table_preparation.rs'
        Old = 'model::clamped_root(10, 1, 11) == 10,'
        New = 'model::clamped_root(10, 1, 11) == 11,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'equivalent-emission-consumed-width'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        position.length - position.drop,'
        New = '        (position.length - position.drop) + 0,'
        Failure = $null
    },
    @{
        Name = 'equivalent-paired-emission-absolute-base'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        layout,'
        New = '        &TableLayout { next: layout.next + 0, width: layout.width, used: layout.used },'
        Failure = $null
        Additional = @(@{
            File = 'specs\table_emission.rs'
            Old = 'h::table_replica(base, prefix, bits, width, index)'
            New = 'h::table_replica(base + 0, prefix, bits, width, index)'
        })
    },
    @{
        Name = 'wrong-emission-absolute-base'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        layout,'
        New = '        &TableLayout { next: 0, width: layout.width, used: layout.used - layout.next },'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'paired-wrong-emission-absolute-base'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        layout,'
        New = '        &TableLayout { next: 0, width: layout.width, used: layout.used - layout.next },'
        Failure = 'postcondition not satisfied'
        DiagnosticFile = 'proofs\table_emission.rs'
        Additional = @(@{
            File = 'specs\table_emission.rs'
            Old = 'h::table_replica(base, prefix, bits, width, index)'
            New = 'h::table_replica(0, prefix, bits, width, index)'
        })
    },
    @{
        Name = 'wrong-emission-prefix'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        position.prefix,'
        New = '        0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-emission-consumed-width'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        position.length - position.drop,'
        New = '        position.length,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-emission-drop'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        position.drop,'
        New = '        0,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-emission-symbol'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = 'let entry = entries::make_entry('
        New = 'let symbol = 0; let entry = entries::make_entry('
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'wrong-emission-threshold'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '        parameters.2,'
        New = '        0,'
        Failure = 'precondition not satisfied'
    },
    @{
        Name = 'wrong-emission-returned-size'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '    (entry, previous_size)'
        New = '    (entry, previous_size - 1)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'clobbered-emission-outside-cell'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '    (entry, previous_size)'
        New = '    { table[0] = Code { bits: 0, op: 0, val: 0 }; (entry, previous_size) }'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'omitted-emission-replication'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = 'let previous_size = replicate::replicate_entry('
        New = 'let previous_size = layout.used - layout.next; /* replicate::replicate_entry('
        Failure = 'postcondition not satisfied'
        Additional = @(@{
            File = 'zlib-rs\src\inflate\inftrees\emission.rs'
            Old = '    (entry, previous_size)'
            New = '    */ (entry, previous_size)'
        })
    },
    @{
        Name = 'wrong-emission-returned-entry'
        File = 'zlib-rs\src\inflate\inftrees\emission.rs'
        Old = '    (entry, previous_size)'
        New = '    (Code { bits: 0, op: 0, val: 0 }, previous_size)'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-emission-cell'
        File = 'proofs\table_emission.rs'
        Old = 'Seq::new(24, |index: int| if index == 9 || index == 17 {'
        New = 'Seq::new(24, |index: int| if index == 9 || index == 18 {'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-emission-link-offset'
        File = 'proofs\table_emission.rs'
        Old = 'h::subtable_index(Code { bits: 2, op: 4, val: 4 }, 53) == 17,'
        New = 'h::subtable_index(Code { bits: 2, op: 4, val: 4 }, 53) == 16,'
        Failure = 'postcondition not satisfied'
    },
    @{
        Name = 'false-independent-emission-eob-role'
        File = 'proofs\table_emission.rs'
        Old = 'entry.op & 32 != 0 ==> matches!(alphabet, Alphabet::LiteralLengths) && symbol == 256,'
        New = 'entry.op & 32 != 0 ==> matches!(alphabet, Alphabet::LiteralLengths) && symbol == 255,'
        Failure = 'postcondition not satisfied'
    }
)

$duplicateCases = @($cases | Group-Object -Property Name | Where-Object Count -gt 1)
if ($duplicateCases.Count -gt 0) {
    throw "Control names must be unique: $($duplicateCases.Name -join ', ')"
}

if ($Controls.Count -gt 0) {
    $unknown = @($Controls | Where-Object { $_ -notin $cases.Name })
    if ($unknown.Count -gt 0) { throw "Unknown controls: $($unknown -join ', ')" }
    $cases = @($cases | Where-Object { $_.Name -in $Controls })
}

$baseline = Join-Path $EvidenceDirectory 'baseline'
$hashes = [ordered]@{}
foreach ($file in $files) {
    $destination = Join-Path $baseline $file
    New-Item -ItemType Directory -Force -Path (Split-Path $destination) | Out-Null
    Copy-Item -LiteralPath (Join-Path $root $file) -Destination $destination
    $hashes[$file] = (Get-FileHash -LiteralPath $destination -Algorithm SHA256).Hash
}
$hashes | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $EvidenceDirectory 'baseline-source-sha256.json')

$results = foreach ($case in $cases) {
    $copy = Join-Path $EvidenceDirectory $case.Name
    foreach ($file in $files) {
        $destination = Join-Path $copy $file
        New-Item -ItemType Directory -Force -Path (Split-Path $destination) | Out-Null
        Copy-Item -LiteralPath (Join-Path $baseline $file) -Destination $destination
    }
    $mutations = @($case)
    if ($case.Additional) { $mutations += @($case.Additional) }
    $mutatedHashes = [ordered]@{}
    foreach ($mutation in $mutations) {
        $changed = Join-Path $copy $mutation.File
        $source = [IO.File]::ReadAllText($changed)
        if ([regex]::Matches($source, [regex]::Escape($mutation.Old)).Count -ne 1) {
            throw "Mutation must bind exactly once: $($case.Name) $($mutation.File)"
        }
        [IO.File]::WriteAllText($changed, $source.Replace($mutation.Old, $mutation.New))
        $mutatedHashes[$mutation.File] = $null
    }
    foreach ($file in @($mutatedHashes.Keys)) {
        $mutatedHashes[$file] = (Get-FileHash -LiteralPath (Join-Path $copy $file) -Algorithm SHA256).Hash
    }
    $stdout = Join-Path $copy 'stdout.log'
    $stderr = Join-Path $copy 'stderr.log'
    # Reuse only pinned dependencies; always discard the application proof cache.
    & cargo +1.99.1 clean --manifest-path (Join-Path $copy 'verus\Cargo.toml') `
        --target-dir $build --package zlib-rs-verification `
        1> (Join-Path $copy 'application-clean.stdout.log') `
        2> (Join-Path $copy 'application-clean.stderr.log')
    if ($LASTEXITCODE -ne 0) { throw "Application cache cleanup failed: $copy" }
    & cargo +1.99.1 verus verify --manifest-path (Join-Path $copy 'verus\Cargo.toml') `
        --locked --offline --target-dir $build `
        --fwd-verus-args-to roots -- --no-cheating 1> $stdout 2> $stderr
    $code = $LASTEXITCODE
    $output = [IO.File]::ReadAllText($stdout) + [IO.File]::ReadAllText($stderr)
    $summaries = [regex]::Matches($output, 'verification results:: (\d+) verified, (\d+) errors')
    if ($summaries.Count -eq 0) {
        throw "No actual proof summary for $($case.Name); see $copy"
    }
    $summary = $summaries[$summaries.Count - 1]
    $diagnosticFile = if ($case.DiagnosticFile) { $case.DiagnosticFile } else { $case.File }
    if ($case.Failure) {
        if ($code -eq 0 -or [int]$summary.Groups[2].Value -eq 0 `
            -or -not $output.Contains($case.Failure) `
            -or -not $output.Contains((Split-Path $diagnosticFile -Leaf)) `
            -or $output -match 'error\[E\d+\]|resource limit|could not execute|Verus does not currently support') {
            throw "Not the intended semantic rejection for $($case.Name); see $copy"
        }
    } elseif ($code -ne 0 -or [int]$summary.Groups[1].Value -eq 0 `
        -or [int]$summary.Groups[2].Value -ne 0) {
        throw "Equivalent control did not verify; see $copy"
    }
    [pscustomobject]@{
        control = $case.Name
        exit = $code
        verified = [int]$summary.Groups[1].Value
        errors = [int]$summary.Groups[2].Value
        expected_diagnostic = $case.Failure
        mutated_file_sha256 = $mutatedHashes[$case.File]
        mutated_files_sha256 = $mutatedHashes
    }
}
$results | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $EvidenceDirectory 'results.json')
$results | Format-Table -AutoSize
Write-Output "Retained control transcripts: $EvidenceDirectory"
exit 0
