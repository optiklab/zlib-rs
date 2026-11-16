# Verified twin: theorem and induction plan

## Status and intended theorem

Baseline: upstream commit `5dbef50`, initially clean worktree. This is a
same-source verification effort, not a second executable implementation.
The eventual whole-library theorem below is a **target, not an established
result**. See `..\verus\README.md` for the currently checked boundary.

For every finite byte sequence and supported configuration, the actual
compressor produces an RFC-conforming stream representing exactly those bytes.
For every supplied input, the actual decompressor either produces the specified
decoded prefix with correct consumption/accounting and continuation state, or
the specified typed error with its prescribed partial state. Valid complete
streams, given sufficient input/output and successful resource allocation,
must reach `StreamEnd` with precisely the RFC-decoded bytes. Malformed input
must not cause out-of-bounds access, undefined behavior, or unbounded
non-progress. Compression output need not equal another encoder's bytes.

The streaming theorem must quantify over chunk boundaries and flush operations,
relate each transition to an RFC bitstream interpreter, preserve unused output
regions and input identity, and establish progress under an explicit fair
input/output supply policy. It must not be just `Ok ==> correct`, which permits
an always-failing implementation. Allocation failure, output exhaustion,
truncation, dictionary negotiation and misuse require separate exact outcomes.
Termination is not a resource/latency guarantee.

The Rust API, zlib C API compatibility, and each dispatched hardware backend
need separate connected theorems. RFCs do not define C pointer validity, zlib
return codes, flush semantics, or allocation callbacks. These require a pinned
zlib API authority and independently reviewed compatibility decisions.

## Completion roadmap and current position

These are whole-project work packages, not equal-sized progress units.
Completed kernel subtasks and verification counts do not measure library coverage.

| Stage | Completion condition | Current status |
|---|---|---|
| 1. Scope/toolchain | Pinned authorities, target theorem and reproducible same-source verifier | Baseline established; interpretation review remains in stage8 |
| 2. Scalar Adler | Actual scalar caller, overflow/access safety and concatenation | Qualified within its documented scalar boundary |
| 3. CRC | Actual generators/combine/byte/word/braid producers refine CRC semantics | Partial; generator, concatenation and optimized joins open |
| 4. DEFLATE decoder | Actual input, trees, block/literal/match/history transitions and exact partial/error state | **Current: local native header mode/metadata join; dispatch persistence, reset/copy and pointer ownership open; complete decoder open** |
| 5. zlib/gzip wrappers | Headers, dictionaries, checksums/trailers and member/error policy | Open |
| 6. Encoder | Token validity, serialization and RFC roundtrip for actual input | Open |
| 7. Public/platform boundary | Streaming, allocation, Rust/C API, unsafe and every supported backend/dispatch join | Open |
| 8. Assurance | Independent normative/model review plus complete frozen-source/native qualification | Per-stage qualification ongoing; final assurance open |

### Stage4: current critical path

The constructor foundations are no longer the next implementation task.
The general constructor and native fixed-array adapters have checked kernel
proofs, and full kernel qualification is complete at835/628 onbf63.
The subsequent counted-resumption source qualifies fresh836/0 and all six
affected controls; the historical full result is not transferred.
The real decoder-state and physical reader joins remain outstanding.

| Action | Exact remaining obligation | Position |
|---|---|---|
| Qualify the constructor/header kernel source | Complete full inventory and exact-source/paired-proof audit; preserve genuine records | **Done atbf63835/628**:153 equivalents/475 intended rejections;96 live/acceptance/frozen/baseline identities,60288 case hashes and1260 unchanged independent proof hashes in45 pairs reconcile. Genuine full controls/source records retained hash-identically; genuinebf63 acceptance retained and identity rechecked. Failed3b06/d405 runs remain preserved/unqualified. This closes kernel qualification, not actual State/pointer establishment |
| Close reader-state preservation | Derive clean counted buffers across bounded fills, consumption and the actual header register path; then join `BitReader` pointer provenance, empty/nonempty slices, cursor bounds and input replacement to kernel contracts | Header exports qualify820/594; fill820/12; native fast-entry fix/budget821/9; count/alphabet/header exports qualify fa74821/16; priming/bound induction qualify a40b831/6; actual reset producer qualifies f0fa833/3 at5610 with96 identities/288 case hashes and genuine records retained; State/pointer joins open |
| Repair the actual sync null-input boundary | Buffered complete/partial markers with `next_in = null`, `avail_in = 0` must return the same result/accounting as nonnull empty input, without constructing an invalid empty slice | **Fixed:** zero-input slice construction uses `&[]`; four public marker/input combinations and original external probes return `Z_OK`/`Z_DATA_ERROR` with unchanged pointer/availability/totals. Native149, FFI21/1 ignored, release3, qualified lint and formatting pass. Six confirmed defects, all fixed; native pointer/State proof remains open |
| Prove the actual header phase invariant | `LenLens`: valid counts and wire prefix through `have`; `CodeLens`: valid counts, decoded prefix, root-cell bounds, `Codes::Codes` selector and a stable nineteen-length alphabet witness despite scratch-array overwrites | **Kernel transition qualified:** production State/BitReader use shared `header_phase::read_header_phase`; focused two-module4/0 and fresh3a68839/0 with112 production bindings pass. All12 affected controlse5ed pass:4 equivalents/8 intended rejections;98 identities/1176 case hashes reconcile and3 genuine records are retained hash-identically. Targeted split/retry/frame tests and public dynamic-header/sync suites pass. Thin native Mode/selector persistence, reset/copy and pointer ownership remain open |
| Join local native header mode and table selection | Reconstruct the phase from real metadata, apply every returned header step to actual count/selector/root/used fields and native Mode, and retain phase/storage/reader guarantees with exact suspend/error/completion routing | **Qualified:** actual State/BitReader call safe `header_state::read_header_state`; function focus1/0 and two-module11/0 pass. Fresh46ab passes847/0 with116 bindings. All10 selected controls5124 pass:3 equivalents/7 intended rejections;99 identities/990 case hashes reconcile and3 genuine records are retained hash-identically. Native21 targeted header tests, public4+3 tests and lint/formats pass; no full650 replay. Persisted dispatch exits, reset/copy and physical pointer ownership remain separate open joins |
| Join count-aware CodeLens resumption | Carry separate actual `nlen`/`ndist` through the reader; derive combined<=316, completion/EOB/constructor premises, partial storage frames and independent header semantics | **Kernel join qualified:** production State/BitReader call `dynamic_resume::resume_dynamic_header`; freshfcb1836/0 and all6 controls ataeb1 pass:2 equivalents/4 intended rejections.97 identities/582 case hashes reconcile; all3 genuine records retained hash-identically. Native150/FFI21 plus1 ignored/lint/formats pass. Full State establishment of the input phase premises remains open |
| Discharge real constructor-entry premises | From actual completion derive `have == nlen + ndist <= 316`, nonzero EOB, all combined lengths <=15, both native slice extents and fixed-array/workspace premises; preserve exact failure/storage frames | Actual completed-header adapters derive slice/value premises from count/decoded-prefix/EOB contracts without accepted-tree assumptions; qualify fd93835/6 at8326 with96 identities/576 case hashes and genuine records retained. State establishment of those contracts remains open |
| Extend the actual decoder transition proof | Join literal/length and distance decoding, invalid/reserved operations, overlapping match/history copies, block transitions, partial output/input and progress | Open; precedes wrapper/API composition |

The phase invariant must cover both local `mode` and persisted `self.mode`,
including early NeedCounts/NeedAlphabet/NeedInput returns, normal dispatch
exit, reset-to-Head and state-copy restoration. The writer audit covers
`State::new`, `State::dispatch`, `reset_keep` and `copy` in
`zlib-rs\src\inflate.rs`. The callback decoder in `inflate\infback.rs` writes
the same scratch fields through a different path and remains a separate
unproved API boundary; it must not inherit an ordinary-inflate theorem by
assumption.

The constructor critical-path assurance is now complete at its frozen756d
source: all586 controls pass135 equivalents and451 intended rejections, with
95 source identities/55670 final hashes/1215 unchanged proof hashes in45 pairs
audited and three genuine records retained hash-identically.
The qualified reader-cache proposal has been integrated surgically into the
canonical root and actual header loops, preserving newer matcher corrections.
Fresh canonical5d1e820/0 checks96 inputs and106 production/294 proof bindings.
Native146/FFI19 passed+1 ignored, qualified lint and both formatters pass.
All36 promotion controls pass atf62e:10 equivalent820/0,21 incorrect819/1,
2 incorrect817/3,2 incorrect813/7 and1 incorrect812/8.
All96 source identities/3456 final hashes/112 unchanged proof hashes in four
pairs reconcile, and three genuine records are retained hash-identically.
95 non-control-harness inputs match isolated719e; the only delta preserves
the newer canonical link diagnostics. Full594 ata8d1 now passes139 equivalents
and455 intended rejections. All96 identities/57024 case hashes/1260 unchanged
proof hashes in45 pairs reconcile; three genuine full records are retained
hash-identically.820/594 at5d1e is the latest completed whole-inventory snapshot.
These joins still do not establish the actual State/raw-pointer
premises or the nineteen-length alphabet witness.

The next ordinary-reader producer join now adds only a conditional clean-cache
postcondition and checked proof calls to actual `buffer::fill_from_slice`,
covering success and exhaustion with unchanged capacity preconditions.
Function-focused development passes2/0 in11.13s; fresh dde3820/0 and native
gates pass, and all twelve selected controls/audit pass:4 equivalent820/0,
7 incorrect819/1,1 incorrect818/2;96 identities/1152 final hashes reconcile.
Three genuine records are retained hash-identically. No full596 replay
is started after this small change: cached/focused development and affected
controls form the inner loop; full replay is reserved for settled milestones.

For input replacement, `cached_suffix(word, count, pending)` alone depends on
the old unread bytes. A clean counted buffer, expressed using an empty pending
suffix, can support arbitrary new pending input without that dependency.
The bounded exact-fill/consume and register-path induction is being developed
at `verus\target\reader-state-candidate-a5b7f13d8f9449af819471c85cadf345`.
This copy starts from95 hash-checked216b inputs; only its proof root and new
proof module initially differ. The six new lemmas now pass development820/0;
one missing adjacent-step instantiation was repaired explicitly. Proposed
binding and control changes are held inside that copy. Fresh unrestricted
candidate820/0 at `acceptance-reader-cache-5725f3d16f9d43d9b21c56204bdf7a50`
checks96 inputs and106 production/294 proof bindings. All four focused
controls pass at6883:2 equivalent820/0,1 incorrect817/3 and1 incorrect819/1.
All96 identities/384 final hashes reconcile; retained records are hash-identical.
All96 archived proposal inputs match their recorded hashes, and all34 production
files match native-checked216b. Candidate preflight is590/659 anchors/45 pairs/
96 inputs. This is not canonical acceptance or a completed State/reader join.
Promotion waits for a completed current full586 replay and audit. The isolated
extension now applies cache-path induction on every actual symbols-loop exit
and exports arbitrary replacement-input compatibility, then derives a clean
final cache in the actual header wrapper. No initial-cleanliness precondition
is added. Fresh unrestricted extension acceptance passes820/0 at719e;
all ten focused controls pass atc7e2:5 equivalent820/0,2 incorrect819/1,
2 incorrect817/3 and1 incorrect813/7. Its preflight is594/663 anchors/45 pairs/
96 inputs. All96 identities/960 case hashes/56 unchanged proof hashes in two
pairs reconcile; the96 live/accepted/archive inputs match and the95 canonical
inputs remain frozen at8a92. Genuine records and both harness copies are
retained hash-identically, with a separate qualified extension source ZIP.
A checked ghost count-cast equality repairs the prior equivalent
export trigger instantiation failure; models, domains, mutations and budgets
are unchanged. Earlier5725/6883 evidence remains preserved and does not
qualify the extension.
The paired-repeat resource stop released the canonical freeze. Repeat-parser
prover isolation is under qualification; the cache proposal must rebase onto
the qualified repair before promotion.

Current repeat-parser isolation candidate passes fresh unrestricted814/0 at
`acceptance-8a9279244a4840d299472ae0a9d9e673`:95 inputs,106 production/
288 proof bindings. Full586 at2ebd stopped on the paired equivalent repeat-width
edit's resource-only813/1 in `read_repeat_extra`, with no qualified aggregate.
That function now uses the existing function-local prover-isolation pattern.
Runtime, models, domains, original mutations and solver budgets are unchanged.
The original paired pilot passes atad1e: equivalent814/0, incorrect807/7.
All95 identities/190 final hashes/54 unchanged proof hashes in two pairs
reconcile, and retained records are hash-identical. All17 focused controls
pass atc0f8:4 equivalent814/0,12 incorrect813/1,1 incorrect807/7.
Their95 identities/1615 hashes/54 unchanged proof hashes in two pairs reconcile
against live8a92; retained control/source records are hash-identical.
Full58604fb preserves538 transcripts but stops at `wrong-subtable-link-width`:
genuine813/1 is an actual producer assertion failure, not the stale expected
postcondition diagnostic. Root-bits/prefix pilots also produce clean813/1
assertion failures at the same cutpoint; all three matchers now reflect those
actual diagnostics without relaxing guards or changing mutations.
All94 non-harness inputs still match8a92. The changed control harness is itself
the95th frozen input. Fresh unrestricted756d814/0 now checks95 inputs and
106 production/288 proof bindings; all28 focused link/repeat/active-key/frontier
controls pass at7ad9:6 equivalent814/0,19 incorrect813/1,2 incorrect807/7,
1 incorrect806/8. All95 identities/2660 case hashes/108 unchanged proof hashes
in four pairs reconcile against live756d, and three genuine records are retained
hash-identically. All94 non-harness inputs match native-checked8a92.
Full586 has restarted ate13c.
No new whole-inventory qualification is claimed.
Whole-inventory qualification remains637/434; State/reader joins remain open.

The preceding active-key candidate passes fresh unrestricted814/0 at
`acceptance-216b7ff2142f481d99e29d0facd25214`:95 inputs,106 production/
288 proof bindings. Full585 at6ad0 stopped on a resource-contaminated active-key
rejection. A checked ghost equality after the actual assignment isolates that
producer obligation; the original bad mutation now gives clean813/1 at the
equality. Only its diagnostic matcher changes from invariant to assertion
failure, based on the genuine41dd log; all rejection guards are unchanged.
Preflight is586 controls/655 anchors/45 pairs/95 inputs after adding an equivalent
active-key control. All17 focused controls pass at7795:6 equivalent814/0,
7 incorrect813/1,1 incorrect812/2,1 incorrect811/3 and2 incorrect809/5.
Their95 identities/1615 final hashes/54 unchanged proof hashes in two pairs
reconcile; retained records are hash-identical. All34 production inputs match
the native-checked source. Native146, qualified Clippy and both
formatting roots pass. Runtime, models, domains and budgets are unchanged.
Full586 at `controls-2ebd67d84245411ba688ba93ad64a32e` stopped on
`equivalent-paired-repeat-extra-width`: genuine813/1 is resource-only in
`read_repeat_extra`; no qualified aggregate or45-pair audit exists.
Function-local prover isolation is being qualified, without runtime, model,
domain, mutation or budget changes.
Whole-inventory qualification remains637/434; actual State/reader joins remain open.

The preceding histogram-witness candidate passes fresh unrestricted814/0 at
`acceptance-44b5435572f84ff6a4fca55867d2ba3c`:95 inputs,106 production/
288 proof bindings. Full585 at8fbf stopped on a computed sharp-histogram
path simplifying to false plus the intended enumeration-frontier postcondition
failure, without an application summary or qualified aggregate. The exact
sharp witnesses now use explicit frontier certificates and ordinary checked
slot induction rather than computed path assertions. The path model, original
controls, storage expectations, runtime, domains and budgets are unchanged.
All seven unchanged focused controls pass atd451:2 equivalent814/0,
2 incorrect813/1,1 incorrect812/2 and2 incorrect809/5. Their95 identities/
665 hashes reconcile; retained records are hash-identical. All34 production
inputs match native146/quality-checked811/0. Inventory preflight remains
585 controls/654 anchors/45 pairs/95 inputs.
Full585 on the frozen814/0 source at
`controls-6ad0ee52fd504f7f89864cc707f416a7` stopped on an intended active-key
invariant failure plus loop resource exhaustion at813/1, without a qualified
aggregate or full audit. A local checked active-key cutpoint is being qualified.
Whole-inventory qualification remains637/434. Actual State/reader joins remain open.

The preceding closing-arithmetic candidate passes fresh unrestricted812/0 at
`acceptance-81fc99cf8e0242e2bec2f4ca1300d39d`:95 inputs,106 production/
286 proof bindings. Full585 atc7c2 stopped on an equivalent rounding rewrite's
genuine809/2 independent-certificate/empty-forest failures; no aggregate exists.
A universal zero-frontier closing lemma explicitly joins the positive-divisor
quotient interval to those inductions. Both original rounding controls pass
their079d pilot: equivalent812/0 and incorrect809/3;95 identities/190 hashes
audited and retained records byte-identical.
All27 bound production inputs remain identical to tested811/0. Runtime,
contracts/domains/budgets are unchanged. Full585 stopped on that snapshot
at `controls-8fbff9f8460741fe8d8157c46a713a5f` as described above; no full
aggregate or45-pair audit was completed.

The preceding suspended-alphabet candidate passes fresh unrestricted811/0 at
`acceptance-ce1eac113eb541199b7a533447550134`:95 inputs,106 production/
285 proof bindings. Actual alphabet/dynamic producers also export the
NeedAlphabet wire prefix and untouched table/workspace. Predicate opacity,
a suspension-model cutpoint, explicit unfolding and derived19-cell loop
extents repair proof robustness without changing semantics, domains,
executable bodies or budgets. Native146 and quality gates pass.
All585 controls/654 anchors/45 pairs/95 inputs preflight. Four unchanged
wire-prefix controls pass atbb32:2 equivalent811/0,1 incorrect810/1 and
1 incorrect809/2;95 identities/380 final hashes audited, retained records
byte-identical. Its585-case whole-inventory replay at
`controls-c7c20c73a71a4fbc82e8a623a14147d7` stopped as described above.
Two preceding wire-prefix runs were resource-contaminated, not qualified
semantic rejections; unsupported hide probes were removed.

The preceding producer-contract candidate passes fresh unrestricted810/0 at
`acceptance-d6539db23ffd4196a05be5afb1280778`:95 inputs,106 production/
284 proof bindings. The actual alphabet/dynamic header producers now export
constructed root-table extent/cell-width bounds, decoded-prefix bounds and
exact Complete/MissingEob outcomes. Existing bodies, preconditions and budgets
are unchanged. Native146, qualified Clippy and both formatting roots pass.
All581 controls/650 anchors/45 pairs/95 inputs preflight; all14 focused export/
count/EOB/model controls pass at949a:5 equivalent/9 incorrect,95 identities/
1330 final hashes/54 unchanged proof hashes in2 pairs audited and retained
records byte-identical.

The preceding production fixed-array caller candidate passes fresh unrestricted
810/0 at `acceptance-b42a1ebddb5a4aa287ed1c95546917a2`:95 inputs,
106 production/284 proof bindings. The actual decoder calls checked
literal/distance adapters with1332/592 arrays,288-cell workspace and unchanged
10/9 roots. Their exact result/storage frames exclude capacity refusal and
establish accepted-input success. Conservative/root-only backing, generic
288/32 domains and incomplete one-bit outcomes remain available in the
underlying constructor.

All146 native tests,19 FFI tests (1 ignored), qualified Clippy and both
formatting roots pass. All577 controls/646 anchors/45 pairs/95 inputs
preflight. All29 caller/tight-buffer/critical-regression controls pass atab4a:
9 equivalent/20 intended rejections. Its95 identities/2755 case-input hashes/
81 unchanged proof hashes in3 pairs are audited and all retained records
are byte-identical. This qualifiesb42a, not later producer-contract edits.
The preceding807/0 analytic eighteen are qualified at4d2d:4 equivalent/
14 incorrect,94 identities/1692 final hashes/54 unchanged proof hashes in2
pairs audited. The802/0 group eighteen are independently qualified at1bdae.
The resource-contaminated ce1f ledger run was repaired through an equality
cutpoint, preserving its mutation, contracts and solver budgets. Fresh808/0
and its3202 three-control pilot pass, with94 identities/282 hashes/27 unchanged
proof hashes audited and all retained records byte-identical.
The older full458 run stopped on an inspected wrong-link assertion matcher;
no stopped aggregate is qualified. Latest whole-inventory qualification
remains637/434, not the current577-case inventory.

Next complete the current-source whole-inventory replay while keeping its
inputs frozen, then establish
the actual decoder-state producer invariant: successful count parsing gives
257..286 literals and1..30 distances; count fields and decoded-prefix bounds
must survive Table/LenLens/CodeLens suspension/resumption; completed decoding
must provide the two in-bounds slices with all lengths<=15. Use those facts
to discharge the real adapters' remaining premises, not merely assume them
in another wrapper. Then continue literal/match/history and exact partial/
error-state induction. Fixed-array dimension/root joins are now production
proofs; the complete state-machine/decoder/public theorem is still open.

The first missing exported producer facts are now checked on actual source:
`read_alphabet_header` exposes its internal `constructed_root_bounds` facts,
and `read_dynamic_header` propagates those and the decoded-prefix bound for
`Lengths` outcomes. The three-bit alphabet prefix for NeedAlphabet is also
exported on current811/0. Next connect all facts through actual state transitions
and complete the current-source whole control replay.
The raw-pointer BitReader wrappers remain an explicit unproved boundary;
do not infer State or wrapper correctness from these kernel contracts.

The preceding analytic-capacity candidate passes fresh unrestricted802/0 at
`acceptance-d016b0a45ef54811a417f705b129fec1`:94 inputs,104 production/
279 proof bindings. A universal rounding-slack tail certificate replaces the
proposed large finite tables. Minimum short-prefix populations3/6 and even
forest costs give child bounds308/80 for complete286/30-leaf histograms.
Root capacities1024/512 yield1332/592. Independent complete paths attain both
forest bounds. Root clamping, root-only and incomplete one-bit cases join the
histogram bound to the actual typed-result model without a numerical-budget
premise. A pre-allocation ownership lemma bounds the candidate extent without
assuming it fits. The generic288/32 domain is unchanged.

All556 controls/625 anchors/45 pairs/94 inputs preflight; both formatting roots
pass. Eighteen group controls replay on this exact source. Analytic run3a8d
stopped at the wrong-slack mutation's genuine797/5 `requires not satisfied`
diagnostic, rather than its expected postcondition matcher. Inspecting that
transcript justifies a matcher-only correction after the source freeze ends.
The later fourteen-case run c1c6 stopped on a second inspected matcher:
omitted terminal coverage rejects800/2 at assertions. A session-only probe
collects the twelve remaining diagnostics without qualifying mismatches or
producing a successful control aggregate. Correct both matchers after the
concurrent source audit, run fresh acceptance and replay all eighteen.
Earlier group runs c8c6/00416 have no aggregate: the former needed an inspected
postcondition matcher; the latter exposed an equivalent, not incorrect, order
rewrite because selected first groups already exclude duplicate keys. Preserve
both histories, reclassify that case and exercise a bad closed upper endpoint.

Next finish focused qualification, then apply the pre-allocation bound in the
actual loop, retaining the existing conservative backing alternative and small
root-only domains. Discharge real286/30 cardinalities, requested10/9 roots,
workspace and1332/592 supplied slices. The native contract still requires the
larger linked-tree buffer: numerical bounds and a typed-result exclusion do not
by themselves prove tight-buffer access safety or the complete decoder.
Separate805/0 actual-source development already establishes the conservative-
or-tight root, finite-offset and candidate-storage helper obligations.
They are not canonical or installed in the native loop yet.

The preceding closing-cost candidate passes fresh unrestricted744/0 at
`acceptance-e34ce8de2d6341d38cb82ec7c5d376f9`:90 inputs,104 production/
245 proof bindings. Closing charges count canonical root boundaries crossed at
each depth. First long groups start on root boundaries, and a same-root leaf
attains each chosen width. The sparse Bellman forest-bound framework, a
nonvacuous tiny certificate and exact308/80 witness costs are now canonical.
All520 controls/584 anchors/41 pairs/90 inputs preflight; both formatting roots
pass. All15 closing/Bellman controls pass atcafa:6 equivalent744/0,
2 incorrect743/1,5 incorrect742/2 and2 incorrect741/3. All90 own identities,
1350 final hashes and50 unchanged proof hashes in2 pairs reconcile; retained
genuine records are byte-identical.
An earlier equivalent-weight witness failure stoppedf7f8 and pilots6b1a/5aab.
Quotient-interval derivation repairs the same witness contracts and unchanged
mutation: the744/0 equivalent pilotaf7a passes with90 own identities/90 hashes
audited and genuine records byte-identical. No stopped aggregate is claimed.
Separate773/0 development now proves the first-source prefix sum is bounded by
forest cost through injective per-depth root-key counting, plus a two-page
cost4 witness. It also joins a supplied certificate budget to the actual typed
no-capacity-error result for complete trees; the large certificate remains a
premise. These joins are now integrated into the newer canonical773/0 candidate;
their focused qualification is running.
Next qualify them, check the large finite certificates, and connect
the actual tight-buffer callers. Numerical1332/592 sufficiency is not established.

The preceding histogram-cost candidate passes fresh unrestricted713/0 at
`acceptance-aef19eb498444085bfd73ddd6885c316`:88 inputs,104 production/
230 proof bindings. The histogram-only sum joins selected source lengths,
normalized root keys, first groups and charges to the canonical source-prefix
sum. Adjacent detection and independent stopping-width existence are proved.
Complete-tree frontier/path coverage, the actual alphabet leaf budget and the
minimum-depth bound establish finite search premises and non-raising root clamp.
Root-only child cost is zero. Independent fixtures reject wrong leaf totals.
All505 controls/567 anchors/39 pairs/88 inputs preflight; both formatting roots
pass. All21 histogram controls pass at
`controls-5e033820738d417693d3a4b16da5f70c`:8 equivalent713/0,
4 incorrect712/1,7 incorrect711/2 and2 incorrect710/3.
All88 own identities,1848 final hashes and48 unchanged independent proof hashes
in2 pairs reconcile; genuine records are retained byte-identically.
The full505-control replay remains open. The first run exposed a misclassified
chained-bound rewrite: its genuine707/2 rejection is retained as a separate
shifted-start negative control, while the equivalent rewrite preserves the lower
bound explicitly. The second stopped run's missing-first-group mutation rejects
707/2 at assertions; its exact matcher changed after inspected transcripts and
fresh acceptance. Neither stopped run has an aggregate.
The709/0 run at5ea0 then stopped because the wrong frontier caused a preprocessing
`compute` failure without an application summary. Do not count it as a semantic
rejection. The713/0 source integrates inverse path soundness/capacity and derives
the unchanged fixture contract through SMT instead. Explicit scalar slot joins
repair the first unfolding attempt. The unchanged weak-terminal pilot rejects
711/2 at4afa with88 identities/88 final hashes audited.
The actual typed-result no-refusal theorem is conditional on the histogram cost
fitting the alphabet policy. The numerical1332/592 bound is still a premise, not
proved; finite maximum-cost certificates and tight-buffer caller joins remain next.

Inverse path soundness and the remaining-leaf capacity bound are now canonical.
The earlier separate719/0 development proved that a sparse Bellman certificate bounds
closed-layer forest cost over every covered path, plus a two-leaf positive
certificate and rejection of an omitted reachable child. The large certificate
and first-source/closing-cost equality remain open. The framework is now integrated
into the newer744/0 candidate, alongside root-boundary and width-attainment joins.
Exact closed-layer costs308/80 are proved for the two maximizing histograms,
without claiming a universal bound.
The session-only finite-DP probe visits149156
states for286/root10 and1680 states for30/root9, reproducing child maxima308/80.
Actual native construction of its maximizing histograms uses1332/592 cells.
This computation is not formal maximum-bound evidence.
Next join first-source charges to depth-closure charges. For depth `d > root`,
available prefix slots `a`, leaf count `c` and `q = 2^(d-root)`, the proposed
closing charge is `q * (ceil(a/q) - ceil((a-c)/q))`; shallower depths cost zero.
The finite transition is `(d,a,n) -> (d+1,2*(a-c),n-c)`, guarded by the proved
leaf-frontier and capacity constraints. A checked Bellman/finite certificate
must establish the maximum over every covered path, not trust the probe's output
or only its two maximizing witnesses. Preserve the generic288-symbol constructor
domain separately from the actual286/30 caller budgets.

The preceding cost candidate passes fresh unrestricted686/0 at
`acceptance-8f65eb48fa334b0f83ef57d7760b340f`:86 inputs,104 production/
206 proof bindings. Nine new proof bindings establish a cost-only certificate,
strict fresh-candidate frontier, monotone canonical source-prefix cost, page
removal/skipping induction, physical-cell reindexing and the actual typed-refusal
bridge including the rejected candidate. The independent two-page witness checks
child cost4 and attempted extents6/8. All484 controls/544 anchors/37 pairs/86 inputs
preflight and both formatting roots pass. All12 focused controls pass at
`controls-2db593957e2147aba8aea018024431a6`:5 equivalent686/0,3 incorrect685/1,
2 incorrect684/2,1 incorrect683/3 and1 incorrect681/5. Its audit reconciles86 own
identities,1032 final hashes and46 unchanged proof hashes in two pairs.
The first run stopped on an exact
diagnostic mismatch: the weak-frontier case rejects683/3 at assertions, not a
postcondition, without resource/compiler errors. Only its matcher changed after
inspection, followed by fresh acceptance; no stopped aggregate was fabricated.
Numerical1332/592 and tight-buffer caller joins remain open.

The separate actual-source prototype progressed through698/0,704/0,706/0 and709/0,
then was integrated into the current canonical candidate above. The686/0 controls
do not qualify these later inputs.

The preceding actual constructor candidate passed fresh unrestricted676/0 at
`acceptance-5e4784bd037248f998cc892b565ed05e`,84 inputs/104 production/
197 proof bindings. The real loop composes canonical cursor/count/source,
paired pages/openings, processed table progress, actual emit/advance/allocate,
termination and independent all-word linked semantics. Empty/invalid and
accepted incomplete paths remain. Typed later capacity refusal retains the
last successful ledger and committed state, identifying the uninstalled
candidate. Original root-only/small-buffer and legacy contracts are preserved.

The new first-opening predicate says that an opening is the first long source
in the sorted workspace with that canonical wire-root key. The real allocation
branch derives it from processed-source assignment and the fresh empty slot:
any earlier source with that key would already need an assigned page.
A separate first-opening ledger is retained across emissions, source advances
and allocation, alongside the existing population/epoch ownership certificate.
Refusal exports firstness for both the committed ledger and rejected candidate.
An independent two-page witness accepts the true openings and rejects opening
the first page one source late, even though its wire-root key is unchanged.

Six new normalization proofs establish unique remaining populations, stopping
widths, first-source positions and complete first-source window certificates.
A valid retained window equals the independently derived population and width
at its original histogram/source position. Existence and uniqueness justify
the mathematical width choice only under the source-valid window premises.
The shared scalar canonical-prefix join now stabilizes both fixtures.
All19 focused normalization/firstness/refusal controls pass against5e47 at
`controls-4bbb6592f83b4bfd977494060162a12b`:8 equivalent676/0,6 incorrect675/1,
4 incorrect674/2 and1 incorrect673/3. The audit reconciles84 own identities,
1596 final hashes and44 unchanged proof hashes in two pairs; genuine records
are retained byte-identically. That snapshot's inventory was472 controls/
530 anchors/35 pairs/84 inputs. Both formatting roots pass and runtime bodies
are unchanged from existing native144/FFI/qualified-Clippy gates.
The first attempt stopped on the equivalent width-plus-zero choice rewrite.
A named candidate predicate and explicit existence/selection joins repair that
same equivalent case676/0 without domain/budget changes. Both wrong variants
reject675/1 at the explicit assertion; matchers were refreshed after transcript
inspection and fresh acceptance rerun. Stopped attempts have no fabricated aggregate.

All13 focused controls pass against precedinga0ab670/0: eight new firstness/ledger controls
and five result/refusal controls, including two paired production/model cases.
The first attempt stopped on a bad-ledger mutation's additional loop solver
exhaustion. Explicit ledger identity/firstness cutpoints repair the unchanged
case:669/1,84 own identities/84 final hashes audited, without changing budgets
or domains. Refreshed13 replay: `controls-a744e7dedf764939b32a927869e4c2fb`:
5 equivalent670/0,4 incorrect669/1 and4x668/2. All84 own identities,
1092 final hashes and44 unchanged proof hashes in two pairs reconcile;
genuine records are retained byte-identically.
That snapshot's inventory was466 controls/524 anchors/35 pairs/84 inputs.
Those controls do not qualify the later normalization source.

The preceding664/0 snapshotfc55 passed all five refusal controls at
`controls-2fe681e37e824b4593364ede7bfbb1aa`:2 equivalent,2 incorrect663/1 and
1 incorrect662/2, with84 own identities,420 final hashes and44 unchanged proof
hashes in two pairs audited. Its full458 replay/audit runs at
`controls-b42fea3c8db54b03b0a2cf8e6bbd6713`; all84 baseline identities match
fc55. It cannot qualify subsequent firstness edits. The superseded7244
full446 replay was stopped; its partial transcripts remain at
`controls-a5d8025e03fc402fae1e9d2d11faa6f4`, without a completed aggregate.

The larger linked backing premise is still `2^root+2^max`. Next prove a tight
aggregate chosen-width cost for these first-source canonical groups, including
the rejected adjacent candidate; then establish production1332/592 storage
sufficiency and actual caller premises. Firstness is a prerequisite, not that
aggregate bound. The physical ledger's uniform `max-root` bound is insufficient.
Individual group-width normalization and physical-to-canonical prefix-cost
reindexing (including the current rejected group) are proved in the latest
unrestricted candidate. Next bound that independent sum under the actual
caller alphabet-size/root/depth limits. Do not assume the generic288-symbol
constructor and actual dynamic literal caller have identical size premises.
The reindexing induction uses a cost-only page/opening certificate rather
than assuming removal of an arbitrary page preserves physical `pages::valid`
at a smaller `used`: other page bases need not move. Assigned processed sources,
unique first openings and openings strictly before the processed bound identify
the same groups on both sides of the sum. At refusal, derive that strict bound
from the candidate's fresh empty key: an installed opening at the candidate's
position would have the same source/key and contradict freshness. The active
successful page can instead open at the current, not-yet-emitted position;
do not silently apply the strict-prefix lemma at that different program point.
Whole-decoder, wrapper, encoder and public-boundary obligations remain open.

Earlier chain: source coverage612/417 -> frozen opening certificates617/426 ->
ownership637/434 -> table progress/completion659/0 -> actual general
constructor/result664/0 -> retained first-source provenance670/0 ->
canonical opening normalization676/0 -> physical/canonical cost reindexing686/0 ->
histogram-only cost/frontier coverage709/0 -> inverse path soundness/capacity713/0.
The latest fully qualified source is stillc4be637/434:
79 equivalent/355 incorrect,82 own identities/35588 final hashes/693 unchanged
proof hashes in33 pairs audited. Later sources differ and need separate
qualification. Preceding success-onlyc8c6 passed660/0 and all28 focused controls:
9 equivalent/19 incorrect,84 own identities/2352 final hashes/22 unchanged
proof hashes in one pair audited. Earlier7a0b passed21 focused controls:
7 equivalent/14 incorrect,84 own identities/1764 final hashes/22 unchanged proof
hashes in one pair audited. Neither qualifies subsequent source changes.

## Frozen references and decomposition

Reference editions are the May 1996 publications: RFC 1950 version 3.3,
RFC 1951 version 1.3, and RFC 1952 version 4.3. All mathematical byte lengths
are counts of eight-bit octets; wire endianness is stated separately from host
integer representation. Errata/legacy differences require explicit adjudication;
these models do not silently incorporate later errata.

Normative sources: <https://www.rfc-editor.org/rfc/rfc1950>,
<https://www.rfc-editor.org/rfc/rfc1951>, and
<https://www.rfc-editor.org/rfc/rfc1952>.

Several reference/compatibility decisions remain open. RFC 1951 3.2.7
states 1..32 distance-code lengths, but the inherited parser rejects counts
above 30. In [madler/zlib#1068](https://github.com/madler/zlib/issues/1068),
the upstream maintainer calls the RFC range an inadvertent omission and
endorses zlib's narrower limit. Preserve the current runtime behavior during
kernel work, but do not silently narrow the frozen RFC model or claim
whole-parser conformance before this discrepancy is explicitly adjudicated.
Likewise, the code-284 table range 227..257 versus its five extra bits needs
explicit interpretation before an extra-bit parser theorem. The current
metadata proofs do not adjudicate the extra value 31; this is not a confirmed
fork defect or a reason to silently change runtime behavior.

The RFC Editor's [RFC 1951 errata register](https://www.rfc-editor.org/errata/rfc1951)
was checked on 2026-11-10. Technical erratum
[7764](https://errata.rfc-editor.org/eid7764/) proposes changing section
3.2.5's length/distance extra-bit wording from most-significant-first to
least-significant-first. It is **Reported**, not verified. Resolve this
against section 3.1.1 before proving actual extra-field decoding; do not
silently assume a wire-order exception or adopt the proposed correction as
approved RFC text. Technical erratum
[8429](https://errata.rfc-editor.org/eid8429/), also **Reported**, clarifies
that the no-distance case means a single distance code *length* of zero,
not a zero-bit Huffman code. Retain that interpretation question when
extending the distance-constructor exception. These are normative review
items, not newly confirmed runtime defects, and do not change the frozen
May 1996 authority or the current three-bit header proofs.

| ID | Reference chunk | Production boundary | Required induction/join |
|---|---|---|---|
| A1 | RFC 1950 2.2, 8.2, 9: Adler sums | `adler32\generic.rs`, short kernels, combine | Per-byte sums -> delayed reduction -> packing -> chunk composition -> real callers |
| B1 | RFC 1951 3.1, 3.1.1: bit/byte order | `inflate\bitreader.rs`, `deflate\pending.rs` | Available bits, offsets, refill/drop, unchanged tails; Huffman order differs from other fields |
| H1 | RFC 1951 3.2.1-3.2.2: canonical codes | `inflate\inftrees.rs`, `deflate\trees_tbl.rs` | Length counts -> code assignment -> prefix decoding; oversubscription/incompleteness and table capacity |
| D1 | RFC 1951 3.2.3-3.2.4: block framing/stored data | `inflate.rs`, `deflate\algorithm\stored.rs` | BFINAL/BTYPE -> alignment -> LEN/NLEN -> exact payload and next cursor |
| D2 | RFC 1951 3.2.5-3.2.7: fixed/dynamic blocks | `inflate.rs`, fixed tables, `inftrees.rs` | Tree production -> symbol decoding -> extra bits -> literal/match transitions |
| W1 | RFC 1951 3.2.3, 3.2.5: history | `inflate\window.rs`, `inflate\writer.rs` | Distance/history validity -> overlapping copies -> window wrap -> exact decoded prefix |
| E1 | RFC 1951 3.2-3.3: encoder conformance | `deflate.rs`, `deflate\algorithm`, `sym_buf.rs`, `longest_match.rs` | Match discovery -> token validity -> emitted codes -> RFC decode equals original input |
| Z1 | RFC 1950 2.1-2.3: zlib wrapper | header/trailer branches in `inflate.rs`, `deflate.rs` | CM/CINFO/FCHECK/FDICT -> dictionary identity -> DEFLATE -> big-endian Adler trailer |
| G1 | RFC 1952 2.2-2.3.1.2: gzip | `crc32`, gzip branches | Polynomial CRC -> header flags/optional fields/FHCRC -> DEFLATE -> little-endian CRC and ISIZE; member boundary policy |
| S1 | zlib API authority, not an RFC | `stable.rs`, slice helpers, `libz-rs-sys` | Allocation/state initialization -> real parser/encoder -> complete Result/state/counters/frames -> FFI |
| V1 | Backend equivalence, not an RFC | Adler SIMD, CRC braid/intrinsics, deflate optimized paths | Each actual implementation refines the same canonical model; dispatch establishes feature and alignment premises |

This is an initial source map, not a cfg-aware complete function inventory.
No percentage of the production crate is claimed.

## Execution order and acceptance

The qualified frozen-opening-certificate tranche has fresh617/0 at
`acceptance-6f707047e914485e84905b55b7a8a7ac`:80 inputs,104 production/
151 proof bindings. The opening records symbol/position/length and the
then-remaining population, normalized-cursor provenance and canonical wire
key. Its chosen width covers every same-wire-root source. Successful native
allocation conditionally supplies that certificate without changing any
precondition or executable body. A complete six-source fixture pins
root2/key1/width1 and excludes another root; a native accepted-constructor
fixture pins both pages, exact leaves/links and untouched storage. These
are kernel witnesses, not public-stream or general-loop proofs.
Native/extracted144 and established package gates pass. All17 focused controls
pass at `controls-971369b5ea204dbf9846c3a15cf48949`;80 identities,1360 final
hashes and80 unchanged proof hashes in four paired cases reconcile, with
genuine records retained. Full426 passes at
`controls-50a1e2d8596246e5b5087dd56b6b18ed`:76 equivalent and350 incorrect
cases, with80 identities,34080 final hashes and660 unchanged independent
proof hashes in33 paired cases audited. Genuine records are retained.
The opening-certificate snapshot is6f70617/426; the ownership continuation
above is qualified at c4be637/434. The later actual general-loop candidate
instantiates post-advance context and retains per-root snapshots while counts
mutate. Production-tight storage and caller joins remain open as described above.

Accepted source-coverage forwarding has fresh612/0 at
`acceptance-75ec6adbc2144eebbd7716c9d1756d4d`:78 inputs and104 production/
148 proof bindings. The actual allocation and allocation/link callers now
forward same-root original-source width coverage on both acceptance and
rejection, without changing their executable bodies or preconditions.
Native/extracted143 and established package gates pass. All12 focused controls
pass at `controls-17730853e7ce427995b5c42c680b5658`;78 identities,936 final
hashes and76 unchanged proof hashes in four paired cases reconcile, and
genuine records are retained. All417 full controls pass at
`controls-e99f214638e24c5d9a53039370664785`:73 equivalent and344 incorrect.
All78 identities,32526 final hashes and627 unchanged proof hashes in33
paired cases reconcile; genuine full records are retained byte-for-byte.
Latest qualified snapshot is own75ec612/417. Next instantiate this caller
contract at the post-advance opening position/length/population, freeze that
certificate per root, then retain it independently of later count mutations.
Bind the actual link-prefix argument to that source's canonical wire root.
Do not substitute the preceding emitted symbol's position for the opening
position. The complete constructor/source/storage/capacity joins remain open.

Accepted page ownership/native allocation has fresh612/0 at
`acceptance-47c14f9f3d9a457e8f9c4c85ec0021be`:78 inputs and104 production/
148 proof bindings. Its independent root-slot ledger proves Code-cell sums,
nonoverlapping adjacent allocation, root-only preservation and used<=49152
and `u16::MAX`. The real successful allocator conditionally preserves this
ledger when the old slot is empty. Private ghost fixtures are not accepted
constructor-source witnesses. Native/extracted143 and established package
gates pass. Focused16 passes at `controls-db28cb90b6a846c3973277ff04943a9d`;
the audit reconciles78 identities,1248 final hashes and76 unchanged proof
hashes in four paired cases. Genuine focused records are retained.
All413 full controls pass at `controls-93cd462c467642f78cd232b29a30fbfeb`:
71 equivalent and342 incorrect. All78 identities,32214 final hashes and
627 unchanged proof hashes in33 paired cases reconcile; genuine records
are retained byte-for-byte. That own47c1612/413 snapshot is superseded above.
Next join the ledger to original-source progress and actual emitted cells,
derive empty slots from wire-root no-revisit, and retain the opening
source/population certificate while later counts change. Bind active-page
metadata to layout, preserve root links/prior pages/untouched storage, and
derive offset margins. Establish table containment and exact partial-prefix
capacity rejection separately;49152 does not establish1332/592 sufficiency.
Keep the existing root-only/small-buffer and CodeLengths results intact.

Accepted canonical subtable-width coverage has fresh600/0 at
`acceptance-08d41e327d654c23abae3da6b2815f49`:76 inputs,104 production/
139 proof bindings. Actual `subtable_width` now conditionally covers every
original-source symbol in the current root, without changing its algorithm,
numeric contract, preconditions or termination. The remaining-population
lookahead boundary is connected to canonical intervals. Checked root-quotient
order and reversal show no old wire-root revisit after a root change.
Independent complete fixtures pin another-root exclusion and wire order0,2,1,3.
Native/extracted143 and established package gates pass.
All403 controls/459 anchors/33 paired cases preflight. Preceding a4e4
focused20 aborted on preprocessing of a false computed root-scale fixture;
no aggregate is accepted. Scalar-input-only computation preserves all model
expectations/domains/resources. Fresh08d4 remains600/0 and the exact challenge
rejects cleanly594/6;76 own identities/final hashes reconcile.
All20 repaired focused controls pass at
`controls-f08765da7563486d8e40add8cbb151c6`;76 own identities,1520 final
hashes and72 unchanged proof hashes in four paired cases reconcile.
Genuine records were audited/copied after recovering a formatting-only wrapper
error, without rerunning the completed proofs. All403 full controls pass at
`controls-23fec8d052634ab6983871473a0d5bfa`:68 equivalent and335 incorrect.
All76 own identities,30628 final hashes and594 unchanged proof hashes in33
paired cases reconcile; genuine full records are retained byte-for-byte.
That own08d4600/403 snapshot is superseded by page ownership above.
Actual constructor page/progress/error joins are open.

Accepted canonical child-emission bridge has fresh577/0 at
`acceptance-0d4700ebb093412ea5d21d66cb1b43b9`:74 inputs,104 production/
128 proof bindings. Prefix decomposition, full-cache projection and child
replica equivalence connect the actual emitter's unchanged write matrix to
the original source histogram/canonical prefix. Its conditional contract
supplies the matching leaf and exact nonmatching selected-cell frame.
Independent child contexts/effects pin both prefixes, wrong-root rejection
and high cached bits. Native/extracted143 and established package gates pass.
All390 controls/439 anchors/31 paired cases preflight. All16 focused controls
pass at `controls-e27d3bf3ec3248d184250af6f2755dbd`;74 own identities,
1184 final hashes and34 unchanged proof hashes in two paired cases reconcile.
Genuine acceptance/focused records are retained byte-for-byte.
All390 full controls pass at
`controls-c7379bff5f0f45bdafb6b7a1a8d999f7`:65 equivalent and325 incorrect.
All74 own identities,28860 final hashes and527 unchanged proof hashes in31
paired cases reconcile; genuine full records are retained byte-for-byte.
That child-emission snapshot was own0d47577/390; width coverage above
supersedes it. General page ownership, processed-prefix completion,
allocation/capacity outcomes and public premises remain open.

Accepted linked-table semantics/native-index join has fresh567/0 at
`acceptance-dab6561f4d204b4d87477b38a38dc177`:73 inputs,104 production/
121 proof bindings. The independent relation describes root/child containment,
unique canonical source-prefix leaves and cumulative consumed bits for every
raw `u64` cache. A checked corollary preserves the original direct-root
relation. Independent empty/extent/full two-level fixtures establish the new
relation's non-vacuity. The actual native index kernel supplies conditional
selected-cell meaning without changing its executable body or preconditions.
Native/extracted143 and established package gates pass. All380 controls/
429 anchors/31 paired cases preflight. All14 focused controls pass at
`controls-7cae3758ecbd4cce860272419571ed30`;73 own identities,1022 final
hashes and64 unchanged proof hashes in four paired cases reconcile.
Genuine acceptance/focused records are retained byte-for-byte.
All380 full controls pass at
`controls-97506f93257b4b27948b10bc6cb1455f`;73 own identities,27740 final
hashes and496 unchanged proof hashes in31 paired cases reconcile.
Genuine full records are retained byte-for-byte.
That linked-table snapshot was owndab6567/380; the child-emission continuation
above supersedes it.
General constructor progress/allocation/capacity and public state premises
remain open; model and conditional-consumer proofs do not close them.

Accepted actual fixed-literal source/getter join has fresh550/0 at
`acceptance-6aa5638f48bb466e944b1366aac65f3d`:71 inputs and104 production/
111 proof bindings. Independent nine-bit/source-range selection now agrees
with generic canonical prefixes and uniqueness. Exact metadata and eleven
finite fixtures pin literal/EOB/length/reserved meanings.
The original512 cells occur once in32 real const producers of16 cells; the
actual flattening loop verifies every copied cell and termination. Checked
exec `LENFIX` and the getter connect the native source, and both normal
literal selections use that getter. This modular const-time layout is
necessary to qualify bad-cell counterexamples without increasing verifier
or compiler resources. Native/extracted143 and established package gates
pass on the preceding executable source; native143 and format/diff checks
pass again for this ghost-only refinement. All370 controls/419 anchors/31
paired cases preflight. On preceding70ac all18 focused controls pass at
`controls-b9957992a6754df0b487db911511d5b1`;71 own identities,
1278 final hashes and30 unchanged proof hashes in two paired cases reconcile.
Its full370 replay at `controls-23e2e0a52a204f69a83a25f652e961c3` aborted on
a resource-contaminated wrong-first-width rejection in block448. Current6aa5
checks sixteen independent cells per actual producer before sequence
extensionality, preserving every obligation and original budget.
The exact failed width challenge now rejects cleanly514/36.
All29 expanded focused controls pass at
`controls-e0a7cefaa3444ba0941078f89f5fd10f`;71 own identities,2059 final
hashes and30 unchanged proof hashes in two paired cases reconcile.
Current and preceding primary records are retained separately, byte-for-byte.
All370 full controls pass at
`controls-78acc1bb9a06437f96465e4265536c8c`;71 own identities,26270 final
hashes and465 unchanged proof hashes in31 paired cases reconcile.
Genuine full result/source records are retained byte-for-byte.
That continuation's qualified snapshot is own6aa5550/370, superseded above.

The general-constructor join uses the accepted linked-table relation:
canonical root prefixes select either a direct leaf or a contained child
region, whose leaf consumes its own bits plus the root width. Preserve the
existing root-only/CodeLengths theorem as a checked corollary rather than
weakening its root-equals-maximum predicate. The real loop must maintain
processed-prefix semantics, disjoint allocation/link frames and exact
capacity-rejection partial frames; the present root-only invariant makes
allocation unreachable. Fixed-limit sufficiency and public supplied-slice
premises remain separate open obligations.
The intended induction records ghost page descriptors only when the real
allocation/link succeeds: distinct root prefixes own adjacent child regions,
while the active region may still contain unwritten cells. Processed source
prefixes determine leaf writes; link slots and those writes determine the
exact storage frame. Capacity rejection must retain the processed-prefix
state and witness the refused allocation, not allow an arbitrary failure.
Preserve the inherited small root-only buffers; sufficient-storage premises
for newly admitted linked cases must not narrow that existing domain.
None of these constructor progress/budget obligations is discharged by the
accepted lookup relation.
Before lifting the emitter step through that loop, connect the actual
lookahead's chosen width to all remaining canonical symbols in the same root
prefix. Remaining-histogram counts and the normalized canonical cursor must
show that no later same-root symbol exceeds the allocated child width, and
that moving to a different root cannot revisit a completed region.
The coverage/no-revisit lemmas and actual width contract are implemented in
the accepted continuation above; their general-constructor induction and page-ownership
join remain open. A local numeric width bound alone does not establish them.
Accepted incomplete trees have maximum width1,
so preserve their existing direct-root path rather than inventing child holes.

The next constructor obligations below are planned, not established:

- Use this implementation's actual dynamic caller profile, not classic zlib
  defaults: `inflate.rs:1686-1705` requests literal root10 and distance root9.
  The backing arrays at `inflate.rs:451-453` have1332 and592 cells respectively
  (`table_constants.rs:5-7`). Proving these fixed limits sufficient for valid
  source trees remains separate from proving correct capacity rejection.
- A successful page descriptor must retain its root key, adjacent physical
  extent, opening source position/length and opening remaining-population
  certificate. The active width is chosen at allocation, not recomputed from
  the later changing histogram. Lift same-root width coverage from that
  opening certificate; use canonical-order/wire-key no-revisit to preserve
  earlier pages, without assuming wire keys increase numerically.
- Derive storage and `u16` offset bounds from distinct root ownership and
  native width bounds. For linked cases, at most `2^root` pages of size at most
  `2^(max-root)` give a candidate total bound `2^root + 2^max <= 49152`.
  This cardinality/extent argument still needs proof. Keep the direct-root
  storage domain unchanged; do not impose that larger bound on old small
  buffers. For uncapped Codes allocations, sufficient storage needs its own
  explicit input-domain argument.
- Reuse the preparation contract's exact empty/invalid/root-refusal frames;
  not every early `Finished` outcome leaves the table unchanged. In the loop,
  a failed `advance_and_link` advances local layout but preserves the current
  table. Its returned error must retain all already-emitted source prefixes
  and sorted workspace, identify the refused adjacent region and exact
  alphabet policy, and must not claim rollback to the original table.
  Do not append a successful-page descriptor for that rejected region.

Accepted actual fixed-distance source/getter join has fresh504/0 at
`acceptance-a313194cbb334921b94e940781358a96`:71 inputs and70 production/
107 proof bindings. The original32 literal cells are produced by a checked
native const function, retained in exec `DISTFIX`, and returned by a checked
getter used by both normal distance selections. The checked field constructor,
independent reversal/prefix/table bridge and five independent cells supply
the source-to-semantics path. No assumption or proof-only executable substitute
is used. Native/extracted143 and all established package gates pass.
All352 controls/393 anchors/29 paired cases preflight. Corrected focused14
passes, with71 own identities/994 final hashes/30 unchanged proof hashes
in two paired cases audited. Full352 passes at
`controls-98a52c1b12c54b62941781310ccec176`, with24992 final own-source hashes
and435 unchanged proof hashes in29 paired cases audited. That continuation's
fully qualified source is owna313504/352; the literal continuation above
supersedes it. Next join actual public literal/distance production and the
general subtable loop. Neither native fixed-table comparison replaces these
source proofs.

The literal source join reverses the nine low root bits to a canonical
MSB-first integer `r`. Independent source ranges select symbol
`256 + r/4` for `r < 96`, `r/2 - 48` for `96 <= r < 384`,
`r/2 + 88` for `384 <= r < 400`, and `r - 256` thereafter.
The respective leaf widths are7/8/8/9. Establish those source assignments
against the generic canonical-prefix model and existing checked uniqueness,
not against the executing builder. Pin native EOB opcode96 and reserved
opcode64 separately from broader generic operation classification.
Then prove every original literal cell through the actual const producer/
getter, retaining the original512 data entries and twofold/fourfold root
replication. This design is now implemented and fully qualified in the bridge
above. Continue actual dynamic subtable
construction/containment and literal-distance caller semantics; fixed-table
validity alone does not establish available input, exact code/extra-bit
consumption, EOB state transitions or match/history safety.

The accepted fixed-tree foundation has fresh492/0 at
`acceptance-669fe641ed974aa7a59aad53207eb38f`: independent RFC source ranges,
prefix-population counts, canonical code formulas, finite boundary fixtures
and complete accepted distributions. All11 focused controls pass with70 own
identities and770 final hashes audited. Full338 passes at
`controls-8ac4257c192d42a49eae47d5810cac97`;23660 final own-source hashes
and405 unchanged proof hashes in27 paired cases reconcile. Latest fully
qualified source is own669f at492/338.
The foundation alone adds no executing code and does not connect the actual
fixed constants/getters. The later distance candidate is described above.

The accepted native root-lookup join has fresh481/0 at
`acceptance-c3dd6353c65e43c7a574081267650d8e`: root1..15, arbitrary raw cached
bits, exact selected cell and conditional all-alphabet canonical meaning.
The Codes wrapper and normal literal/distance state-machine root probes use
the same inlined kernel; the latter's table/state/bounds premises and complete
decoder proof are not discharged. Native/package gates and focused19 pass,
with1292 final own-source hashes and28 unchanged proof hashes in two paired
cases audited. Full327 qualification passes at
`controls-23a02659af5f4721b992d3f4d244a795`;22236 final own-source hashes
and378 unchanged proof hashes in27 paired cases reconcile. Latest fully
qualified lookup source is preceding c3dd at481/327. No availability or byte-identical
speculative-completion claim is made. Accepted shapes and semantic invalid
classification must be included explicitly in any future stability theorem.

Accepted all-alphabet root-only continuation has fresh478/0 acceptance at
`acceptance-ee258ca466014caaa47ac668539e8894`, native/extracted143 and the
established package gates. Focused16, seven inherited loop controls and
full322 pass with own-source audits; the full audit reconciles21896 final
hashes and378 unchanged proof hashes in27 paired cases.
Own ee25 at478/322 is the preceding qualified snapshot. `specs\root_table.rs` expresses
canonical symbol/leaf selection, with no executable replay. The actual loop
now maintains processed-prefix semantic progress, completes full trees or
the accepted one-bit incomplete hole, and recovers the original exact
CodeLengths theorem as a corollary. The requested root must be at least the
maximum supplied length; actual table/workspace containment is an explicit
premise. Complete subtable construction, fixed-capacity sufficiency, static
fixed-table joins and public literal/distance parser/decoder joins remain
separate next dependencies. No executing algorithm change is made.

1. Establish ordinary Cargo behavior and a pinned isolated Verus package.
   Keep the runtime dependency graph and declared MSRV unchanged.
2. A1: prove actual short checksum kernels and combine arithmetic; prove
   requirement-facing byte-step, initialization and concatenation properties.
   Use independently fixed outputs, including overflow/reduction frontiers.
3. Join the full delayed/unrolled scalar implementation to A1, including
   NMAX overflow bounds and empty/noncanonical seed behavior. Then discharge
   every real scalar/SIMD caller's kernel preconditions; leaves do not prove
   those callers.
4. B1 and H1 precede D1/D2; W1 precedes the complete D2 decoder theorem.
   Use one state refinement invariant, not a bank of assumed parsed results.
5. Connect D1/D2/W1 to Z1; independently establish G1's CRC and gzip framing.
   Model truncation, invalid syntax, trailer mismatch, dictionary and output
   exhaustion distinctly. Preserve first-error and partial-write behavior.
6. E1 proves accepted token production, then serialization and input roundtrip;
   exact compression bit patterns are not required by the RFC.
7. S1 composes real public entry points with allocation and all state
   transitions. V1 and target-specific lifetime/unsafe obligations close
   dispatch/FFI gaps rather than hiding them behind trusted stubs.
8. Each accepted stage requires a fresh unrestricted `--no-cheating` run,
   per-function source bindings, explicit lifetime mode, native regression
   tests, and controlled intended-failure mutations. Retain the exact source,
   tool and output identities. Do not equate vstd counts with project coverage.
   The header-order requirement is also pinned literally, separately from
   the modeled permutation/inverse. Paired controls change both production
   and model while keeping that RFC obligation fixed; equivalent paired
   edits must still verify. Preserve every final mutated-file hash and reject
   compiler, unsupported-operation or resource failures as inconclusive.

## Independent assurance and exclusions

The initial implementation completed A1's entire scalar caller, not only its
leaves: all scalar producer/kernel joins, delayed arithmetic bounds and
concatenation are checked. Public dispatch and SIMD joins remain open.
All B1/H1/D1/D2/W1/E1/Z1/G1/S1/V1 whole-component obligations remain open.
The next dependency-ready work is B1, H1, CRC's scalar semantics, and Adler
dispatch/backend correspondence; none may be inferred from A1's result.

The CRC continuation targets RFC 1952's complemented bit/byte recurrence for
all `u32` seeds and byte slices, then the actual byte/word/braid producers.
The reflected polynomial-product contract is total over all two `u32`
operands, including zero; the public combine-operator function must establish
this contract without assuming that callers used a particular constructor.
Generated table entries must be proved equal to repeated polynomial shifts
before using them as an oracle for a byte-loop proof. Generator/exponentiation
and braid/dispatch joins remain distinct from that arithmetic leaf.

The current CRC tranche verifies the total multiplication/public-op join,
the generic table builder, and the actual static-table/getter/byte-consumer
chain. The initially open const-initializer join is now closed: placing
`cfg_eval` before the const-function annotations expands nested cfg attributes
before Verus erases the const-evaluated body. No table oracle is assumed.
See the acceptance records and confirmed zero-operator hang in
`verification-results.md`.

The next CRC generator theorem must return
`shift_bits(ONE, 8 * length)` for every `u64` length, not just values
constructed by a test. Keep that linear-exponent recurrence independent of
the production binary loop and its cached powers. The induction path is:

1. Establish shift composition, product linearity in the second operand, and
   the reduction identity `product(POLYNOMIAL, value) == shift_bits(value, 32)`.
   A checked finite-basis proof can lift the reduction identity to every
   `u32`; do not assume polynomial irreducibility or a multiplication law.
2. Derive multiplication by `shift_bits(ONE, exponent)` as an exact shift of
   any operand. Check the actual 32-entry `X2N_TABLE` against squared
   monomials, including its wrap from the last entry back to the first.
   Prove the period for power indices rather than treating the cache as an
   oracle or defining the canonical result by that same cache.
3. Join actual `x2nmodp` using residual-exponent conservation and decreasing
   remaining length. Its incrementing `u32` power index needs an explicit
   entry bound and a proved at-most-64-iteration budget. Current direct
   callers use initial indices three (`crc32_combine_gen`) or six (the ARM
   and LoongArch interleaved backends); those caller premises must be
   discharged, not generalized to arbitrary overflowing private indices.
4. Join actual `crc32_combine_gen` and `crc32_combine`, then prove raw-update
   concatenation and affine seed/XOR transport. This connects the generated
   operator to independently specified checksum concatenation: the first
   block may start from any raw seed, while the second block's independently
   computed checksum starts from zero. Include empty operands and a second
   byte length representable by `u64`; do not assume arbitrary independently
   seeded second checksums satisfy the same combine formula. ISA/backend/
   dispatch proofs remain separate even after a correct shared generator.

This is a source-grounded pending induction plan, not an established theorem.
The relevant direct callers are `crc32\combine.rs`, `crc32\acle.rs` and
`crc32\loongarch.rs`; the actual cached powers live in `combine.rs`.

The bit-reader continuation starts with the actual synchronization drain:
discard the partial octet in least-significant-first order, preserve all
remaining whole octets, and drain no more than four bytes under the existing
32-bit sync-entry bound. The public recovery regression exposed a left/right
shift defect. This leaf is an S1/B1 prerequisite, not a proof of pointer
refill, parser state, Huffman decoding, or the bound at every real caller.

The next B1 theorem is an exact refinement of the actual buffered-word
operations: peeking preserves precisely the requested low bits and zeros
all others; consuming removes exactly a prefix of the available bit sequence;
byte alignment removes exactly `count % 8` bits. Count/shift bounds are
explicit premises. Peeking deliberately does not require the requested bits
to be available: the lazy Huffman loop checks entry availability separately.
Do not assume the word is zero above the available count. Fast refill caches
an additional, not-yet-accounted input byte in that region. Pointer/refill/
append correspondence and streaming state remain separate obligations.

The register-append/refill theorem now preserves exact word/count
and byte-advance accounting for every supplied byte/read word under capacity
bounds. Its bit-sequence concatenation clause is conditional on cached upper
one-bits agreeing with the appended input. Real pointer/refill callers must
establish that compatibility, not assume all upper bits are zero.
Bulk refill's XOR-derived byte increment must equal `(63-count)/8`, with
final count exactly `old_count + 8*increment` in 56..63. This does not prove
the unsafe eight-byte read, input identity or pointer bounds.

The next state join uses a ghost pending-input bit sequence. Every upper set
cache bit must agree with that input; upper zeros need not have been read.
Actual consume/alignment preserve this invariant, and actual byte/full-word
append derive OR-compatibility from the incoming input prefix and preserve the
remaining pending suffix. These joins are checked under explicit input-identity
premises, not yet established by the actual pointer reader. The actual
unused-byte register update also proves exact whole-byte count, retained partial
octet and cache clearing.

The actual `need_bits` byte loop is now a same-source safe slice-input kernel.
An independent octet-to-bit interpretation composes with actual append to
prove exact success/exhaustion, minimum byte consumption, complete partial
register state, cached unread suffix and termination. Capacity and cache/input
identity are explicit entry premises. The next missing reader boundaries are
the native unsafe slice/pointer adapter, `pull_byte`/bulk-read identity,
pointer rewind, slice-update transitions and parser establishment of these
premises, not the extracted input loop itself.

The actual bulk-refill producer also now interprets eight actual input octets
in low-first order and composes that verified word with register refill.
Its exact count/advance/raw-word/cache/whole-stream contract does not rely on
a supplied read word or an assumed endian-conversion primitive. Native and
proof modes share a checked octet packer; the native unsafe slice/pointer
adapter and performance qualification remain separate obligations.

The actual code-length header field now composes that input loop with
numeric three-bit interpretation, the RFC permutation write and consumption.
Success and exhaustion both have exact byte/header progress, storage/raw-word
frames and unread-stream conservation. The real `Mode::LenLens` uses this
same helper through a native pointer adapter.

The actual `Mode::Table` count predecessor now uses a shared `read_counts`
body. Its theorem quantifies over every count 0..64 and coherent pending
input, and proves exact extraction of successive 5/5/4-bit raw fields,
all-or-none tuple readiness, minimal byte consumption, partial registers,
cache and unread-stream conservation. A recursive low-first binary numeral
defines the mathematical meaning independently of machine masks; induction
connects it to the real peeks. Fixed bounds and a fourteen-Boolean fixture
challenge paired code/model errors. Raw HLIT values 287/288 and HDIST 31/32
are intentionally representable; the existing parser guard is unchanged.
This does not settle the HDIST compatibility question or prove the native
pointer adapter and all parser-entry premises.

The actual complete header-input loop now preloads a bounded target of at
most 57 bits, then composes actual field reads over its preserved pending
input suffix. Whole-octet rounding is proved to fit in 64 bits for every
initial count 0..64. The loop maintains every wire field, full storage frames,
exact minimal byte consumption, partial exhaustion, raw word/count,
cache/input coherence, the complete unread stream and termination. This
changes internal pull timing but not returned state: three-bit header values
have no intervening syntax-error check. No runtime clone is used.
The next actual `read_code_length_table` producer now connects this exact
prefix to padding/constructor invocation. Its independent `length_header`
view maps the source bits directly into wire positions and omitted zeros.
The complete contract covers exact input readiness, minimum advancement,
partial header state and untouched table/workspace on exhaustion, every
constructed outcome, raw registers/cache/unread stream and all storage tails.
The real `Mode::LenLens` calls this combined body, not a proof-only producer.
Pointer-adapter and parser-entry premises remain open, as do the retained
header snapshot and actual `CodeLens` decode/repeat/refill transitions. These
helpers do not prove the full parser or chunked public-API transitions.

The next `CodeLens` boundary is the actual lazy lookup/pull predecessor.
For a root of 1..7 bits, derive every active entry's positive bit count and
root bound from the constructor result, including its empty-tree invalid
entries. Prove that lookup returns immediately without prefetch when its
entry is already available, otherwise reads exactly one byte when supplied
or reports exhaustion without changing registers. A byte suffices because
the entire root fits in seven bits. The ready entry must equal actual lookup,
carry the canonical meaning when the table represents a complete tree, and
require no more bits than are buffered. Preserve the whole unread stream and
cache; consume no code bits yet. Then connect direct/repeat consumption and
error precedence using a retained ghost code-length alphabet. These are
separate joins; the lookup theorem alone is not full `CodeLens` verification.

The repeat-extra input stage now has a shared actual parser body, reused
by all three native repeat branches. Its independent RFC model defines
two/three/seven-bit low-first values, and a separate pinned baseline policy
defines partial commits and first-error precedence. Establish complete
`NeedInput`, `MissingPrevious` and `Value` outcomes: code/extra bits remain
pending on truncation; the repeat-16 error consumes only code bits, after
checking full availability; successful parsing consumes both. Preserve
minimal byte advance, exact raw/cache/whole-stream state and both empty and
populated caches for every count. Qualification must challenge paired
production/model widths against fixed bounds and field/commit fixtures.
Actual `read_repeat_lengths` now composes this actual producer with existing
repeat expansion. Its independent transition and fixed fixtures distinguish
input suspension from missing-previous/overrun errors, pin exact fit versus
one-short capacity, and retain every error's array/progress and bit frames.
The real native repeat branches use this join. Its 377/0 frozen acceptance
and native gates pass; all twelve focused controls pass, including the paired
production/model error caught only by the unchanged independent fixture.
The original 187-control replay aborted on resource-contaminated incorrect
byte-reporting rejection and is not accepted. The actual field reader now
establishes its returned tuple's exact byte count before its raw/stream
witnesses; its expansion caller establishes the matching scalar boundary.
Next include actual opcode lookup and direct writes, then retain the header
alphabet while scratch lengths are replaced.
This staged result must not be presented as complete opcode provenance,
whole-parser error precedence or the streaming theorem.

For the next lookup-to-symbol join, interpret the actual source prefix
against the canonical code-length alphabet, not an assumed decoded opcode.
The actual reader now transfers root-entry meaning from its raw register
to that source through three numeric/entry/readiness bridges, proving
source-code meaning on success and absence of a full code on suspension.
An independent literal RFC 3.2.2 eight-symbol assignment/wire fixture and
native actual-constructor/reader oracle qualify the interpretation.
Fresh 382/0 acceptance and native gates pass; all fourteen focused controls
pass, with both wrong source models caught by unchanged source/RFC obligations.
The original 193-control replay aborted on an omitted-padding mutation:
intended precondition failures were contaminated by constructor resource
exhaustion. Profiling and an unchanged-limit, function-local isolated
constructor prover removed that contamination. Final fresh 382/0 acceptance
and native gates pass, and all five affected equivalence/accounting/padding
controls reject or verify as intended. A new complete 193-control replay is
tied to that snapshot subsequently stopped at the wrong parsed-repeat-value
mutation: intended value rejection was contaminated by resource exhaustion.
An explicit proof of the actual peeked value and bound now precedes consumption
and raw/stream witnesses. The first focused replay then exposed independent
false-bound rejection exhausting the reader's proof search. Reader isolation
and scoped bound assertion alone did not resolve it and are not accepted
repairs. Profiling identifies sequence/numeral/raw-state quantifier expansion.
Selective opacity of the unchanged repeat-value definition, revealed only
at the actual numeric cut and independent fixtures, resolves the targeted
failure; remove the ineffective reader-isolation attribute.
The models and contracts remain unchanged. The final affected sixteen controls
and complete 193-control replay now pass and are reconciled with their own
fresh 382/0 frozen acceptance and all current source identities. The failed
intermediate runs remain unaccepted. See
`verification-results.md` for exact identities and acceptance status.
Retain the alphabet before output overwrites `lens`; the
constructor must establish the table relationship. Do not silently exclude
the constructor's successful empty-tree case: its two invalid entries are
not a canonical nonempty alphabet. Preserve the baseline transition there
and show why completed header decoding cannot pass the end-of-block-code
check. Join direct writes and repeat parsing/expansion, frame the table and
scratch tails, then induct on remaining output lengths for the actual loop.

The symbol-step contract must also compose exact raw loads across lookup
and repeat-field input, not just conserve the abstract bitstream. Derive
minimal combined byte advancement from no-prefetch lookup and the remaining
field width; distinguish no complete code, truncated extra field, missing
previous, overrun and successful direct/repeated writes. Frame every error's
lengths/progress and preserve the original source through both fills.
Establish the raw-load bridge independently first: filling `A` bits at count
`c`, then `B` bits at count `c + A.len()`, equals one fill of `A + B`, with
explicit capacity bounds and all 64 raw bits retained. Include empty fills
and count 64 without introducing a shift by 64. Lookup consumes no code bits,
so both loads precede the single modeled code/extra-bit shift. Separately
prove that a successful zero/one-byte lookup advance followed by a minimal
remaining fill advances exactly the minimum needed for the complete field,
capped by available input. Neither identity may assume zero upper cache bits.
Only after these bridges and the source-prefix/repeat prerequisites are
accepted should the actual symbol-step consume their contracts.
The three model-level bridges are now proved at the 385/0 candidate:
`filled_word_composes`, `needed_bytes_after_prefix` and
`capped_fill_after_prefix`. Their focused/full qualification is tracked
separately. The actual lookup must still establish that its prefix advance
does not exceed the complete field's minimum; metadata alone does not prove
canonical prefix stability for an arbitrary table. These foundation lemmas
do not discharge the actual symbol-step or persistent-alphabet caller.
The next missing producer contract is exact minimal input for the selected
code, not just for the initial table index. Under the canonical table relation,
prove that a post-refill entry fitting the old count would force the old
lookup to have returned the same ready entry, contradicting refill. Derive
the common low-word projection from the actual fill witness, including count
zero, rather than assuming it. Retain the successful empty-tree case: its
constant one-bit invalid entries supply the corresponding accounting directly.
That actual producer contract and projection bridge are accepted at the
386/200 snapshot, including unconditional root-1 accounting, without changing
entry premises or runtime behavior. Qualification remains tied to that
snapshot's own sources. The next actual symbol-step must still compose both
fills, derive opcode/value provenance, preserve alphabet and table/array frames,
and distinguish all suspension/error/partial-consumption outcomes.
An independent bounded Python C-zlib 1.3.1 fixture pins the empty-alphabet
continuation policy: raw DEFLATE `05 00 00 00` followed by 31 zero octets
suspends without output; an empty retry also suspends. The next zero octet
rejects with `invalid code -- missing end-of-block`. All three split schedules
`(35)`, `(4, 31)` and `(4, 8, 23)` agree. The 29-bit header leaves 251 one-bit
zero lengths at byte 35; byte 36 supplies the remaining seven of 258 lengths.
This baseline error-timing evidence now also has an ordinary Rust public FFI
regression, including exact counters, cached-bit counts, null/empty retries
and untouched output. It is not a valid canonical-tree interpretation or a
proved streaming caller.
At the public continuation boundary, `BitReader::update_slice` retains the
raw word rather than masking cached bits. Do not silently require callers
to preserve unconsumed input contents: prove the appropriate boundary
invariant, including the fast path's common `return_unused_bytes` exit and
the slow paths' preservation, before re-establishing the incoming cache
premise for replacement slices. That native caller proof remains open.

The next lookup-to-symbol candidate now verifies at 400/0 and is native-used.
The actual `read_length_symbol` calls the actual lookup, then the actual
`read_selected_length_symbol` dispatcher; its full source-prefix transition
joins direct writes or repeat parsing/expansion, both raw loads and exact
minimum accounting. A successful step strictly increases `have`.
The original monolithic proof exhausted its budget; actual-function and
semantic-bridge decomposition resolves it without raising limits.
Fresh acceptance/native gates and fourteen focused controls pass.
The first full replay stopped on resource exhaustion in an equivalent paired
repeat-width control. Scoping its numeric-field/sequence proof inside the
existing scalar-value assertion repairs that failure without changing the
executable sequence, contracts or limits. The next full replay reached the
last new symbol control, whose intended rejection was contaminated by resource
exhaustion in the unchanged header-wire loop. Supported prover isolation for
the selected-symbol dispatcher removes that contamination in the focused
reproduction, at unchanged limits. All ten new symbol controls and four
repeat-width controls now pass together on the fresh 400/0 candidate.
Its complete 210-control replay now passes and is fully reconciled against
its own frozen `c355` source: 32 equivalent 400/0, 157 incorrect 399/1,
14 incorrect 398/2, five incorrect 397/3 and two incorrect 396/4.
All 51 baseline/current/frozen identities, 10,710 final case-input identities
and unchanged independent proof inputs in all nine paired controls match.
This actual symbol-step prerequisite is accepted at 400/210. The actual bounded
`CodeLens` loop is now also accepted, as described below, with induction on
`total - have`, source/drop/input suffix composition and stopped-error frames,
retaining one original alphabet through scratch-array overwrites. No trace
assumes supplied parsed symbols or replaces the original alphabet per iteration.
The actual missing-EOB caller is being qualified as described below; public
continuation and unsafe pointer premises remain separate unproved joins.
An independent 94-bit valid fixture for that loop is
`05 c1 85 00 00 00 00 00 20 7f ea 26`: two symbol-18 runs encode
255 zero lengths, a direct one sets literal 255, and repeat 16 starts at
combined index 256, filling EOB 256 and both distance lengths with one.
C-zlib 1.3.1 accepts empty output and reaches EOF only at the final byte for
all twelve chunk sizes. This fixture now runs in the ordinary Rust public
regression across those same chunk sizes and null-input retries.

The actual native-used bounded loop now verifies at 419/0, with 56 production
and 59 explicit proof/requirement bindings. Its ghost path couples each original
alphabet/source transition to the same physical word/count/input state and
exact OR/shift, rather than allowing unrelated semantic/register witnesses.
It preserves successful partial prefixes on suspension/error and retains
the original table/alphabet meaning through scratch overwrites without runtime
clones. Independent complete/repeat and suspended/overrun model fixtures and
an empty-path missing-EOB theorem supplement the public regression.
Native/package/MSRV/qualified lint/format gates pass on its exact inputs.
Focused sixteen and complete 221-control qualification pass on its own frozen
`bab336` acceptance: 34 equivalent 419/0 and 187 incorrect controls rejected.
All 54 input identities, 11,934 final case-input identities and unchanged
independent proof inputs in all ten paired controls reconcile.
A duplicate control-name collision in the initial focused attempt was caught
during provenance review, not accepted, and repaired with unique naming and a
checked rejection guard.
The actual native-used loop/EOB caller and message selector now verify at 427/0,
with 58 production and 62 explicit proof/requirement bindings. Distinct
NeedInput/InvalidRepeat/MissingEob/Complete outcomes preserve first-error
precedence, existing native messages/timing, arrays/progress and exact
raw/cache/byte/stream accounting. Completed empty-alphabet rejection derives
from the independent empty-path theorem, not a supplied EOB predicate.
Independent complete-zero/nonzero-EOB and stopped-field model fixtures accompany
a native regression for all four outcomes and exact partial frames.
All native/package/MSRV/qualified lint/format gates and sixteen focused controls
pass on its own frozen `d3b3` source. All 54 input and 864 final case-input
identities reconcile, with independent proofs unchanged in all five paired
controls. The paired wrong EOB value preserves executing-check/model/local-
contract agreement but fails the independent empty-alphabet theorem and EOB
fixture. The complete 233-control replay now also passes: 36 equivalent 427/0
and 197 incorrect controls rejected. All 54 input and 12,582 final case-input
identities reconcile, with independent proofs unchanged in all twelve paired
controls. This caller is accepted at its own frozen 427/233 source.

The next H1/H2 join must execute the real code-length input/table constructor
and then the decoded-length/EOB caller on its exact remaining input, in one
same-source native-used function. Its theorem distinguishes suspension while
reading the alphabet, invalid alphabet construction, and constructed-table
decoded-length outcomes. The alphabet must be the actual nineteen produced
lengths before scratch overwrites, not an arbitrary supplied table premise.
Compose both exact byte advances, raw states, dropped-bit coordinates, storage
and table/work frames; reset decoded progress only after successful construction.
Retain an intermediate state tying the canonical wire-field interpretation and
constructor result to that same alphabet and the subsequent loop's source.
Native `LenLens`/`CodeLens` continuation, error precedence and messages must remain
unchanged. Cross-call pointer/cache/original-alphabet persistence and the full
public mode/exit theorem remain separate.

This actual native-used constructor/decoder composition now verifies at 435/0,
with 59 production and 66 explicit proof/requirement bindings over 57 inputs.
The three typed phase outcomes and one shared intermediate state connect the
real wire alphabet, table/work construction and subsequent loop source/state,
with exact global/local byte/drop accounting and no runtime alphabet clone.
Independent empty-alphabet construction/suspension and native partial/error/
missing-EOB cases supplement the prior public fixtures.
Fresh `cbb6` acceptance passes 434/0 and all native/package/MSRV/qualified
lint/format gates pass on that exact source. Explicit raw-fill witnesses and
immediate canonical reset/actual byte-result bridges repair trigger sensitivity
and resource contamination without weakening any domain, contract or limit.
All seventeen focused controls pass; all 57 own source identities and 969 final
case-input hashes reconcile, with independent proofs unchanged in all six paired
controls. The paired wrong reset rejects solely in the independent fixture.
Aborted replays are not qualification evidence. The complete 245-control replay
aborted on resource contamination in the older constructor-result clobber case.
An immediate zero-index entry/opcode proof at the real constructor's return
boundary decomposes its existing meaning without runtime or contract changes.
Fresh `ad1a` acceptance and native/package gates pass; all eighteen focused
controls pass, including that constructor mutation. All 57 own identities and
1,026 final case-input hashes reconcile; independent proofs remain unchanged in
all six paired controls. Its next complete replay aborted on resource
contamination in the nondecreasing constructor variant. The identical
`total - processed` ranking is now a named internal spec with a separately
verified strict-descent arithmetic step, called by the actual loop with premises
from real symbol advancement. Constant/equivalent ranking mutations now target
that actual ranking definition and fail/pass respectively. Fresh `3602`
acceptance passes 435/0, and native/package gates pass. All twenty focused
controls pass; all 57 own identities and 1,140 final case-input hashes reconcile,
with unchanged independent proofs in all six paired cases. The complete
246-control replay passes at `controls-d3d232e2990749c69e27ad15322639f0`;
all 57 own live/acceptance/frozen/baseline identities and 14,022 final case-input
hashes reconcile, with all independent proof inputs unchanged in all fourteen
paired cases. **435/246 is accepted at its own frozen `3602` source**, not a
whole-parser or whole-library proof.

The next producer join is the actual fourteen-bit
HLIT/HDIST/HCLEN reader, its native profile check and this alphabet/header
caller. Establish exact NeedCounts/InvalidCounts/Alphabet outcomes, preserve
the raw 257..288, 1..32 and 4..19 field interpretations, and name the inherited
`nlen <= 286 && ndist <= 30` check as compatibility policy, not RFC text.
Only that executed check may establish total 258..316 and target 4..19 for
the following caller. Reset progress only after profile acceptance, retain
parsed counts across alphabet suspension, and compose all consumed-byte,
dropped-bit, raw/cache/source and storage coordinates through one actual
intermediate state. The independent fixture must distinguish truncated counts,
out-of-profile counts and accepted counts followed by alphabet suspension.
Do not treat the existing private total-257 fixture as a public count/header
witness. The unresolved RFC distance-count policy remains a separate gate.

This join is now implemented in the native-used `read_dynamic_header` and the
Table/LenLens/CodeLens consumer. Fresh `c4b2` verification passes 441/0. One
actual count-stage state supplies the remaining input, zero progress and
derived ncode/total to the existing alphabet/header caller; all cumulative
byte/drop/raw/cache/stream and storage frames compose. The independent
13/14-buffered-bit fixture checks reset/phase precedence within actual storage
bounds. Raw RFC count interpretation and narrower compatibility policy remain
separate. Native132 and all established native/reference/MSRV/qualified lint/
format/77-file package gates pass. All twenty focused controls pass at
`controls-f1239c1be13d4094b7ae2cd7a7f4f75f`; all 60 own source identities
and 1,200 final case-input hashes reconcile, with all eleven independent proof
inputs unchanged in each of eight paired controls. The paired wrong profile
rejects solely in the fixed independent compatibility-boundary proof.
All 258 complete controls pass at
`controls-ce0ec6d3943044eba6ffa5b847b8bae2`; all 60 own source identities
and 15,480 final case-input hashes reconcile. All eleven independent proof
inputs remain unchanged in each of sixteen paired cases. **441/258 is
accepted at its own frozen `c4b2` source**, not as a whole-parser theorem.

The next general-constructor join is the actual subtable allocation/root-link
transition. Establish one shared old/new layout, exact capacity rejection with
no table write, successful root-cell metadata and complete outside-cell frame.
The installed absolute offset and width must describe the same adjacent region
returned by the actual width/allocation producer, not an independently supplied
pointer. Prove mathematical second-level indices stay within that region,
including nonzero prior-subtable offsets. Independent boundary fixtures must
challenge absolute-versus-relative offsets and rejection side effects.
This is a representation/allocation bridge, not yet canonical decoding:
the outer constructor must still connect canonical prefixes, root-link
selection, replicated leaf meanings and fixed-limit sufficiency.

This join is now implemented in the native-used `layout::advance_and_link`.
Fresh `7049` acceptance passes 445/0, with 61 production/71 proof bindings and
60 live/frozen input identities reconciled. The same actual allocator produces
the checked link fields and rejection state; all outside-cell frames compose.
The mathematical index theorem does not yet refine a native lookup, and
full-buffer containment and the general outer-loop premises remain open.
An independent sixteen-cell fixture pins nonzero absolute offsets, wrap and
rejection side effects. Native135/extracted135 and all established native/
reference/MSRV/qualified lint/format/77-file package gates pass. All 269 names
and 294 anchors preflight uniquely. All twenty-one focused controls pass at
`controls-480e806e99d940efa4bd6931bfea04f1`; all 60 own identities and 1,260
final case-input hashes reconcile, with all eleven independent proof inputs
unchanged in each of four paired cases. The coupled offset defect rejects
only the independent index-bound and fixed-fixture proofs.
All 269 complete controls pass at
`controls-3692b57a4bb04413bcfd224ae9f285b4`; all 60 own source identities
and 16,140 final case-input hashes reconcile, with all eleven independent
proof inputs unchanged in each of eighteen paired cases. **445/269 is
accepted at its own frozen `7049` source**, not as a general-constructor proof.

Next connect the actual distance-subtable mask/shift/index calculation to
the independent mathematical `subtable_index`. Preserve lazy lookahead:
selection itself consumes no input/bits and does not assume sufficient
available bits; the enclosing loop still establishes readiness before
committing drops. Derive conditional region bounds from the same
allocator-produced link, including high cached bits and a nonzero prior
subtable offset. Native hot/cold distance consumers must execute the proved
index kernel without changing refill, error or bit-drop order. The
constructor/public-state premises, canonical leaf meaning, actual table read
and full streaming theorem remain separate joins.

This index join is now implemented in the native-used `lookup_subtable_index`
and both slow distance consumers. Preceding `f44e` acceptance passes 449/0, with
62 production/73 proof bindings and 60 live/frozen input identities reconciled.
The actual peek/mask/shift/base equals the mathematical index for all raw words,
without an available-bit premise, and the same allocator link supplies
conditional region bounds. The literal/length and fast-loop paths are unchanged.
An independent unequal-width/high-word/full-offset fixture and native
constructor/index oracle check the coordinates; no public-stream witness is
claimed for the private maximum-offset endpoint. Native136/extracted136 and all
established reference/MSRV/qualified lint/format/77-file package gates pass.
A test-only identity-operation lint repair has distinct preceding positive/
failed-native provenance. All 279 names/308 anchors preflight uniquely;
all twenty-three focused controls pass at
`controls-e5e5584d698f4769abdafb6e55a0b345`. All 60 own source identities and
1,380 final case-input hashes reconcile, with all eleven independent proof
inputs unchanged in each of four paired cases. A coupled code/model/local-
contract missing-base mutation rejects only through the unchanged independent
link-bound and two fixed-fixture obligations. The first complete 279-control
replay at `controls-250ebd2001e94ea399c42b4896eb8b9b` aborted on resource-
contaminated omission of the actual alphabet constructor. It is not accepted.
Immediate progress/padding/result checkpoints and a function-local isolated
prover now decompose that unchanged call contract without execution/domain/
contract/limit changes. Fresh `ca8d` acceptance passes 449/0 and all native/
package gates pass. The original omission rejects 448/1 at
`controls-af188eabac8047c5849bc1c7095def71`; all 60 own identities and 60
final case-input hashes reconcile. All twenty-nine expanded focused controls
pass at `controls-dc4d27d4b4f443bb8540b93085baab7d`; all 60 own identities
and 1,740 final case-input hashes reconcile, with all eleven independent proof
inputs unchanged in each of four paired cases. All 279 complete controls pass
at `controls-9ba84c4bc72746ec8d0b35333685660a`; all 60 own identities and
16,740 final case-input hashes reconcile, with all eleven independent proof
inputs unchanged in each of twenty paired cases. **449/279 is accepted
at its own frozen `ca8d` source**, not as a general-constructor theorem.

The real general constructor's preparation-stage candidate now joins Codes, Lens
and Dists: classification/stable sorting, exact empty fallback, clamped
requested root, actual table parameters and fixed root-capacity policy.
Quantify over all requested `usize` widths, length values 0..15 and histogram-
representable populations, not just the code-length alphabet. Invalid/empty
input must preserve workspace; capacity rejection occurs after sorting and
must preserve the table while retaining that sorted workspace and its suffix.
Ready must supply the same actual histogram, root allocation and selector
metadata consumed by the existing constructor loop. Name 1332/592 as baseline
table-capacity policy, not RFC requirements. Do not equate that policy check
with actual supplied-slice containment or general canonical table semantics.
The actual typed producer, scalar clamp/capacity decisions and existing root-only
caller pass fresh unrestricted454/0 at
`acceptance-e08dfd21febf4034834d24dc48e4ef9d`, with 65 production/
75 proof bindings and 63 inputs. Native/extracted138 and all established gates,
including package78, pass. All295 names/327 anchors preflight. The preceding
focused35 aborted on a capacity mutation's intended failure plus resource
exhaustion. Extracting the actual scalar capacity decision preserves execution,
domains, contracts and limits while removing irrelevant array context from
that policy obligation. All four targeted policy controls pass at
`controls-1a3e3f664dad47e39e7476359f296ecc`, with63 own identities/252 final
hashes and24 unchanged independent proof hashes in two paired cases.
The preceding453/0 focused35 replay aborted on resource-contaminated rejection
of a wrong root clamp. Actual clamping is now a separate native scalar kernel;
the array-rich preparation body uses a function-local isolated prover, without
execution/domain/contract/resource-limit weakening. All sixteen focused controls
pass on fresh454/0 at `controls-dfa0c4bac2ed4f5699da595eeaeee72d`: two equivalent
454/0 and fourteen incorrect453/1. All63 own identities/1008 final case-input
hashes reconcile; all twelve proof inputs remain unchanged in three paired
cases (36 hashes). Coupled code/model clamp/capacity mutations reject only
unchanged independent fixtures. All295 complete controls pass at
`controls-f6958bc6da144988ac1b9665b0a3156b`, with all63 own identities/
18585 final case-input hashes and276 unchanged proof hashes in23 paired cases.
**454/295 is accepted at its own frozen `e08d` source.**

The actual entry-maker/replicator candidate now joins the real constructor
loop for all alphabets and root/subtable leaf widths. It preserves the same
produced entry, replication geometry, complete outside-cell frame, layout
and returned prior-region size. Fresh463/0 at
`acceptance-2c1ef82382f14b4d9bab6c60a53131cb` has66 production/79 proof bindings
over66 inputs; native/extracted140 and all established gates/package79 pass.
The first focused25 aborted on a resource-contaminated root-clobber assertion.
Opaque full-result semantics plus checked scalar/root projections preserve
the entire contract without resource-limit/domain changes. All three targeted
projection controls pass on907e; its focused25 then aborted on a resource-
contaminated ranking-lemma rejection. The same loop metric is now opaque at
callers and explicitly revealed in its checked decrease lemma, with no change
to its definition, the loop expression or resource limits. Four targeted
ranking/projection controls pass and reconcile on precedingb499. A native
constructor-input witness now reaches the independent nonzero-base fixture
with a complete twenty-six-symbol literal tree, including EOB, and checks
the root links and table/work suffixes. It is not a public-stream witness.
On preceding9241, all25 focused controls pass at
`controls-7e3ee1d2537743de8cec9f7a508d83d6`:
four equivalent461/0, twenty-one incorrect460/1,66 own identities/1650
final hashes and39 unchanged proof hashes in three paired cases.
Its full311 replay at `controls-27546c864f5e48eaa6a84a7b35540314` aborted
on the paired clamp mutation: the intended independent boundary failure was
contaminated by parent-constructor resource exhaustion. The unchanged clamp
model is now opaque at callers; scalar/boundary proofs reveal it, and a checked
upper-bound lemma supplies the actual root-only caller. No domain/contract/
control/resource-limit weakening. All eight targeted controls pass at
`controls-153e6964e43849fb8ad1ad472b80f392`: two equivalent462/0,
six incorrect461/1,66 own identities/528 final hashes and26 unchanged proof
hashes in two paired cases. Coupled clamp/base mutations reject only their
unchanged independent fixtures. That source's focused41 at
`controls-51fb9ff22e304c9dbccdcda9aba17db7` aborted on an equivalent paired
literal-capacity edit with constructor resource exhaustion. The unchanged
capacity-policy model is now also opaque, revealed in its scalar and independent
boundary proofs; a checked universal CodeLengths-capacity lemma supplies the
actual constructor without the other alphabets' thresholds. No domain/contract/
control/resource changes. All41 focused controls pass at
`controls-e780f394dc0e4bbcbe514b82021f70d3`: six equivalent463/0,
thirty-five incorrect462/1,66 own identities/2706 final hashes and78 unchanged
proof hashes in six paired cases. Coupled clamp/capacity/base mutations reject
only their unchanged independent fixtures. All311 full controls pass at
`controls-4232d1134e134781b57d43207a69c30f`, with66 own identities/20526
final hashes and325 unchanged independent proof hashes in25 paired cases.
**463/311 is accepted at its own frozen2c1e source.**
Then extend the root-only loop to alphabet-aware
canonical meaning, including the accepted incomplete one-bit hole, while
retaining the existing exact code-length theorem. The general subtable loop,
fixed-capacity sufficiency and actual public parser/decoder premises remain open.

The H1 path now joins actual histogram production, binary-prefix space,
length classification, offset generation and stable symbol sorting.
These are not a Huffman decoder proof:

| H1 step | Current boundary |
|---|---|
| Histogram and metadata | Checked for <=65535 lengths, each <=15; zero lengths are unassigned |
| Prefix-space arithmetic | Checked for every 16-entry `u16` histogram, including exact failure |
| Classification caller | Actual producer/checker join checked, with complete-code flag and one-bit exception |
| Offset generation and stable symbol sorting | Checked actual loops; accepted classifier supplies the histogram premise; exact stable ranks, all assigned symbols covered, untouched workspace suffix |
| RFC canonical assignment model | Checked histogram agreement, declared-width bound and normative eight-symbol example |
| Normalized successor and word reversal | Actual kernels and caller checked for every cursor and lengths 1..15; root-only constructor maintains the sequence invariant |
| Table-entry replication | Actual loop checked for every entry under prefix/space premises; exact replicated cells, complete slice frame and termination |
| Actual root-only code-length constructor | Checked exact outcomes, canonical replication, root/used counts, bounds, termination and unused table/workspace frames under explicit root-only premises |
| Normalized canonical interval partition | Checked pairwise disjointness/bounds and, for complete exact histograms with sorted workspace, existence/uniqueness for every integer in `[0, 2^32)` |
| Low-bit table-prefix bridge and root-only returned-table meaning | Checked reversal totality/truncation, prefix uniqueness/coverage, exact root-cell entries and lookup meaning for every complete `u32` word |
| Actual dynamic-header wire writes, zero padding and constructor caller | Accepted exact permutation, bounded values, read-prefix/tail frames and complete constructor outcome; actual parser/reader premises remain open |
| Actual direct/repeat decoded-length expansion | Accepted exact writes/progress, count bounds, previous-length handling, failure frames and termination |
| Root lookahead completion stability | Accepted mathematical proof under returned-table meaning and available low-bit agreement; actual refill loop remains open |
| Actual buffered peek/drop/byte alignment and code-length table lookup | Accepted exact bit-sequence and actual canonical lookup composition; pointer/parser invariants remain open |
| Actual HLIT/HDIST/HCLEN input producer | Fresh exact raw values, complete success/exhaustion state and accounting; focused/full mutation qualification tracked separately |
| General subtable replication and real parser/bit-reader decoding | Open |
| Actual parser premises, symbol decoding and exact error/state joins | Open |

For sorting, the mathematical position of an assigned symbol is the number
of symbols having a smaller positive length plus the number of earlier
symbols with the same length. `before` sums histogram buckets independently
of the production loop; `count_before` counts qualifying input symbols.
Their equality connects actual offsets to input multiplicities. Bucket-entry
contracts and strict occurrence-rank lemmas establish stability and coverage,
not merely sorted lengths or successful writes. The actual
`analyze_and_sort_lengths` caller proves that accepted lengths are sorted and
empty/invalid inputs leave the entire workspace unchanged. Its workspace
premise applies only to accepted input and requires the nonzero population,
not the full input length.

The canonical model uses unbounded mathematical occurrence counts for RFC
1951 3.2.2's first-code recurrence, independently of machine histogram storage.
The histogram agreement and code-space partition relate this model to the
accepted producer. The actual successor adds `2^(32-length)` modulo `2^32`;
the actual word-reversal kernel maps every output bit to input bit `31-index`.
Its actual `next_code` caller composes both results. The classifier now proves
the initial remaining-count/bucket/canonical-cursor state. The actual
`advance_symbol` joins the successor to one-symbol consumption, preserves the
canonical sequence across empty buckets, and stops exactly at the assigned
population. The actual root-only constructor now maintains this state through
entry creation, replication and exact outcomes. The general constructor must
extend it through subtable allocation and root links, then establish complete
table semantics and decoding.
No standard-library `reverse_bits` contract is assumed: the runtime now uses
the same explicitly proved five-stage word permutation as Verus.
The eventual dynamic-parser invariant must retain a ghost snapshot of the
nineteen code-length alphabet lengths: `Mode::CodeLens` overwrites that same
scratch `lens` storage while continuing to use the constructed table.
The growing decoded prefix must separately track the combined literal/distance
length sequence; repeats may cross that alphabet boundary. Bit availability,
drop/refill offsets and error timing are still separate obligations.
Alignment is preserved by the actual successor and weakening to a longer code
length; reversing an aligned cursor produces a value within the declared
code width. A shifted-code bound connects that width to the subtable prefix.
The actual replication loop fills precisely the matching-prefix cells and
preserves every other table entry, conditional on its region fitting the
provided slice. The root-only constructor discharges those dimensions,
prefix, capacity and semantic-entry premises together; the general subtable
constructor remains open.

The actual lookup-table selector and entry maker now prove entry-field meaning:
direct symbols, literals, EOB, RFC length/distance bases and extra-bit counts,
and reserved-operation flags. The normative base/extra definitions use grouped
integer/power formulas, not production arrays. The actual subtable-width
lookahead and its region-allocation/capacity join now establish the first
stopping depth, exact adjacent regions, used
accounting and the inherited per-kind capacity decisions. Replication derives
its region bounds from this live-region invariant. The real constructor now
connects the cursor/count transition, entry meanings, layout and exact
replication frame in one outer-loop invariant for the root-only code-length
domain. Explicit premises are at most nineteen lengths in 0..7,
`maximum_length <= bits <= 7`, fitting root capacity and accepted-population
workspace. The theorem covers empty/invalid/accepted outcomes, excludes
capacity failure, and proves exact canonical replication plus unused-cell
frames. A separate normalized canonical interval theorem now proves
cross-depth/same-bucket separation, bounds and complete existence/uniqueness
using depth induction and quotient/remainder selection through the sorted
workspace. The low-bit join is now checked: a constructive erased reversal
witness, exact truncation/alignment and mask/modulus lemmas connect canonical
intervals to matching prefixes. Last-writer induction establishes each
returned root cell's unique symbol and exact bit count; root-width remainder
projection extends this meaning to every complete `u32` input word. The
actual constructor guarantees this returned-table relation in its restricted
code-length domain. This is not a proof of actual bit-reader consumption,
truncation handling or repeat interpretation. Next extend the actual
constructor beyond that domain, through subtable links, and prove fixed-limit sufficiency rather than
assuming the historical exhaustive search. Subsequent extra-bit parsing,
reserved-symbol error propagation and complete decoding are separate joins.

The agent-authored mathematical interpretation needs independent human
RFC/model review. The solver does not establish that the model captured prose.
No assumptions, admissions, project-owned external bodies, blanket termination
opt-outs, or alternate proof-only executable algorithms are permitted to close
missing joins. Rust standard-library contracts, Verus/vstd, rustc and Z3 form
the documented trusted foundation.

Retain existing platform CI, differential tests, conformance fixtures, fuzzing,
package-extraction/MSRV tests, memory/FFI review and performance qualification.
Proofs do not imply absence of exploitable bugs, resistance to decompression
bombs, allocator correctness, constant-time behavior, or whole-program
concurrency guarantees. Report a suspected private-helper defect separately
from a confirmed public-input bug; severity requires demonstrated impact.
