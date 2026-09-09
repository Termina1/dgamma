# R196 main-lane grind-shift audit

## Baseline and bounded scope

Start2026-09-09T03:44:35Z: exact HEAD58f88c63ea70bca97bc974648f8e4939055fffd7,
branch cp5-thm73-scoping; tracked clean, only allowed untracked paper/ and
review-o6-body-adversarial.md. Idris2 v0.8.0. Root-contract manifest read FIRST,
then R195 audit, deferred visibility manifest and R194/R193 convergence audits.
No deferred visibility edit or full-paper-rereading attestation this shift.
Timeout07:44:35Z; new-proof cutoff07:04:35Z; validation-start cutoff07:19:35Z;
final owner gate deadline07:29:35Z. Production/src/package remain byte-frozen
against34b21c9; CP3 blob2c697e532e83989de8591fa6a4378747c6a501c0.

A<=12 invocations: exact approved adjacent helper, stored root law/fill, deletion
stored root law/fill, empty-root fixture fill. B: serialized seeded rechecks.
C<=10 invocations ONLY after B: actual root-law consumers, then paired fold if
inputs are producer-owned. D<=4 artifact/documentation units. No O17/O21,
convergence/bridge body, lane-owned edit, unsafe escape or new hole is authorized.

## Exact pre-execution gate and topology correction

Owner ACK is retained verbatim in O6-R196-ROOT-CONTRACT-GATE.md. The immutable
execution JSON SHA18b4ebf7c396b3407f4de3e2fc617dfa86af1bc7849746b0ff63352e07e98340
contains every exact diff and stage before/after hash; its original proposal
status is historical, superseded by the separate ACK, not silently rewritten.
Both new fields match the R195 manifest verbatim. A1 helper has zero hidden
indices and no new export; only the stored root-law field becomes public.

R19 imports DeletionChain. Owner therefore explicitly approved A1→A2→A4→A3,
rather than implicitly rebuilding DeletionChain inside A3. No additional
LocalDiamond/DeletionChain byte, frozen O19 constructor or body needs changing.
A1/A2 are explicitly52GiB (54,525,952KiB), including A1's NEW helper; all other
modules48GiB. DeletionChain's own prior peak5,044,256KiB is below40GiB. Only
LocalDiamond exceeds40GiB in the retained inventory (50,598,096KiB).

The conservative244-entry invalidation inventory is NOT a runnable suite.
Owner approved122 applicable source modules plus the seeded package; three
source paths are checked directly in A and120 remaining slots in B. All65
inherited validation targets are included.113 unclassified fixtures and11
legacy R11 files are excluded by explicit path, NOT claimed passed; refreshed
inventory must label them stale TTC/not re-checked. The runnable plan retains
all per-path historical estimates;60 B targets have UNKNOWN direct cost.
Measured-time subtotal758.38s is not a prediction for the whole rebuild.
Approved prose correction117→113 yields sealed plan
4fb11fbc5550c070badacd8f7301b16a821296a80b88c2d3353b528409a9b29a; original plan
SHAa14a48c7c75b880dca43ec08a41ad1289539b31411dfd4bd609b2aaca2109087 is archived.

## Continuous heavy rebuild window

Detached Python -I window ownerPID86408 acquired atomic /tmp/dgamma-heavy.lock
at03:51:48.540837Z, recording lane/pid/timestampUTC/unit/path. Required window
JSON has note "LocalDiamond contract rebuild; lane 2 must not run heavy checks"
and expectedEnd07:19:35Z. Continuous ownership spans A through B/package.
All direct checks are detached Python -I wrappers; own target Building, exact
source snapshots,1s sampled RSS, target mutation interruption, no extra Building
and source-pinned thresholds are authenticated. No TTC deletion/cold build,
implicit bulk dependency rebuild, parallel main compiler or lane2 operation.
No stale lock removed; only age>25min AND dead pid permits logged cleanup.

## Micro-unit ledger

A1-1 launched03:51:59.024694Z at exact approveda2175a16 under52GiB; fresh
own-Building PASS489.272s, sampled50,036,832KiB, no extra Building/interruption/
mutation. Immediately guarded committedeff1e877 at04:00:18Z. This is the exact
private root specialization, not yet the storing-field revision. Twelve
noncompiler evidence-contract regressions PASS. D1 bootstraps the gated plan,
check/commit/window/evidence guards and this audit from that same fresh PASS.

## Unit A completed; A4 syntax amendment is explicit

| Unit | Invocation | Result | Seconds | Sample KiB | Guarded commit |
|---|---|---|---:|---:|---|
| A1 helper | A1-1 | PASS |489.272|50036832|eff1e877|
| A2 adjacent field/fill | A2-1 | PASS |488.094|50611312|72624ff7|
| A4 deletion field/fill | A4-1 | parser REJECTED |4.190|468992|none|
| A4 deletion field/fill | A4-2 | PASS |77.839|4830272|35e1fe89|
| A3 empty-root fixture | A3-1 | PASS |2.089|727504|512affed|

A4-1's proposed implicit-lambda binder was rejected by the parser. No mathematical
failure or resource stop is inferred. Owner explicitly approved replacing ONLY
that fill's lambda head with `\occurrence => cong (MkRegistrationGeneration _)`;
the root index is determined by the field's expected equality, not a proof hole
or a freely supplied premise. Exact field text stays verbatim. Append-only
O6-R196-A4-SYNTAX-AMENDMENT.json SHA50cbc4dab9df4781ebf81965b96536a782c3160e9656c782ca880fd1550d7f4f
retains the full ruling, original rejected hash/diff and successful revised hash.
The original proposal and A4-1 snapshot/log/record were NOT rewritten. No3/3.

New frozen LocalDiamond SHA:
`9f9216170853624cff30449696f2540da0ed48e0b42504533aa587cb70dfc037`.
New frozen DeletionChain SHA:
`7fadaf6b3e71030290813393d8954afee0da79ec93b293fcfcd977deb4562578`.
R19 fixture SHA:
`4f30ab58cae44bc89bf3c9cc940d3ab63bf1f0af99494cfd157d6db21617bd80`.
Both exact stored producer contracts now typecheck with their actual constructor
fills. Generic ARRC is unchanged; no extra LocalDiamond/DeletionChain bytes.

A5 read-only exact-delta audit and independent receipt/snapshot authentication
PASS at512affed. O19 closed declaration/body1286B SHA
`cbd0954303c35141af0309e515bdb9e98e988e7c23be70b9764d8c1ce18fd396` unchanged;
adjacent1470B/1154B hashes unchanged; production empty against34b21c9, CP3 pinned,
census4=1/2/0/0/1 and207/207 seeded TTCs retained. This is NOT yet a fresh package
PASS. Five A invocations=4PASS/1 parser rejection,0 interruption/mutation/resource
stop, four immediate source receipts. D2 records amendment/A outcomes and guards.

## Unit B topology-contract stop and approved import-closed continuation

Original B1 at04:17:02Z returned exit0/own Building in5.183s, sample795,120KiB,
but correctly FAILED the runner's one-source contract: it additionally built
R45BareDiamondDisciplineCounterexamplePositive. This is a topology-contract
stop, NOT a resource stop; resourceStopped/interrupted/mutation are all false.
No B2 followed in that original batch. The planner had filtered unclassified
fixtures before taking import closure; this was our planning defect. Original
plan and B1 source/log/JSON remain unmodified; B1 is never relabelled PASS.

Owner ACK approved an append-only import-closed continuation with13 mandatory
positive imported fixture dependencies, one same-hash B1R1 retry and the original
unrun slots dependency-first. It is O6-R196-DEPENDENT-RECHECK-CONTINUATION.json,
SHAbcbc36528127e2291cc90bf37c86259a038499652646891dc1cbf1cbe08d6e7d. New applicable
scope135 source modules+package,133 B acceptance slots;100 unclassified+11legacy
remain stale/notchecked by explicit path. The13 additions include a constructive
RevisedSafetyNegative module actually imported by the positive all-four fixture;
it is not an expected compiler-failure target. Preflight records actual import
edges, source hashes and no holes/unsafe/partial; all13 direct costs UNKNOWN and
all checks48GiB under the same continuous window.

Before the first continuation compiler,16 noncompiler tests PASS, INCLUDING an
original-plan closure rejection and full corrected-plan import closure/topology
PASS. The continuation runner requires that exact successful test receipt and
plan hash. BD13 directly checked R45 PASS4.147s; B1R1 then PASS1.044s at the same
pinned source. Both have ONLY their own Building line. Other targets proceed
serially; no final completion claim at this entry.

New measured cost: B6 CP5UniqueRawNameOrdinalCapital (47 source lines) fresh
PASS300.121s, sampled44,790,080KiB (~42.715GiB) under48GiB. It was UNKNOWN in
R195; source size is not a reliable cost estimate. This >40GiB measurement must
be included in future per-target resource gates; no repeat is planned here.

## Unit B complete; C privacy boundary and second reserved rebuild

B133/133 continuation acceptance slots completed04:50:27Z (package16.668s).
The original B1 remains rejected;133/244 inventoried entries and two inherited
main baseline modules were rechecked, plus the package. All135 applicable source
paths had current-hash direct checks. First continuous window released after
its frozen/independent audits. No new C source existed before B completed.

C1 actual finite-adjacent root law PASS/committed2172eef5. C2-1 direct deletion
projection FAILED2.087s at the private action-origin alias: the stored field's
whole-source expression cannot convert to deletionProducerActionOrigin in an
importer. This is a privacy/elaboration boundary, NOT a false root law or RSS
stop. The failed declaration was fully reverted to C1 before requesting a gate.
No exhausted3/3 statement or unapproved source revision occurred.

Owner separately approved exactly the opaque erased exported proof helper
`deletionBuiltRootOrdinalPreserved` in the defining DeletionChain module, after
the existing operational occurrence builder and before DeletionChainStep. Its
body ONLY projects the same stored capital's root law; the private action-origin
unfolding happens there. No private function keyword changed, no root premise
or oracle was added. C3-1 fresh PASS77.924s/4,976,464KiB at48GiB, immediate
commit30bd2a68. New final frozen DeletionChain SHA:
`91e8fd290cc4fedae9656ce5b4ae3ea0b38509f6e0250f51b4a7aa2aea09067b`.
Exact35-line exception and verbatim ruling are in
O6-R196-C3-DELETION-HELPER-MANIFEST.json,
SHA93ef4450009443c19cef8791b8ee6a91cd920da582d4f6f308df7e5f1b4c611a.

The owner reserved a SECOND continuous heavy window with note
"DeletionChain helper rebuild; lane 2 light only". The separate hash-pinned
O6-R196-SECOND-WINDOW-PLAN.json,
SHA062d5797604fbc3c232c42992b9e100ceb0619060e66bccbdbc83fa0dd364382,
checks the126 affected source dependencies plus package after C3. LocalDiamond
and B6 are unaffected and NOT rerun. All have measured costs below40GiB, so48GiB
throughout. W127/127 expected outcomes completed; package16.583s. Second-window
frozen/independent audits PASS; release requested05:26:32Z. Only then C2 retried.
Both original B plans/records and both window logs remain append-only evidence.

## Unit C root consumers complete to cap; whole pairing NOT claimed

| Unit | Result | Guarded commit | Exact boundary |
|---|---|---|---|
| C1 | PASS1 |2172eef5|finite adjacent root law from actual enriched folds|
| C2 | rejection1 / PASS2 |a3aec4f9|actual deletion builder root-law wrapper|
| C3 | PASS1 |30bd2a68|owner-gated defining-module raw root proof|
| C4 | PASS1 |530d759a|stored deletion correspondence's OWN exactness field|
| C5 | PASS1 |eec98e47|whole actual deletion derivation identity/composition|
| C6 | PASS1 |94a1268f|EXACT canonicalOccurrenceCorrespondence capital|
| C7 | PASS1 |06e9c24c|actual operational permutation's finite block folds|
| C8 | PASS1 |cc86171f|same canonical trace followed by actual operational replay|
| C9 | PASS1 |1fd9bbcb|literal canonicalOccurrenceCorrespondence + permutationOccurrenceCorrespondence execution|

C6 has EXACTLY `O20RootReplayOrdinals … (canonicalOccurrenceCorrespondence capital)`;
C9 has that record for the literal composed convergence-facing occurrence map.
All root laws are outputs from actual producer-owned capital, not hypotheses
added to a protected consumer. Generic ARRC remains unchanged and R195's root
necessity fixture freshly typechecks in both applicable validation windows.
All four protected hole statements and all other frozen bodies are untouched.

C source cap10 invocations=9PASS/1 preserved privacy rejection, nine immediate
source receipts. No slots remain for the first whole paired-stage fold, which
was NOT attempted. A full original-to-canonical/root-opposite occurrence pairing,
whole accepted paired history, canonical vestigial/opposite-image absence,
all-name endpoint cut and D5 bridge remain separate obligations. No O17/O21 or
bridge/body attempt, freely supplied all-root oracle, postulate or new hole.
Source freeze1fd9bbcb60bfb3168ebc001d33d908377268fbd2.

## Status

Checked PARTIAL overall: A contract execution complete; B133/133 and extra
W127/127 complete; C root consumers complete to its10-invocation cap; whole
paired-stage fold and endpoint bridge open. Total276 native invocations=
273 expected PASS/3 preserved rejections, thirteen guarded source commits.
No resource stop, mutation, interruption, cold build or seed deletion. The
initial B1 extra Building is explicitly the sole one-source contract violation,
caught/rejected and cured by the owner-approved import-closed continuation.
Eighteen noncompiler evidence regressions PASS. Measurements are one-second
samples, not OS high-water; zeros mean no live sample captured.

D3 synchronizes NOTES/THM73-PLAN/README, the new frozen baselines, refreshed
inherited244-entry inventory plus one new consumer, per-module measurements,
compiler ledger/archive and independent verification.100 unclassified+11legacy
paths remain explicitly stale/notchecked. Lane2 lifecycle-replay note is ONLY
a future main candidate: "observed retired-head guard at the source". No lane2
new-result certification or worktree/source operation. D1/D2 used; D4 reserved
for the owner gate note. Owner final gate and parent-owned reviewer pending.
