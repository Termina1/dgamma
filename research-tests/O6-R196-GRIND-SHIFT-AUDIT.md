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

## Status

A1/A2/A4/A3/A5 complete. Serialized B window is next; C has ZERO invocations and
remains ineligible until B completes. No new convergence, canonical root consumer,
whole paired fold, canonical all-name cut or bridge completion is claimed. The
R195 necessity witness remains required: generic ActionRegistrationReplayCorrespondence
still does not own an all-root law. Both ACTUAL storing producer contracts are
now strengthened instead of assuming that false generic extraction.
