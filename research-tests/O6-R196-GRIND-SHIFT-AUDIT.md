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

## Status

Execution in progress. No new convergence, canonical root consumer, whole
paired fold, canonical all-name cut or bridge completion is claimed. The R195
necessity witness remains required: generic ActionRegistrationReplayCorrespondence
still does not own an all-root law. This shift strengthens the two ACTUAL
storing producer contracts instead of assuming that false generic extraction.
