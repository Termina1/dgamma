# R197 main-lane grind-shift audit

## Baseline and bounds

Exact starting HEAD e2ebe3b5c61f75dc760a72ede14ebaf426823ef7, branch
cp5-thm73-scoping, tracked clean; only allowed paper/ and
review-o6-body-adversarial.md untracked. Idris2 v0.8.0. R196 audit read FIRST,
then R195/R194/R193/R192/R191 audits. No full-paper rereading attestation.
Conservative start06:18Z, timeout10:18Z on2026-09-09; new-proof cutoff09:38Z,
frozen-validation-start cutoff09:53Z, final gate deadline10:03Z.

A<=26 whole pairing/history; B<=16 actual all-name endpoint/bridge; C<=3 body
ONLY after A/B owned; D<=8 research observed provider guard; E<=4 docs. One
new declaration per native invocation, at most3 invocations per micro-unit;
full revert and gate on exhausted unit. No src/package, lane-owned module,
frozen source, selector, O17/O21 or new hole edit. Main-only compiler scope.

R196 check/commit/artifact guards adapted as R197, retaining own-target
Building and extra-Building rejection, mutation interruption, full source/log/
JSON snapshots and one-second RSS samples. ALL checks conservatively take the
shared heavy lock, including unknown costs;48GiB except byte-frozen
LocalDiamond52GiB. No seed deletion/from-scratch build. Stale lock cleanup
requires age>25min AND dead owner PID, with a log. Maximum wait20min.

## Initial owner gates

Supervisor approved the unchanged source-pinned mandatory
CP5UniqueRawNameOrdinalCapital check under48GiB/shared lock, with prior
measurement44,790,080KiB (~42.715GiB). Any stop remains a resource stop, not PASS.
Supervisor approved reading the missing provider TYPE by read-only git show
from origin/cp5-thm73-lane-a8a10, no lane worktree access. Read at commit
94273eaab85e4edf0145027418fb0f1c387bb824, path
research-tests/O6-L2R5-Sources/DGamma/L2R5ProviderObservation.idr.
Copy TYPE into a distinct new main research module; no lane implementation
or exhausted statement is copied/retried.

## Baseline check

S0-1 exact R196 RootReplayLawProducer PASS3.112s, sampled2,353,808KiB,
only its own73/73 Building. No target mutation/interruption/extra rebuild.
E1 bootstraps guards and this audit from that fresh PASS. This is not final
validation, whole-pair extraction or convergence closure.

## Status

In progress. Inherited root C6/C9 owned; whole paired extraction and all-name
rebasing remain unproved. D5 remains a consumer. Frozen census last inherited
4=1/2/0/0/1; fresh final audit pending. No body attempt.
