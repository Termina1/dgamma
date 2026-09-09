# R198 main-lane grind-shift audit

## Baseline and bounds

Exact starting HEAD2c9c2e19 on cp5-thm73-scoping; tracked clean; only permitted
paper/ and review-o6-body-adversarial.md untracked. Idris2 v0.8.0. R197 audit
read FIRST, then R196/R195/R194/R193/R192 and R190 design, with separate small
reads replacing truncated aggregate portions. No full-paper-reread attestation.
Conservative start08:49Z Sep9; timeout12:49Z; no-new-attempt12:09Z;
final-validation-start12:24Z; final gate12:34Z.

A<=26 (analysis first, <=2 docs-only analysis commits); B<=16; C<=3 invocations
ONLY after A/B producer-owned; D<=4 docs. One declaration/native invocation;
<=3 attempts/micro-unit; immediate authenticated guarded commit on fresh PASS,
or full revert+audit+gate. No extension or exhausted-statement retry.

All checks detached Python -I, source snapshots/log/JSON/RSS retained, target
mutation interrupts, missing/empty target and extra Building reject. ALL checks
conservatively take shared heavy lock (including unknown costs);48GiB except
source-frozen LocalDiamond52GiB. Mandatory unchanged UniqueOrdinal48GiB is
explicitly gated by this task with prior42.7GiB. Wait<=20min; stale cleanup only
age>25min AND dead owner pid with logged event. No lane2 worktree operations;
compiler/orphan scope main-only. Seeds never removed; no cold rebuild.

Production==34b21c9, CP3blob2c697e532e83989de8591fa6a4378747c6a501c0,
LocalDiamond9f921617…/DeletionChain91e8fd29…, all protected statements/bodies,
A11 bridge surface and selector frozen. No O17/O21, G31, unsafe escape or
public production revision. Owner OPTION A remains deferred.

## A analysis, first docs-only checkpoint

S0-1 exact synchronization GOAL module seeded fresh PASS3.118s/3,008,704KiB;
only own80/80 Building, no mutation/resource stop/extra build. Bootstrap guards
are adaptations of run-r197-* with baseline/clock/lane changed, no exemptions.

See O6-R198-SYNCHRONIZATION-ANALYSIS.md. The exact retained-sequence implication
needs a native test: E8 child positions do not obviously determine iterator
Advance positions when the parent has repeated equal yielding tags. A fresh
one-origin two-step parent fixture is proposed; NOT the excluded R178 mismatch
or the exhausted R192 retirement relocation. No counterexample/full capital or
synchronization producer is yet claimed. A analysis commit1/2; D unused.

## Status

Analysis in progress; zero new proof declarations. A synchronization OPEN,
B original->canonical/replayed all-name controls OPEN, C0/ineligible. Final
inherited143-source+package validation, fresh hashes/census, ledger/archive/
verification and owner/reviewer gates pending. No changed frozen/source bytes.
