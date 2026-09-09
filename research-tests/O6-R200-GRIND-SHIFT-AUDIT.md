# R200 main-lane grind-shift audit

## Baseline and bounds

Started 2026-09-09T13:14Z at exact HEAD60869648 on cp5-thm73-scoping.
Tracked clean; only permitted paper/ and review-o6-body-adversarial.md untracked.
Idris2 v0.8.0. Read FIRST R199 audit, then R198/R197/R196/R195 and R190 design;
further R194/R193/R192 readings follow dependencies. No full-paper-reread claim.
Timeout17:14Z; no new proof attempt after16:34Z; validation starts by16:49Z;
final owner gate by16:59Z. B<=24, A<=20, C<=3 only after A+B producers; D<=4.
One new declaration per native invocation, <=3 invocations per micro-unit,
immediate guarded commit after fresh PASS or full revert/audit/gate. No fourth
attempt or silent scope extension. Production, protected statements/bodies,
lane-owned modules, selector/O17/O21 are unchanged and off limits.

No cross-lane locks or rebuild windows. One compiler in THIS lane at a time;
48GiB sampled RSS guard except byte-frozen LocalDiamond52GiB. Unchanged
UniqueRawNameOrdinalCapital48GiB is explicitly authorized by task. Detached
Python -I seeded checks preserve build/, require their own Building line and
reject extras/missing/empty targets, interrupt on mutation/resource excess.
Foreign-lane overlap is timestamp-only and no foreign compiler is signalled.

## Initial check and authorized comment correction

S0-1 fresh own-target DeletionDisappearance PASS4.178s, sampled3,008,752KiB;
no extra Building, mutation, interruption or resource stop. Guards adapted
from R199 with obsolete mid-run continuation-only restriction removed: R200
begins under the already-effective no-lock rule; no lock-path operations.

Supervisor R199 independent review ACCEPT-WITH-NOTES, no proof blocker.
Authorized P2 COMMENT-ONLY correction deferred to Unit D: the helper
`o20SelectedVestigialDisappears` consumes an actual DeletionResult; it produces
table reconciliation and absence, NOT that input result. Before/after SHA and
fresh own-target check will be disclosed. No mathematical/source API change.

## Status

Initial checkpoint only. B global selected-coverage/all-name rebase/D5 bridge,
A remainder elimination/Insert pairing/whole-history synchronization and C
convergence remain OPEN. No new theorem or hole. Full inherited157-source
validation plus changes/package, ledger/archive/verification and reviewer gate
are pending. S0 bootstrap is not a mathematical milestone.
