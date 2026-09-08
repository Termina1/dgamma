# R187 grind-shift audit

## Authenticated start and binding guard

2026-09-08 05:23:56 UTC: cp5-thm73-scoping, HEAD e535e3613932aaf8e18d6ac4a9faf04c6bb6d072,
tracked clean; only permitted paper/ and frozen review-o6-body-adversarial.md.
No compiler orphan found. No new attempt after 08:43:56 UTC; final safe gate
by 09:08:56; timeout 09:23:56. One detached Python-I seeded compiler at a time,
48 GiB sampled RSS guard, no seed deletion/from-scratch build, immediate exact-
source fresh PASS guarded commit, one new declaration/check, <=3 attempts/unit.
A<=12 then B<=16 then O19 body only after prerequisite assembly is committed;
C<=6 remaining selector slots after body gate or unit stop with >=60 minutes.
No production change, LocalDiamond visibility/declaration without prior gate,
with, unsafe/partial/postulate/new hole, frozen deletion call, scalar observer
of nested builders, nested Either/DPair producer, computed-existential case,
O17/root/O21 withdrawal/O20 body work. Public O19 safety surface stays frozen.

## Unit 0 — R186 ledger/archive repair (compiler-free)

Reconstructed all 99 invocations from surviving /tmp/dgamma-r186/ledger.jsonl;
checked bijection/equality against individual JSON records, exact SHA256 of
EVERY source snapshot, and byte-equivalent compiler transcript against logs.
99 records = 89 PASS, 7 diagnostic rejections, 3 interrupted D3 stalls. Baseline,
rollback, cap checks, both consolidated matrices and package invocations retained.
O6-R186-COMPILER-LEDGER.json records unit/attempt/target/start/end UTC/exit/fresh/
passed/interrupted/sourceHash and matchingSourceCommits per invocation. Matching
commits mean baseline or target-changing commits with the same source bytes,
not an invented one-to-one commit chronology. Rejected uncommitted sources have
no matches. Package `fresh` is inherited seeded-build success, explicitly NOT a
forced source compilation (P9/Q10 transcripts are empty); source freshness is
an actual target Building line.

O6-R186-COMPILER-EVIDENCE.tar.gz archives all surviving R186 logs, records,
source snapshots and diagnostic samples; each invocation's JSON/log/source
was re-read from the archive and byte-verified. Archive SHA256 is recorded in
the ledger. Reproducible repair/shift archival utility run-r187-archive.py and
R187 check/commit/artifact/frozen guard wrappers are retained. Unit 0 artifact
path reuses authenticated R186 Q9 fresh source PASS at its unchanged source
hash; NO compiler invoked during documentation repair. This fixes R186's
missing committed consolidated ledger/archive regression, without rewriting
R186 evidence or source history. Repair completed before the 20-minute cap.

## Status

Unit 0 complete pending guarded artifact commit. A/B/C not yet attempted;
O19/O20/O21 bodies 0, holes unchanged 5 = 1/3/0/0/1. Independent review pending.

Supervisor review note: R186 ACCEPT-WITH-NOTES/P2 confirmed this missing artifact.
R186 recorded NO guarded-commit receipts; historical guarded commits remain
audit-asserted, not receipt-authenticated. No retrospective receipts fabricated.
R187 source/artifact guards now append timestamped actual resulting commit hashes,
unit/attempt/source hash and guard-check lists to commit-receipts.jsonl at commit;
consolidated R187 ledger/archive will include them. Final archive cannot contain
its own self-referential artifact-commit receipt; that receipt remains in /tmp
and is supplied at the final supervisor gate.
