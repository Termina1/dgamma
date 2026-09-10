# R197 checked PARTIAL — verification guide

## Results

- Immutable plan SHA256 `6695cab51ae1239cd9750defc3953ff36bff47d3d17c572cf3fe2a7d73bb6d53`.
- 144/144 planned expected outcomes:143 source paths + seeded package;7 exact
  expected-negative checks. All136 inherited current R196 paths and7 new.
- 189 native records,178 expected PASS,11 rejected micro-attempts retained;
 33 source receipts, one declaration per retained commit. D5 STOP3/3 reverted.
- 18 adversarial evidence tests PASS. No resource stop, mutation, extra Building
  or own-compiler overlap. All lock intervals authenticated.
- Production unchanged vs34b21c9; all frozen hashes unchanged; census4=1/2/0/0/1.
- LocalDiamond50,615,728KiB under52GiB; UniqueOrdinal44,692,640KiB under48GiB.
  One-second samples, not OS high-water. Zero is unknown, not zero actual peak.
- 111 excluded inventory paths are NOT rechecked; no cold build or lane2 claim.

A remains conditional on supplied synchronization; universal pairing and
exact B rebasing/bridge are unproduced, C0. D observed producer is proved;
its optional generic consumer is not. Goal Type functions are not inhabitants.

## Compiler-free replay (the supervisor has CLOSED further native work)

```sh
python3 -I research-tests/test_r197_evidence_contract.py
python3 -I research-tests/run-r197-independent-verify.py --require-final-complete /tmp/dgamma-r197/review-independent.json
python3 -I research-tests/run-r197-frozen-audit.py /tmp/dgamma-r197/review-frozen.json
python3 -I research-tests/run-r197-resource-audit.py
python3 -I research-tests/run-r197-verify-archive.py
```

The first three original logs are in the committed evidence archive together
with ALL native `.json`/`.source`/`.log` snapshots, append-only raw ledger,
receipts, plan, rollback and lock history. The archive verifier checks every
archived member hash, all records, logs and source snapshots, plan coverage,
and archived receipt source bytes at their actual git commits. Verification
uses the recorded main-worktree environment; this is not a cold rebuild.

Archive anchor precedes E3 publication and future E4 note; own/future receipts
are intentionally outside it, never backdated. The archive's post-creation
verification is also outside itself. Later compiler-free verification files
may have later artifact-only HEADs without changing source/plan provenance.
Machine checks are not parent acceptance or independent human proof review.

## Provider interruption

Detached validation completed at08:15:37Z, on time. Provider usage-limit
interruption delayed publication/final gate. Supervisor explicitly revived
compiler-free E3 completion and closed further proof/native work. No source or
native work was resumed. Printed08:38 publication predates recorded09:38/10:03
UTC bounds; do not infer a missed UTC deadline. The original archived NON-NATIVE
resume note conflated the closed-work instruction with literal UTC lateness;
O6-R197-TIMING-QUALIFICATION.json corrects it, preserving archive bytes.
