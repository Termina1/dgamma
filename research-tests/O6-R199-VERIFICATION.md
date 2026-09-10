# R199 checked PARTIAL — final native/evidence verification

- Proof source freeze: `a240d3726ccfa36988562791fcb6fd1e76564f02`.
- Baseline: `fdf96f9a3af849263f2d5ce58693aa1dba89a46d`.
- Final plan: `cd367286435987976d77d3ce7b44eee67caa127ac5b6a915deaf206138678503`.
- Final validation:158/158 expected outcomes, finished2026-09-09T13:01:05.524119Z.
- ALL150 inherited sources +7 new +seeded package;7 exact expected negatives.
-211 native records,204 expected PASS,7 rejected snapshots;44 guarded source
  commits. B3-1 native PASS was whitespace-guard rejected, B3-2 freshly checked.
-28 distinct adversarial tests (21 original evidence tests, rechecked;7 owner-
  policy tests). Source/log/receipt/plan/frozen/resource/policy audits PASS.
- Production==34b21c9; CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`;
  all named frozen bytes unchanged, census4=1/2/0/0/1,207 package seeds present.
- No resource stop, target mutation, unexpected build, exhausted micro-unit or
  source/proof change after freeze. No cold-build or111 excluded-path claim.

## Owner-authorized validation policy continuation

See `O6-R199-OWNER-POLICY-CHANGE.md` (verbatim ruling) and its machine JSON.
V1–V11 retain old runner/lock evidence. At the safe boundary V11's own checker
released its lock; no native compiler was signalled. The Python driver alone
was replaced to cross its pinned-runner-hash invariant. V12–V158 ran under the
new authenticated runner, with no shared-lock path access, no repeated target
and the SAME immutable source/validation plan. Per-lane serialization and52/48GiB
RSS guards remain. Cross-lane heavy checks are permitted; sampled overlap
observations contain timestamps only (not an OS-scheduler trace).

Policy SHA256: `020d0da1d5a1fb22ba044350f830101bbe133903ad7834b618ff5337732ac412`.
Old/new runner hashes and driver hashes are independently checked against the
original launch commit and current code. Historical64 lock intervals and147
post-policy final checks are authenticated separately. Samples50,612,064KiB
LocalDiamond and44,800,976KiB other/Unique are below limits, NOT OS high-water.

## Reproducible evidence commands (no new native invocations)

```
python3 -I research-tests/test_r199_evidence_contract.py
python3 -I research-tests/test_r199_policy_contract.py
python3 -I research-tests/run-r199-independent-verify.py --require-final-complete
python3 -I research-tests/run-r199-resource-audit.py
python3 -I research-tests/run-r199-frozen-audit.py
python3 -I research-tests/run-r199-verify-archive.py
```

The first audits use `/tmp/dgamma-r199` records; the final archive verifier
reads the committed archive without extracting it, authenticating every raw
record/source/log against the source anchor. D3 archive publication is pending
at this D2 entry. Native launchers are append-only evidence operations, not
commands to casually rerun after this shift's clock/source freeze.

## Mathematical and review status

Checked PARTIAL only.44 declarations: own canonical coverage/order/shared Begin,
whole native actor-role consumption, accepted AUGMENTED role-word equality,
authentic public bilateral scan/deletion table reconciliation, and construction-
owned HEAD-SELECTED vestigial disappearance through deletion/sort/replay. The
mixed present-vestigial/absent current-map name class and native/conditional
fixtures are checked. No unconditional canonical fixture is fabricated.

A universal ordered occurrence-labelled modulo synchronization remains open;
B exhaustive discarded-to-deletion selection and universal current-map all-name
rebase remain open. D5 bridge not applied; C0/ineligible. The independent Python
machine audit is NOT an independent human mathematical review. Parent owns the
required reviewer gate. No full-paper-reread attestation is made by this shift.


## R199 D3 — append-only archive published and verified

Archive anchor `4987a366df85a9d33e89c8e4baaed62ac129a150`; SHA256
`b10faf5e75b57f53dd7f17d6f287c2a4df461e6c4dc072f29941f990a1c9dd8a`; 1,229,236 bytes,
1104 regular files. Full read-only archive authentication PASS:
211 native records/source snapshots/raw logs,44 source receipts,3 historical
artifact receipts,158 final outcomes and all7 rejected snapshots. The archive
also authenticates the explicit owner policy transition and old/new runner
boundary. Its own/future publication and gate receipts are intentionally outside
its anchor, not circularly asserted inside it.

The refreshed266-entry inventory marks155 directly checked inventory entries
plus2 auxiliary inherited sources =157 source targets.111 excluded legacy/
unclassified inventory entries remain NOT rechecked. Future cross-lane heavy-
lock flags are false under the owner ruling; older per-check lock use is retained
as historical, not rewritten. No archive replacement, source/native work or
clock extension. D3/4; final owner D4 gate/clean close remains. Independent human
review is parent-owned and not claimed complete.

Mathematical status remains checked PARTIAL: A universal ordered occurrence
synchronization, B exhaustive vestigial selection/all-name rebase and bridge
remain OPEN. Head-selection membership and augmented-word end remainders remain
explicit; conditional canonical fixtures are not fabricated capital. C0.
