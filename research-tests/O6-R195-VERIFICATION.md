# R195 verification — checked PARTIAL

## Scope and anchors

- Branch `cp5-thm73-scoping`; exact start `981e613795ddb04306a8009b6707defa76f9c8a7`.
- Source freeze `3bd991710c76170d358dd5dadc07c676dfdb21f0`; pre-publication evidence
  anchor `21269c8e935125e8101b2ebd62592bb36a0c7f07`.
- A26/B16 =42 retained declarations/specifications,42 immediate source receipts.
  C0 (producer-owned A/B incomplete; body explicitly prohibited). D1 findings,
  D2 final validation/evidence; D3 reserved final-gate note, D4 unused.
- Source-cap gate RATIFIED the parked/capped boundary and accepted the stronger
  root-contract manifest as R196 execution basis. It authorized ONLY final65
  checks/evidence in R195; no new proof/field/keyword/body extension.

## Actual results

| Evidence | Result |
| --- | --- |
| Total serialized compiler invocations |112 =108 expected PASS +4 rejected development attempts |
| Retained source units |42/42 immediate guarded commits;6 changed Idris files |
| Final frozen plan |65/65 expected results:58positive/7named negative |
| Inherited main-tree coverage |ALL59 inherited targets +6 changed; exclusions[] |
| Positive freshness |Each source check owns its Building line; package is seeded --build |
| Negative authentication |Nonzero exit + prescribed diagnostic and symbol; not positive proofs |
| Mutations / interruptions / exhausted3/3 |0 /0 /0 (B6 passed attempt3, no fourth attempt) |
| Seeded package |PASS;207/207 TTC retained, no cold rebuild/deletion |
| Unchanged LocalDiamond |V2 fresh PASS490.233s; source SHA256 `f77f66a3e3a62f2ff757709f08d1488a25d54d425af74dcec4c2c0f0ed28c6fd` |
| Largest retained RSS sample |50,598,096KiB =48.254105GiB at V2, below52GiB |
| Resources |All11 known/observed-heavy checks acquired/released shared lock;0 stale cleanups |
| Other checks |48GiB guard; nine very short checks had no live RSS sample, not zero actual memory |
| Evidence-contract unit tests |12/12 PASS, last run after all compiler validation |
| Final plan window |2026-09-09T03:09:52Z—03:32:15Z; before every cutoff |
| Independent source/receipt/monitor audit |PASS at21269c8e; all112 records,42 receipts,65 final sources authenticated |
| Main tree at pre-publication gate |Clean tracked tree, baseline-only untracked, no staged files or own compiler |

Rejected compiler snapshots are A15-1 (missing direct RenamingComposition import),
B3-1 (implicit error index), B6-1 (missing direct effect-cut defining import),
B6-2 (wrong ordered-table equality lambda arity). They are archived verbatim,
never committed as proofs. No successful proof retry exception is used.

## Frozen capital / semantic limits

- `src/` and `dgamma.ipkg` diff vs34b21c9 is EMPTY.
- CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0` retained.
- LocalDiamond, CanonicalSort, DeletionChain, CrossTrace, RenamingComposition,
  O19 surface and inherited baseline validation source bytes remain unchanged.
- A11 manifest SHA256 `b391c8bc6d5e4400266af7bff67cd88133da1082b9baa788169e5f6d815e5382`
  authenticates the approved fourth field, all first-three fields and O21.
- `adjacentSwapSuffixSpike`1470-byte full SHA256
  `2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf`;
  1154-byte statement SHA256
  `3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf`.
- Census4 = CanonicalSort1 / CrossTrace2 / DeletionChain0 / LocalDiamond0 /
  RenamingComposition1. No new named hole, unsafe/partial/postulate escape.
- Neither the generic-root necessity witness nor the strengthened ORIGINAL
  rebasing obstruction is an independently authenticated canonical counterexample.
- Whole actual canonical/replayed stage alignment/history fold, producer-owned
  root law, exact all-name canonical endpoint cut/absence/remainder and D5
  producer remain open. Full original vestigial evidence is SELECTED/RETAINED
  from accepted CurrentEndpointRenaming, not conjured from history alone.
- No lane WORKTREE operation or lane-owned source edit occurred. Only inherited
  MAIN-tree baseline variants were checked, not ongoing lane-created results.
  A pinned L2R3 AUDIT was read from MAIN Git objects for D findings.
- Relevant paper lines2170–2399 were re-inspected; no full-rereading attestation.

## Committed evidence and reproduction

- [Audit](O6-R195-GRIND-SHIFT-AUDIT.md), [findings](O6-R195-FINDINGS.md),
  [micro-unit receipts](O6-R195-MICRO-UNITS.md).
- [Frozen plan](O6-R195-FINAL-VALIDATION-PLAN.json),
  [scope](O6-R195-FINAL-VALIDATION-SCOPE.json), [frozen audit](O6-R195-FROZEN-AUDIT.json).
- [Independent report](O6-R195-INDEPENDENT-REPORT.json),
  [resource audit](O6-R195-RESOURCE-AUDIT.json).
- [Compiler ledger](O6-R195-COMPILER-LEDGER.json),
  [raw evidence archive](O6-R195-COMPILER-EVIDENCE.tar.gz).
- Archive SHA256 `1b726f8fbdab952195f95b8d3936c0abbae9f5b9acd07446701c40a8f634544e`.
- [R196 root contract](O6-R195-ROOT-CONTRACT-MANIFEST.md),
  [244-module cost inventory](O6-R195-ROOT-CONTRACT-COSTS.json). The latter is NOT
  a runnable suite:182 direct costs unknown; legacy R11 and diagnostic-unclassified
  fixtures are explicitly not automatically runnable.

The archive retains112 raw JSON/log/source triples, monitor samples, append-only
ledger/receipts, source-cap ruling and read-only inspections/audits. The normalized
ledger reauthenticates each triple and source-commit matching; immediate-commit
claims are separately receipt-verified. Its anchor precedes its own publication
commit. Archive-generation stdout, its own artifact receipt and later gate notes
are NOT self-referentially certified. No withdrawn or superseded final plan.

Read-only review commands (after unpacking the archive into `/tmp/dgamma-r195`
if necessary; do not rerun a compiler or overwrite an existing evidence directory):

```text
python3 -B -I research-tests/run-r195-frozen-audit.py
python3 -B -I research-tests/run-r195-independent-verify.py
python3 -B -I research-tests/run-r195-resource-audit.py
python3 -B -I -m unittest discover -v -s research-tests -p test_r195_evidence_contract.py
shasum -a 256 research-tests/O6-R195-COMPILER-EVIDENCE.tar.gz
git diff --check
git diff --cached --name-only
```

Fresh final compilation was the DETACHED `run-r195-final-validation.py` supervisor
with immutable65-slot plan and per-target detached guards, not an unmonitored
foreground build. Do not automatically rerun it as part of read-only acceptance.

Independent acceptance review is parent-owned/required and pending, not claimed
by this worker's audit. Final owner gate follows the committed publication.

## Final-gate addendum (D3, artifact only)

Supervisor independently verified and RATIFIEDd7b2fc98 as checked PARTIAL;
permitted this gate note and clean close. Full verbatim ruling is in NOTES and
the shift audit. Post-publication frozen/independent read-only audits passed
atd7b2fc98 before the gate. No further Idris/source/compiler work followed it.
Independent reviewer is parent-owned/launched/pending, not self-certified here.
The raw archive is NOT regenerated for this note or given self-referential
receipt claims. Source freeze3bd99171 and all65 final checks remain unchanged.
