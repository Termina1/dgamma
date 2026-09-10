# R193 independent verification

**Owner-ratified checked partial milestone at dd8fb9e9; independent reviewer pending.** No Theorem73
completion or protected convergence-body attempt is claimed.

- Source freeze: `ad77399f55d8bc935e0f26714f532370da4aa918`.
- Read-only evidence anchor: `20fbd8e76b4f42f51b028c33db2496f09a5105c4`.
- **115 retained declarations /115 authenticated source commits**, A30/D10/E75.
- **52 effective final checks:45 positives /7 expected negatives**, completed
  2026-09-08T23:27:55Z; all13 changed Idris targets have their own fresh check.
- 53 raw final invocations;178 checking/build invocations overall,168 matched
  outcomes /10 non-PASS (9 rejected proof attempts and1 resource interruption).
- Eight noncompiler continuation-gate regression tests PASS. No exhausted unit.

## Resource exception: original failure retained

Original V2 LocalDiamond auto-stopped at50,461,760KiB (48.12408GiB) under48GiB;
exit-15, freshfalse, interrupted, non-PASS. The supervisor approved exactly one
append-only unchanged-source retry under52GiB. Its source hash is pinned to
both the original plan and baseline77a9efe1. V2R1 PASS/fresh/exit0 in491.214s,
sampled50,480,768KiB (48.14221GiB). The heavy lock covered the whole retry.
Every other check retained48GiB; no third retry or source edit occurred.
The original plan and failed V2 record remain byte-authenticated, never rewritten.

RSS values are1s samples, not OS high-water marks. A zero records no captured
live sample, not zero memory usage; exact affected units are in the ledger's
monitoring qualifications. No cold build or TTC deletion occurred. Package
freshness means successful seeded --build; Idris source checks require their
own fresh Building line.

## Frozen invariants

Read-only frozen audit PASS: `src/` and `dgamma.ipkg` byte-identical to34b21c9;
CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`; LocalDiamond diff versus
77a9efe1 empty; O19 and all five protected spike bodies/statements unchanged.
Hole census **4=1/2/0/0/1**. All207 package TTC seeds retained/refreshed.
No new hole, unsafe escape hatch, partial, with, local let, forbidden binder,
frozen deletion-body call, or scoped-to-raw cast. No main compiler/staged files.
Only pre-existing `paper/` and `review-o6-body-adversarial.md` remain untracked.
The immutable review file's hash is preserved.

## Remaining semantic obligations

A(i): local history transport/successors are proved; arbitrary paired
initial-to-final history-cut production, occurrence-owned insertion-stamp
transport, all-name endpoint rebasing and vestigial remainder handling are open.

A(ii): actual role completeness is unilateral; native Iter/Finish extractors
are separate. Whole paired canonical alignment/extraction and callback-success
wiring remain open.

A(iii): a producer-owned final bridge remains missing. D5 consumes an all-name
cut; it is not the bridge producer. `canonicalSchedulesConvergeSpike` is untouched.

D: enumeration and conditional whole search are proved; whole native block
frames use frozen ActorLifecycleOnly, not lane2's extended grammar. Two physical
reference-component attachments, four own-cut safety clauses and whole stopped
order equality are not generally produced. Main consumes actual gap0.

Fixtures are scoped honestly: the present-vestigial fixture supplies full
same-inputs history data but no independent canonical schedules; the nonempty
resolver fixture uses physical host data, not original registration history.
The premature20-call paper-reading claim is preserved/withdrawn, followed by
an actual36-call fully visible reread of all3882 content lines.

## Lane2

See [versioned copied inventory and qualifications](O6-R193-LANE2-INTEGRATION.md).
L2R1 artifact98634230 reports35 retained /15 final checks, with its C9 active
source mutation, preflight and RSS caveats preserved. It is not a certificate
for ongoing L2R2 sources. No lane2 source merge or main build of the copies
occurred; main baseline B/C checks certify main baseline only.

## Committed evidence and reproduction

- [Audit](O6-R193-GRIND-SHIFT-AUDIT.md).
- [Immutable52-slot plan](O6-R193-FINAL-VALIDATION-PLAN.json).
- [One authorized substitution and verbatim ruling](O6-R193-FINAL-VALIDATION-CONTINUATION.json).
- [Independent report](O6-R193-INDEPENDENT-VERIFICATION.json).
- [Frozen audit](O6-R193-FROZEN-AUDIT.json).
- [Compiler ledger](O6-R193-COMPILER-LEDGER.json).
- [Exact source/log/receipt archive](O6-R193-COMPILER-EVIDENCE.tar.gz).

Archive SHA256: `657344f62451f9fb306dae03d7265da3073b5f856310813835faf3f7fde7a237`.
The archive is anchored before its own artifact commit; it does not claim to
contain the receipt for that self-referential commit. All proof-source receipts
and all178 compiler records are included.

```sh
python3 -B -I -m unittest discover -v -s research-tests -p test_r193_validation_continuation.py
python3 -I research-tests/run-r193-frozen-audit.py
python3 -I research-tests/run-r193-independent-verify.py
```

The tests fall back to the committed archive if temporary evidence is absent.
The read-only audits use /tmp/dgamma-r193; restore that archived directory when
reviewing on another checkout. Do not cold-rebuild or delete TTC seeds.


Owner ruling: ACCEPT-WITH-NOTES for the checked partial milestone, with all
qualifications retained; verbatim in NOTES.md and the audit. No implementation
source or compiler work followed. This artifact-only addendum does not re-label
the independent reviewer as complete or alter the archived evidence anchor.
