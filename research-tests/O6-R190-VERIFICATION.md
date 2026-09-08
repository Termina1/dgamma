# R190 verification / partial O20 milestone

Branch `cp5-thm73-scoping`; exact start `4c6cfb176251e205d8ee0b98f287adff8e33d2da`.
Source/audit cutoff `8b513696957d8f9114c90893a219ac21430747c7`.
The consolidated artifact commit follows this cutoff with **no Idris delta**.
Idris2 **0.8.0**, seeded checks only, `%default total`, one compiler at a time,
48GiB sampled-process guard. No TTC/build deletion or cold-build claim.

## Outcome and correspondence

- **38 new retained declarations**, in five research modules and one positive
  integration module: A23/24 and B15/16. All40 producer units consumed.
- A24 and B7 exhausted3/3, reverted and supervisor-ratified. No fourth retry.
  B8 was a separately ratified shared-component prerequisite, not a B7 retry.
- Selector: real fixed-goal global rank drop, actual O19 progress, total actual
  reached-state reselection and same-chain operational certificate fold proved.
  `o20RunOperationalSearch` reaches a **blocked** order, not a proved canonical one.
- Convergence: real all-name empty/insert/shared-observation Begin successors,
  exact first-three-clause projection, and actual supported/unsupported birth
  classification proved. Two nonempty insertion/checked-Begin fixtures pass.
- **No O20 body attempted or closed.** Paper Theorem73 remains partial:
  `selectOperationalCanonicalPermutationSpike` and
  `canonicalSchedulesConvergeSpike` retain their original statements/holes.

## Exact remaining obligations (not hidden premises)

Selector: instantiate the supported common reference and goalState/goal
linearization for the inverse-renamed right target; exact actor-set matching;
finite adjacent-inversion availability; success of the ACTUAL full safety
checker; terminal stoppedOrder=goal. Do not reinstate R143-refuted universal
transport of all original-left SupportPaths through withdrawn intermediates.

Convergence: select/align every actual paired cut; general shared-component
observation adapter (B7 wall); whole Begin/Advance/Finish/external/generated-gap
induction maintaining global ordered effects and EVERY raw-name control;
unsupported child's mapped canonical birth and exact original-origin triangle.
`O20UnsupportedBirth` is a real explicit unresolved branch, not impossibility or
an invented fourth-clause proof. Local cut premises are not endpoint oracles.

New proofs are conditional proof-level capital; imported canonical-capital
premises are not magically discharged. All new witnesses are erased; the goal
rank is executable, but no plugin runtime or runtime performance is claimed.
No new hole, unsafe axiom, partiality, let/with, prohibited binding, computed
existential elimination or new Either producer. No O17/O19/O21 or public type
rehome/statement/visibility change. Author review is **not** the independent gate.

## Final validation

All74 final checks passed: **71 positive source checks + 2 expected native
rejections + 1 seeded package build**. All73 source checks have their own exact
Building line and current source hash; package freshness means successful
seeded `--build`, not a forced rebuild of all207 production modules.
Completion: `2026-09-08T14:45:48.775779+00:00` (cutoff16:41:47Z).
Maximum sampled RSS49,831,232KiB <50,331,648KiB (48GiB). No interruption.

| Run | Exact target | Native exit | Seconds | Guard result |
| --- | --- | --- | --- | --- |
| V1 | `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr` | 0 | 492.369 | PASS |
| V2 | `research/DGamma/CP5ConfluenceDeletionChainSpike.idr` | 0 | 77.932 | PASS |
| V3 | `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr` | 0 | 53.984 | PASS |
| V4 | `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr` | 0 | 9.330 | PASS |
| V5 | `research/DGamma/CP5O19SurfaceSpike.idr` | 0 | 5.200 | PASS |
| V6 | `research/DGamma/CP5ConfluenceCrossTraceSpike.idr` | 0 | 6.228 | PASS |
| V60 | `research-tests/DGamma/R6SafetyDetachmentNegative.idr` | 1 | 1.071 | expected rejection PASS |
| V61 | `research-tests/DGamma/R8ZeroDerivationOperationalStepNegative.idr` | 1 | 1.056 | expected rejection PASS |
| V67 | `research/DGamma/CP5O20BlockMeasureSpike.idr` | 0 | 3.115 | PASS |
| V68 | `research/DGamma/CP5O20OperationalProgressSpike.idr` | 0 | 4.160 | PASS |
| V69 | `research/DGamma/CP5O20OperationalDescentSpike.idr` | 0 | 4.171 | PASS |
| V70 | `research/DGamma/CP5O20AllNameSynchronizationSpike.idr` | 0 | 3.125 | PASS |
| V71 | `research/DGamma/CP5O20BirthBridgeRemainderSpike.idr` | 0 | 3.144 | PASS |
| V72 | `research-tests/DGamma/R190O20AllNameSynchronizationPositive.idr` | 0 | 3.145 | PASS |
| V73 | `research-tests/DGamma/R6FourFiberStatic.idr` | 0 | 4.173 | PASS |
| V74 | `package` | 0 | 16.608 | PASS |

The other final checks cover the inherited O19 producer chain and positive
regressions. The complete immutable74-target plan and every raw log/source/JSON
are archived; the ledger lists all commands, timestamps, hashes and source
commits. `prebody` is only the inherited runner phase label: no body followed it.

## Accounting / reproducible evidence

129 exact invocations,114 native exit0 and15 native exit1. Raw guard outcomes
118 passed/11 failed:10 rejected producer attempts and AP1-1's expected-wording
mismatch remain failures. AP1-2/BP1-1 and final V60/V61 are four expected native
rejections counted as guard passes. No historical result is rewritten.

38 source commit receipts authenticate exact-source freshPASS, latest compiler
invocation, one new declaration, no compiler and no staged files. Audit receipts
through8b513696 are also archived. The final artifact commit cannot include its
own receipt in its own archive; it contains no source changes and is re-audited.

- `research-tests/O6-R190-COMPILER-LEDGER.json`
- `research-tests/O6-R190-COMPILER-EVIDENCE.tar.gz`
- `research-tests/O6-R190-GRIND-SHIFT-AUDIT.md`
- `research-tests/O6-R190-O20-DESIGN.md`

Archive SHA256: `56a8684348ce2e525e8a72868f0c028106a6589d56676dcf4453ead2fc3697c5`.
The archive additionally includes author manual review, producer provenance
review, final validation authentication, immutable plan and frozen-source audits.

Commands (all compiler checks launched detached through Python `-I`):

```
python3 -I research-tests/run-r190-final-validation.py prebody
python3 -I research-tests/run-r190-frozen-audit.py /tmp/dgamma-r190/final-frozen.json
python3 -I research-tests/run-r190-archive.py R190 4c6cfb17 8b513696
```

Individual source checks use `run-r190-check.py UNIT PATH`; successful new
units immediately use `run-r190-commit.py`. All exact arguments are in the ledger.
The final plan is embedded in the archive, not silently regenerated for replay.

## Frozen sources / final hashes

Holes unchanged **4 = 1/2/0/0/1** (CanonicalSort/CrossTrace/DeletionChain/
LocalDiamond/RenamingComposition). Production `src/` and `dgamma.ipkg` have an
empty diff versus34b21c9. CP3 blob:
`2c697e532e83989de8591fa6a4378747c6a501c0`.
All5 confluence entry modules and O19 Surface/LocalDiamond byte-identical to start.
207/207 production TTC seeds retained; no unauthorized untracked files.

`adjacentSwapSuffixSpike`:1470-byte full block SHA256
`2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf`;
1154-byte statement SHA256
`3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf`.
Immutable review SHA256
`61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8`.

| New source | Final SHA256 |
| --- | --- |
| `research-tests/DGamma/R190O20AllNameSynchronizationPositive.idr` | `90494b1c7aca187f96212400ae619f5415f4eb1433487da9994918257dc9ee11` |
| `research/DGamma/CP5O20AllNameSynchronizationSpike.idr` | `eb34b80def8d87fb099c8a06d9836d33f27f6faa3bc47ca198c5b79275fdf2dd` |
| `research/DGamma/CP5O20BirthBridgeRemainderSpike.idr` | `8a759194ca994ed430352eaafb738d03c99e0801d73744e0fd6c63c8974d123d` |
| `research/DGamma/CP5O20BlockMeasureSpike.idr` | `868ccd417293ef6672ac9b11c913aa1b06efb07e287b5a085378372aa3e1714e` |
| `research/DGamma/CP5O20OperationalDescentSpike.idr` | `040cfc4785f3155f3016201142f3dbf0ba4a6c95b159cec87fb6ae90e20b7ffb` |
| `research/DGamma/CP5O20OperationalProgressSpike.idr` | `039b1baf2d459ae46d6593cd8571f8abebec6d7f1b1e565d8709218dc25449d8` |

## Status

Checked partial milestone, not Theorem73 closure. All final regressions pass;
A/B quotas and stops respected; no staged files at final source audit. Next
work is the explicit selector completeness and whole-convergence obligations
above, subject to the final supervisor/independent reviewer gate.
