# R187 checked capital and exact R188 residuals

## Status

**O19 remains OPEN. O19/O20/O21 body attempts: 0/0/0.** R187's last proof
commit is `af7255ecf55de51794dc1484b68af559f8f786f6` (F14). The cap audit is
`499d8fc1`. A12/B16/C8/D16/E16/F14 allocations are consumed; C includes two
inherited R186 slots and six R187 slots. No further proof allocation was
inferred. R187 retained **80 new top-level declarations**, each with a fresh
exact-source PASS and real guarded source-commit receipt.

Census remains **5 = 1/3/0/0/1** (CanonicalSort/CrossTrace/DeletionChain/
LocalDiamond/RenamingComposition), with zero new holes. O17 stays owner-paused
pending A8; O21 withdrawal work stays parked. No O20/O21 body was attempted.
The paper's Confluence theorem is not thereby closed; production remains
frozen against `34b21c9`, CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`.

## What R187 actually proves

All paths below are `research/DGamma/` and use `%default total` and
`%unbound_implicits off`. Proof specifications are erased; numeric site/pair
calculations and actual finite replay producers remain executable.

| File | Principal checked capital | Status / limit |
|---|---|---|
| `CP5O19PaperBranchCompletenessSpike.idr` | `o19OriginalClasses`, `o19OriginalPaperBranch`, Unloading absorption and original-block no-unload lemmas | **Proved** from actual original blocks/bundle/safety. Installed does NOT imply paper; both old F8 hypotheses are discharged, not assumed. |
| `CP5O19ActualCartesianSpike.idr` | `o19ActualBlockSpines`, `o19CartesianActualBlocks` | **Proved actual entry** with original inputs and uniqueness, no internal classifier/cut/row oracle. |
| `CP5O19OrdinalPlanSpike.idr` | `o19BuildGlobalOriginPlan`, `o19FiniteOrdinalInjective`, `o19IdentityOrdinalMapPoint` | **Proved** whole actual-chain source origins and ALL-action occurrence injectivity, including identical repeated Iter labels. Neither cardinality nor injectivity alone proves pair coverage. |
| `CP5O19CartesianSitePlanSpike.idr` | `o19GlobalPlanSites`, site execution and concatenation | **Proved** actual global list equals numeric execution of actual sites. |
| `CP5O19CartesianWordRowSpike.idr` | `o19BubbleWordRowSites` | **Proved** exact actual arbitrary mixed-row site pattern. |
| `CP5O19CartesianColumnsSpike.idr` | `o19CartesianColumnsSites`, `o19CartesianSourceSpinesSites` | **Proved** exact actual column pattern with actual transition counts. |
| `CP5O19CartesianNumericSpike.idr` | `o19RowSitesPull`, `o19RowOriginPairs`, `o19RowBandsAfter`, `o19NumericColumnGrid`, `o19GridPairsShift` | **Proved** pointwise row rotation at every ordinal, exact mapped row pairs, both next-map bands, full numeric grid equality, independent coordinate shifts. No function-extensionality axiom. |
| `CP5O19ActualCartesianSpike.idr` | `o19CartesianActualBlocksSites`, `o19ActualGlobalGrid`, `o19AdjacentBlockStartCount`, `o19ActualLocalOriginPlan` | **Proved on SAME B3/B13 chain**: actual sites, authenticated right start, global grid equality, then B14's exact offset equation and actual source-local `BlockCrossingOriginPlan`. No offset/plan oracle. |
| `CP5O20LinearExtensionSpike.idr` | `o20SelectOrientedSafeBlocks`, `o20OrientedCannotReverse`, `o20OrientedSupportIncomparable` | **Proved positive selector/orientation**; incomparability assumes both orders linearize the SAME reference state. `Nothing` is not a completeness/canonicality certificate. |

Actual O19 origin positions now use

```text
o19GridPairs Z Z leftBlockCount rightBlockCount
```

The order is descending left coordinates inside each row, then advancing
right-source coordinates. F11 proves the ACTUAL original right-block start
is original left-block start + left-block count from `BlockBefore`'s actual
prefix equation and `safetyBlocksAdjacent`'s empty gap. F12 discharges both
current-map bands from the owning identity producer. F14 derives and consumes
B14's exact shifted-list equality internally to obtain the local plan on
`cursorDerivation (columnCursor (o19CartesianActualBlocks ...))`.

This closes the **offset-equation gap**, not the whole Cartesian certificate.
No unchecked statement was inserted to bridge the difference.

## Exact remaining O19 list, in dependency order

1. **Certify the explicit local grid.** For `o19GridPairs Z Z width height`,
   prove every bounded pair is an `Elem`; every `Elem` has both required
   `LTE (S position) count` bounds; and `UniqueKeys`. These are precisely the
   `everyBlockPairCrossed`, `everyCrossingUsesSelectedBlocks`, and
   `blockCrossingPositionsUnique` fields of `WholeBlockSwapDerivation`.
   Do not substitute product cardinality or all-action ordinal injectivity
   for these proofs. Suggested small dependencies: fixed-row membership /
   bounds / uniqueness, then disjoint right-coordinate column induction.
2. **Nonempty actual chain and WholeBlockSwapDerivation.** Both actual block
   counts are successors. Use the SAME actual-chain product count
   (`o19ActualGlobalOriginProductCount`) to rule out a zero-node derivation;
   construct `NonEmptyFiniteAdjacentSwapDerivation` and its exact forgetful
   equation, retaining the F14 local plan on that SAME chain. Supply
   `blockCrossingNodeCountExact` as well. Do not replace the derivation by an
   equal-length, same-label, or separately replayed chain.
3. **Actually reached installed target blocks and decomposition.** Extract
   the moved right/left Begin/body ranges from the ACTUAL reached trace,
   prove installed episode properties and exact decompositions, transport
   all untouched blocks, and construct `ActorBlockDecomposition` at the
   target order. Reuse actual reached-length and sealed-suffix capital,
   including `CP5O19CartesianLengthSpike.idr`, not source-trace bounds on an
   arbitrary reached trace. Derive the corresponding reached origin-plan
   updates. This reconstruction has not been started.
4. **Same-chain final assembly.** Produce `blockSwapEndpoint`,
   `blockSwapPremises` (the full bundle), and `blockSwapSameExternalInputs`
   for that ACTUAL `blockSwapTrace`; retain source/raw insertion uniqueness
   and generated orchestration matching through the real cursor/derivation.
   Do not conflate an action-label map with occurrence/external
   correspondence. Then assemble `MkOperationalAdjacentBlockSwap` with
   the same whole derivation and reached block decomposition.
5. **Only then O19 body**, fresh 3/3 allocation after committed prerequisites
   and supervisor authorization. Closure would require the fresh census
   **4 = 1/2/0/0/1** and immediate milestone gate. No body budget was consumed
   in R187, and no closure is claimed.

## Remaining O20 / other seams

O20 still needs reached/common-reference-state linearization, selector
completeness, genuine strict descent toward the fixed goal, and operational
reselection after each actual O19 step. A positive safe oriented choice and
same-reference support incomparability do not provide these. No global sorter
or O20 body was produced. Do not start O17 root work, O21 withdrawals, O20/O21
bodies, or G31 from this handoff: each remains subject to its owning gate.

## Evidence and permanent qualifications

- R186 durable repair: `O6-R186-COMPILER-LEDGER.json` and
  `O6-R186-COMPILER-EVIDENCE.tar.gz`; 99 surviving exact invocations, 89 PASS,
  10 non-PASS (three interrupted stalls). Historical commit-time receipts
  are **not recorded**. Byte-matching commits are not invented chronology.
- R187 exact records, transcripts, source snapshots and actual source/artifact
  receipts are in `O6-R187-COMPILER-LEDGER.json` / its named archive. The final
  archive cannot contain its own later artifact-commit receipt; that receipt
  remains live under `/tmp/dgamma-r187/commit-receipts.jsonl` and is reported
  separately at the final gate.
- Unit0's original compiler-free artifact receipt lacks separately named
  unit/attempt/sourceInvocation fields; it is retained honestly. Subsequent
  artifact receipts carry them. D9-1 passed the compiler but its whitespace
  commit guard failed; D9-2 was freshly checked and committed. No fictitious
  receipt was created for D9-1.
- V3 mistyped the LocalDiamond target and checked a newly created EMPTY
  module. Its raw PASS/fresh record is explicitly INVALID validation, not
  counted by `qualifiedPassedCount`. The checker now rejects missing/empty
  targets before touch or compiler launch; its compiler-free guard test
  passed. V4 freshly checked the REAL frozen
  `CP5ConfluenceLocalDiamondSpike.idr`: PASS, 491.17 s, 49,771,216 KiB sampled
  peak below the 50,331,648 KiB guard. Frozen-source warnings are retained.
- Exactly the two spurious `CP5LocalDiamondSpike.ttc/.ttm` build files were
  removed under an explicit supervisor cleanup gate, with exact name / root
  / count assertions and byte/hash backups. The REAL Confluence TTC/TTM and
  all 207 production seeds were retained. These probe backups and cleanup
  receipt are preserved in the archive; no cache/source reset occurred.
- Seeded `idris2 --build dgamma.ipkg` PASS does not imply a forced source
  rebuild. Source checks require the target's actual `Building` line.
- Independent compiler-free verification:
  `python3 -I research-tests/run-r187-verify-evidence.py` authenticates both
  archives, raw records and byte matches; source receipts and one new
  declaration per source commit; serialized invocations/RSS guard; explicit
  V3 exclusion and authorized cleanup backups; production freeze/no staging.

All source checks were serialized detached Python-`-I` runs with the 48 GiB
RSS guard. No `believe_me`, `assert_total`, postulate, partiality, new hole,
`with`, scoped-to-raw cast, or frozen deletion theorem was added or used.
LocalDiamond/protected declarations and the sanctioned O19 safety surface
were not changed. No compatibility/runtime architecture change was made.
