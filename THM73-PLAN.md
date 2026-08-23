# Theorem 73 (Confluence) — CP5 scoping plan, revision 10

Branch: `cp5-thm73-scoping`

Review trail:

- rounds 1–9: REJECT;
- `review-cp5-plan-round9.md`: one provenance-laundering blocker and four
  calibration/reproducibility/estimate majors.

This remains research-only interface scoping. Accepted statements, every file
under `src/`, `dgamma.ipkg`, and `confluenceTheorem` are immutable. Hole-bearing
modules under `research/DGamma/` remain excluded from the package and must not
merge unchanged to `main`.

## Executive estimate

The post-repair provisional budget is **129–226 engineering shifts**. Revision
9's 110–193 is withdrawn. The increase charges occurrence provenance at its
first operational sources, recursive deletion/sorting derivations, the honestly
unresolved concrete O16 fixture, tracked constructor fixtures, and a committed
serial adversarial suite.

Mandatory re-estimation gates remain:

1. the first complete general `operationalAdjacentBlockSwapSpike`, including a
   reachable repeated-Iter 2×2 trace rather than only raw semantic constructor
   materialization;
2. the first complete O7/O8/O9 pipeline and O10/O11 recursive occurrence fold;
3. the first genuinely concrete O16 trace with two generated births and one
   withdrawal; and
4. the first complete accepted-correspondence same-name scanner proof matching
   concrete births 6/18 and 9/14.

No proof grind is authorized before external ACCEPT and user budget approval.

## 1. Round-9 supervision correction

Revision 9 cited temporary `/tmp` modules as if they were release artifacts.
That was incorrect. Revision 10 adopts the following evidence rule:

> A gate claim names only a tracked file at the target commit. Temporary probes
> may be reported as temporary diagnostics, but never as committed calibration.

All retained positive and negative probes now live under `research-tests/`, and
`research-tests/run-r10-suite.sh` runs the complete declared front serially.

The former “nontrivial O16 fixture” claim is explicitly withdrawn. The renamed
`AbstractTwoBirthOneWithdrawalAssembly` remains useful dependent packaging, but
it assumes the hard reduction, sorting, two births, singleton withdrawal, and
ordinary CP3 accounting laws. It is not evidence that O16 is constructible.

## 2. First-source adjacent-swap sealing

### 2.1 Globally fixed fold

`AdjacentSwapResult` no longer stores
`swappedOccurrenceCorrespondence`. Instead:

- `AdjacentSwapOperationalOccurrenceFold` contains the fold map and laws;
- `adjacentSwapOperationalOccurrenceFoldSpike` is the named O6 proof obligation
  applied to the exact original decomposition, moved transitions, replayed
  suffix, swapped trace, and swapped decomposition;
- `swappedOccurrenceFold` applies that globally fixed function to an actual
  result; and
- `swappedOccurrenceCorrespondence` projects
  `operationalOccurrenceCorrespondence` from that fold.

The fold's type pins:

- moved-right's replay origin to the original right ordinal;
- moved-left's replay origin to the original left ordinal; and
- every recursive suffix occurrence to the same absolute source ordinal.

A caller cannot replace both action/generated halves coherently because no map
slot remains in `MkAdjacentSwapResult`.

### 2.2 Checked boundary

Tracked `R10AdjacentSwapMapCloneNegative` asks for equality with an arbitrary
coherent alternate map and fails at:

```text
alternate
vs
(swappedOccurrenceFold result).operationalOccurrenceCorrespondence
```

Tracked `R10ProvenanceProjectionPositive` proves the real projection equation by
`Refl`.

## 3. Deletion provenance

### 3.1 O9 step seal

`deletionStepOperationalOccurrenceFoldSpike` is the named operational deletion
fold for the exact immutable Lemma-72 result. `DeletionChainStep` retains its
runtime occurrence map only with erased equality to that fold:

```text
deletionOccurrenceCorrespondence =
  deletionStepOperationalOccurrenceFoldSpike ... deletionResult
```

Thus a map-only step clone cannot reuse the seal. Tracked
`R10DeletionStepMapCloneNegative` fails before O10 or accounting.

### 3.2 Explicit recursive derivation

`ClosingFreeDeletionDerivation` is an indexed recursive family:

- `ClosingFreeDeletionDone` is identity; and
- `ClosingFreeDeletionStep` carries the actual `DeletionChainStep` and recursive
  survivor derivation.

`closingFreeDeletionOccurrenceFold` composes the sealed O9 maps over this family.
`ClosingFreeTraceCore` and `ClosingFreeReduction` carry explicit derivations;
`coreOccurrenceCorrespondence` and `reductionOccurrenceCorrespondence` are
computed projections, not constructor fields.

Tracked `R10ReductionMapCloneNegative` fails before accounting, while
`coreMapIsRecursiveDeletionFold` and `reductionMapIsRecursiveDeletionFold` are
`Refl` projections.

## 4. Sorting provenance

`SortedClosingFreeTrace` no longer stores an arbitrary occurrence map. It carries
an exact `FiniteAdjacentSwapDerivation original sortedTrace`. The only exported
map is:

```text
sortingOccurrenceCorrespondence sorted =
  finiteDerivationOccurrenceCorrespondence
    (sortingAdjacentDerivation sorted)
```

Every node of that finite derivation contains an actual `AdjacentSwapResult`,
whose map is already sealed at O6. Tracked `R10SortedMapCloneNegative` fails
before CP3 accounting; `sortingMapIsAdjacentDerivationFold` is `Refl`.

`deletionSortingOccurrenceCorrespondence`, O16 accounting, O18 capital, O19,
O20, O21, and the bridge continue to project through these source seals.

## 5. Coherent-both-halves laundering closure

An `ActionRegistrationReplayCorrespondence` may still represent an internally
coherent automorphism in isolation. That algebraic record is intentionally
generic. It acquires operational authority only through a source fold.

The committed rejection chain is:

1. actual adjacent swap: no map field;
2. O9 deletion step: equality to exact deletion fold;
3. O10/O11 reduction: recursive derivation projection;
4. O17 sorting: finite adjacent-derivation projection;
5. O18: exact carried deletion/sorting chain plus runtime schedule seal; and
6. O20 bridge: exact capital projections.

`R10CoherentBothHalvesCapitalNegative` confirms an alternate coherent map cannot
become the O18 output. Retained generated-only, public-schedule, tree-only,
wrong-birth, wrong-generation, wrong-occurrence, wrong-trace, stale/mixed, and
pollution negatives remain in the committed suite.

## 6. O16 fixture status: honestly withdrawn

Revision 10 does **not** claim a concrete two-birth/one-withdrawal fixture.

The renamed research interface is:

- `AbstractTwoBirthOneWithdrawalAssembly`;
- `assembleAbstractTwoBirthOneWithdrawalAssembly`; and
- `abstractTwoBirthOneWithdrawalAccounting`.

It assumes:

- a complete sealed `ClosingFreeReduction`;
- a complete derivation-carrying `SortedClosingFreeTrace`;
- two located generated births;
- exact singleton withdrawal and endpoint equality;
- external-input equality; and
- all `CanonicalReplayAccountingLaws`.

It constructively builds the replay-origin CP3 tree and `Refl` authentication,
but it is only an abstract assembler. A genuinely concrete trace remains O16's
mandatory XL gate and is charged in phase F.

## 7. Tracked origin-plan and coordinate materialization

### 7.1 Raw operational materializer

`R10OperationalOriginPlanFixturesPositive` is tracked. Its
`RawOperationalOriginPlan` stores the semantic inputs of each swap but does not
store an `AdjacentSwapResult`, finite derivation, occurrence map, label, origin
plan, or whole-block record.

`materializeOperationalOriginPlan` recursively constructs:

- `MkAdjacentSwapResult` at every node;
- `FiniteAdjacentSwapStep`;
- `CrossingOriginPlanStep`; and
- the exact recursively composed prefix occurrence maps.

`materializeNonEmptyOperationalOriginPlan` constructs the nonempty head and tail
under one dependent index. `oneByOneWholeFromRaw`, `twoByOneWholeFromRaw`, and
`repeatedIterTwoByTwoWholeFromRaw` then construct
`MkWholeBlockSwapDerivation` through the checked Cartesian wrappers.

`RawPlanIsRepeatedIter` is an executable predicate over the actual raw
transitions. The 2×2 entry requires all four source pairs to be `LAdvance` with
`LIterTag`; it does not accept a prebuilt tag list or label list.

These are tracked constructor-materialization fixtures, not claims that the hard
local-diamond premises are already proved reachable. The first reachable
repeated-Iter fixture remains a mandatory phase-B re-estimation gate.

### 7.2 Decomposition range construction

`R10ActorBlockDecompositionFixturesPositive` constructs
`MkActorBlockDecomposition` for exact 1×1, 2×1, and 2×2 geometries. It accepts
located blocks/order/coverage and exact starts/counts, but **not** a range law.
The four-orientation range function is proved by finite-bound elimination and
exact Nat contradiction inside the module.

The tracked Cartesian wrapper modules construct
`MkWholeBlockSwapDerivation` and prove completeness, soundness, uniqueness, and
node counts for 1×1, 2×1, and 2×2.

Retained tracked coordinate negatives cover shifted starts, equal starts,
one-past-end, literal duplicate positions, alternate identity root, and
zero-node use.

## 8. Reproducible validation suite

`research-tests/run-r10-suite.sh` is the authoritative suite. It:

1. builds `dgamma.ipkg`;
2. checks all five research spikes serially;
3. checks every tracked positive module serially;
4. checks every tracked negative module serially, requiring nonzero status and
   an intended dependent-index diagnostic; and
5. emits `R10_REPRODUCIBLE_SUITE=passed`.

The tracked front covers:

- source-seal projections and map-clone attacks;
- pure/outer pollution;
- safety detachment and generated-child exclusion;
- wrong trace, wrong occurrence, wrong birth, wrong generation;
- stale quotient and mixed capital;
- zero/duplicate/root/coordinate boundaries;
- all scanner orderings and wrong-generation rejection;
- four-fiber and two-intermediate static variants;
- O/A application;
- occurrence and operational occurrence folds;
- vestigial assembly;
- deletion boundaries and operational threading;
- outer schedules; and
- the full producer/consumer pipeline.

No future gate may cite an untracked `/tmp` probe as release calibration.

## 9. Producer/consumer pipeline

| Producer | Exact output | Immediate consumer |
|---|---|---|
| O1 algebra | coherent all-action/generated map algebra | source folds |
| O6 adjacent fold | moved-node/suffix-pinned map | actual swap result |
| Actual swap result | definitionally projected source map | finite sorting derivation |
| O9 deletion fold | sealed one-step deletion map | O10 derivation |
| O10 derivation | recursive composed deletion map | O11 reduction |
| O11 reduction | derivation-projected map | O16/O17/O18 |
| O17 sorting | finite-swap-derived map and ranges | O16/O18/O19 |
| O16 | fold-indexed authenticated accounting | O18 |
| O18 | producer-chain sealed capital | O19/O20/O21 |
| O19 | safe operational permutation | O20 |
| O20 | source-authentic bridge | O21 |
| O21 | vestigial endpoint composition | O22 |
| O22 | original schedules plus equivalence | immutable result |

## 10. Obligations and status

There remain **23 obligations**.

| ID | Obligation | Producer status | Grade |
|---|---|---|---|
| **O1** | External/replay/endpoint/generation and coherent occurrence algebra. | **5 holes**; identity/composition complete. | **L.** |
| **O2** | Transport both `TraceIndependent` fields. | **2 holes.** | **M–L.** |
| **O3** | A/A diamonds. | **1 hole.** | **L–XL.** |
| **O4** | A/O and O/A licensing/applicability. | **2 holes.** | **XL gate.** |
| **O5** | O/O freshness/generation discipline. | **1 hole.** | **XL gate.** |
| **O6** | Local suffix replay, first-source occurrence fold, whole-block producer. | **3 holes**; map seal/materializers complete. | **XL gate.** |
| **O7** | Complete/unique closing scan. | **1 hole.** | **L–XL.** |
| **O8** | Maximal deletable candidate. | **1 hole.** | **XL.** |
| **O9** | Enriched D72 plus exact operational deletion occurrence fold. | **2 holes**; equality seal complete. | **XL.** |
| **O10** | Well-founded recursive deletion derivation. | **1 hole**; fold function complete. | **L–XL.** |
| **O11** | Cumulative endpoint/history/accounting. | **1 hole**; reduction map derived. | **XL.** |
| **O12** | Closing-free open-block shape. | **1 hole.** | **L–XL.** |
| **O13** | Reached-state/Lemma-68/70 projections. | **Complete.** | **S–M.** |
| **O14** | Duplicate-free support ordering. | **1 hole.** | **M–L.** |
| **O15** | Minimal support truth/placement bridge. | **1 hole.** | **L–XL.** |
| **O16** | Concrete fold accounting and authentication. | **1 hole**; only abstract assembler, concrete fixture withdrawn. | **XL gate.** |
| **O17** | Sorting with explicit adjacent derivation and range capital. | **1 hole.** | **XL.** |
| **O18** | Assemble source-sealed producer capital. | **1 hole**; sealing assembler complete. | **M–L.** |
| **O19** | Renamed matching plus safe selector. | **2 holes.** | **XL gate.** |
| **O20** | Aggregate folds and source-authentic bridge. | **1 hole.** | **XL.** |
| **O21** | Scanner inductions and vestigial composition. | **3 holes.** | **XL gate.** |
| **O22** | Build immutable result. | **Complete.** | **S.** |
| **O23** | Committed adversarial validation/release isolation. | **Tracked script/modules.** | **M–L.** |

## 11. Exact hole reconciliation

Revision 10 contains **32 deliberate named research holes**:

- canonical sort: 6;
- cross-trace: 4;
- deletion chain: 11;
- local diamonds: 9;
- renaming/O21: 2.

The two new holes are explicit provenance obligations:

- `adjacentSwapOperationalOccurrenceFoldSpike_rhs` — O6; and
- `deletionStepOperationalOccurrenceFoldSpike_rhs` — O9.

Forward/reverse map:

- O1=5, O2=2, O3=1, O4=2, O5=1, O6=3;
- O7=1, O8=1, O9=2, O10=1, O11=1, O12=1;
- O13=0, O14=1, O15=1, O16=1, O17=1, O18=1;
- O19=2, O20=1, O21=3, O22=0, O23=0.

The values sum to 32.

## 12. Post-repair phase arithmetic: 129–226

| Phase | Obligations | Raw band |
|---|---|---:|
| A — coherent replay/occurrence algebra and independence | O1–O2 | 8–15 |
| B — four orientations, source fold, reachable Cartesian producer | O3–O6 | 27–47 |
| C — scan, selection, enriched D72 and step seal | O7–O9 | 12–21 |
| D — recursive deletion derivation/accounting | O10–O11 | 12–23 |
| E — shape/support/minimal bridge | O12–O15 | 7–13 |
| F — concrete O16, derivation sorting, authentication, O18 | O16–O18 | 23–41 |
| G — safe matching, source-authentic bridge, scanners/O21 | O19–O21 | 36–58 |
| H — outer theorem and committed validation | O22–O23 | 4–8 |

The rows sum exactly to **129–226**. No overlap deduction is applied.

## 13. Round-9 finding closure

| Finding | Revision-10 resolution |
|---:|---|
| **1 blocker — maps replaceable inside producer chain** | Adjacent result has no map field; deletion step is equality-sealed; core/reduction carry recursive derivations; sorting carries finite adjacent derivation; all public maps are projections. |
| **2 major — concrete O16 fixture absent** | Claim explicitly withdrawn; record renamed abstract; O16 remains mandatory XL gate and phase-F charge. |
| **3 major — origin-plan producers absent** | Tracked raw-semantic materializer constructs actual adjacent results, finite nodes, crossing steps, nonempty and whole records; tracked decomposition modules construct range laws for 1×1/2×1/2×2. Reachable repeated-Iter execution remains honestly gated. |
| **4 major — suite absent** | 43 tracked test modules plus serial `run-r10-suite.sh`; temporary artifacts are not cited. |
| **5 major — estimate undercharged** | Exact 32-hole map; A/B/C/D/F/G/H regraded to post-repair 129–226. |

## 14. Eight exact round-10 changes

| # | Required change | Resolution |
|---:|---|---|
| 1 | Seal first operational swap source | No free result map; exact globally fixed fold with moved/suffix ordinal laws; clone negative tracked. |
| 2 | Derive deletion/sorting maps | Recursive deletion family and finite sorting derivation; map clones fail before laws. |
| 3 | Repeat coherent-both-halves laundering | Rejected at actual swap, deletion step/reduction, sorting, and O18; retained bridge negatives tracked. |
| 4 | Concrete O16 or honest withdrawal | Honest withdrawal and abstract rename; no concrete claim. |
| 5 | Ship actual constructor materialization | Tracked raw-semantic 1×1/2×1/repeated-Iter 2×2 result/plan/whole construction and derived range fixtures. |
| 6 | Reproducible full suite | Tracked serial script and modules. |
| 7 | Reconcile/re-estimate | 32 holes; exact 129–226 sum with new work charged. |
| 8 | Release closure | Five spikes, suite, immutable source/CP3, isolation, 207/207, clean tracked/index required. |

## 15. Release boundary

External round-10 review must run only tracked artifacts and verify:

- all source map-clone negatives fail at their intended folds;
- coherent both-halves maps cannot reach O18/bridge outputs;
- source projection positives reduce by `Refl`;
- actual constructor-use search finds adjacent results, crossing steps,
  decomposition range proofs, and whole records in tracked tests;
- O16 concrete calibration is absent and explicitly withdrawn;
- all 43 tracked test modules plus five spikes run serially;
- exact 32-hole reverse map and 129–226 arithmetic;
- exact external production build reaches 207/207;
- `src/`, `dgamma.ipkg`, and CP3 remain byte-identical to baseline; and
- tracked worktree and index are clean.

Theorem 73 remains unproved by design after revision 10.
