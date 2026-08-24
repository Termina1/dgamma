# Theorem 73 (Confluence) — CP5 proof plan, revision 14 O4 alignment repair

Branch: `cp5-thm73-scoping`

Review trail:

- rounds 1–10: REJECT;
- round 11: accepted the frozen 32-hole scoping interfaces;
- grind shifts 1–9 filled six holes and retired one audited false/orphan generic
  composition declaration;
- revision 12 accepted that retirement after scoped fresh-context review;
- revision 13 authorized only the O3 dictionary-alignment repair audited below;
- grind shifts 15–17 supplied that repair and constructively closed O3, leaving
  24 holes;
- the scoped revision-13 review accepted O3 with two bookkeeping changes, closed
  at `91118c7` and `3ead7d0`; and
- revision 14 authorizes only the O4 dictionary-alignment repair audited below.

This is still research-only interface scoping. Every file under `src/`,
`dgamma.ipkg`, the immutable CP3 `confluenceTheorem`, and the accepted production
module graph remain unchanged. Hole-bearing modules under `research/DGamma/`
remain excluded from the package.

### Revision 13: O3 dictionary alignment

`research-tests/O3-DICTIONARY-COHERENCE-AUDIT.md` traces the genuine adjacent-swap,
sorting, and O19 consumers and shows that their `ReplayInvariantBundle` already
carries literal `AlignedTransitions ... nameEq keyEq` evidence. Revision 13 adds
to `activationActivationDiamondSpike` only the erased source-pair and singleton
`earlyRight` alignment premises that those producers supply definitionally. O3
is closed, and `review-cp5-r13-scoped.md` accepted the repair and proof with two
minor bookkeeping changes; both are now closed.

### Revision 14: O4 dictionary alignment

`research-tests/O4-DICTIONARY-COHERENCE-AUDIT.md` reproduces the same executable
`DecEq` mismatch for the A/O and O/A bodies, traces the exact O6/O17/O19
consumers, and shows that their replay bundles supply the pair alignment. A
checked early O/A activation supplies its singleton alignment definitionally.
Revision 14 therefore adds only:

- one erased source-pair `AlignedTransitions` premise to A/O; and
- that same erased source-pair premise plus one erased singleton `earlyRight`
  premise to O/A.

The O4-specific aligned producer and independent-dictionary negative are tracked.
No O/O declaration, raw dictionary equality, caller-selected map, transition, or
evaluator output is authorized. Scoped adversarial review of this delta is
deferred until both O4 holes close.

## Executive estimate

The post-retirement provisional budget is **148–249 engineering shifts**:
Phase A closed in 9 grind shifts, and phases B–H retain a **139–240** remaining
band. Revision 10's 129–226 is withdrawn. The increase charges complete O6
ordinal semantics, O9 retained-subsequence certificate construction,
downstream certificate threading through O16/O20, the still-unproved reachable
repeated-Iter producer, and the still-unproved concrete O16 example. Revision 13
did not change this phase band. O3 subsequently closed in two proof shifts after
the alignment-repair shift, within the accepted revised remainder.

Mandatory re-estimation gates:

1. the first proved `adjacentSwapOperationalOccurrenceFoldSpike` body, including
   repeated identical prefix actions;
2. the first proved O9 `DeletionOperationalOccurrenceCertificate` from all three
   immutable `GenerationActionSubsequence` values;
3. the first reachable repeated-Iter 2×2 execution;
4. the first concrete O16 two-birth/one-withdrawal trace; and
5. the first accepted-correspondence same-name scanner proof for concrete births
   6/18 and 9/14.

No proof grind is authorized before external ACCEPT and explicit user approval
of the current budget.

## 1. Claims-evidence discipline

Two consecutive revisions overstated temporary or generic artifacts. Revision
11 uses this hard rule:

> Every plan sentence asserting tracked, committed, constructed, retained, or
> passing evidence names a file present at the target commit and rechecked by
> `research-tests/run-r11-suite.sh` or a stated release command.

Generic repackaging is called repackaging. A type-level constructor wrapper is
not called a concrete fixture. Temporary `/tmp` diagnostics are never counted as
release evidence.

The final gate must state that a tracked-claims audit was run at HEAD.

## 2. O6 exhaustive adjacent-swap ordinal certificate

### 2.1 One indexed four-region relation

`AdjacentSwapOrdinalRelation prefixCount targetOrdinal sourceOrdinal` has exactly
four constructors:

- `AdjacentPrefixOrdinal`: `targetOrdinal < prefixCount`, source equals target;
- `AdjacentMovedRightOrdinal`: target `prefixCount`, source `S prefixCount`;
- `AdjacentMovedLeftOrdinal`: target `S prefixCount`, source `prefixCount`; and
- `AdjacentSuffixOrdinal`: target at least `prefixCount + 2`, source equals
  target.

Thus untouched prefix and suffix occurrences preserve absolute ordinal, while
the moved pair exchanges the two adjacent source positions.

`adjacentSwapOrdinalExhaustive` is a complete recursive classifier for every Nat
target ordinal. Pairwise disjointness is checked by:

- `adjacentPrefixNotMovedRight`;
- `adjacentPrefixNotMovedLeft`;
- `adjacentPrefixNotSuffix`;
- `adjacentMovedRightNotSuffix`; and
- `adjacentMovedLeftNotSuffix`.

These functions are complete, hole-free research definitions in
`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr`.

### 2.2 Fold contract

`AdjacentSwapOperationalOccurrenceFold` now carries one exhaustive field:

```text
operationalOrdinalRelation :
  (occurrence : LocatedActionOccurrence action swappedTrace) ->
  AdjacentSwapOrdinalRelation
    (transitionCount prefixTrace)
    (locatedActionOrdinal occurrence)
    (locatedActionOrdinal
      (replayActionOrigin operationalOccurrenceCorrespondence occurrence))
```

The previous three partial laws were removed. Every target occurrence,
regardless of action/tag equality, is classified. Generated/action coherence
remains inside `ActionRegistrationReplayCorrespondence`.

`AdjacentSwapResult` still has no map field. Its public map is the projection of
`adjacentSwapOperationalOccurrenceFoldSpike` at the exact decomposition.

### 2.3 Tracked malicious-prefix evidence

Tracked `research-tests/DGamma/R11AdjacentPrefixMalicePositive.idr` proves:

- `adjacentPrefixRelationForcesIdentity`;
- `repeatedPrefixCollapseRejected`; and
- `repeatedPrefixPermutationRejected`.

The latter two quantify two occurrences of the same action with equal transition
tags, so repeated Iter-style prefix nodes are covered explicitly.

Tracked expected-failure
`R11AdjacentPrefixCollapsedCertificateNegative.idr` attempts to inhabit a strict
prefix relation with a distinct source ordinal and fails at the relation index.

Existing tracked `R10AdjacentSwapMapCloneNegative.idr` separately retains the
constructor-projection substitution boundary.

## 3. O9 operational deletion certificate

### 3.1 Executable subsequence ordinal fold

`generationSubsequenceSourceOrdinal` recursively evaluates the exact immutable
`GenerationActionSubsequence`:

- end returns `Nothing`;
- keep at survivor ordinal zero returns source zero;
- keep later increments both ordinals; and
- delete increments only the source ordinal.

No caller-selected embedding function is stored.

### 3.2 Full before/episode/after embedding

`DeletionSurvivingOrdinalEmbedding result survivingOrdinal originalOrdinal` has
three constructors tied directly to:

- `beforeDeletion result`;
- `episodeDeletion result`; and
- `afterDeletion result`.

Each constructor requires the exact executable subsequence computation to equal
`Just originalOrdinal`. Episode and after constructors add exact source and
survivor segment offsets using the immutable deletion result.

### 3.3 Certificate and step seal

`DeletionOperationalOccurrenceCertificate` contains:

- `deletionOperationalCorrespondence`; and
- for every located survivor occurrence, a
  `DeletionSurvivingOrdinalEmbedding` between its target ordinal and the ordinal
  of its actual replay origin.

The generic correspondence continues to provide action/tag and generated/action
coherence. The new embedding supplies the missing operational source-position
authority.

`deletionStepOperationalOccurrenceFoldSpike` now returns this certificate, not a
bare correspondence. `DeletionChainStep` equality-seals its runtime map to
`deletionOperationalCorrespondence` projected from that exact certificate.
Recursive reductions and sorting continue to consume only this sealed map.

### 3.4 Tracked O9 evidence

Tracked files:

- `R11DeletionCertificateProjectionPositive.idr` checks the runtime projection
  and per-survivor embedding consumer;
- `R11DeletionFillerMapCertificateNegative.idr` shows a filler coherent map plus
  `Refl` cannot supply retained-subsequence evidence;
- `R11DirectDeletionStepCloneNegative.idr` reconstructs the full step while
  replacing only the runtime map and fails at the erased certificate equality;
- `R10ReductionMapCloneNegative.idr` rejects recursive reduction-map
  replacement; and
- `R10SortedMapCloneNegative.idr` rejects sorting-map replacement.

## 4. Per-derivation authority, not path independence

Revision 11 does **not** add a path-independence theorem equating occurrence maps
from different valid deletion/sorting derivations.

This is deliberate and sufficient for the current immutable Confluence
statement:

1. each selected derivation carries a complete operational certificate;
2. O16 authenticates its CP3 tree against that exact selected derivation;
3. O18 seals the schedule and occurrence map to that same producer chain; and
4. O20 consumes the left and right selected capitals separately and compares
   accepted generations through their own authenticated maps.

The theorem is existential in the produced convergence schedules. It does not
require two alternative canonicalization algorithms to expose definitionally or
propositionally equal occurrence maps. If a later runtime API demands canonical
algorithm independence, that is a separate theorem and budget, not a hidden O20
premise.

Phase F/G still charge proof work needed to thread each per-derivation certificate
through O16/O20.

## 5. Origin-plan calibration option (a): generic repackager

Revision 11 chooses the permitted honest option **(a)**.

The tracked module is renamed to:

```text
research-tests/DGamma/R11GenericRawPlanRepackagerPositive.idr
```

Its main input is renamed `SuppliedOriginPlanIngredients`. The module explicitly
discloses that each step accepts:

- a threaded `prefixOccurrences` correspondence;
- both source-origin equations; and
- a prebuilt recursive supplied tail.

The module constructs target records from those premises, but does not prove or
construct the premises themselves. Its 1×1, 2×1, and 2×2 exports are named
`repackage...`, not fixtures.

The separate tracked
`R10ActorBlockDecompositionFixturesPositive.idr` remains accurately described:
it constructs decomposition records and proves finite range disjointness
internally from supplied exact geometry. It is not evidence for the missing
origin equations.

A reachable repeated-Iter 2×2 execution remains an explicit phase-B gate.

## 6. Tracked authenticity suite coverage

The omissions identified in round 10 are repaired by tracked files:

- generated-only retarget:
  `R11GeneratedOnlyRetargetNegative.idr`;
- tree/schedule-only capital clone:
  `R11TreeOnlyCapitalCloneNegative.idr`;
- direct deletion-step constructor clone:
  `R11DirectDeletionStepCloneNegative.idr`;
- producer-reassembly coherent-map attack:
  `R11CoherentBothHalvesAssemblyPositive.idr` and
  `R11CoherentBothHalvesAssemblyNegative.idr`; and
- dedicated bridge accepted-generation attack:
  `R11BridgeWrongGenerationNegative.idr`.

The producer-reassembly positive proves an arbitrary coherent map cannot affect
O18 output; the paired negative tries to make it the actual assembled output.

The weaker earlier projection negatives remain tracked as separate regression
boundaries; they are not described as direct constructor attacks.

## 7. Reproducible suite with exact diagnostics

The authoritative runner is:

```text
research-tests/run-r11-suite.sh
```

It runs serially:

- five research spikes;
- 29 tracked positive modules; and
- 28 tracked expected-failure modules.

All 57 tracked Idris test modules occur exactly once. Every negative specification
contains its own mandatory diagnostic substring and source declaration name. A
generic dependent error no longer suffices.

The tracked front covers source certificates, malicious prefixes, deletion
subsequence authority, generated-only/tree-only/producer assembly attacks,
bridge generation, pollution, detachment, scanner orders/generation, static
variants, O/A application, occurrence folds, vestigial assembly, deletion
boundaries, threading, outer schedules, Cartesian boundaries, and the full
pipeline.

## 8. O16 status

The honest round-10 withdrawal is retained unchanged:

- `AbstractTwoBirthOneWithdrawalAssembly` is an abstract hard-premise assembler;
- no concrete two-birth/one-withdrawal producer is claimed; and
- concrete O16 remains an XL gate charged in phase F.

## 9. Producer/consumer pipeline

| Producer | Exact authority | Consumer |
|---|---|---|
| O6 ordinal certificate | exhaustive prefix/moved/suffix relation | adjacent result |
| finite adjacent derivation | composition of O6-certified maps | O17 sorting |
| O9 deletion certificate | exact three-subsequence survivor embedding | O10 |
| O10 derivation | composition of O9-certified maps | O11 reduction |
| O17 sorting | per-derivation certified map | O16/O18 |
| O16 | tree authenticated to exact selected derivation | O18 |
| O18 | schedule/map sealed to exact chain | O19/O20/O21 |
| O20 | two per-derivation authenticated capitals | O21 |
| O21 | vestigial endpoint equivalence | O22 |
| O22 | immutable `ConfluenceResult` | theorem statement |

### O1 generic-composition retirement

The audit in `research-tests/O1-INTERFACE-REPAIR-AUDIT.md` found no producer of
two adjacent raw modulo-vestigial endpoint relations and no consumer of their
generic composed result. The immutable theorem chain is heterogeneous and is
already sealed at `replayedCanonicalToOriginalEndpointSpike` (O21): it composes
the two canonical endpoint relations, the relational replay endpoint, and the
exact replay-to-right bridge under the single accepted outer registration/current
capital. Therefore the false, orphan generic pairwise-transitivity declaration
was retired. Proven generation/name/scanner composition helpers remain checked
research capital; no CP3 production declaration changed.

## 10. Obligations and status

There remain **23 obligations**.

| ID | Obligation | Status | Grade |
|---|---|---|---|
| **O1** | External/replay/endpoint/generation and coherent occurrence algebra. | **Complete after authorized retirement of the false/orphan generic endpoint-transitivity claim; pure composition helpers retained.** | **9 grind shifts actual for Phase A with O2.** |
| **O2** | Transport both independence fields. | **Complete.** | **M–L.** |
| **O3** | A/A diamonds. | **Complete: the aligned producer drives checked crossed transitions, framed iterator outcomes, exact replacement controls, and `LocalRelationalDiamond`; scoped revision-13 review accepted with both minors closed.** | **Closed in shifts 15–17.** |
| **O4** | A/O and O/A licensing/applicability. | **1 hole: O/A is constructively proved; A/O remains. Revision-14 alignment premises are producer-probed.** | **XL gate.** |
| **O5** | O/O freshness/generation discipline. | **1 hole.** | **XL gate.** |
| **O6** | Exhaustive adjacent occurrence fold, suffix replay, whole block. | **3 holes**; certificate/interface complete. | **XL gate.** |
| **O7** | Complete closing scan. | **1 hole.** | **L–XL.** |
| **O8** | Maximal candidate. | **1 hole.** | **XL.** |
| **O9** | Operational deletion certificate and enriched D72. | **2 holes**; certificate/interface complete. | **XL gate.** |
| **O10** | Recursive deletion derivation. | **1 hole.** | **L–XL.** |
| **O11** | Cumulative endpoint/history/accounting. | **1 hole.** | **XL.** |
| **O12** | Closing-free open-block shape. | **1 hole.** | **L–XL.** |
| **O13** | Reached-state/Lemma-68/70 projections. | **Complete.** | **S–M.** |
| **O14** | Duplicate-free ordering. | **1 hole.** | **M–L.** |
| **O15** | Minimal support bridge. | **1 hole.** | **L–XL.** |
| **O16** | Concrete fold accounting/authentication. | **1 hole; concrete fixture absent.** | **XL gate.** |
| **O17** | Derivation-carrying sorting. | **1 hole.** | **XL.** |
| **O18** | Assemble sealed capital. | **1 hole.** | **M–L.** |
| **O19** | Renamed matching and safe selector. | **2 holes.** | **XL gate.** |
| **O20** | Aggregate certified folds and bridge. | **1 hole.** | **XL.** |
| **O21** | Scanner inductions and vestigial composition. | **3 holes.** | **XL gate.** |
| **O22** | Build immutable result. | **Complete.** | **S.** |
| **O23** | Tracked adversarial validation/release isolation. | **Tracked runner.** | **M–L.** |

## 11. Exact hole reconciliation

After authorized retirement of the orphan O1 declaration, constructive O3
closure, and the proved O/A half of O4, **23 deliberate named research holes
remain**:

- canonical sort: 6;
- cross-trace: 4;
- deletion chain: 8;
- local diamonds: 4;
- renaming/O21: 1.

No hole was moved or renamed. Four O1 relation-law bodies and both O2
replay-independence transport bodies were filled in place; the remaining O1 hole
was retired only after the producer/consumer audit and decomposition gate proved
that its generic result was orphaned and its premise was not producer-suppliable.

Forward/reverse map:

- O1=0, O2=0, O3=0, O4=1, O5=1, O6=3;
- O7=1, O8=1, O9=2, O10=1, O11=1, O12=1;
- O13=0, O14=1, O15=1, O16=1, O17=1, O18=1;
- O19=2, O20=1, O21=3, O22=0, O23=0.

The values sum to 23.

## 12. Post-retirement phase arithmetic: 148–249 total, 139–240 remaining

| Phase | Obligations | Raw band |
|---|---|---:|
| A — occurrence algebra and independence | O1–O2 | 9–9 |
| B — diamonds, exhaustive O6 certificate, reachable whole replay | O3–O6 | 32–55 |
| C — scan, selection, O9 retained-subsequence certificate | O7–O9 | 15–26 |
| D — recursive certified deletion/accounting | O10–O11 | 14–27 |
| E — shape/support/minimal bridge | O12–O15 | 7–13 |
| F — concrete O16, certified sorting, sealed capital | O16–O18 | 27–47 |
| G — matching, per-derivation O20 bridge, scanners/O21 | O19–O21 | 39–64 |
| H — outer theorem and exact validation | O22–O23 | 5–8 |

The rows sum exactly to **148–249** including Phase A's actual 9 shifts. The
uncompleted B–H rows sum to **139–240**. No overlap deduction is applied. The
mandatory one-round retirement review is reported separately rather than hidden
inside a proof-phase band.

## 13. Round-10 finding closure

| Finding | Revision-11 resolution |
|---:|---|
| **1 blocker — O6 prefix gap** | One exhaustive four-region relation for every occurrence; total classifier and pairwise disjointness; repeated-prefix collapse/permutation tests tracked. |
| **2 blocker — O9 bare map** | Exact executable subsequence ordinal fold and three-segment survivor certificate; step seals to certificate projection; filler negative tracked. |
| **3 major — fake raw fixtures** | Option (a): module/type/exports renamed as supplied-plan repackager; map/equations/tail explicitly disclosed; no fixture claim. |
| **4 major — omitted retained tests** | Five missing authenticity fronts are tracked and included in runner. |
| **5 minor — generic diagnostics** | Per-module diagnostic substring and declaration symbol required. |

## 14. Eight exact round-11 changes

| # | Required change | Resolution |
|---:|---|---|
| 1 | Complete O6 ordinal contract | Exhaustive indexed relation, total classifier, pairwise disjointness. |
| 2 | Malicious prefix probes | Same-action/same-tag collapse and permutation rejection plus expected failure. |
| 3 | Operational O9 certificate | Exact before/episode/after subsequence computation and per-occurrence embedding. |
| 4 | O9 under-specification negatives | Filler-map and direct full-constructor clone tracked; downstream attacks retained. |
| 5 | Honest origin calibration | Option (a), renamed generic repackager and disclosed supplied capital. |
| 6 | Repair suite coverage/diagnostics | Missing tests tracked; runner upgraded to exact per-module expectations. |
| 7 | Reconcile/estimate/path coherence | 23 holes remain after audited O1 retirement, O3 closure, and O/A closure; phase bands remain planning bounds; per-derivation authority rationale explicit. |
| 8 | Release closure | Serial suite, scans, immutable production, seeded 207/207, best-effort unseeded, clean index required. |

## 15. Release boundary

The deferred scoped revision-14/O4 closure review must verify only tracked HEAD
artifacts:

- the O4 interface delta is exactly the three authorized erased
  `AlignedTransitions` premise occurrences;
- those premises are constructible at the actual O6, O17, O19, and immutable
  statement-input consumer boundaries;
- the tracked R14 positive producer probe succeeds and its independent-dictionary
  negative fails at the intended dictionary-index mismatch;
- both closed O4 bodies genuinely consume alignment, checked execution,
  independence, licensing/applicability exclusions, effects, and ordered controls
  without escape hatches or surviving-hole dependencies;
- exact 57-module runner coverage with module-specific negative diagnostics;
- exact current 6/4/8/4/1 hole split and 148–249 total / 139–240
  implementation-remaining arithmetic;
- all five spikes and every tracked test serially;
- exact CP3 blob and empty `src/`/package diff;
- research isolation and empty escape scans;
- seeded exact 207/207 build and best-effort unseeded result; and
- no tracked/staged changes.

Theorem 73 remains unproved by design after constructive O3 and O/A closure;
the other 23 named obligations remain isolated in research modules.
