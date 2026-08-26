# O6 revision 39 — relational map scoping audit

Status: **SCOPING COMPLETE; DESIGN GATE REQUIRED; NOT LANDED**.

Base: `cp5-thm73-scoping@9793ec9775ecbc10ace3499ad464c4e151448600`.
This revision changes no frozen declaration and does not fill
`adjacentSwapSuffixSpike_rhs`.  The machine-readable proposal is
`research-tests/cp5-r20-proposed-manifest-delta.json`.

## 1. Selected shape

The candidate replacement for exact generator/head map equality is the existing
coeffect relation:

```idris
PartialMapsRelated (EffectStateEquivalence keyEq) sourceMap targetMap
```

It quantifies over *arbitrary related source and target inputs* and returns
matching undefinedness or `EffectStateRelated` defined outputs.  At the public
`RelationalReplayCorrespondence` boundary the field additionally quantifies
`(keyEq : DecEq key)`, avoiding a new record parameter and avoiding any claim
that independently stored dictionaries are equal.

A same-input-only
`PartialMapsEquivalent (EffectStateEquivalence keyEq) sourceMap targetMap` is
rejected.  It is producer-friendly but not closed under transformation
composition: after the first partial map, source and target intermediate states
are only related, not propositionally equal.  `R39RelationalMapAlgebraPositive`
constructs composition and `PartialCommute` transport for the selected stronger
shape.

## 2. Complete affected frozen and derived surface

### 2.1 Frozen fields that change

1. `RelationalReplayCorrespondence.replayGeneratorMapPreserved` becomes
   `replayGeneratorMapsRelated`.  It quantifies a `keyEq`, actor, target
   generator, and arbitrary related inputs.
2. Private `PointwiseRelationalHeadReplay.headReplayMapPreserved` becomes
   `headReplayMapsRelated` under the record's existing `keyEq`.
3. Private `SealedSuffixReplayStep.headMapPreserved` becomes
   `headMapsRelated` under `SealedSuffixReplaySpine`'s existing `keyEq`.

The exact old/new signatures are in the proposed manifest delta.

### 2.2 Derived definitions that change with those fields

- `replayTransformationMapPreserved` is replaced by
  `replayTransformationMapsRelated`; composition uses relational partial-map
  composition rather than rewriting equal intermediate results.
- A relational `PartialCommute` transport is added.  The existing exact
  `replayPartialComposeCong` and `replayPartialCommuteTransport` are **retained**
  because lines 8238 and 8661 use the latter independently in local
  activation/orchestration effect diamonds.
- `replayIteratorStable` consumes relational foreign-map output.  Its stage
  comparison remains the existing exact `replayIteratorOutcomePreserved`, then
  `iteratorStageOutcomeRelated` moves the target stage between related states.
- `traceIndependentAfterRelationalReplaySpike` keeps its public type and changes
  only its implementation.
- `composeRelationalReplayCorrespondence` composes relational map fields.
- Identity RAR constructors use a generic proof that every Definition-54
  generator respects `EffectStateRelated`.
- `singletonNonAdvanceGeneratorMapPreserved` becomes a relational generator-map
  lemma; `singletonNonAdvanceRAR` accepts relational transition-map capital.
- `packagePointwiseRelationalHeadReplay` accepts relational transition-map
  capital.
- `sealPointwiseRelationalHead` copies the relational field definitionally.
- The six existing head producers replace local `mapPreserved : ... = ...`
  bindings with producer-owned relational bindings.  No output-shaped caller
  premise is introduced.
- Future L-Unload and L-Advance heads construct the same relational binding from
  related owner/accumulator/runtime observations.

### 2.3 Explicit non-changes

The following stay frozen:

- all `RelationalReplayCorrespondence` parameters;
- `replayIteratorOutcomePreserved`;
- `ReplayInvariantBundle`, including field 9 `replayIndependent`;
- `TraceIndependent`;
- endpoint, local-diamond, sealed occurrence, and opaque result types;
- `adjacentSwapSuffixSpike`'s 1183-byte declaration/body hole;
- R27's stronger test-local `retainedTargetMapIdentity`;
- production `src/` and `dgamma.ipkg`.

## 3. Every direct consumer of exact RAR map capital

A complete symbol scan has only these direct paths:

1. `replayGeneratorMapPreserved` is consumed by
   `replayTransformationMapPreserved` and
   `composeRelationalReplayCorrespondence`.
2. `replayTransformationMapPreserved` is consumed by:
   - `replayIteratorStable` to identify the source foreign moved state; and
   - both transformation arguments of the generated-monoid commute clause in
     `traceIndependentAfterRelationalReplaySpike`.
3. `traceIndependentAfterRelationalReplaySpike` constructs both fields of
   `TraceIndependent` and is wrapped by
   `traceIndependentAfterDeletionReplaySpike`.
4. Whole-bundle field 9 is projected by:
   - `originalTraceIndependent` from `chainReplayCapital`; and
   - `canonicalTraceIndependent` from `sortedPremises`.
   The bundle itself is reconstructed at the adjacent replay boundary and in
   R16/R23/R29 fixtures; none requires exact proof-bearing map equality as a
   statement.

`R39RelationalIndependenceConsumerPositive` constructs the complete replacement
consumer, including arbitrary transformation composition, generated-monoid
commutation, and Equation-55 iterator stability.  Thus `replayIndependent` is
consumer-closed, not merely stated.

## 4. Every structural carrier / composition consumer

Although most consumers do not project the map field directly, all RAR-bearing
records and recursive chains must rebuild the revised constructor:

- `SealedSuffixReplaySpine.headRAR`;
- `PointwiseRelationalHeadReplay.headReplayRAR`;
- `AdjacentSwapResult.adjacentReplayCorrespondence` and public
  `swappedReplayCorrespondence`;
- `finiteDerivationReplayCorrespondence`;
- `OperationalAdjacentBlockSwap` via `blockSwapReplayCorrespondence`;
- `operationalPermutationReplayCorrespondence`;
- deletion records `DeletionChainStep.deletionReplayCorrespondence`,
  `ClosingFreeTraceCore.coreReplayCorrespondence`, and
  `ClosingFreeReduction.reductionReplayCorrespondence`;
- sorting record `SortedClosingFreeTrace.sortingReplayCorrespondence`;
- `canonicalReplayCorrespondence`;
- the replayed-canonical endpoint bridge in
  `CP5ConfluenceRenamingCompositionSpike`;
- historical/test carriers in R11, R19, R20, and R23.

The identity constructors at `finiteDerivationReplayCorrespondence`,
`OperationalActorDone`, R19 sealed-certificate probes, and suffix-free R19
fixtures are not allowed to use `Refl` as a relational map proof.  They use the
generic all-generator respect theorem.  Composition is checked by
`r39ComposeRelationalReplayCorrespondence`.

## 5. Consumer probes

### 5.1 Transformation and commute algebra

`R39RelationalMapAlgebraPositive` proves:

- exact equality plus target map respect implies the selected relation;
- relational maps compose through executable `partialCompose`;
- relational map correspondence is transitive; and
- a source `PartialCommute` square transports to the target square.

### 5.2 Whole-bundle field 9

`R39RelationalIndependenceConsumerPositive` defines a probe-only shadow RAR and
constructs `r39TraceIndependentAfterRelationalReplay`.  It proves both:

- `generatedMonoidsCommute` for every pair of replayed transformations; and
- `iteratorYieldsStable` when the foreign transformation returns only a related
  moved state.

The iterator proof composes target-to-source moved-stage agreement, the source
stability theorem, and source-to-target origin-stage agreement.  The existing
exact stage-output field is sufficient via
`r39StageOutcomesRelatedFromExact`; no second frozen field is weakened.

### 5.3 R27-style retained target totality

`R39RelationalFixtureRetentionPositive.r39TargetDefinedFromRelatedSource` proves
that a defined source map and relational head map produce an existentially
defined target map.  `r39R27StyleTargetMapTotal` packages exactly the theorem
shape used by an `ActualMapsTotalStep`; exact target identity is unnecessary.
Both actual R23/R27 finish envelopes construct the relational field from their
producer-owned exact field.  R29's target bundle field 9 remains
`r28WholeIndependent`.

## 6. Producer probes

### 6.1 Six closed semantic families

`R39RelationalHeadProducerPositive` provides one named conversion for each
closed producer:

- `r39InsertProducerSuppliesRelated`;
- `r39RetireProducerSuppliesRelated`;
- `r39RemoveProducerSuppliesRelated`;
- `r39BeginProducerSuppliesRelated`;
- `r39DivertProducerSuppliesRelated`; and
- `r39LeaveProducerSuppliesRelated`.

Each consumes the producer's existing exact proof plus the target checked
transition's `partialEffectMapRespects` proof.  The result is constructed, not
asserted, and no transition dictionaries are identified.

### 6.2 L-Unload

`r39RelatedAccumulatorsSupplyRelatedMaps` is valid for arbitrary
`AccumulatorRelated` functions.  It first runs the source accumulator on
related inputs using `accumulatorRuntimeEffectMapRespects`, then relates source
and target accumulator outputs at the target input.  Its proof works for the
R38 `probeFreshLeft`/`probeFreshRight` class because it compares ambient values
and ordered bindings, never uniqueness-proof closures.

`r39RelatedLifecycleOwnersSupplyRelatedMaps` lifts the same result to arbitrary
related lifecycle owner fibers and covers the exact Table-1 map expected by the
future L-Unload producer.

### 6.3 L-Advance, including yielded maps

The pre-shape demand analysis is
`O6-R39-LADVANCE-MAP-DEMAND-ANALYSIS.md`.

`R39AdvanceYieldedMapProducerPositive` proves all runtime outcome branches:

- undefined and failure forward projections are jointly undefined;
- successful forward projections retain `EffectStateRelated` after-states;
- every `yieldedInverseEffectMap` respects related inputs because it is the same
  lifted local-state operation as the accumulator runtime map; and
- `RuntimeYieldsAgree`'s existing inverse `PartialMapsEquivalent`, combined with
  target inverse respect, yields the selected strong relation without inverse
  function equality.

`R39TraceGeneratorRespectPositive` strengthens the stage runtime agreement to
retain successful forward states and proves the generic theorem
`r39TraceGeneratorMapRespects` by all three generator constructors:
actual-forward, iterator-forward, and iterator-yielded.  This closes the
identity-producer case and proves that L-Advance does not create a later
second-interface campaign.

The existing exact `replayIteratorOutcomePreserved` remains producer-suppliable:
corresponding source/target stages retain the same component, remaining suffix,
view, step, and continuation; accumulator and occurrence proofs are absent from
`iteratorStageOutcome`'s runtime projection.  Related moved inputs are handled
by `iteratorStageOutcomeRelated`, not exact output-state equality.

## 7. Anti-oscillation matrix

| Requirement | Consumer sufficient | Producer sufficient | Probe |
|---|---:|---:|---|
| partial composition | yes | n/a | `r39PartialMapsRelatedCompose` |
| RAR composition | yes | yes | `r39ComposeRelationalReplayCorrespondence` |
| identity RAR | yes | all 3 generators | `r39IdentityRelationalReplayCorrespondence`, `r39TraceGeneratorMapRespects` |
| generated commute | yes | yes | `r39PartialCommuteFromRelatedMaps` |
| iterator stability | yes | exact stage field retained | `r39TraceIndependentAfterRelationalReplay` |
| bundle field 9 | yes | yes | complete `TraceIndependent` probe |
| six closed heads | yes | yes | six named conversions |
| L-Unload | yes | proof-distinct accumulators | `r39RelatedAccumulatorsSupplyRelatedMaps` |
| L-Advance actual map | yes | related lifecycle owners | `r39RelatedLifecycleOwnersSupplyRelatedMaps` |
| L-Advance forward map | yes | all result branches | strengthened runtime outcome probe |
| L-Advance yielded map | yes | every lifted callback inverse | yielded-map probes |
| R27 target totality | existentially yes | both R23 envelopes | fixture-retention probe |

No row relies on output-shaped caller capital.

## 8. Historical pin plan

At a later authorized landing, the removed exact shapes must remain
self-contained as:

- `RetiredExactRelationalReplayGeneratorMapPreservation`;
- `RetiredExactPointwiseHeadMapPreservation`; and
- `RetiredExactSealedSuffixHeadMapPreservation`.

R38 remains the concrete proof-distinct accumulator negative against the retired
exact shape.  R26 and R27 negatives continue to target the stronger test-local
R27 exact retention and the independent-transition dictionary boundary; those
records need not be weakened and their diagnostics must remain unchanged.

## 9. Decision requested

Approve or reject only the proposed manifest delta.  No declaration should be
changed until the design gate approves:

1. the strong `PartialMapsRelated` field;
2. universal `keyEq` quantification at the public RAR field rather than a new
   record parameter;
3. retaining exact iterator outcome preservation;
4. the three retired exact historical shapes; and
5. one combined landing campaign for L-Unload and L-Advance.
