# O6 endpoint-controls audit

Date: 2026-08-16  
Branch: `cp5-thm73-scoping`  
Review coordinate: `5f9d45cecccbfce049f7d313d52f27569dde1999`  
Reject report: `ad21f1d90db0fb22c3b78a806131fb1dff0b049f`

## 1. Stop reason and status

The combined revision-15/revision-16 review accepted revision 15, all nine O5
rule pairs, the local O5 effect proof, and the mechanical removal of
`LocalRelationalDiamond.swappedControls`. It rejected pipeline closure with B1:
`RelationalReplayEndpoint.replayedControls` still requires
`OrderedRegistryControlsRelated`, so the same distinct O-Insert/O-Insert head
transposition is demanded by O6 one layer later.

The reviewer proved this constructively. The proof is now tracked as
`research-tests/DGamma/R16EndpointControlsImpossibilityPositive.idr`, including:

- `checkedInsertSwapEndpointControlsImpossible`;
- `emptySuffixReplayEndpointImpossible`;
- `pairFoldForcesEmptyReplayedSuffix`; and
- `suffixFreeInsertSwapResultImpossible`.

No research declaration is changed by this audit. O5 remains a proved local
diamond, but is **pipeline-blocked** until the O6 endpoint contract becomes
producer-suppliable. The two O6 declarations cannot both be filled as currently
typed for the accepted suffix-free distinct-insert case.

## 2. Literal inventory

### 2.1 `RelationalReplayEndpoint` and `replayedControls`

There is no occurrence of `RelationalReplayEndpoint` under `src/`.
The research record is declared only in
`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:479-490`.
Its ordered field is:

```idris
0 replayedControls : OrderedRegistryControlsRelated ...
  (bindings (registry sourceFinal))
  (bindings (registry replayedFinal))
```

Literal tracked uses of the endpoint type are exactly:

- `CP5ConfluenceLocalDiamondSpike.idr`: 11 occurrences;
- `CP5ConfluenceCrossTraceSpike.idr`: 2 occurrences;
- `CP5ConfluenceRenamingCompositionSpike.idr`: 1 occurrence;
- `R11GenericRawPlanRepackagerPositive.idr`: 2 occurrences;
- `R6StaleQuotientNegative.idr`: 1 occurrence;
- `R8ZeroDerivationOperationalStepNegative.idr`: 1 occurrence; and
- `R16EndpointControlsImpossibilityPositive.idr`: 3 occurrences.

`replayedControls` itself has one production-research declaration and one direct
tracked projection: the B1 proof in
`R16EndpointControlsImpossibilityPositive.emptySuffixReplayEndpointImpossible`.
Before that probe was tracked, no positive pipeline module projected the field
by name because the relevant producers remain holes. The obligation was still
present positionally and by record type, as detailed below.

### 2.2 Pattern matches and algebra

`CP5ConfluenceLocalDiamondSpike.idr` contains the complete current algebra:

1. `relationalReplayEndpointReflexiveSpike` constructs the endpoint using
   `orderedControlsReflexive`.
2. `relationalReplayEndpointTransitiveSpike` pattern-matches both endpoint
   constructors as
   `MkRelationalReplayEndpoint ... firstControls ...` and
   `MkRelationalReplayEndpoint ... secondControls ...`.
3. Its private `controlsTransitive` recursively pattern-matches
   `OrderedControlsNil`/`OrderedControlsCons` and requires the same actor at every
   intermediate head.
4. `AdjacentSwapResult.swappedEndpoint` stores the resulting endpoint from the
   original final state to the suffix-replayed final state.

These are genuine positional consumers even though only the B1 probe spells
`replayedControls` as a projection.

## 3. Full transitive consumer trace through the 21-hole pipeline

### O6: adjacent swap and suffix replay

- `adjacentSwapOperationalOccurrenceFoldSpike` authenticates the exact target
  occurrence map. It does **not** need endpoint controls itself.
- `adjacentSwapSuffixSpike` must construct `AdjacentSwapResult`.
- `AdjacentSwapResult.swappedEndpoint` therefore requires a
  `RelationalReplayEndpoint originalFinal replayedFinal` for every local
  orientation.
- For an empty source suffix, `operationalOrdinalRelation` prevents appending a
  hidden third target transition. The replayed suffix is empty and the endpoint
  is exactly the local swapped endpoint.
- For distinct O-Insert/O-Insert, checked evaluator equations force heads
  `right :: left :: source` and `left :: right :: source`; ordered controls are
  uninhabitable. Thus this is a current producer failure, not merely an unused
  projection.

**Actual O6 need:** effect-state correspondence, target well-formedness, and
actor-name-indexed control correspondence. Exact list order is neither preserved
nor observed. Exact endpoint state equality is false for the insertion pair.

### O17: sorting by finite adjacent derivations

- `FiniteAdjacentSwapDerivation` stores each concrete `AdjacentSwapResult`.
- `sortClosingFreeTraceSpike` must recursively consume those results and produce
  `SortedClosingFreeTrace`.
- `SortedClosingFreeTrace.sortedEndpoint` is a `CanonicalEndpointRelation` with
  no withdrawn names for pure sorting.
- Its `endpointControlsOutside []` is pointwise by actor lookup, not by registry
  list position.
- Although the O17 body is a hole and has no literal endpoint projection yet,
  its only authenticated local endpoint capital is the sequence of
  `AdjacentSwapResult.swappedEndpoint` values. Removing all control information
  would leave no sealed proof of `sortedEndpoint.endpointControlsOutside`.

**Actual O17 need:** pointwise `FiberControlMaybeRelated` for every actor, stable
under composition of swaps. It does not need binding order or endpoint equality.

### O19: whole-block and selected canonical permutation

- `operationalAdjacentBlockSwapSpike` must turn a nonempty finite adjacent
  derivation into `OperationalAdjacentBlockSwap`.
- `OperationalAdjacentBlockSwap.blockSwapEndpoint` is a
  `RelationalReplayEndpoint sourceFinal blockSwapFinal`.
- `OperationalActorPermutation` recursively chains such block swaps. Its replay
  and occurrence correspondences have explicit composition functions, while
  endpoint composition must use the endpoint algebra when constructing later
  packages.
- `CertifiedOperationalCanonicalPermutation.selectedPermutationRealized` seals
  the exact operational chain; no caller may choose an unrelated endpoint map.

**Actual O19 need:** a composable, source-authenticated, name-lookup control
relation for each block-swap endpoint. It does not need exact binding order.

### O20: composed canonical permutation endpoint

- `PermutedCanonicalExecution.composedPermutationEndpoint` is a
  `RelationalReplayEndpoint` from the left canonical final state to the selected
  operational target.
- `canonicalSchedulesConvergeSpike` must construct it from the sealed
  `OperationalActorPermutation`, hence transitively from `blockSwapEndpoint`
  values.
- `permutationReplayCorrespondence` and
  `permutationOccurrenceCorrespondence` do not carry control observations; they
  cannot replace the endpoint field.

**Actual O20 need:** transitive effect and pointwise control equivalence from the
canonical left endpoint to the operational target. It does not need list order.

### O21: canonical convergence and final system equivalence

- `replayedCanonicalToOriginalEndpointSpike` explicitly accepts the composed
  `RelationalReplayEndpoint` from the left canonical final state to the replayed
  left final state.
- `ReplayedCanonicalEndpointBridge.replayBridgeControls` relates the replayed
  left endpoint to the right canonical endpoint under the fixed name bijection.
- To produce `SystemEquivalentByRenamingModuloVestigial`, O21 must compose the
  same-name left-canonical-to-replay control relation with the renamed
  replay-to-right bridge.
- The final CP3 observation is lookup-based. `ControlEquivalent` and
  `ControlEquivalentOutside` are defined pointwise by `lookupFiber`; no final
  theorem observes registry list order.

**Actual O21 need:** same-name lookup control equivalence for the replay endpoint,
then renamed lookup correspondence through the bridge. It does not need exact
state equality or ordered binding lists.

### Canonical endpoint composition outside this chain

Deletion uses `CanonicalEndpointRelation`, whose control field is
`ControlEquivalentOutside`/`ControlEquivalentOutsideGenerations`, already
lookup-indexed. Sorting has an empty withdrawal list, so its exact consumer is
`ControlEquivalentOutside []`, equivalent to total actor-name lookup control
correspondence. This confirms that ordered controls are stronger than every
final canonical consumer.

## 4. Research-test consumers

- `R11GenericRawPlanRepackagerPositive` accepts an endpoint opaquely and places it
  into `AdjacentSwapResult` and recursive supplied ingredients. It proves only
  generic repackaging, not endpoint producer-suppliability.
- `R6StaleQuotientNegative` returns `composedPermutationEndpoint first` at the
  index of a distinct selected operation; it checks sealing of endpoint indices,
  not control contents.
- `R8ZeroDerivationOperationalStepNegative` accepts an endpoint input while
  attempting a zero-node whole-block derivation. It is an intended-negative
  boundary and does not project controls.
- `R16ConfluenceTheoremAssemblyPositive` has no endpoint projection. Its success
  is interface assembly through holes and does not discharge O6.
- `R16EndpointControlsImpossibilityPositive` is the genuine adversarial consumer:
  it projects `replayedControls` at exact evaluator-produced endpoints and proves
  the simultaneous O6 result impossible.

## 5. Sealed production usage of ordered controls

There is no production import or use of `RelationalReplayEndpoint`.
`OrderedRegistryControlsRelated` itself is legitimate production capital for
synchronized deletion/replay operations that preserve actor order.

A complete `.idr` scan finds 76 direct lines in 16 production files:

- definition, reflexivity, lookup conversion, and relational boundary:
  `CP4DeletionRelationalBoundary.idr`;
- transport, lookup, replace/delete/cons congruence:
  `CP4DeletionRelationalActionCore.idr`;
- same-action O-Insert/O-Retire/O-Remove relational replay:
  `CP4DeletionRelationalActionOrchestration.idr`;
- lifecycle core and Begin/Advance/Divert/Leave/Unload cases:
  `CP4DeletionRelationalLifecycleCore.idr`,
  `CP4DeletionRelationalLifecycleBegin.idr`,
  `CP4DeletionRelationalLifecycleAdvance.idr`,
  `CP4DeletionRelationalLifecycleAdvanceCases.idr`,
  `CP4DeletionRelationalLifecycleAdvanceDispatch.idr`,
  `CP4DeletionRelationalLifecycleDivert.idr`,
  `CP4DeletionRelationalLifecycleLeave.idr`,
  `CP4DeletionRelationalLifecycleUnload.idr`, and
  `CP4DeletionRelationalLifecycleSources.idr`;
- suffix/post-close composition:
  `CP4DeletionRelationalSuffixFold.idr`,
  `CP4DeletionPostCloseOrchestration.idr`,
  `CP4DeletionPostCloseRemove.idr`, and
  `CP4DeletionPostCloseUpgrade.idr`.

A further 110 substring occurrences are the distinct
`SelectedOrderedRegistryControlsRelated` family across selected-deletion
modules. Neither family should be retired or changed in `src/` for revision 17.
Production already exposes the required weakening lemma:

```idris
orderedControlsGiveControlEquivalent :
  OrderedRegistryControlsRelated ... -> ControlEquivalent ...
```

and `orderedControlsLookup` provides its pointwise form.

## 6. Design options

### Option (a): retire `replayedControls`

Immediate change:

- remove the field from `RelationalReplayEndpoint`;
- remove the reflexive/transitive ordered arguments; and
- mechanically update record constructors.

**Immediate cost:** 1–2 shifts plus a scoped review.

**Grade:** technically removes B1 from O6, but not recommended.

Why it is incomplete: O17 must still construct
`CanonicalEndpointRelation.endpointControlsOutside []`, and O21 must compose the
left-canonical-to-replay controls with `replayBridgeControls`. Neither replay
correspondence nor occurrence correspondence contains control observations.
Retirement therefore moves the missing evidence to O17/O21 exactly as revision
16 moved it from O5 to O6. Reintroducing a sealed relation later is estimated at
another 3–6 shifts and another interface gate. Total honest cost is 4–8 shifts,
with a high risk of another anti-oscillation rejection.

### Option (b): use authenticated actor-name lookup control equivalence

Use the existing production definition rather than inventing speculative
capital:

```idris
ControlEquivalent name key world error value nameEq sourceFinal replayedFinal
```

Recommended revision-17 shape:

1. `LocalRelationalDiamond` gains a consumer-needed
   `swappedControlEquivalent : ControlEquivalent ... originalFinal swappedFinal`.
2. `RelationalReplayEndpoint.replayedControls` changes from ordered lists to
   `ControlEquivalent ... sourceFinal replayedFinal`.
3. Reflexivity/transitivity use pointwise fiber-control reflexivity and existing
   `controlEquivalentTransitive`.
4. `AdjacentSwapResult` retains the exact endpoint indices and sealed suffix
   producer; no caller-selected permutation or endpoint is added.
5. O3/O4 existing ordered outputs coerce via
   `orderedControlsGiveControlEquivalent`; their private ordered lemmas remain.
6. O5 constructs pointwise correspondence for all nine genuine checked pairs.
   In O-Insert/O-Insert, lookup ignores the head permutation while preserving
   each named fresh fiber. Retire/remove cases use the actual checked lookup and
   static-component/static-parent framing already proved.
7. O6 suffix replay composes the local pointwise relation through the actual
   checked suffix; O17/O19/O20 compose it transitively; O21 consumes exactly its
   lookup form.

An explicit permutation certificate is **not** recommended unless a later
consumer demonstrates that need. Exact checked transitions already authenticate
both endpoint registries, and every current consumer asks only by actor name.
Adding a caller-selectable permutation would violate the same anti-oscillation
rule.

**Cost before resuming the O6 body:** 5–9 shifts:

- 1 shift for exact revision-17 declarations, algebra, manifest, and producer
  probes;
- 1 shift for O3/O4 coercions and coordinate revalidation;
- 2–4 shifts for the nine O5 pointwise producers and adversarial transposed-head
  positive/negative coverage;
- 1–3 shifts for endpoint/suffix composition probes and scoped review.

The remaining O6 occurrence/suffix implementation is still an independent XL
estimate after this repair; revision 17 does not claim to solve O6 itself.

**Grade:** recommended. It is producer-suppliable, transitive, already part of
sealed production semantics, and exactly matches O17/O21 consumers.

## 7. Recommendation and revision-17 gate request

Recommend option **(b)** using existing `ControlEquivalent`, not a new loose
permutation record. Revision 17 should be limited to:

- the two research record fields above;
- reflexive/transitive endpoint algebra;
- the four local-diamond family producers/coercions;
- O6-facing positive and transposed-insert adversarial probes;
- manifest/harness bookkeeping; and
- no production, CP3, O6 body, or unrelated hole-signature change.

O5 status until then: **locally proved / pipeline-blocked**. Hole arithmetic
remains 21 with split `6/4/8/2/1`; the local O5 hole stays absent and must not be
reintroduced.
