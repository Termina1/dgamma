# CP5 revision-17 scoped adversarial review

Reviewed coordinate: branch `cp5-thm73-scoping`, requested HEAD
`677b974f0eb5aa39c851a0450ec585f60528d04a`, diff base `ad0e1cb`.
The accepted revision-13/revision-14 material, revision-15 premises and nine local
O5 rule pairs, and round-11/12 scoping were not re-litigated.

## Verdict

**REJECT**

The `ControlEquivalent` endpoint repair itself is sound, genuinely produced, and
concretely inhabited for evaluator-checked transposed insertions. However, the
charter requires the **full** repaired `AdjacentSwapResult` to be inhabited for a
suffix-free distinct O-Insert/O-Insert case. It is not: an independently checked
total Idris proof shows that a genuine distinct root-insert/root-insert instance
still makes the full result `Void`, now through the unchanged
`SameExternalOrchestration` field rather than through endpoint controls. This
triggers the review's explicit rejection condition.

## Findings

### B1 — blocker — the requested full suffix-free result remains uninhabited

The repaired local endpoint is constructible, but the enclosing full result is
not constructible for the concrete distinct root-insert instance used by the
independent evaluator probe:

- `AdjacentSwapResult.swappedSameExternalInputs` requires
  `SameExternalOrchestration` at
  `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:863-864`.
- `swappedOccurrenceFold` seals the operational occurrence fold at `:873-884`.
  For a two-node source and empty source suffix, its four-region ordinal contract
  rules out any hidden third target node, so `replayedSuffix` is empty.
- `SameExternalOrchestration` at `src/DGamma/CP3.idr:2051-2091` may skip only
  non-root/internal transitions. Root O-Insert is externally observable through
  `RootInsertStep`; therefore the relation cannot skip either head and must match
  the original left root insertion with the moved-right root insertion.
- The local diamond authenticates
  `transitionAction (movedRight diamond) = transitionAction right`. Matching the
  two external heads therefore equates the distinct left and right insertion
  actors, a contradiction.

The total independent proof is
`/tmp/thm73-r17-probes/DGamma/R17FullResultImpossibility.idr`:

- `pairFoldForcesEmptyReplayedSuffix` independently reconstructs the accepted
  two-node ordinal argument;
- `sameExternalAfterEmptySuffix` transports the actual result field to the exact
  two-node swapped trace;
- `transposedRootInputsImpossible` inverts every constructor of
  `SameExternalOrchestration`; and
- `suffixFreeDistinctRootInsertResultImpossible` proves the current repaired
  full `AdjacentSwapResult -> Void` for two genuine checked distinct root
  insertions, without using the retired ordered endpoint.

This is not a defect in `ControlEquivalent`; it is a separate, pre-existing
full-interface obstruction. Nevertheless, the charter explicitly requires an
own construction of the full result and says to reject when that repaired
interface is not inhabited at the former case. The unqualified plan claims at
`THM73-PLAN.md:432-433,528-534,554-556` (“pipeline-unblocked”, all O/O insert
producers) are therefore too broad. A future repair must either narrow the O6
applicability contract to pairs that may legally change order under
`SameExternalOrchestration`, and update the mandated positive case accordingly,
or exhibit a genuinely reachable child-insert case satisfying every full result
field. Merely weakening controls cannot address this obstruction.

### N1 — note — the authorized ControlEquivalent repair itself passes

The two declaration edits in `3e932f3` are exactly the authorized fields:

1. `RelationalReplayEndpoint.replayedControls` changes from
   `OrderedRegistryControlsRelated` to production
   `ControlEquivalent`; and
2. `LocalRelationalDiamond` gains `swappedControlEquivalent`.

`ControlEquivalent` is the existing immutable production record at
`src/DGamma/CP3.idr:1561-1570`; there is no research lookalike. Endpoint
reflexivity constructs pointwise fiber-control reflexivity, and transitivity uses
the existing `controlEquivalentTransitive` at
`src/DGamma/CP3Support.idr:87-95`.

The new diamond field has a genuine endpoint-assembly consumer, not merely
producer projections. Tracked
`research-tests/DGamma/R15O5AlignedProducerPositive.idr:226-228` projects it into
`MkRelationalReplayEndpoint`. Independently,
`assembleSuffixFreeCheckedInsertResult` in
`/tmp/thm73-r17-probes/DGamma/R17IndependentReview.idr` constructs the complete
record constructor from the explicit non-control O6 fields and projects
`swappedControlEquivalent` specifically into `swappedEndpoint`.

The same independent module also defines `probeEndpointFromEvaluator`. It:

- reduces actual `checkedApplyAction` calls for distinct `False`/`True` root
  insertions;
- constructs exact aligned transitions, root registration discipline, generation
  scan, and `OrchestrationSwapSafety`;
- calls the genuine O5 producer, which checks/packages the fourth moved insert;
- builds the repaired `RelationalReplayEndpoint`; and
- proves `isJust probeEndpointFromEvaluator = True` by `Refl`.

Thus the old ordered-head B1 is discharged at the endpoint layer. The blocker is
only the charter's stronger full-result requirement.

## 1. Immutability and interface discipline

Passed:

- `git diff 34b21c9..677b974 -- src dgamma.ipkg` is empty.
- `HEAD:src/DGamma/CP3.idr` and the worktree blob are exactly
  `2c697e532e83989de8591fa6a4378747c6a501c0`.
- All 27 frozen declarations in
  `research-tests/cp5-hole-interface-baseline.json` are byte-identical to their
  declarations at `ad0e1cb`.
- Both local O6 declarations are byte-identical to `ad0e1cb`; their bodies remain
  exactly the named holes `adjacentSwapOperationalOccurrenceFoldSpike_rhs` and
  `adjacentSwapSuffixSpike_rhs`.
- There are 21 holes with split `6/4/8/2/1`; no O6 body work, new hole, moved
  hole, or unrelated signature change occurred.
- The revision-17 manifest contains exactly the two authorized record fields.

## 2. Producer genuineness

All four local-diamond families use checked endpoint capital:

- A/A at `CP5ConfluenceLocalDiamondSpike.idr:7982-7999` converts its existing
  checked ordered proof only through production
  `orderedControlsGiveControlEquivalent`.
- A/O at `:8209-8224` and O/A at `:8411-8426` do the same.
- O/O at `:8434-8572,8660-8710` constructs pointwise controls directly through
  `orchestrationPairControlEquivalent`.

The direct O/O proof does not fake endpoint lookups:

- both owner cases call `orchestrationOwnerOutputsRelated` with the original and
  moved checked equations;
- OInsert recovers both actual checked insertion views and their actual inserted
  fresh fibers;
- ORetire recovers both actual source fibers, uses the framed source lookup to
  identify them, and proves both actual replacements;
- ORemove recovers both actual delete successes and proves both endpoint owner
  lookups absent; and
- every outside actor is framed through four calls to `transitionForeignLookup`,
  each derived from a specific checked evaluator equation.

No producer selects a convenient registry or lookup equality independently of
its checked endpoint. The direct generic proof covers all three-by-three O/O rule
pairs; the already accepted nine-pair local body was not otherwise changed.

## 3. Negative and historical evidence

`R17WrongLookupControlNegative` fails at
`wrongLookupControlPairRejected:26` with:

```text
Can't solve constraint between: Nothing and with block in lookupEntries ...
```

The failure is exactly the attempted `NoControlFibers` for a present-left,
absent-right lookup at `False`, not an unrelated type error.

`RetiredOrderedReplayEndpoint` at
`research-tests/DGamma/R16EndpointControlsImpossibilityPositive.idr:249-261`
faithfully reproduces every retired field from the pre-repair
`RelationalReplayEndpoint` at `ad0e1cb`: effects, ordered bindings control, and
replayed well-formedness have identical indices (only record/field names differ).
`emptySuffixReplayEndpointImpossible` projects the ordered field, and
`suffixFreeInsertSwapResultImpossible` requires the retired endpoint explicitly.
The historical Void evidence is neither weakened nor vacuous.

## 4. Full theorem assembly

`research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr` remains:

- `%default total`;
- hole/escape-free;
- declared exactly as
  `r16ConfluenceTheoremAssembly : confluenceTheorem name key value world error`;
- constructing the replay bundle from immutable theorem inputs; and
- calling `fullPipelineFromBundles`.

It fresh-builds in the 21-hole pipeline. As the file itself states, this is
assembly through O6/O17/etc. holes, not evidence against B1 above.

## 5. Downstream sufficiency of ControlEquivalent

The audit's control-specific consumer claims are correct:

- O17's `SortedClosingFreeTrace.sortedEndpoint` is a
  `CanonicalEndpointRelation` and `sortedWithdrawsNoNames` fixes its withdrawn
  names to `[]` at
  `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:149-153`.
  `ControlEquivalent` supplies `endpointControlsOutside []` pointwise directly.
- O19/O20 store `RelationalReplayEndpoint` in `blockSwapEndpoint` and
  `composedPermutationEndpoint`; the existing
  `controlEquivalentTransitive` is exactly strong enough for their endpoint
  chains.
- O21 accepts that composed endpoint at
  `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:2280-2289` and the
  bridge supplies `replayBridgeControls` at `:1767-1773`.

The independent positive probe typechecks both
`controlEquivalentSuppliesOutsideEmpty` and a structural
`controlEquivalentThenRenamedBridge`. The latter composes
`FiberControlMaybeRelated` with `MaybeFiberRelatedBy` through inactive,
reloading, active, and unloading lifecycle cases. No O17/O21 declared control
consumer is provably too strong for `ControlEquivalent`.

## 6. Harness and bookkeeping

Both required commands ran serially from a tracked/index-clean state. There was
no SIGKILL, retry, or seeded fallback.

`research-tests/run-r11-suite.sh --fresh` passed with:

```text
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=37
R11_REPRODUCIBLE_SUITE=passed
```

Independent counts: 5 spike headers, 32 positive headers, 30 intended-negative
headers, 37 successful build markers, and zero successful-output `Error:`
diagnostics.

`research-tests/audit-r11-claims.sh` passed with:

```text
R12_RUNNER_INVENTORY=passed
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=37
R11_REPRODUCIBLE_SUITE=passed
R12_CLAIMS_AUDIT=passed
```

Inventory is consistent: 62 tracked test modules (32 positives / 30 negatives),
5 spikes, 27 frozen declarations, exactly two approved revision-17 fields, and
21 holes split `6/4/8/2/1`. The revision-17 plan rows accurately describe the
mechanical control repair and hole counts, but their unqualified full-pipeline
inhabitance claim is contradicted by B1.

## Residual risks

- Theorem 73 remains unproved with 21 research holes.
- The repaired endpoint relation is sound, but no closed full suffix-free
  distinct-insert `AdjacentSwapResult` witness was produced; the independent
  root/root case is constructively impossible through external-input order.
- The yielded-child alternative also needs explicit reachability/full-bundle
  evidence before it can replace the rejected unqualified case; the present
  tracked positive constructs only the local endpoint.
- The independent probes are intentionally under `/tmp/thm73-r17-probes/`, not
  tracked in the repository.

## Commands and evidence summary

- frozen production diff / CP3 blob / 27-signature comparison — passed;
- independent concrete evaluator + repaired endpoint + endpoint-consumer and
  O17/O21 composition probe — passed;
- independent full-result impossibility proof — passed;
- direct R17 wrong-lookup negative with intended diagnostic — passed;
- R16 historical record comparison against `ad0e1cb` — passed;
- R16 exact theorem assembly syntactic checks and fresh build — passed;
- `research-tests/run-r11-suite.sh --fresh` — passed 37/30/zero Error;
- `research-tests/audit-r11-claims.sh` — passed.
