# O6 revision-24 pointwise two-head replay audit

## 1. Authorized scope

Revision 24 started from `cp5-thm73-scoping@dcfb516` with only
research-test, declaration-local work authorized:

1. replay the first R23 suffix `LAdvance 1 / LFinish` from the local diamond's
   pointwise endpoint;
2. derive every per-step certificate from the checked transition;
3. replay `LAdvance 2 / LFinish` from the first result's checked endpoint;
4. resume the whole target `ReplayInvariantBundle` in field order; and
5. stop at the first genuine lifecycle/effect/control/invariant gap.

No ordered-list control premise, frozen declaration, O6 hole body, manifest,
production source, package, or CP3 change was allowed.

## 2. Pointwise checked finish producer

`R23CorrectedInternalFixturePositive` now contains the test-local
`R24CheckedEmptyFinishReplay` and its producer.  The public result record owns:

- the target state;
- the exact checked target `LAdvance / LFinish` transition;
- transition/action/tag/alignment equalities tied to that exact transition;
- a `RelationalReplayEndpoint` for the post-state;
- singleton `RelationalReplayCorrespondence`;
- singleton `ActionRegistrationReplayCorrespondence`; and
- the exact relative ordinal theorem for every located target occurrence.

None of those fields is accepted from the caller.

The producer obtains the target owner only by applying
`controlEquivalentTargetHasSource` to the symmetric pointwise endpoint.  Its
`FiberControlRelated` payload reconstructs the target `Reloading []`
continuation, accumulator, committed view, parent, and retirement bit.  The
producer then executes the exact target evaluator branch, proves preservation,
updates all other actors pointwise with
`controlEquivalentAfterRelatedReplacement`, and constructs the post-state
endpoint.  `R23Key` is empty, so post-state effects are related by the already
proved concrete effect theorem without any table-domain premise.

The singleton RAR is operational.  Its only actual generator maps to the exact
source transition.  Empty-continuation iterator stages are refuted from the
checked owner lookup and `ReachableSuffix [] (step :: rest)`.  Both actual
partial maps compute to identity.  The occurrence correspondence proves that a
singleton L-Advance contains no generated registration; the ordinal proof
eliminates every nonempty prefix by transition count.

## 3. Both heads close

The first result is:

```idris
r24FirstFinishReplay : R24CheckedEmptyFinishReplay 1 r23AfterPair
  r23AfterAdvance1 (swappedFinal r23Diamond) r23Advance1Checked
```

The second producer consumes exactly `replayedEndpoint r24FirstFinishReplay`:

```idris
r24SecondFinishReplay : R24CheckedEmptyFinishReplay 2 r23AfterAdvance1
  r23Final (replayedAfter r24FirstFinishReplay) r23Advance2Checked
```

Thus the second head cannot be detached from, or evaluated at a caller-selected
intermediate state.  `R24CheckedTwoHeadSuffix` seals the exact source and target
two-node suffixes, and `r24FinalEndpoint` relates `r23Final` to the checked
second target endpoint.  No `OrderedRegistryControlsRelated` value occurs in any
revision-24 producer or result type.

## 4. Whole-bundle hard stop: field 1 (`replayAligned`)

After both heads replay, the strict bundle order restarts at
`ReplayInvariantBundle.replayAligned`, not at quietness.  Prefix alignment and
both replayed singleton alignments are constructive.  The moved pair is the
first failure.

The unmodified `LocalRelationalDiamond` still does not retain revision 21's
producer-owned outer-dictionary alignment.  Destructing its exact R23 moved
transitions and attempting to construct `AlignedTransitions` fails at:

```text
Mismatch between: storedRightKeyEq and keyEq.
```

`R24CorrectedWholeAlignmentNegative` pins this exact failure at
`correctedFixtureCannotRecoverMovedPairAlignment`.  It is not a new semantic
counterexample: it is precisely combined-package item A, already scoped by
`R21MovedOutputAlignmentScopingPositive` and its independent-dictionary
negative.  The R23 producer created the moved transitions with the outer
dictionaries, but the live result type erased that constructor-local capital.
A consumer may not recover it by identifying independently stored `DecEq`
closures.

Because `replayAligned` is the first record field, revision 24 makes no target
`replayDiscipline`, `replayQuiet`, or later field claim.  The R22 quietness and
no-failure lemmas remain ready, and `r24FinalEndpoint` supplies their pointwise
endpoint, but using them out of declaration order would hide the alignment gap.

## 5. Gate status and revised estimate

The two-head pointwise replay checkpoint is complete.  The combined A/B/C/D
package remains prepared and **unissued**.  This creates an explicit ordering
constraint: end-to-end bundle closure now needs A's producer-owned moved
alignment, while the current gate rule allows A to land only atomically at
end-to-end closure.  No loose alignment premise or dictionary identity is an
acceptable workaround.

The remaining O6 estimate is revised from **25–42** to **26–44 shifts**.  The
lower-level suffix work shrank, but the newly concrete atomic-gate ordering
problem adds a scoped producer/boundary decision before the bundle can resume.
If A is authorized only as a test-local corrected producer envelope first, the
lower end is plausible; if the combined boundary must remain strictly atomic,
review and reassembly occupy the upper end.

Next work requires a supervisor decision on that ordering.  Until then the
correct action is to stop at field 1.  Frozen declarations, the O6 bodies, the
manifest, production source, `dgamma.ipkg`, and CP3 remain unchanged.
