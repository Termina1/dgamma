# O6 revision 137: O8 generation-interval ratification

## Result

The revised O8 predicate is independently ratified in both directions on the
checked countershape from commit `2a92a1b`.  This series changes no production
source and spends **0/3** O8 body attempts.

The proof module is
`research-tests/DGamma/R137O8GenerationIntervalRatification.idr`.

## Positive ratification

`r137RevisedO8CandidateExists` constructs a complete
`DeletableClosingEpisode`, not merely the revised negative field.

The selected occurrence is first-generation `ActorB`:

- `scanGenerations` constructs its exact start ordinal/live environment and
  `GenerationTraceScan` proof from the genuine trace prefix;
- `selectedRegistrations = []`, with both directions of
  `RegisteredGenerationsDuring` proved (the selected center contains only
  L-Begin/L-Advance/L-Unload);
- the global `NoRegisteredEpisode` for the empty generation list is built by a
  total structural scan;
- `r137FirstBNoDependentForGeneration` proves the revised dependency negative:
  `closedInside` consists of one L-Advance, so an exact located consumer L-Begin
  is impossible; and
- the later second-generation `ActorB -> ActorA` edge is outside the selected
  installed interval and therefore no longer falsely rejects the candidate.

This directly establishes that a real O8 candidate exists under the repaired
surface.

## Negative ratification

`r137RevisedPredicateRejectsInIntervalDependency` selects the genuine first
`ActorA` activation.  The test constructs:

- its exact located closed episode from L-Begin through L-Unload;
- an `InstalledTrace` over every internal checked transition;
- generation `MkRegistrationGeneration ActorA 3`, current in the exact
  generation environment at global opening ordinal 4;
- the exact located first-generation `ActorB` opening inside that installed
  interval, with local ordinal 2 and global ordinal `4 + 1 + 2 = 7`; and
- the concrete `PrecedenceEdge ActorA ActorB` at that consumer start.

Applying any alleged revised negative to these witnesses yields `Void`.  The
repair therefore still forbids precisely the dependency that would make
selected-activation deletion unsound.

## Proof engineering

The fixture exports only the additional erased boundary facts needed by the
ratification.  `r137ProofLocatedActionOccurs` is a total prefix recursion that
turns an exact `LocatedActionOccurrence` into `ActionOccurs`; no proof-term
comparison or proof irrelevance is used.  Constructor disjointness rules out
L-Begin/O-Insert in the exact short traces.

There are no holes, postulates, `believe_me`, `assert_total`, or
`unsafePerformIO` in the ratification delta.

## Fresh checks

Executed serially after deleting each terminal TTC/TTM:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
1/1: Building DGamma.R7DeletionBoundariesPositive
4/4: Building DGamma.R137O8GenerationIntervalRatification
```

All exited 0 with no `Error:` diagnostic.  The direct O7 consumer remains valid,
and every downstream declaration in the DeletionChain spike still checks.

## Next gate

The O8 body now receives its fresh **3-attempt** budget.  The frozen CP3/O9
raw-predicate mismatch recorded in the surface audit remains explicit and is not
addressed or weakened by these tests.
