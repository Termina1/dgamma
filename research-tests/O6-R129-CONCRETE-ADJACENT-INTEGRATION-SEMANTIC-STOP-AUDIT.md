# O6 revision 129: concrete adjacent integration semantic stop audit

## Scope and coordinate

This grind shift started at the required coordinate
`9c3d7018dc9afd9ae0efc2bf2f42cdbaac4b763b` on branch
`cp5-thm73-scoping`.  The worktree contained only the permitted untracked
`paper/` directory and `review-o6-body-adversarial.md`.

Unit A was mandatory before the R128 bookkeeping correction or any
CanonicalSort hole.  It attempted to add a positive `research-tests` consumer
which calls `adjacentSwapSuffixSpike` on the concrete R23 opening/opening
fixture and checks the result against the independently constructed R27 target
trace and R29 target bundle.  The unit exhausted its three-attempt budget and
hit the semantic opacity/correlation boundary described below.  Per the
standing semantic-stop rule, the candidate test source and its TTC/TTM outputs
were removed; Unit B and all CanonicalSort work remain unopened.

## Three attempts

| Attempt | Representation | Result |
|---:|---|---|
| 1 | A new `R129ConcreteAdjacentSwapEndToEndPositive` module, a generic internal-pair external-order producer, a concrete call, and a matcher with exact final/trace patterns | Infrastructure failure: missing explicit `Decidable.Equality` import.  The first matcher telescope also compared endpoint-indexed traces before transporting the final-state equality. |
| 2 | Added the import and transported the returned trace across the proposed final equality | Infrastructure failure: `%unbound_implicits off` required the helper's type/state telescope explicitly.  The matcher also named private `r23Initial`, confirming that the imported public trace exposes the index but the test cannot name it. |
| 3 | Added the complete explicit helper telescope and a generic `transportTraceFinal` helper, avoiding any direct reference to private `r23Initial` | **Semantic stop.**  The consumer cannot eliminate the opaque returned `AdjacentSwapResult`, cannot use the private `lifecycleCannotBeRoot` helper, and—most importantly—the exact `Refl` checks do not identify `AdjacentSwapResult.replayedFinal r129ConcreteAdjacentResult` with the independently produced R27 final, nor the transported returned trace with `r27WholeTargetTrace`. |

The decisive attempt-3 diagnostics were:

```text
Undefined name lifecycleCannotBeRoot.
Can't solve constraint between: True and
  isLifecycleAction (transitionAction r23Begin1).
Can't solve constraint between:
  MoreTransitions r23Insert1 ...
and
  transportTraceFinal ... (swappedTrace ?result).
Can't solve constraint between:
  (baseFinishReplay r27SecondFinishEnvelope) .replayedAfter
and
  adjacentReplayedFinal r129ConcreteAdjacentResult.
```

The first two diagnostics concern test-local construction of the pair-external
witness and could be addressed by a separately reviewed public fixture witness.
They are not the reason to extend the budget.  The last two are the binding
correlation-class wall: the imported result keeps an existential replayed final
and replay trace behind an `export record` whose constructor
`MkAdjacentSwapResult` is private.  Public projections expose well-typed replay
capital and a relational endpoint, but no exact equality that identifies those
producer-owned indices with the independently reconstructed R27/R29 indices.
The test therefore cannot pattern-match the returned record as requested, and
normalization through the public `adjacentSwapSuffixSpike` call does not expose
the private producer/constructor enough to make those equalities `Refl`.

Accepting only both bundles as inhabitants after assuming a caller-supplied
final/trace equality would not be an end-to-end cross-check; it would merely
restate the missing correlation as a premise.  Adding such a premise, exporting
the private constructor, or adding a new exact producer theorem would widen the
frozen O6 surface and is outside this unit.

## Disposition

No positive test is retained, so the harness remains correctly unchanged at:

```text
SPIKES=5
POSITIVES=57
NEGATIVES=50
TRACKED_TESTS=107
FRESH_SUCCESSFUL_BUILD_MARKERS=62
```

The research-hole census remains **19**, split **6/4/8/0/1**:
CanonicalSort 6, CrossTrace 4, DeletionChain 8, LocalDiamond 0, and
RenamingComposition 1.

Unit B's R128 chain-coordinate correction remains pending.  In particular, the
current sentence incorrectly says the successor relation and positional
producer were committed together at `065c0d0`; history shows the successor
lemma is its own commit `27c1e52` and is not part of `065c0d0`.  The line was
not edited because the mandatory Unit A stop forbids continuing to a new unit.

A future authorized route must first choose one of these honest interfaces:

1. expose a concrete R23 pair-external witness and an exact producer-owned
   result-to-R27/R29 correlation theorem from a module allowed to eliminate the
   private result constructor; or
2. restate the integration check to compare only the public relational endpoint
   and replay correspondence, explicitly dropping the requested exact
   R27/R29 pattern match.

No production file, package manifest, research proof source, frozen O6
surface, or existing test inventory was changed in this stopped unit.
