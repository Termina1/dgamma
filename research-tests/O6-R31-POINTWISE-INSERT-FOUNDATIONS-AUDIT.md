# O6 revision 31: pointwise insert foundations and bounded-attempt audit

## Scope

This continuation stays behind the frozen `adjacentSwapSuffixSpike` boundary.
It adds only private implementation lemmas to
`CP5ConfluenceLocalDiamondSpike`; there is no new theorem premise, result field,
constructor, export, production edit, or manifest exception.

## Closed foundations

Four lemma commits extend the generic pointwise head replayer:

1. `0ede24c` derives target lookup absence, lookup-presence equality, and parent
   presence directly from `ControlEquivalent`. No list-order relation is used.
2. `9848bd3` proves that provision disjointness transports to an independently
   ordered target registry. The proof audits every uniquely named target entry,
   finds its same-component source fiber through symmetric pointwise control,
   and projects the source disjointness predicate at that exact entry.
3. `4bb465a` proves pointwise control preservation after O-Insert. The new actor
   has the identical fresh fiber on both sides; every other actor reduces by the
   distinct-key insertion lookup frame.
4. `9d28d61` specializes the generic checked actual-transition frame to the
   empty effect table installed by O-Insert.

Together these discharge O-Insert freshness, parent, declaration-disjointness,
post-control, and post-effect foundations under pointwise control.

## Bounded full-head attempt

A full `replayPointwiseInsertHead` was attempted against those foundations and
then reverted under the per-lemma attempt budget. The attempt constructively
reached:

- target guards;
- a checked target insertion;
- target well-formedness;
- source/target empty-table effect framing;
- producer-owned map equality; and
- the non-advance singleton RAR packaging path.

The resisting point was source endpoint indexing. Pattern matching the indexed
`ForeignInsertPlanView` refines the source endpoint to the concrete inserted
state, while the independently stored original checked proof remains indexed by
`sourceAfter`. Direct construction then fails at the exact mismatch:

```text
Mismatch between: MkSystemState sourceWorld
  (insertBinding actor (freshFiber component parent) sourceRegistry sourceAbsent)
and sourceAfter.
```

An unindexed source-ingredient wrapper was tried so it could retain the equality
explicitly, analogous to `retireSourceIngredients`. That attempt stopped because
the imported helper was not available to this research consumer:

```text
DGamma.CP4DeletionSelectedForeignOrchestration.foreignInsertPlanView
is not accessible in this context.
```

The partial full head and wrapper were reverted. No hole, cast, postulate,
caller-selected equality, target map, endpoint, occurrence, ordinal, or bundle
was retained. The checked insert-effect frame is independent and elaborates.

This is not evidence that O-Insert or the action family is uninhabitable, and it
is not an output-shaped-capital finding. The next bounded attempt should derive
an unindexed `(absence, guards, concrete-after equality)` package directly from
`applyAction`, rather than pattern-match an indexed view in the final producer.
If that package cannot be derived within a fresh three-attempt budget, O-Insert
must receive a dedicated exact negative before any interface discussion.

## Replayer inventory and estimate

Fully closed semantic action heads: `O-Retire` only.

O-Insert foundations now closed but final head still open: freshness,
parent/disjoint guards, post-control, checked effect frame.

Still-open action heads: O-Insert, O-Remove, L-Begin, L-Advance, L-Divert,
L-Leave, and L-Unload. L-Advance still owns the additional iterator-stage and
yielded-map provenance obligation; L-Unload owns accumulator map transport.

The remaining O6 band is revised from **22–38** to **20–36 shifts**. Four
foundation shifts were consumed, but the source-index packaging diagnostic adds
back roughly two shifts of bounded O-Insert work. Hole count remains 20 with
split `6/4/8/1/1`; the sole LocalDiamond hole is unchanged.
