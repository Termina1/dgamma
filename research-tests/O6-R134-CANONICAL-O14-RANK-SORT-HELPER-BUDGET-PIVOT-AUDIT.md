# O6 revision 134: Canonical O14 rank-sort helper budget pivot audit

## Scope

R133 was accepted at `28959a9c26eee2d3dd0c175dbea458c64ee363fd`,
ratifying O12 and canonizing the erased-view recipe.  The supervisor authorized
continued CanonicalSort work with fresh three-attempt budgets and a motivated
pivot to DeletionChain if CanonicalSort blocked.

Only O14 preparation was opened.  The actual `supportOrderingSpike_rhs` fill
remained untouched at **0/3** attempts.

## Attempted helper unit

The candidate used a protocol-rank topological strategy rather than assuming
that registry order or fixed-point discovery order is canonical.  It defined:

- stable insertion sort and list sort by an arbitrary `item -> Nat` rank;
- an indexed `CanonicalRankOrdered` invariant saying each head rank is below
  every rank in its tail;
- insertion/order preservation;
- insertion/sort membership reflection and inclusion;
- insertion/sort uniqueness preservation; and
- strict-rank-to-`BeforeIn` conversion.

This is the appropriate semantic route because retained
`supportPathRankIncreases` gives strict protocol-rank growth along every support
path.  It would next have sorted the duplicate-free executable `supportSet` and
used the replay bundle's ranked/current endpoint capital.

The helper unit exhausted its strict three-attempt budget:

| Attempt | Result |
|---:|---|
| 1 | Parser stopped at an impossible `Elem` tail pattern whose binder was named `impossible`; it was changed to an ordinary binder followed by the `impossible` clause marker. |
| 2 | The inserted-head branch needed transitivity from inserted≤old-head and old-head≤later.  A `with` child clause also failed to match the parent because its aliased `UniqueCons` pattern was not repeated exactly. |
| 3 | After adding transitivity and matching the alias text, the descending insertion branch used `fromLteSucc` at the wrong shape; `notLTEImpliesGT` yields `LTE (S old) inserted`, so `lteSuccLeft` is the required weakening.  The `UniqueCons` `with` parent/child alias mismatch remained. |

These are mechanical proof-engineering errors, not a semantic or correlation
wall.  Nevertheless no fourth helper attempt was made.  The complete candidate
was restored; no O14 body attempt, later CanonicalSort hole, or production edit
was made.

## Disposition

CanonicalSort remains at five holes and the project split remains
**5/4/8/0/1**.  Per the R133 ruling, the exhausted O14 helper unit is parked and
the campaign may pivot directly to DeletionChain without an intermediate
supervisor gate.  Any later O14 return should resume the protocol-rank sort
strategy from the two exact corrections above under a newly authorized unit,
not silently spend a fourth attempt.
