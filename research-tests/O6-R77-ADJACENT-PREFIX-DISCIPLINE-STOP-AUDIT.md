# O6 revision 77: adjacent-prefix discipline stop

## Scope

Grind shift #85 (overall #139) resumed from accepted revision-76 boundary
`25150d3`. It executed the authorized decomposition in order. Every retained
proof commit was preceded by TTC/TTM removal and a visible direct CP5 source
rebuild, then followed by R16 as additional evidence.

## Retained units

The shift constructively closed and retained:

1. `checkedInsertRequiresAbsentExplicit` — a tag-independent checked-insert
   absence projection with every `lookupFiber` type parameter and the `Action`
   type explicit at statement level;
2. `checkedRetireRequiresFoundExplicit` — the separately checked retirement
   presence projection under the same explicitness discipline;
3. `movedRetireBeforeInsertedChildImpossible` — consumes the frozen
   `MovedRightRetirePackage` once, reindexes both source insertion and moved
   retirement before lookup projection, and contradicts `Nothing = Just fiber`;
4. action-indexed moved registration callbacks and their reindexing wrapper;
5. moved-right retirement-tail provenance;
6. moved-left retirement-tail provenance, including the now-closed impossible
   insert/retire crossing;
7. `adjacentPairRegistrationDiscipline` — completely reconstructs the two
   moved registration-step obligations and producer-sealed suffix discipline.

All proof locals are quantity 0. The frozen revision-76 package, revision-21
surface, and existing replay capital were not altered.

## Exhausted unit

The next unit was whole-prefix `adjacentRegistrationDiscipline`. Three fresh
attempts were spent:

1. The first placement preceded `sealedSuffixRegistrationDiscipline`; direct
   fresh compilation rejected the declaration-order dependency.
2. Moving the unit after sealed-suffix discipline exposed the next declaration
   dependency on `adjacentChildRetirementProvenance`; after moving it after that
   producer, the recursive prefix head had an accidentally implicit `_` source
   state rather than exact `initial`.
3. Replacing `_` by `initial` closed the source-state mismatch. The final error
   was the nonlinear dependent tail index:

```text
Can't solve constraint between:
  sourceRest
and:
  appendTransitions prefixTail
    (MoreTransitions left (MoreTransitions right suffix)).
```

The recursive proof's `sourceRetirement` remains indexed by the constructor's
fresh `sourceRest`, while `adjacentChildRetirementProvenance` requires the exact
append expression. This is the already-known correlated dependent-prefix
projection class, not a new semantic premise gap. The entire unverified
`adjacentRegistrationDiscipline` unit was removed. All seven prior units remain
at the safe checked boundary `c67796e`.

## Recommended next cure

Introduce one producer-owned `PrefixRegistrationDisciplineView` for a nonempty
prefix. It must seal under one elimination:

- the exact prefix head;
- the exact append-expression source tail;
- its `RegistrationStepDiscipline`;
- the tail `RegistrationDiscipline`;
- the equation identifying the constructor-stored rest with the append tail.

The recursive consumer should eliminate this package once, reindex
`sourceRetirement` before calling `adjacentChildRetirementProvenance`, and never
name a second independent `sourceRest`. That package and its consumer receive
separate fresh three-attempt budgets.

## Status

- insert-absence projection: **closed**;
- retire-presence projection: **closed**;
- moved-retire/insert consumer: **closed**;
- adjacent moved-pair discipline: **closed**;
- whole adjacent prefix discipline: **not closed**;
- field 2: **not yet complete**;
- fields 3–15: **unopened**;
- final assembly/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

Substantial field-2 capital closed this shift. The prior **2–14** remainder is
reduced to an honest **1–13 shifts**.

## Frozen-capital audit

`adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain isolated. No public surface,
hole, or escape hatch was added.
