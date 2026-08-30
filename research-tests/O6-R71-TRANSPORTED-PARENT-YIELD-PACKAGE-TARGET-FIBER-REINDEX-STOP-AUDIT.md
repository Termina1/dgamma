# O6 revision 71: transported parent-yield package target-fiber reindex stop

## Scope

Grind shift #79 (overall #133) resumed from the accepted revision-21 landing at
`cde0289`. It used the fresh three-attempt budget authorized by the shift-78
review for one private `LocatedTransportedParentYield` unit. No public
interface, retained revision-21 field, producer, bundle field, or adjacent body
was changed.

All three package attempts were reverted in full when the budget exhausted.
The safe source remains the exact accepted O6 boundary from revision 70.

## Intended package boundary

The private dependent package carried, as one erased value:

- the exact source and target parent fibers;
- exact source and target lookup equations;
- every field of the source `ParentRegistrationYield`, indexed directly by the
  source fiber rather than by a later record projection; and
- `FiberControlRelated sourceFiber targetFiber`.

The producer opened `ParentRegistrationYield` where its parent fiber was
concrete, called `pointwiseControlLookupFound`, and sealed the returned target
fiber, target lookup, and relatedness with the deconstructed yield evidence.
That producer body elaborated. The consumer opened the package once and was
intended to construct only the target `ParentRegistrationYield`.

Every package field and local proof was quantity 0. The package was private and
introduced no caller-owned target capital.

## Attempt ledger

### Attempt 1 — parser form

The first declaration used record-style parameter syntax for an indexed data
family:

```idris
data LocatedTransportedParentYield
  (name, key, world, error : Type) ... where
```

Idris requires a colon and function-kind arrows for this form. The parser
reported:

```text
Expected 'where'.
```

Parser failures count against the fresh budget. The declaration was corrected
to:

```idris
data LocatedTransportedParentYield :
  (name, key, world, error : Type) -> ... -> Type where
```

### Attempt 2 — separate fiber patterns

The package producer checked. The projection-only consumer then matched the
source and target fiber variables separately from the final
`FibersControlRelated` evidence. Idris correctly diagnosed the repeated target
index:

```text
Pattern variable targetFiber unifies with:
  MkFiber ... rightLifecycle
Suggestion: Use the same name for both pattern variables, since they unify.
```

This confirmed the package had successfully moved the earlier
`.parentFiberAtYield` wall into an ordinary named-fiber unification.

### Attempt 3 — correlated constructor patterns

The consumer was revised to pattern the two package fibers directly as:

```idris
MkFiber component leftParent leftRetired leftTable leftLifecycle
MkFiber component rightParent rightRetired rightTable rightLifecycle
```

and reused the same names in `FibersControlRelated`. This closed the repeated
fiber-variable wall. The source lifecycle equation then reindexed
`LifecycleControlRelated` to a source `Reloading` lifecycle, and matching
`ReloadingControls` exposed the target accumulator/view and exact remaining
program.

The final target record construction reached one strictly narrower equality:

```text
Mismatch between:
  Reloading (sourceStep :: sourceContinuation) rightAccumulator rightView
and:
  rightLifecycle.
```

The target lookup still mentioned the package's original `rightLifecycle`,
while eliminating a *derived* reindexed lifecycle relation did not rewrite that
original index. No source projection, component mismatch, protocol mismatch, or
dictionary mismatch remains.

## Classification

This is not a new semantic wall class. The target lifecycle is constructively
known to be the corresponding `Reloading` state through
`ReloadingControls`; only an explicit equality must be returned to reindex the
target lookup proof. The diagnostic progression is monotone:

1. projection-indexed source fiber (revision 70);
2. ordinary target-fiber nonlinear pattern (attempt 2);
3. target lifecycle equality at `targetFound` (attempt 3).

The three-attempt package budget is exhausted, so the whole uncommitted unit was
reverted as required. Bundle field 2 was not opened after that stop.

## Recommended next unit

Separate the lifecycle view from the outer package, while keeping it private and
producer-owned:

```idris
data LocatedReloadingControl ... leftLifecycle rightLifecycle where
  MkLocatedReloadingControl :
    (rightAccumulator : ...) ->
    (rightView : ...) ->
    rightLifecycle = Reloading
      (sourceStep :: sourceContinuation) rightAccumulator rightView ->
    LocatedReloadingControl ... leftLifecycle rightLifecycle
```

A single erased producer should consume:

- `leftLifecycle = Reloading ...`; and
- `LifecycleControlRelated leftLifecycle rightLifecycle`;

then return the explicit target lifecycle equality. The outer
`LocatedTransportedParentYield` producer can immediately `replace` the target
lookup equation along that equality and seal an already constructed target
`ParentRegistrationYield`. Its consumer then becomes a literal projection of
the target yield, with no second lifecycle or fiber elimination.

This is still the accepted whole-package transport pattern. It adds no public
surface and no detached target premise.

## Frozen-capital audit

The reverted experiment did not change:

- `CandidateRegistrationSwapSafety` or
  `LocalRelationalDiamond.registrationSwapSafety`;
- any of the four genuine diamond producers or R19;
- `ReplayInvariantBundle`, `AdjacentSwapResult`, RAR, or revision-20 maps;
- the joint generator, generator-origin, RAR chain, projection conversion,
  global ordinal, occurrence correspondence, or suffix alignment regions;
- the 1183-byte `adjacentSwapSuffixSpike` declaration, SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- `src/`, `dgamma.ipkg`, or CP3 blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.

## Status

- transported parent-yield package: **not retained; attempt budget exhausted**;
- package producer before lifecycle consumption: **elaborated experimentally**;
- remaining obstruction: **explicit target lifecycle equality for target-lookup reindex**;
- bundle field 1: **proved**;
- bundle field 2: **unchanged / not proved**;
- bundle fields 3–15: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against accepted 3–17 band: **one shift consumed; 2–16 remain**.
