# O6 revision 66: conversion closes; empty occurrence semantic stop

## Scope

Grind shift #74 (overall #128) resumed from accepted revision-65 HEAD
`80e160d`. Authorized cure 1 for the indexed action-to-generated-registration
conversion closed on its first attempt and is retained at `35dcbe5`.

The next whole-suffix occurrence-fold attempt reached elaboration, but failed
semantically at the empty-trace action-occurrence eliminator. Per the explicit
revision-65 gate ruling, any semantic elaboration/unification/coverage failure
requires an immediate stop-audit rather than switching to cure 2 or consuming
more attempts. The full uncommitted fold was reverted.

Global positional ordinal composition, identity generation renaming, target
bundle composition, and final adjacent-result assembly remain unopened. The
frozen generator, stage, whole-suffix RAR, revision-20, and result interfaces
were not modified. Safe retained HEAD is `35dcbe5`.

## Cure 1 conversion — `35dcbe5`

`locatedChildRegistrationFromAction` has the exact authorized type:

```idris
LocatedActionOccurrence
  (OInsert child (ChildOf parent) component) trace ->
LocatedGeneratedRegistration child parent component trace
```

Its left-hand side is an ordinary variable. The body constructs
`MkLocatedGeneratedRegistration` exclusively from the seven projections of the
input occurrence:

- action-before state;
- action-after state;
- dependent prefix;
- exact located transition;
- dependent suffix;
- exact child O-Insert action equation; and
- exact whole-trace decomposition.

No indexed record constructor occurs in the left-hand side. The declaration and
containing module checked on attempt 1. R16 passed before and after commit.

This confirms the three revision-65 failures were declaration-pattern parser
failures rather than a type obstruction in the conversion itself. Cure 2 was
not activated.

## Whole-suffix occurrence fold: semantic stop

The uncommitted continuation contained:

- projection-based conversion round-trip;
- an empty-trace action-occurrence eliminator;
- recursive whole-suffix action origin;
- recursive tag preservation;
- a global positional action-ordinal theorem;
- generated-registration origin and action-origin coherence;
- generated ordinal preservation; and
- final `ActionRegistrationReplayCorrespondence` construction using identity
  generation renaming only after the global positional theorem.

Parsing succeeded. Elaboration stopped at the first empty-trace helper:

```idris
0 noLocatedActionOccurrenceInEmpty :
  LocatedActionOccurrence action NoTransitions -> Void
```

The attempted proof used:

```idris
case cong transitionCount decomposition of Refl impossible
```

Idris rejected the `Refl` branch as not definitionally impossible:

```text
Error: While processing right hand side of
noLocatedActionOccurrenceInEmpty.
... is not a valid impossible case.
```

The reason is precise: the occurrence prefix is abstract. Although
`appendTransitions prefix (MoreTransitions located suffix)` is mathematically
nonempty, `transitionCount` cannot normalize through an abstract prefix far
enough for constructor disjointness to discharge `Refl` definitionally.

This is an elaboration-level semantic failure, not another parser/mechanical
failure. The gate therefore forbids switching to cure 2 and requires stopping
immediately. No repair attempt was made, and identity generation renaming was
not retained.

## Next design gate

The narrow constructive repair is an explicit structural nonemptiness lemma:

```idris
appendLocatedTransitionNotEmpty :
  (prefix : Transitions initial before) ->
  (located : Transition before afterState) ->
  (suffix : Transitions afterState finalState) ->
  appendTransitions prefix (MoreTransitions located suffix) = NoTransitions ->
  Void
```

It can recurse on `prefix`; both `NoTransitions` and `MoreTransitions` cases
reduce the left side to `MoreTransitions ...`, so constructor disjointness is
visible without arithmetic normalization. The empty-occurrence eliminator would
apply this lemma to its stored decomposition.

Authorization is required because the current fold unit has encountered the
semantic stop condition. If opened, the retry must preserve the closed
projection conversion and must still establish global positional ordinal
preservation before selecting identity generation renaming. Cure 2 remains
unused and should not be activated unless a new gate explicitly allows it.

No public or frozen declaration needs to change.

## Status

- projection-based generated-registration conversion: **closed**;
- generated-registration cure 2: **not activated**;
- whole-suffix action occurrence origin/tag/ordinal fold: **semantic STOP; reverted**;
- whole-suffix `ActionRegistrationReplayCorrespondence`: **blocked**;
- global identity generation renaming: **not selected**;
- target `ReplayInvariantBundle` composition: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against nominal 1–13: **1 shift consumed; lower bound exhausted, upper remainder 12**.
