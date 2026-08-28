# O6 revision 59: target-localization producer coverage gate

## Scope

Shift #67 (overall #121) resumed from accepted revision-58 HEAD `39c5546` and
implemented the authorized private six-constructor target-generator localization
GADT. The constructors themselves elaborated after explicit endpoint repair,
but the total generic producer exhausted its fresh three-attempt budget at a
coverage wall before a commit-worthy unit existed. All localization code was
reverted.

The iterator-stage localization GADT, both located cons origin packages, cons
RAR, occurrence/ordinal/bundle composition, and final adjacent assembly were not
opened. The safe retained boundary remains `39c5546`; the indexed semantic-head
eliminator and concrete eight-family suffix spine remain intact.

## Attempted joint-introduction GADT

`LocatedConsTargetGenerator` was indexed by:

- the original target head and target tail;
- actor; and
- the original whole-target `TraceEffectGenerator` over that cons trace.

Its six constructors jointly introduced the original whole target and its exact
local occurrence form:

1. actual generator at `OccursHere`;
2. actual generator at `OccursLater`;
3. iterator-forward generator at `OccursHere`;
4. iterator-forward generator at `OccursLater`;
5. iterator-yielded generator at `OccursHere`;
6. iterator-yielded generator at `OccursLater`.

Every `Here` constructor fixed the target head index to the exact stored
`Fired`; every `Later` constructor retained the exact target head and an
`OccursIn ... targetTail`. Iterator constructors retained all exact stage
indices, source lookup, program suffix, and yielded origin. No equality premise,
dictionary identity, or caller capital appeared.

## Attempt 1: target-tail endpoint not introduced

The first constructor declaration left the `Here` target tail implicit while
refining the target head's middle state to the actual transition endpoint. Idris
could not infer the refined tail type:

```text
Can't solve constraint between:
  ?type_of_targetTail
and:
  Transitions afterState ?targetFinal.
```

This was repaired by making the exact `targetTail : Transitions afterState
 targetFinal` an argument of each `Here` constructor. The change strengthens no
boundary; it only introduces the already indexed tail at the constructor.

## Attempt 2: hidden stage endpoints not bound

After the tail repair the constructor family elaborated far enough to reach the
producer. Iterator locator clauses attempted to pass the hidden `before` and
`afterState` indices of `StageFromAdvance`, but their patterns had not named
those implicits:

```text
Undefined name before.
```

All four iterator patterns were repaired with explicit
`StageFromAdvance {before} {afterState} ...` bindings.

## Attempt 3: producer still has two scrutinees

The six-constructor GADT declaration then elaborated, but its generic producer
was rejected as non-covering. The producer statement took both:

```text
(targetHead : Transition targetFirst targetMiddle)
```

and:

```text
(target : TraceEffectGenerator ...
  (MoreTransitions targetHead targetTail))
```

as explicit arguments. Although every target generator occurrence constrains
its cons head, coverage continued to scrutinize the explicit head and generator
independently. It reported a very large family of indistinguishable cases such
as:

```text
locateConsTargetGenerator (Fired _ _ _ _ _) _ _
  (IteratorForwardGenerator _)
```

and the analogous yielded cases.

Thus joint introduction successfully describes the *result*, but its producer
cannot be total while the target head remains a separate explicit scrutinee.
This is the same structural coverage class as the pre-indexed head dispatcher,
now localized one level earlier at target classification. It is not a failure
of the six constructors' target identity: no consumer was reached.

The third attempt exhausted the unit budget. No fourth clause strategy,
coverage pragma, partiality, or statement rewrite was attempted. All code was
reverted.

## Statement-shape question

The minimal private candidate is to make `targetHead` and `targetTail` implicit
indices of the locator and leave the whole target generator as its only
explicit scrutinee. Each generator constructor's `OccursIn` proof would then
refine the implicit cons head while returning the six-constructor GADT. This is
analogous to the successful revision-57 change that made `sourceStep` implicit
in `replayPointwiseJointHead`.

A stronger alternative would re-quantify the whole cons-RAR statement around an
already localized target package. That is the escalation named by the
revision-58 gate and may intersect frozen revision-20 surfaces. It is not
proposed or drafted here.

The narrow implicit-index locator change is private, but the bounded failure
requires a supervisor gate before even that change is attempted. No direct
target elimination inside separate RAR fields is admissible.

## Status

- six target-generator localization constructors: **type shape elaborated, but
  whole unit reverted because its producer is not total**;
- target-generator localization producer: **STOP at coverage after 3 attempts**;
- target-stage localization GADT: **unopened**;
- located cons packages: **unopened**;
- whole-suffix RAR: **blocked**;
- occurrence/ordinal/bundle composition: **unopened**;
- final adjacent assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- estimate: accepted **3–15 shift** band held pending the target-localization
  producer statement gate.
