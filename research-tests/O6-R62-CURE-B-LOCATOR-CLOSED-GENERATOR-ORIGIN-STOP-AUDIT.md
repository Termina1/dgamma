# O6 revision 62: cure-(b) locator closed; generator-origin package stop

## Scope

Grind shift #70 (overall #124) resumed from the accepted revision-61 design at
`006108d`. Four cure-(b) dependency units closed in lemma-sized commits. The
next unit, `LocatedConsReplayGeneratorOrigin`, exhausted its fresh three-attempt
budget at the first iterator-forward target-identity transport. All uncommitted
code for that package was reverted.

`LocatedConsIteratorStageOrigin`, whole-suffix cons RAR, occurrence/ordinal/
bundle composition, and final adjacent assembly were not opened. The safe
retained boundary is `5c82ad0`.

## Closed units

### Exact occurrence view — `2042729`

The R44-validated `ConsStageOccurrenceView` and `viewConsStageOccurrence` are
now private research-spike capital. The family has exactly two constructors:
head and tail. It is total, keeps deeper positions under the tail witness, and
introduces no equality or dictionary premise.

### Whole-stage target package — `1949342`

`LocatedConsTargetStage` is indexed by the original whole `IteratorStage` over
the target cons trace. `locateConsTargetStage` matches `StageFromAdvance` once,
constructs the exact occurrence view once, and retains every dictionary,
checked equation, fiber lookup, lifecycle program, and reachable suffix under
the original stage index. The containing module and R16 passed on attempt 1.

### Whole-generator outer locator — `11eb0c4`

The first attempt tried to consume the occurrence view immediately into the six
revision-60 `Here`/`Later` target constructors. Idris accepted the outer wrapper
matches but marked the inner dependent case blocks non-covering:

```text
Calls non covering functions:
  case block in case block in locateConsTargetGenerator
```

This is the same nested dependent-result limitation pinned by R44, now at the
specific six-constructor codomain.

On attempt 2 the accepted cure-(b) package shape was used directly:

- actual generators carry the original occurrence and exact occurrence view;
- forward generators carry the original stage and one
  `LocatedConsTargetStage`;
- yielded generators carry the original stage, origin, and one stage package.

The outer `locateConsTargetGenerator` has exactly three clauses and is total.
It matches only the generator wrapper and never decomposes stage occurrence in a
left-hand side.

The old six-way GADT is preserved explicitly as
`RetiredSixWayLocatedConsTargetGenerator`, with all six constructors renamed
`RetiredConsTarget...`. Its documentation records why it was superseded. No
capital was silently dropped.

### Cons-lift and correlated RAR capital — `5c82ad0`

The shift retained constructive helpers for:

- widening a singleton occurrence, stage, or generator under a suffix;
- prepending a head before a tail occurrence, stage, or generator;
- exact executable generator-map preservation for both lifts; and
- `LocatedReplayGeneratorOrigin`, produced by one
  `MkRelationalReplayCorrespondence` elimination so an origin and its map proof
  remain correlated.

These helpers checked on attempt 1 and R16 remained green. They do not widen a
caller boundary and expose no public constructor.

## `LocatedConsReplayGeneratorOrigin`: three-attempt stop

The attempted record remained indexed by the original whole-target generator.
Its fields were the whole-source generator and universally quantified
`PartialMapsRelated` evidence to that exact target. The producer consumed:

1. the total cure-(b) whole-generator location once; and
2. the selected head/tail RAR once through `LocatedReplayGeneratorOrigin`.

It then widened a head source origin or prepended a head to a tail source
origin.

### Attempt 1: original target still not identified at the record boundary

The first body reconstructed a local target generator inside each occurrence
view branch and used the correlated head/tail origin/map package. Source origin
correlation was solved, but the record constructor could not identify the
reconstructed local target map with the original whole-target parameter:

```text
Can't solve constraint between:
  traceGeneratorRuntimeMap
    (traceEffectGeneratorRuntime targetSingleton) y
and:
  partialEffectMapFor nameEq keyEq action tag before y.
```

This is narrower than revision 58: the target wrapper and occurrence view are
now retained, and only the final local-to-original executable-map identity is
missing.

### Attempt 2: explicit local-to-original runtime-map bridge

Each branch added a producer-owned pointwise `targetExact` bridge from the local
target generator map to the original target expression, then used
`replayPartialRewrite` together with the source lift equation.

Idris rejected the first actual-head bridge as `Refl` because the inferred local
`targetSingleton` still remained behind a proof-free runtime projection rather
than reducing to the explicit actual map:

```text
Can't solve constraint between:
  partialEffectMapFor nameEq keyEq action tag before state
and:
  traceGeneratorRuntimeMap
    (traceEffectGeneratorRuntime targetSingleton) state.
```

### Attempt 3: exact local generator and stage annotations

All six local target generators received exact singleton/tail trace types, and
all four iterator local stages received exact `IteratorStage` trace types. This
closed the actual-generator identity and advanced to the first iterator-forward
branch.

The remaining failure is now precisely the original whole-stage identity:

```text
Can't solve constraint between:
  traceGeneratorRuntimeMap
    (traceEffectGeneratorRuntime (IteratorForwardGenerator stage)) state
and:
  map (...) (iteratorStageEffectData nameEq keyEq actor fiber view step rest state).
```

The right side is the explicitly reconstructed local stage's forward map. The
left side is the original whole `stage` parameter stored by
`LocatedConsForwardGenerator`. Matching the nested `LocatedConsTargetStage`
package exposes all its fields, but Idris does not rewrite the independently
stored outer `stage` variable to that constructor expression strongly enough for
`Refl`.

The third attempt exhausted the unit budget. No fourth nested pattern, equality
field, caller premise, direct RAR-field elimination, or dictionary identity was
attempted. The whole generator-origin package was reverted.

## Exact next representation question

Cure (b) solved coverage and retained the original whole generator, but the
outer wrapper currently stores:

```text
(stage : IteratorStage ... whole)
(located : LocatedConsTargetStage ... stage)
```

as two constructor arguments. Eliminating `located` refines its own index, yet
the executable map of the separately named outer `stage` does not reduce. The
next representation must jointly introduce the original whole generator and
the exact stage constructor expression under one package elimination, or must
package the producer-owned local-to-whole runtime-map bridge at target
localization time when both are definitionally available.

The most local candidates are:

1. strengthen `LocatedConsTargetStage` with producer-owned runtime equations for
   forward and yielded projections, indexed directly by its original stage; or
2. make the forward/yielded `LocatedConsTargetGenerator` constructors introduce
   the exact `StageFromAdvance ... occurs ...` expression in their result rather
   than storing an independently named `stage` plus package.

Candidate 2 risks restoring the nested-pattern coverage failure unless the
outer producer still delegates through the stage package. Candidate 1 preserves
the successful three-clause locator and is the narrower likely direction, but
requires a new supervisor-approved package change after the bounded stop.

No revision-20 surface or public result is implicated by either private
candidate. Cure (c) remains unopened.

## Status

- occurrence view: **closed**;
- whole-stage target package: **closed**;
- cure-(b) outer generator locator: **closed**;
- retired six-way shape: **explicitly retained and documented**;
- cons-lift and inner RAR correlation helpers: **closed**;
- `LocatedConsReplayGeneratorOrigin`: **STOP after 3 attempts; reverted**;
- `LocatedConsIteratorStageOrigin`: **unopened**;
- whole-suffix cons RAR: **blocked**;
- occurrence/ordinal/bundle composition: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- accepted remaining band: **3–15 shifts**, held pending this private
  target-stage identity package gate.
