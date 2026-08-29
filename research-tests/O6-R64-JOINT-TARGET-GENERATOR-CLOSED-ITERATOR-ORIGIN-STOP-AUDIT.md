# O6 revision 64: joint target generator closes; iterator origin stop

## Scope

Grind shift #72 (overall #126) resumed from accepted revision-63 HEAD
`5b70da8`. The authorized candidate-(2) dependent outer wrapper, its producer
delegation through the closed candidate-(1) package, and
`LocatedConsReplayGeneratorOrigin` all closed constructively in three retained
commits. `LocatedConsIteratorStageOrigin` then exhausted its own three-attempt
budget. Its uncommitted code and the associated attempted strengthening of the
already-committed wrapper were reverted.

Whole-suffix cons RAR, occurrence/ordinal/bundle composition, and final assembly
were not opened. Safe retained HEAD is `e3fab3a`.

## Candidate-(2) outer wrapper — `817f4a8`

`JointLocatedConsTargetGenerator` adds six direct target regions:

- actual Here/Tail regions carry the original whole target, its exact local
  generator, and the local-to-whole runtime map equation;
- forward Here/Tail regions jointly carry the original whole iterator stage,
  its exact locally reconstructed `StageFromAdvance` result, its runtime map
  equation, and its exact iterator-outcome equation;
- yielded Here/Tail regions carry the same capital plus the exact yielded
  origin.

The iterator constructors therefore expose no captured `occurs` index to their
consumers. The wrapper declaration checked on its first attempt. It is private,
so its constructors do not widen public revision-20 surfaces.

## Producer delegation — `7e40403`

The producer delegates strictly through the existing total chain:

```text
locateConsTargetGenerator
  -> LocatedConsTargetStageRuntime
  -> consumeJointConsTargetGenerator
```

No generator/stage nested left-hand-side pattern was restored.

Two global dependent region functions explicitly quantify the occurrence as an
argument together with the whole stage, complete `StageFromAdvance` payload,
local stage result, runtime equation, and outcome equation.

### Attempt 1

All intended constructor bodies were present. Three local alias identities
remained abstract:

- the exact local stage alias prevented the outcome equation from reducing in
  forward Here;
- the analogous yielded Here alias failed identically;
- an unannotated actual `targetWhole` alias failed to unify with its exact whole
  generator.

The iterator bodies were repaired by passing the exact `StageFromAdvance`
expression directly and explicitly composing the outcome equation. Actual
whole/local generator aliases received exact `TraceEffectGenerator` types.

### Attempt 2

All bodies elaborated. Coverage reported seven hidden dependent payload
families in each `OccursLater` clause because the clauses redundantly matched
both the universally quantified `OccursLater later` argument and the
`ConsStageOccursLater targetHead later` view.

### Attempt 3

The region functions now eliminate only their universally quantified
`OccursIn` argument. The corresponding view remains a dependent argument but is
not independently refined. This covers exactly `OccursHere` and
`OccursLater later`, and both producer functions checked total.

This is the precise repair requested by the revision-63 gate: `occurs` is no
longer captured as a fixed outer value. R16 passed before and after commit.

## Whole-cons generator origin — `e3fab3a`

`LocatedConsReplayGeneratorOrigin` owns the exact source whole-cons generator
and its universally quantified relational map proof against the exact original
whole target generator.

The producer uses:

- one-elimination head/tail `LocatedReplayGeneratorOrigin` packages;
- retained widening/prepending generator lifts and exact lift-map lemmas;
- the six candidate-(2) regions, which require no nested occurrence case;
- the exact target annotations established by revision-63 attempt 2.

All six branches and `locateConsReplayGeneratorOrigin` checked on attempt 1.
R16 passed before and after commit. This closes the generator-origin component
of whole-cons RAR.

## `LocatedConsIteratorStageOrigin`: three-attempt stop

The attempted package paired the whole-cons source iterator stage with exact
preservation of the original target iterator outcome. It introduced local
head/tail stage-origin packages, exact outcome lemmas for widening/prepending,
and a consumer of forward candidate-(2) regions.

### Attempt 1: local aliases and deliberately generic actual regions

Two local `sourceWhole` aliases did not unfold in the final outcome equations:

```text
Can't solve constraint between:
  widenSingletonIteratorStage sourceTail sourceSingleton
and:
  sourceWhole.
```

The prepend branch failed analogously.

More importantly, coverage correctly observed that the private actual-region
constructors from `817f4a8` are deliberately typed over generic whole/local
`TraceEffectGenerator` values. Their types therefore admit a value whose
`targetWhole` is an `IteratorForwardGenerator`, even though the live producer
constructs those regions only for actual generators:

```text
Missing cases:
  ... (JointConsActualHere (IteratorForwardGenerator _) _ _)
  ... (JointConsActualLater (IteratorForwardGenerator _) _ _)
```

Direct source-stage construction fixed the alias equations, but not this
constructor-level coverage fact.

### Attempt 2: exact actual-constructor strengthening

The two generic actual constructors were privately strengthened to introduce
only exact `ActualForwardGenerator` Here/Tail results, and the live producer and
generator consumer were updated accordingly.

Idris rejected the first generator-consumer left-hand side because its separate
`targetHead` pattern variable was forced to the constructor's exact fired
transition:

```text
Pattern variable targetHead unifies with:
  Fired ...
Suggestion: Use the same name for both pattern variables, since they unify.
```

There is no constructor field naming that fired transition, so the suggested
same-name repair is unavailable in that clause shape.

### Attempt 3: anonymous outer target head

Replacing the separate target-head pattern with `_` allowed the body to type,
but totality then generated four hidden `Fired` dependent families for the
previously closed generator-origin consumer:

```text
consumeJointConsReplayGeneratorOrigin is not covering.
Missing cases:
  consumeJointConsReplayGeneratorOrigin _ (Fired _ _ _ _ _) _ _ _ _ _
  ... (four residual families)
```

Thus strengthening the existing candidate-(2) generator wrapper would reopen
the just-closed generator producer with the same hidden dependent left-hand-side
coverage problem the architecture was designed to avoid.

The iterator-origin budget was exhausted. All iterator-origin code and wrapper
strengthening were reverted together, restoring exact retained HEAD `e3fab3a`.
No fourth encoding, impossible clause, target equality, public change, or
whole-cons RAR assembly was attempted.

## Next design gate

The generator wrapper is sufficient and now proven for generator origin. The
iterator stage needs a narrower producer-owned target view whose codomain is
indexed directly by an `IteratorStage`, not by the more general
`TraceEffectGenerator` wrapper. A two-constructor Here/Tail stage-region family
can be produced from `LocatedConsTargetStageRuntime` by the already-proved
universally quantified occurrence eliminator recipe, without changing
`JointLocatedConsTargetGenerator` or reopening generator origin.

This is a new private stage-only package/consumer design. It must be approved
before implementation. It may not add equality premises or alter
`RelationalReplayCorrespondence`, revision-20 fields, the outer endpoint/result
interfaces, or any public signature.

Cure (c) remains unopened.

## Status

- candidate-(2) joint generator wrapper: **closed**;
- producer delegation through candidate-(1): **closed**;
- `LocatedConsReplayGeneratorOrigin`: **closed**;
- `LocatedConsIteratorStageOrigin`: **STOP after 3 attempts; reverted**;
- whole-suffix cons RAR: **blocked at iterator origin**;
- occurrence/ordinal/bundle composition: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against accepted 3–15 band: **1 shift consumed; nominal 2–14 remain**.
