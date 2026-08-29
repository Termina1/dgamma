# O6 revision 65: stage origin and whole RAR close; occurrence fold stop

## Scope

Grind shift #73 (overall #127) resumed from accepted revision-64 HEAD
`a2f839e`. The authorized private stage-only Here/Tail target view, its producer,
`LocatedConsIteratorStageOrigin`, the whole-cons RAR constructor, the recursive
whole-suffix RAR fold, and positional action-occurrence/ordinal cons helpers all
closed constructively in six retained commits.

The next generated-registration occurrence-fold unit exhausted its three-attempt
budget at one parser-stable conversion declaration. Its uncommitted code was
reverted. Bundle composition and final adjacent-result assembly were not
opened. Safe retained HEAD is `43c6e18`.

The frozen `JointLocatedConsTargetGenerator` and closed generator-origin proof
from `e3fab3a` were not modified.

## Stage-only target view — `5a3927c`

`JointLocatedConsTargetStage` is private and indexed directly by the exact
original whole `IteratorStage`. It has exactly two constructors:

- `JointConsTargetStageHere`, carrying an exact singleton local stage;
- `JointConsTargetStageLater`, carrying an exact tail-local stage.

Both constructors own local-to-whole forward and yielded runtime equations and
the exact whole-to-local iterator-outcome equation. The declaration checked on
attempt 1. It changes no public or revision-20 surface.

## Stage-only producer — `b2dc9ea`

`jointConsTargetStageRegion` applies the revision-64 total recipe literally:

- `occurs` is a universally quantified explicit argument;
- only `OccursHere` / `OccursLater later` is eliminated;
- `occurrenceView` remains an untouched dependent argument;
- exact local `StageFromAdvance` values are constructed at the producer;
- runtime equations are projected from `LocatedConsTargetStageRuntime`.

`consumeJointConsTargetStageRuntime` and `locateJointConsTargetStage` delegate
through the closed candidate-(1) producer. No nested generator/stage left-hand
side exists. The complete producer checked on attempt 1.

## Iterator origin — `8aeb192`

The retained iterator-origin chain contains:

- exact widening/prepending iterator-outcome lemmas;
- one-elimination `LocatedReplayIteratorStageOrigin` for a head or tail RAR;
- `LocatedConsIteratorStageOrigin`, owning the exact whole source stage and
  target-to-source outcome equation;
- widening and prepending lifts; and
- a two-clause consumer of the stage-only view.

Both Here and Tail clauses closed on attempt 1. This avoids all generic
`TraceEffectGenerator` junk cases diagnosed in revision 64. R16 passed before
and after commit.

## Whole-cons and whole-suffix RAR

### Cons constructor — `bc70c03`

`consRelationalReplayCorrespondence` constructs all four RAR fields by
projecting:

- generator origin and universally quantified relational map capital from
  `LocatedConsReplayGeneratorOrigin`; and
- iterator origin and exact outcome capital from
  `LocatedConsIteratorStageOrigin`.

The constructor checked on attempt 1. Both producer packages occur under
syntactically identical target applications, so field correlation remains
definitional rather than caller-supplied.

### Recursive suffix fold — `4dec598`

`sealedSuffixRelationalReplayCorrespondence` folds a
`SealedSuffixReplaySpine` recursively through the cons constructor.

Attempt 1 found the correct empty-boundary issue: source and replayed empty
traces may be indexed by different states, so an identity iterator-stage lambda
cannot identify their phantom endpoints:

```text
Mismatch between:
  replayedFinal and sourceFinal.
```

Attempt 2 added constructive impossibility eliminators for a
`TraceEffectGenerator` or `IteratorStage` over `NoTransitions`. The empty RAR
then eliminates impossible inputs rather than equating endpoints. The recursive
case uses `consRelationalReplayCorrespondence`. The fold checked total.

## Positional action occurrence and ordinal composition — `43c6e18`

Three cons helpers now reconstruct target action occurrences over a source cons
trace:

- `consPointwiseActionOrigin`;
- `consPointwiseActionTagPreserved`;
- `consPointwiseActionOrdinalPreserved`.

They distinguish head/tail by the dependent occurrence prefix and use the exact
whole-trace decomposition. Tail occurrences recurse beneath one source head,
so ordinal preservation is `cong S` of the recursive equality. No raw action
filtering, DecEq dictionary identity, or detached occurrence enters.

Attempt 1 was parser-only: an inline `case ... of Refl =>` application wrapped
onto the following line was indented as a second block entry. Attempt 2 used
explicit two-line case clauses and checked. This unit is retained.

## Generated-registration whole-occurrence fold: three-attempt stop

The intended next unit would:

1. eliminate occurrences in `NoTransitions`;
2. convert an exact located child O-Insert action occurrence into
   `LocatedGeneratedRegistration` without changing its dependent prefix;
3. recursively build whole-suffix action origin, tag, and ordinal functions;
4. derive generated-origin coherence and generation preservation; and
5. construct `ActionRegistrationReplayCorrespondence` with identity generation
   renaming, justified by positional ordinal preservation.

All recursive action bodies were written, but parsing stopped at the first
conversion implementation before elaboration.

### Attempt 1

The conversion was named `actionOccurrenceAsGenerated` and pattern matched the
`MkLocatedActionOccurrence` constructor directly. Idris reported:

```text
Error: Couldn't parse declaration.
... actionOccurrenceAsGenerated
```

### Attempt 2

The declaration was renamed `actionOccurrenceToGenerated` and its left-hand
side placed on one logical clause. The parser stopped at the same declaration
start with the same error.

### Attempt 3

The declaration was renamed `actionOccurrenceToBirth`, removing `Generated`
from the identifier entirely. The parser again stopped at the implementation
start:

```text
Error: Couldn't parse declaration.
... actionOccurrenceToBirth (MkLocatedActionOccurrence ...
```

The unchanged error across three names shows the identifier was not the cause.
No generated-registration body reached elaboration or totality checking. Parser
failures consume the budget under the grind rules, so the complete uncommitted
unit was reverted.

## Next design gate

Two narrow cures are available without reopening retained capital:

1. keep the conversion type but implement it with an ordinary variable left-hand
   side and record projections in the body, avoiding the indexed record
   constructor pattern at the declaration boundary; or
2. avoid the conversion entirely and define a direct structural
   `LocatedGeneratedRegistration` cons-origin helper parallel to
   `consPointwiseActionOrigin`, then prove action-origin coherence field by
   field.

Candidate 1 is the smaller parser cure. Candidate 2 is fallback if the variable
body elaborates but loses field correlation. Either cure must leave all stage,
generator, RAR, spine, public, and result interfaces unchanged. The next unit
must still use identity generation renaming only after proving global positional
ordinal preservation.

Cure (c), bundle assembly, and final result assembly remain unopened.

## Status

- stage-only Here/Tail view: **closed**;
- stage-only producer: **closed**;
- `LocatedConsIteratorStageOrigin`: **closed**;
- whole-cons RAR: **closed**;
- recursive whole-suffix RAR: **closed**;
- positional action occurrence/tag/ordinal cons helpers: **closed**;
- whole-suffix `ActionRegistrationReplayCorrespondence`: **STOP after 3 attempts; reverted**;
- target `ReplayInvariantBundle` composition: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against nominal 2–14: **1 shift consumed; nominal 1–13 remain**.
