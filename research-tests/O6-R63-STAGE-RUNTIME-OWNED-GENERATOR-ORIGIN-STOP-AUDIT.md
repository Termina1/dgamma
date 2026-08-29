# O6 revision 63: stage runtime equations retained; generator origin stop

## Scope

Grind shift #71 (overall #125) resumed from accepted revision-62 HEAD
`64e6280`. The authorized candidate-(1) target-stage runtime-equation package
and its producer closed in two lemma-sized commits. The subsequent fresh
three-attempt `LocatedConsReplayGeneratorOrigin` retry exhausted at dependent
occurrence-view elimination. All uncommitted generator-origin code was reverted.

`LocatedConsIteratorStageOrigin`, whole-suffix cons RAR, occurrence/ordinal/
bundle composition, and final assembly were not opened. Safe retained HEAD is
`6710446`.

## Candidate-(1) package revision

### Runtime-owning package declaration — `b74fbc1`

`LocatedConsTargetStageRuntime` is indexed by the original whole
`IteratorStage`. Its sole constructor stores:

- that exact original stage;
- the complete `StageFromAdvance` payload;
- the exact `ConsStageOccurrenceView`;
- a forward-generator runtime projection equation from the original stage to
  the explicit stored stage payload;
- a yielded-generator runtime projection equation for every origin/input; and
- an exact `iteratorStageOutcome` equation.

The first declaration attempt exposed a purely syntactic actor ambiguity: the
original stage used an implicit actor before a later explicit actor argument.
The constructor was repaired by introducing the actor first and indexing the
stored stage with that same value. Attempt 2 checked. No target equality,
dictionary equality, or caller-supplied equation was introduced.

### Producer and live locator update — `6710446`

`locateConsTargetStageRuntime` matches the original stage once as
`stage@(StageFromAdvance ...)` and constructs all three runtime equations by
`Refl` at the producer. The live forward/yielded
`LocatedConsTargetGenerator` constructors now own this runtime package rather
than the earlier structural package. The three-clause outer generator locator
remains total and unchanged in shape.

The original structural `LocatedConsTargetStage` remains as prior checked
private evidence; the runtime-owning package is the live one. The containing
module and R16 passed on attempt 1.

## `LocatedConsReplayGeneratorOrigin`: three-attempt stop

The retry used producer-correlated head/tail RAR origins plus generic widening
and prepending helpers. Its record remained indexed by the exact original whole
Target generator. Actual, forward, and yielded target localizations were
consumed through the live three-constructor wrapper.

### Attempt 1: unannotated whole target alias

The new runtime equations were used to bridge locally reconstructed iterator
stages to the original packaged stage. The first forward bridge nevertheless
failed because an unannotated local `targetWhole` alias stayed abstract:

```text
When unifying:
  IteratorForwardGenerator packagedStage
and:
  targetWhole
Mismatch between:
  IteratorForwardGenerator packagedStage and targetWhole.
```

The runtime equation itself had the required endpoints; the local alias needed
its exact full cons-trace generator type.

### Attempt 2: runtime identity closes, occurrence case coverage remains

All four forward/yielded `targetWhole` aliases received exact
`TraceEffectGenerator ... (MoreTransitions targetHead targetTail)` types. The
runtime equations then closed the local-to-original map identities and every
record body elaborated.

Totality failed only because the two inner occurrence-view case blocks
(forward/yielded) were marked non-covering:

```text
Calls non covering functions:
  case block in case block in consumeConsReplayGeneratorOrigin
```

Thus candidate (1) solved the stage runtime identity wall it was designed to
solve. The residual is again dependent elimination shape: a case block returning
the generator-indexed origin record is not accepted even though
`ConsStageOccurrenceView` has exactly two constructors.

### Attempt 3: named local eliminator cannot refine a fixed occurrence index

Each forward/yielded case was replaced with a named local `go` function whose
explicit argument was:

```idris
(locatedView : ConsStageOccurrenceView occurs)
```

The first `ConsStageOccursHere` clause was rejected before its body because the
captured `occurs` index was fixed rather than universally quantified:

```text
When unifying:
  ConsStageOccurrenceView OccursHere
and:
  ConsStageOccurrenceView occurs
Mismatch between: OccursHere and occurs.
```

The local function did not gain a dependent occurrence index merely by naming
the view; it must quantify the occurrence (and the corresponding whole stage
expression) together. That is precisely the joint-introduction shape reserved
as candidate (2).

The third attempt exhausted the package budget. No fourth eliminator, coverage
escape, equality premise, direct RAR-field match, or public change was
attempted. Generator-origin code was reverted.

## Candidate-(2) gate

The accepted revision-62 ruling designated candidate (2) as fallback only after
candidate (1) exhaustion. That condition has now fired, but candidate (1) itself
is retained because its runtime equations constructively solved the identity
wall and will also be needed by iterator-stage origin.

The narrow fallback must make the live forward/yielded target wrapper jointly
introduce:

- the original whole generator result;
- the exact `StageFromAdvance ... occurs ...` expression;
- the `Here` or `Later` region; and
- the producer-owned runtime equations.

Its producer must still delegate through the already-total stage runtime
package; it must not restore the failed nested generator/stage/occurrence
left-hand sides. A dependent helper that universally quantifies `occurs` and
returns the corresponding wrapper constructor is the expected representation.
Because this revises the just-closed private locator result constructors, it
requires the explicit supervisor gate before implementation.

No revision-20 public surface is implicated. Cure (c) remains unopened.

## Status

- runtime-owning target-stage package declaration: **closed**;
- runtime package producer: **closed**;
- live outer locator updated to runtime package: **closed**;
- candidate-(1) runtime identity: **validated in generator-origin bodies**;
- `LocatedConsReplayGeneratorOrigin`: **STOP after 3 attempts; reverted**;
- candidate (2): **fallback gate triggered, not implemented**;
- `LocatedConsIteratorStageOrigin`: **unopened**;
- whole-suffix cons RAR: **blocked**;
- occurrence/ordinal/bundle composition: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- accepted remaining band: **3–15 shifts**, held pending candidate-(2) review.
