# O6 revision 97: split append closed; equal-owner classifier producer stops

## Scope

Design-only shift #105 (overall grind #159) had exactly two objectives:

1. split, zero-hidden append localization and the exact field-9 whole
   prefix/pair/suffix RAR consumer;
2. an abstract equal-owner classifier with only Iter/Iter and Retire/Retire
   cases and a one-elimination consumer.

The append objective closed completely. The exact two-cell representation and
consumer also checked, but the generic producer stopped when its first required
semantic exclusion helper exhausted three attempts. Therefore field-9
composition is no longer a blocker, while pair-RAR implementation remains
blocked on the abstract classifier producer.

All probes were same-module disposable copies. No Idris source proof or frozen
surface changed.

## Objective 1: append locator and RAR

### 1. Explicit occurrence view

The successful probe used local total embeddings:

```idris
r97AppendLeftOccurrence :
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (selected : Transition selectedBefore selectedAfter) ->
  OccursIn selected left -> OccursIn selected (appendTransitions left right)

r97AppendRightOccurrence :
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (selected : Transition selectedBefore selectedAfter) ->
  OccursIn selected right -> OccursIn selected (appendTransitions left right)
```

`R97AppendOccurrenceView` carries all five state endpoints as ordinary explicit
parameters. Its total producer recursively distinguishes the left and right
append components.

### 2. Generator package, producer, and consumer

`R97AppendGeneratorPackage` carries the ordinary explicit types, three state
indices, both traces, actor, and exact target generator. Its two constructors
own either:

```idris
local : TraceEffectGenerator ... actor left
```

or:

```idris
local : TraceEffectGenerator ... actor right
```

plus an exact map equation. Every `traceGeneratorMap` application explicitly
fixes `{trace = left}`, `{trace = right}`, or
`{trace = appendTransitions left right}`.

`r97LocateAppendGenerator` covers all three constructors:

- `ActualForwardGenerator`;
- `IteratorForwardGenerator`;
- `IteratorYieldedGenerator`.

`r97ConsumeAppendGenerator` eliminates the producer package once and gives each
branch its correlated local generator and exact equation.

Attempt record:

1. undefined local occurrence embeddings and two forced pattern equalities;
2. forced `OccursHere` head/state names and actor/selected equality remained;
3. those pattern names were unified explicitly; package, producer, and consumer
   checked.

Marker:

```text
R97_APPEND_GENERATOR_PACKAGE_PRODUCER_CONSUMER=passed
```

### 3. Stage package, producer, and consumer

`R97AppendStagePackage` follows the same zero-hidden design. Its exact equations
are parenthesized and explicitly fix every trace argument of
`iteratorStageOutcome`.

`r97LocateAppendStage` covers the sole `StageFromAdvance` constructor and uses
`actor` consistently in the dependent pattern. `r97ConsumeAppendStage` is a
one-elimination consumer.

It checked on attempt 1:

```text
R97_APPEND_STAGE_PACKAGE_PRODUCER_CONSUMER=passed
```

### 4. Producer-correlated mapped packages

The first wrapper attempt exposed an important correlation boundary. Calling
the locator separately in `replayGeneratorOrigin` and
`replayGeneratorMapsRelated` does not definitionally identify the two selected
local generators. The successful cure packages the output generator and its
map proof together:

```idris
record R97MappedAppendGenerator ... target where
  mappedAppendGenerator : TraceEffectGenerator ... sourceAppend
  0 mappedAppendGeneratorRelated : (observedKeyEq : DecEq key) ->
    PartialMapsRelated (EffectStateEquivalence observedKeyEq)
      (traceGeneratorMap mappedAppendGenerator)
      (traceGeneratorMap target)
```

The map proof is quantified over the observer dictionary. It is not used to
choose the source generator. This avoids both repeated locator elimination and
independent stored-dictionary identification.

`R97MappedAppendStage` similarly owns the correlated source stage and exact
outcome equation.

Wrapper attempt record:

1. separate locator eliminations left the stored `generatorOrigin` opaque in the
   map field;
2. producer-correlated mapped packages, with the observer dictionary quantified
   inside the generator package, checked.

Marker:

```text
R97_APPEND_RAR_WRAPPER=passed
```

### 5. Exact append RAR type

The checked wrapper has the generic type:

```idris
r97AppendRelationalReplayCorrespondence :
  (sourceLeft : Transitions sourceFirst sourceMiddle) ->
  (sourceRight : Transitions sourceMiddle sourceFinal) ->
  (targetLeft : Transitions targetFirst targetMiddle) ->
  (targetRight : Transitions targetMiddle targetFinal) ->
  RelationalReplayCorrespondence ... sourceLeft targetLeft ->
  RelationalReplayCorrespondence ... sourceRight targetRight ->
  RelationalReplayCorrespondence ...
    (appendTransitions sourceLeft sourceRight)
    (appendTransitions targetLeft targetRight)
```

No implicit lambda syntax is used. Map relation inputs are consumed by ordinary
function clauses with `{x}` and `{y}` on the left-hand side.

## Make-or-break field-9 verdict: passed

`r97Field9WholeAppendCorrespondence` checked on attempt 1. It composes:

```text
appendRAR prefixRAR (appendRAR pairRAR suffixRAR)
```

and reindexes the source with the exact adjacent decomposition, producing:

```idris
RelationalReplayCorrespondence name key world error value original
  (appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix)))
```

Marker:

```text
R97_FIELD9_WHOLE_APPEND_CORRESPONDENCE=passed
```

A second make-or-break consumer instantiated the real frozen capital directly:

```idris
r97Field9ConcreteCapitalConsumer ... pairRAR seal =
  r97Field9WholeAppendCorrespondence ...
    (identityRelationalReplayCorrespondence tracePrefix)
    pairRAR
    (sealedSuffixRelationalReplayCorrespondence seal)
```

Its exact result is the whole `RelationalReplayCorrespondence original
 targetTrace` required before `traceIndependentAfterRelationalReplaySpike` can
populate field 9.

It checked on attempt 1:

```text
R97_FIELD9_CONCRETE_CAPITAL_CONSUMER=passed
```

**Composition verdict: CLOSED.** Field 9 now depends only on construction of the
pair RAR; append localization and whole composition no longer block it.

## Objective 2: abstract equal-owner classifier

### Checked representation and one-elimination consumer

The disposable `R97EqualOwnerPairClassification` has exactly two constructors:

- `R97EqualOwnerIterIter`;
- `R97EqualOwnerRetireRetire`.

Each constructor owns:

- the common actor;
- exact source-left/source-right action and tag equations;
- exact moved-right/moved-left action and tag equations;
- `swappedMiddle diamond = middle`;
- `swappedFinal diamond = originalFinal`.

The last two fields are the exact reindexing boundary needed before applying
`activationSingletonRAR` twice or `orchestrationSingletonRAR` twice.

`r97ConsumeEqualOwnerPairClassification` eliminates the package once and gives
one handler all ten correlated Iter payloads and the other all ten correlated
Retire payloads. It checked on attempt 1:

```text
R97_EQUAL_OWNER_CLASSIFICATION_CONSUMER=passed
```

Exact consumer shape:

```idris
R97EqualOwnerPairClassification ... left right diamond ->
((actor : name) ->
  transitionAction left = LAdvance actor ->
  transitionTag left = LIterTag ->
  transitionAction right = LAdvance actor ->
  transitionTag right = LIterTag ->
  transitionAction (movedRight diamond) = LAdvance actor ->
  transitionTag (movedRight diamond) = LIterTag ->
  transitionAction (movedLeft diamond) = LAdvance actor ->
  transitionTag (movedLeft diamond) = LIterTag ->
  swappedMiddle diamond = middle ->
  swappedFinal diamond = originalFinal -> result) ->
((actor : name) ->
  transitionAction left = ORetire actor ->
  transitionTag left = ORetireTag ->
  transitionAction right = ORetire actor ->
  transitionTag right = ORetireTag ->
  transitionAction (movedRight diamond) = ORetire actor ->
  transitionTag (movedRight diamond) = ORetireTag ->
  transitionAction (movedLeft diamond) = ORetire actor ->
  transitionTag (movedLeft diamond) = ORetireTag ->
  swappedMiddle diamond = middle ->
  swappedFinal diamond = originalFinal -> result) -> result
```

### Generic producer verdict: stopped

The producer needs abstract exclusions, not only the R96 concrete evaluator
pins. The first required generic lemma was:

```idris
checked ORetire actor first ->
checked paperActivation(actor) middle -> Void
```

The probe correctly chose the raw operational route:

1. project `checkedApplyAction` to `applyAction`;
2. eliminate `retireSuccessView`, reindexing the middle state to a registry with
   `retireFiber oldFiber` at the owner;
3. use `lookupReplacedFiber`;
4. exclude Begin because `targetFiber` is `Nothing`;
5. exclude Iter/Finish by complete lifecycle, capability-resolution, and
   `runStepEffect` cases, whose successful retired branch has L-Divert rather
   than the paper tag.

Attempt record:

1. parser stopped at compact nested equality eliminations in the Iter/Finish
   calls;
2. after parser repair, rewriting the lookup equation did not affect the opaque
   checked equation, demonstrating that raw projection must occur inside each
   helper;
3. raw projection was added, but the final parser attempt stopped at indentation
   of the nonempty Reloading resolution case.

Parser failures count under the permanent budget, so the semantic helper was
removed after attempt 3. Marker:

```text
R97_RETIRE_THEN_PAPER_ACTIVATION_EXCLUDED=failed_after_3
```

No fourth attempt was made. Without this helper and the analogous two-order
activation and orchestration exclusions, no honest abstract producer can be
claimed.

**Classifier verdict: PARTIAL.** The exact two-case output and consumer are
checked; the generic producer is not.

## Correct implementation order after the next gate

Implementation is not yet recommended. The narrow next design should split the
classifier semantics into independent units:

1. `retireThenPaperActivationImpossible`, with raw projection factored before
   lifecycle dispatch and the Reloading branch delegated to a separate helper;
2. same-owner two-order activation classifier, excluding Begin and Finish
   positions and returning Iter/Iter;
3. same-owner two-order orchestration classifier, using presence/absence
   observations and returning Retire/Retire;
4. four-way `CandidateRegistrationSwapSafety` producer of the checked two-case
   package;
5. one producer-owned endpoint-determinism package for `swappedMiddle = middle`
   and `swappedFinal = originalFinal`;
6. only after these check, retained implementation in this order:
   classifier -> positional pair RAR -> append RAR -> field 9 -> fields 10–15 ->
   occurrence fold -> result -> O6 body.

## Capital and manifest audit

The append solution consumes only accepted capital:

- `identityRelationalReplayCorrespondence` (`84c1b81`);
- `sealedSuffixRelationalReplayCorrespondence`;
- a producer-owned pair RAR;
- the frozen adjacent decomposition and moved transitions.

It introduces no caller-supplied occurrence, stage, map, RAR, endpoint,
alignment, dictionary equality, or global invariant capital. The observer's
`DecEq key` is quantified only over a map proof and never selects runtime data.

Expected manifest delta remains:

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

Retained additions should be private quantity-0 declarations in the CP5 spike.
Revision-21 surfaces, `AdjacentSwapResult`, `ReplayInvariantBundle`, the four
producer signatures, and `adjacentSwapSuffixSpike` remain untouched.

## Status and band

- split append occurrence/generator/stage packages: **checked**;
- producer-correlated append wrapper: **checked**;
- exact whole field-9 capital consumer: **checked**;
- two-cell classifier type and one-elimination consumer: **checked**;
- generic classifier producer: **not checked; semantic prerequisite exhausted**;
- pair RAR: **design-complete but not implementable until classifier producer**;
- field 9 and later fields: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The proposed **2–8 implementation-shift** band remains suspended because both
objectives did not fully close. Once the abstract classifier producer checks,
the append result supports re-establishing that band immediately; no further
composition design gate should be necessary.

## Isolation

The adjacent interface remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`, revision-21 surfaces, fields 1–8,
and all frozen singleton/prefix/suffix capital are unchanged. No source probe,
proof hole, postulate, or escape hatch is retained.
