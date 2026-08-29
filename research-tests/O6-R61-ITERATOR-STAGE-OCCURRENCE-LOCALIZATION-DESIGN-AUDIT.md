# O6 revision 61: iterator-stage occurrence localization design audit

## Scope and ruling carried into this shift

Design shift #69 (overall #123) starts from accepted revision-60 HEAD
`98d3fc6`. It is design-only under the revision-60 supervisor ruling. The six
private `LocatedConsTargetGenerator` constructors retained at `b0c1d4b` remain
unchanged. No locator, target-stage implementation, located origin package, cons
RAR, occurrence/ordinal/bundle composition, or adjacent-result assembly is
added to the research spike.

This audit enumerates the index space behind revision 60's diagnostics, pins the
failure with tracked expected-failure probes, tests a stage-indexed alternative
constructively in a research-test probe, evaluates the mandated cure ladder,
and recommends the next implementation shape.

## 1. Exact index-space enumeration

### 1.1 Source constructors

The relevant production definitions are exhaustive inductive families:

```idris
data IteratorStage ... trace where
  StageFromAdvance :
    ... ->
    (0 occurs : OccursIn fired trace) ->
    ... ->
    IteratorStage ... trace
```

`StageFromAdvance` is the **only** `IteratorStage` constructor. For a target cons
trace its stored occurrence has this exact shape:

```idris
OccursIn fired (MoreTransitions targetHead targetTail)
```

`OccursIn` itself has exactly two constructors:

```idris
OccursHere  : OccursIn targetHead
  (MoreTransitions targetHead targetTail)

OccursLater : OccursIn fired targetTail ->
  OccursIn fired (MoreTransitions targetHead targetTail)
```

Therefore the exact semantic occurrence partition is:

1. **head** — `OccursHere`, which definitionally identifies the stage's stored
   `Fired nameEq keyEq (LAdvance actor) tag equation` with `targetHead`;
2. **tail** — `OccursLater later`, where `later : OccursIn fired targetTail` and
   may itself select any depth in the tail.

There is no third constructible stage-occurrence configuration. In particular:

- deeper positions are already represented by the single tail case because
  `later` recursively owns the remaining depth;
- `ReachableSuffix remaining (step :: rest)` chooses an iterator continuation,
  not a transition occurrence;
- the fiber, lookup, lifecycle, accumulator, view, step, rest, dictionaries,
  checked equation, and suffix proof are dependent stage payload dimensions,
  not additional `OccursIn` constructors;
- `IteratorForwardGenerator` versus `IteratorYieldedGenerator` is a generator
  projection dimension; the yielded origin adds runtime data but no occurrence
  case.

The revision-60 phrase “uncovered index space” must consequently be read as
**coverage-checker residual families over hidden dependent payload indices**, not
as additional inhabitants beyond `StageFromAdvance` + `OccursHere`/`OccursLater`.
This shift corrects the provisional interpretation that the six constructors
had omitted a semantic occurrence constructor.

### 1.2 Constructive partition probe

`research-tests/DGamma/R44IteratorStageOccurrencePartitionPositive.idr`
defines the exact dependent view:

```idris
data ConsStageOccurrenceView ...
  (occurs : OccursIn selected (MoreTransitions head tail)) where
  ConsStageOccursHere  : ConsStageOccurrenceView OccursHere
  ConsStageOccursLater : (later : OccursIn selected tail) ->
    ConsStageOccurrenceView (OccursLater later)
```

`viewConsStageOccurrence` is total by the two `OccursIn` constructors. The probe
then defines `LocatedConsIteratorStageProbe`, indexed by the **original whole
stage**, which stores this occurrence view under one `StageFromAdvance`
elimination. Finally `LocatedConsGeneratorProbe` is indexed by the **original
whole generator** and has total actual, forward, and yielded producers. Forward
and yielded branches match only the generator wrapper and call the stage
producer once.

This complete dependent probe elaborates with `%default total`. It preserves:

- the original whole stage index;
- the original whole generator index;
- exact target head and target tail;
- every stored dictionary, checked equation, fiber lookup, lifecycle program,
  reachable suffix, and yielded origin; and
- the exact head/tail occurrence view.

It introduces no target equality premise and no dictionary equality.

### 1.3 Expected-failure probes

Two tracked negatives isolate the diagnostic independently of the difficult RAR
codomain:

1. `R44IteratorForwardNestedCoverageNegative.idr` covers actual and yielded
   generators with one pattern, then splits only the forward
   `StageFromAdvance` occurrence into nested left-hand-side `OccursHere` and
   `OccursLater` patterns. Its codomain is erased `Bool`. Idris rejects it with:

   ```text
   directIteratorForwardNestedCoverage is not covering.
   Missing cases:
     directIteratorForwardNestedCoverage (IteratorForwardGenerator _)
   ```

2. `R44IteratorYieldedNestedCoverageNegative.idr` covers actual and forward
   generators with one pattern, then splits only the yielded stage occurrence.
   Idris rejects it with:

   ```text
   directIteratorYieldedNestedCoverage is not covering.
   Missing cases:
     directIteratorYieldedNestedCoverage (IteratorYieldedGenerator _ _)
   ```

Because both failures occur with a non-dependent `Bool` codomain, they are not
target identity or RAR-field failures. The nested generator/stage/occurrence
left-hand-side decomposition itself exceeds Idris 2 v0.8.0's dependent coverage
analysis. The positive probe shows the identical semantic partition becomes
total when stage construction and occurrence elimination are sequenced.

## 2. Minimal cure ladder

### 2.1 Cure (a): add target-generator constructors

**Evaluation: insufficient as a distinct cure.**

There are no additional semantic stage-occurrence configurations for honest
constructors to represent. Adding more `Here`/`Later` variants would duplicate
the six retained constructors without covering a new `OccursIn` constructor.
Adding broad catch-all constructors such as:

```idris
IteratorForwardGenerator stage
```

would make the outer locator syntactically total but would not jointly introduce
the required exact singleton/tail local stage. Such a constructor cannot support
the downstream RAR map and origin fields without re-eliminating the hidden stage
occurrence and losing the identity the localization package exists to preserve.

A constructor carrying a separately stage-indexed location package would work,
but that is cure (b), not an extension justified by a newly enumerated case.
Therefore the retained six constructors should remain available, but constructor
count alone must not be used to repair coverage.

### 2.2 Cure (b): index localization on the stage-occurrence family

**Evaluation: sufficient in a constructive full-index probe; recommended.**

The positive R44 probe validates this two-phase architecture:

1. eliminate `IteratorStage` once as `StageFromAdvance ... occurs ...`;
2. eliminate `occurs` in a nested `case`, producing an exact dependent
   `ConsStageOccurrenceView` (`Here` or `Later`);
3. seal the original stage plus that exact view in a stage-indexed package;
4. eliminate `TraceEffectGenerator` only at its outer constructor;
5. for forward/yielded wrappers, call the stage producer once and carry the
   resulting package under the original whole-generator index.

For the implementation retry, the private stage package may use either:

- two exact constructors (`LocatedConsStageHere` / `LocatedConsStageLater`) with
  a producer whose **single** `StageFromAdvance` clause performs the inner
  occurrence case; or
- the probe's one stage-owning constructor plus the two-constructor
  `ConsStageOccurrenceView` field.

The latter has already elaborated with all exact indices and is the lower-risk
representation. The former is presentation-equivalent but must be independently
budgeted because its two dependent result constructors were not this shift's
implementation target.

The target-generator locator must not restore nested
`IteratorForwardGenerator (StageFromAdvance ... OccursHere/Later ...)` clauses.
Instead it should use:

```text
IteratorForwardGenerator stage -> locateConsTargetStage stage
IteratorYieldedGenerator stage origin -> locateConsTargetStage stage
```

and eliminate each sealed stage package once. This preserves the retained six
target constructors as consumers while avoiding their failed direct producer
shape.

### 2.3 Cure (c): re-quantify whole-suffix cons

**Evaluation: not reached and not justified.**

Cure (b) is constructively inhabited through both the exact stage and exact
whole-generator indices. No revision-20 frozen surface needs to change.
Accordingly:

- no scoped revision-21 campaign is activated;
- no public signature or manifest delta is proposed;
- no probe in either direction for a re-quantified cons statement is warranted;
- `RelationalReplayCorrespondence`, `ReplayInvariantBundle`, RAR record
  parameters, map fields, iterator outcome fields, and the frozen outer result
  interfaces remain byte-for-byte out of scope.

If a future cure-(b) implementation loses identity when projecting into the
actual located origin packages, it must stop at that exact consumer and open a
new gate. Such a future failure would not retroactively authorize cure (c).

## 3. Recommendation and next retry order

**Recommend cure (b), using the exact stage-indexed package shape proven by
R44.** The next implementation shift should have fresh budgets in this order:

1. add private `ConsStageOccurrenceView` and its total producer;
2. add private whole-stage-indexed `LocatedConsTargetStage`, constructed by one
   `StageFromAdvance` match plus the occurrence view;
3. add the target-generator locator with actual branches unchanged and generic
   forward/yielded wrapper branches consuming that stage package once;
4. only after the locator checks, construct `LocatedConsReplayGeneratorOrigin`;
5. then construct `LocatedConsIteratorStageOrigin` and whole-suffix cons RAR;
6. gate occurrence/ordinal/bundle composition behind cons RAR as before.

If either exact original stage or exact original whole generator is lost through
this package, revert that unit and stop. Do not add equality premises, direct
per-RAR-field elimination, detached map capital, dictionary identity, or public
statement changes.

## 4. Estimate and status

Cure (c) does not look likely on current evidence. The accepted **3–15 remaining
shift** band therefore remains unchanged rather than widening. The probe closes
the representation-design uncertainty but does not close an O6 body hole, so
this design-only shift is not used to claim a reduced lower or upper bound.

Current status:

- retained target-generator constructors: **6/6 checked, unchanged**;
- semantic stage-occurrence configurations: **exactly 2** (`Here`, `Later`);
- forward nested-pattern failure: **pinned expected failure**;
- yielded nested-pattern failure: **pinned expected failure**;
- exact stage-indexed cure-(b) probe: **proved total**;
- exact generator-indexed cure-(b) wrapper probe: **proved total**;
- cure (a): **insufficient without becoming cure (b)**;
- cure (b): **recommended**;
- cure (c): **not activated; no manifest delta**;
- iterator localization in the research spike: **unopened**;
- located origin packages / cons RAR / composition / assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.
