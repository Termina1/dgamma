# O6 revision 60: single-scrutinee target locator coverage stop

## Scope

Shift #68 (overall #122) resumed from the accepted revision-59 gate at
`ecb8b4a`. It first re-landed the validated private six-constructor
`LocatedConsTargetGenerator` declaration as a separately checked commit. It then
attempted the specifically authorized locator signature:

- `targetHead` and `targetTail` were implicit indices;
- `actor` was also an implicit index; and
- the original whole-target `TraceEffectGenerator` was the locator's sole
  explicit scrutinee.

The locator remained non-covering on the first attempt. The accepted revision-59
ruling explicitly required an immediate stop-audit if coverage still failed with
one explicit scrutinee, so no clause workaround or second/third attempt was
opened. The failed locator was reverted. The constructor commit is retained.

The iterator-stage localization GADT, located origin packages, cons RAR,
occurrence/ordinal/bundle composition, and final adjacent assembly were not
opened.

## Retained constructor capital

`LocatedConsTargetGenerator` now has six private constructors jointly indexed by
its original whole target generator:

1. actual generator at `OccursHere`;
2. actual generator at `OccursLater`;
3. iterator-forward generator at `OccursHere`;
4. iterator-forward generator at `OccursLater`;
5. iterator-yielded generator at `OccursHere`;
6. iterator-yielded generator at `OccursLater`.

Each `Here` constructor owns its exact `targetTail : Transitions afterState
 targetFinal`, so refining the stored `Fired` head also refines the tail's start
state. Iterator constructors retain the exact stage lookup, lifecycle program,
reachable suffix, and yielded origin. The hidden `StageFromAdvance` endpoint
indices were explicitly named in the validated producer clauses. No equality
premise, detached map evidence, dictionary identity, or caller capital was
introduced.

The containing research module and mandatory
`R16ConfluenceTheoremAssemblyPositive.idr` both checked before the constructor
commit.

## Authorized locator statement

The attempted locator used exactly the narrow private statement authorized at
revision 59:

```idris
0 locateConsTargetGenerator :
  {targetHead : Transition targetFirst targetMiddle} ->
  {targetTail : Transitions targetMiddle targetFinal} ->
  {actor : name} ->
  (target : TraceEffectGenerator name key world error value actor
    (MoreTransitions targetHead targetTail)) ->
  LocatedConsTargetGenerator name key world error value
    targetHead targetTail actor target
```

Its six clauses matched only `target`; implicit indices were named solely where
the corresponding located constructor needed `targetHead` or `targetTail`.
All four iterator stage patterns named `{before}` and `{afterState}`. Thus the
failure cannot be attributed to the earlier two-explicit-scrutinee locator
shape.

## Coverage failure

Idris rejected the locator as non-covering. The diagnostic no longer displayed
a separate target-head pattern. Its missing cases were exclusively single
whole-generator patterns, repeated across hidden dependent stage indices:

```text
locateConsTargetGenerator (IteratorForwardGenerator _)
```

and:

```text
locateConsTargetGenerator (IteratorYieldedGenerator _ _)
```

The actual-generator clauses were accepted. The iterator constructors carry a
`LocatedIteratorStage` whose occurrence proof relates a stored `Fired` to the
cons trace, but coverage does not use that hidden occurrence proof to establish
that a stage must be either the exact head or in the exact tail. Even with the
whole generator as the only explicit scrutinee, decomposing `StageFromAdvance`
into `OccursHere`/`OccursLater` does not cover Idris's hidden dependent index
space.

This is the precise escalation condition from the accepted revision-59 ruling:
coverage still fails with a single explicit scrutinee. The failure is now a true
statement/representation-shape question rather than independent scrutinee
correlation.

## Gate

The whole-cons statement-shape gate is now open. No redesign is attempted here.
In particular, this shift does **not**:

- re-quantify any revision-20 public surface;
- move target localization into separate RAR fields;
- add a target equality premise;
- widen caller capital;
- use partiality or a coverage escape hatch; or
- introduce dictionary identity.

Any next design must explain how the iterator stage occurrence is eliminated
once while preserving the original whole target and local target together. A
statement quantified over an already located target package is the known
stronger candidate, but remains supervisor-controlled and undrafted.

## Status

- six target-generator localization constructors: **retained and checked**;
- single-explicit-scrutinee target locator: **STOP, non-covering; reverted**;
- iterator target-stage localization GADT: **unopened**;
- `LocatedConsReplayGeneratorOrigin`: **unopened**;
- `LocatedConsIteratorStageOrigin`: **unopened**;
- whole-suffix cons RAR: **blocked**;
- occurrence/ordinal/bundle composition: **unopened**;
- final adjacent assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- accepted remaining estimate: **3–15 shifts**, now held at the opened
  whole-cons statement-shape gate.
