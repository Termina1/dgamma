# O6 revision 84: field 6 and failure-freedom field 7 close

## Scope

Grind shift #92 (overall #146) resumed from reviewer-accepted revision 83 at
`d6de3c6`. It closed the fixed-registry aggregation wrapper and bundle field 6,
then completed bundle field 7 (`replayNoFailure`). It stopped at a clean
committed boundary before opening the substantially different trace-totality
field 8. Fields 8–15 and final result/body assembly were not opened.

## Fixed-registry aggregation and field 6

The exact reviewer-authorized converter
`quietFoldPredicateToQuietEntries` passed on its first fresh attempt at
`6f0c754`:

- `registryEntries` and `registryUnique` stay fixed;
- only `currentEntries` changes recursively;
- the input folds `quietFoldEntryPredicate` over `currentEntries`;
- the output folds the canonical `quietEntryFor` against the fixed registry over
  the same `currentEntries`.

The one-clause `pointwiseQuietTrue` instantiates
`currentEntries = registryEntries`. It composes the retained explicit fold
(`08be6e7`) with that structural predicate conversion, so the result reduces to
canonical endpoint `quiet` without function extensionality.

`alignedReplayQuiet` was then added as erased field 6 of the private
`AdjacentAlignedPointwiseReplay` package and populated on the first fresh
attempt at `c832454`, using the exact sealed endpoint's controls, effects, and
well-formedness together with source `replayQuiet`.

**Field 6 is fully closed end-to-end.** The #90 aggregation design escalation is
not triggered.

## Field 7: failure freedom

Failure freedom was transported constructively in four lemma-sized retained
units:

1. `lifecycleNotFailedAt` and `lifecycleControlNotFailedSame` (`914b3b1`). The
   first attempt exposed polymorphic case-result implicits; the executable
   classifier form passed on attempt 2.
2. `fiberNotFailedAsLifecycleNotFailedAt` and
   `fiberControlNotFailedSame` (`263a0c5`). The first attempt exposed the same
   opaque-classifier normalization class already solved for quietness; explicit
   normalization on both sides passed on attempt 2.
3. `noFailedEntryPredicateExplicit` and
   `pointwiseNoFailedEntriesTrueExplicit` (`f1bfae9`). The target-entry fold uses
   exact membership/lookup and symmetric pointwise controls, obtains source
   failure freedom with `noFailureFromState`, transports it through the exact
   fiber relation, and recurses. Attempts 1–2 exposed generated hidden arguments
   from the canonical lowercase predicate; the ordinary explicit executable
   predicate passed on attempt 3.
4. `pointwiseNoFailedTrue` (`b844662`). Its first attempt tried a structural
   converter whose canonical predicate reintroduced hidden dependent
   arguments. On attempt 2, the explicit predicate was eta-defined as
   `DGamma.CP3.notFailedEntry`, allowing direct definitional reduction and a
   one-clause state-pattern wrapper.

`alignedReplayNoFailure` was added and populated on the first fresh attempt at
`42005b6` from the exact sealed endpoint controls and source
`replayNoFailure`.

**Bundle field 7 is fully closed.** All proof premises and locals are quantity
0.

## Clean stopping point

Field 8 is `TraceComponentsTotal` for the entire moved/replayed target trace. It
is not another endpoint Boolean fold: its witness is indexed at every
transition boundary. It will require a dedicated producer-owned transport
through the unchanged prefix, moved pair, and sealed suffix spine. Starting it
without a full fresh unit budget would violate the lemma-sized and semantic-stop
protocol, so this shift ends before that unit.

## Status

- fields 1–5: **closed and frozen**;
- field 6 (`replayQuiet`): **closed**;
- field 7 (`replayNoFailure`): **closed**;
- fields 8–15: **unopened in this shift**;
- final `AdjacentSwapResult`/body assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The previous accepted **1–11 shift** remainder is provisionally narrowed to
**1–10 shifts**, reflecting closure of the aggregation wall and field 7 while
retaining explicit allowance for the harder trace-totality transport.

## Isolation

The 1183-byte public spike interface and its SHA, revisions 19–21, fields 1–5,
all registration/yield/generator/RAR capital, production `src/`, `dgamma.ipkg`,
and CP3 remain unchanged. Only private research helpers/package fields were
added. No hole, postulate, escape hatch, detached caller premise, public surface,
or package input was added.
