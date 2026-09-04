# R137 — O8 raw-name reuse countershape and stop audit

## Scope and ruling

O8 was not opened or edited during this unit.  The frozen production/research
surface remains unchanged.  This audit discharges the mandatory precondition for
revising O8: it supplies a checked two-generation execution in which the current
raw-name `NoDependentClosingEpisode` field rejects both possible closing actors,
even though every pointwise precedence graph is acyclic.

The result is a semantic stop, not an elaborator inconvenience.  O8 must not be
filled against the current raw-name predicate.  The smallest honest repair is to
index the negative dependency condition by the selected registration generation,
as the surrounding deletion bookkeeping already does.

## Checked artifacts

The countershape is split so elaboration stays bounded and every semantic edge is
still authenticated by `checkedApplyAction`:

- `research-tests/DGamma/R137O8RawNameReuseCountershape.idr`
  - concrete names, keys, executable effects, fibers, and all 25 states;
  - `r137E0`–`r137E23`: exact raw evaluator equations;
  - `r137W0`–`r137W24`: exact well-formedness checks;
  - `r137FirstGenerationEdge : PrecedenceEdge ... ActorA ActorB r137S8`;
  - `r137SecondGenerationEdge : PrecedenceEdge ... ActorB ActorA r137S22`;
  - `r137EveryRegistryRankedAcyclicTrue`: exhaustive finite-name/rank check of
    every state.  The first era uses `Anchor < ActorA < ActorB`; after reuse the
    second era uses `Anchor < ActorB < ActorA`.
- `research-tests/DGamma/R137O8RawNameReuseCountershapeTrace.idr`
  - `r137C0`–`r137C23`: exact checked-evaluator equations;
  - `r137Trace : Transitions r137S0 r137S24`.
- `research-tests/DGamma/R137O8RawNameReuseCountershapeProof.idr`
  - genuine located closing episode for first-generation `ActorB`;
  - genuine located closing episode for second-generation `ActorA`;
  - `r137RawActorANotDeletionMaximal`;
  - `r137RawActorBNotDeletionMaximal`.

There are no holes, postulates, `believe_me`, or `assert_total` in these files.

## Countershape

The trace commits the following births and dependency edges.

1. `Anchor` is inserted and activated, providing `SourceKey`.
2. First-generation `ActorA` is inserted, consumes `SourceKey`, activates, and
   provides `LinkKey`.
3. First-generation `ActorB` is inserted, begins with the committed view
   `LinkKey -> ActorA`, raises, and unloads.  At its episode start the concrete
   edge is `ActorA -> ActorB`.
4. `ActorB` is retired and removed.  `Anchor` and first-generation `ActorA` are
   retired; `ActorA` leaves, unloads, and is removed.
5. Second-generation `ActorB` is inserted under the same raw name, activates,
   and provides `LinkKey`.
6. Second-generation `ActorA` is inserted under the same raw name, begins with
   the committed view `LinkKey -> ActorB`, raises, and unloads.  At its episode
   start the concrete edge is `ActorB -> ActorA`.

Thus the pointwise direction changes only across a deletion/rebirth boundary.
No registry contains a cycle: the exhaustive check validates all nine ordered
name pairs at each state against a strict rank, and its closed result is `True`.
There is deliberately no single global raw-name rank: requiring one would erase
the generation boundary that the LTS explicitly records.

## Why the current O8 predicate is false for the candidate set

The current alias is:

```idris
NoDependentClosingEpisode selected global =
  (consumer : name) ->
  (consumerEpisode : LocatedClosedEpisode ... consumer global) ->
  PrecedenceEdge nameEq selected consumer
    (closedStartState (locatedEpisode consumerEpisode)) -> Void
```

It quantifies the provider only by raw `selected : name` over the entire global
trace.

- If O8 selects the closing occurrence for raw `ActorA`,
  `r137RawActorANotDeletionMaximal` applies the alleged negative to the located
  first-generation `ActorB` episode and the concrete first-generation edge
  `ActorA -> ActorB`.
- If O8 selects the closing occurrence for raw `ActorB`,
  `r137RawActorBNotDeletionMaximal` applies it to the located second-generation
  `ActorA` episode and the concrete second-generation edge
  `ActorB -> ActorA`.

These dependencies belong to different births.  The raw predicate conflates
those births, so the finite maximal-element argument has no admissible actor even
though each pointwise graph is acyclic.  This is exactly the shape O8's current
hole would have to rule out, and it cannot.

`Anchor` is not an O8 closing candidate in this trace: it has no located closing
episode.  O8 selects only from the exact O7 closing-occurrence scan, whose actor
projection here is covered by the two theorems above.

## Required revision boundary

Revise only the O8/deletion-candidate dependency-negative from raw actor identity
to the exact selected registration generation.  The intended proposition is:

- dependencies from the selected generation's installed interval to a consumer
  closing episode in that interval are forbidden;
- dependencies from an earlier or later birth with the same raw name are
  irrelevant.

The revised field must be tied to the already-computed
`selectedStartOrdinal`/`selectedStartLive` and the selected registration
witnesses.  It must not weaken pointwise `PrecedenceEdge`, erase O7 occurrence
authenticity, assume raw proof irrelevance, or add a global name-renaming premise.
All consumers of `selectedNoDependentClose` must be audited before editing.

## Fresh checks

Executed serially with Idris 2 v0.8.0 and a fresh target TTC for each module:

```text
idris2 --source-dir research-tests --check research-tests/DGamma/R137O8RawNameReuseCountershape.idr
1/1: Building DGamma.R137O8RawNameReuseCountershape

idris2 --source-dir research-tests --check research-tests/DGamma/R137O8RawNameReuseCountershapeTrace.idr
2/2: Building DGamma.R137O8RawNameReuseCountershapeTrace

idris2 --source-dir research-tests --check research-tests/DGamma/R137O8RawNameReuseCountershapeProof.idr
3/3: Building DGamma.R137O8RawNameReuseCountershapeProof
```

One earlier monolithic construction exceeded the time budget; its process group
was terminated and the fixture was split into evaluator, trace, and proof layers.
No Idris/Chez process remained afterward.  The split changes no proposition.

## R137 stop

**STOP on filling the current O8 hole.**  The raw-name maximality premise is
constructively refuted on the exact checked LTS.  Proceed only by the scoped,
generation-indexed revision above, then re-run the direct DeletionChain check,
real-consumer checks, hole census, and invariant scan before spending any O8 body
attempt.
