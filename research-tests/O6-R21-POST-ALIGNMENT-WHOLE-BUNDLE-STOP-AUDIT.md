# Revision-21 post-alignment whole-bundle checkpoint — quietness stop

Coordinate: `cp5-thm73-scoping@d69ea26`.

## Decision

The authorized zero-consumer helper retirement is complete.  The exhaustive
producer set now has five direct `MkLocalRelationalDiamond` applications: four
operational constructors plus the actual full suffix-free fixture.  Every one
has a checked moved-pair alignment producer.

The R20 whole-bundle fixture now consumes the exact proposed O5 output and gets
strictly past `ReplayInvariantBundle.replayAligned`.  It constructs the first
five fields in declaration order:

1. `replayAligned`;
2. `replayDiscipline`;
3. `replayInitialWellFormed`;
4. `replayInitialEmpty`; and
5. `replayFinalWellFormed`.

The next field, `replayQuiet`, does not follow directly from current endpoint
capital.  Per the original stop condition for any final-invariant gap, the
combined interface package remains prepared but is **not issued as a gate**.
No later bundle field is assumed.

## 1. Authorized retirement

Commit `98dbd09` removes only the private, zero-consumer test helper
`repeatedIterIdentityDiamond` from
`R19SuffixFreeFullAdjacentCertificatePositive.idr`.  Its historical unsuppliable
signature remains pinned in `R21RepeatedIterProducerAlignmentNegative`, which
still fails at:

```text
Mismatch between: storedRightKeyEq and storedLeftKeyEq.
```

The exported `scopedFullSuffixFreeAdjacentCertificateProducer` remains intact.
It constructs the same identity moved pair from an authenticated source bundle,
and `fullSuffixFreeFixtureMovedAlignment = replayAligned` continues to check.

No operational producer, frozen declaration, manifest entry, O6 body,
production file, CP3 file, or package file changed.

## 2. Exact retained O5 output

The test-local boundary simulation consumes:

```idris
retainedO5Output : AlignedTransitions ...
  (MoreTransitions (movedRight r20Diamond)
    (MoreTransitions (movedLeft r20Diamond) NoTransitions))
```

This is exactly the proposed erased `LocalRelationalDiamond.movedPairAligned`
field indexed by the concrete genuine O5 result.  It is not a caller-selected
trace or unrelated alignment relation.  The O5 constructor-site proof in
`R21MovedOutputAlignmentScopingPositive` separately constructs this exact shape
from `earlyRightAligned` and outer `movedLeftChecked` before the record hides its
dictionaries.

`r21RetainedRetireTransition` similarly uses the exact outer checked equation
already produced by `checkedRetireReplayAcrossLocalSwap`; it does not reuse the
legacy transition's potentially hidden dictionary.

## 3. Whole alignment closes

`r21AppendAligned` is a total structural append lemma.
`r21WholeReplayAlignedAfterRetainedO5` combines:

- the checked from-empty prefix insert;
- the exact retained O5 moved pair; and
- the explicit checked cross-state retire head.

The result is literal outer-dictionary `AlignedTransitions` for
`r21RetainedSwappedTrace` from `r20Initial` to the cross-state replay target.
This is the former revision-20 blocker and it now elaborates.

## 4. Discipline and empty-start fields close

The moved-action equalities already stored by the diamond show both moved
orchestration actions are root inserts.  The helper
`r21RootStepDisciplineFromAction` transports the root-rank witness without
identifying dictionaries. `r21WholeReplayDiscipline` then builds the exact
four-step discipline:

```text
OInsert 0 Root
moved OInsert 2 Root
moved OInsert 1 Root
replayed ORetire 0
```

The globally empty initial registry gives `r21WholeReplayInitialWellFormed` and
`r21WholeReplayInitialEmpty` by computation.  Target well-formedness is not
assumed: `r21WholeReplayFinalWellFormed` projects it from the genuine per-step
relational endpoint built by the checked cross-state replay.

`R21WholeBundleThroughFinalWellFormed` packages exactly these first five fields.
Its constructor accepts no quietness, no-failure, totality, independence,
provenance, rank, precedence, well-foundedness, or support field.

## 5. First remaining field: quietness

`ReplayInvariantBundle` next requires:

```idris
quiet @{nameEq} @{keyEq} replayedFinal = True
```

The available `RelationalReplayEndpoint` contains:

- `EffectStateRelated`;
- `ControlEquivalent`; and
- target registry well-formedness.

It contains no quietness projection, and no checked theorem currently transports
`quiet` across `ControlEquivalent`.  `R21WholeBundleQuietTransportNegative`
pattern matches all endpoint fields and attempts the direct transport from
source quietness. Idris rejects it exactly with:

```text
Mismatch between: source and target.
```

This negative does not claim the implication is mathematically false.  It pins
the missing constructive bridge: quietness is a recursive registry/lifecycle
predicate, while the endpoint exposes only pointwise
`FiberControlMaybeRelated`.  A genuine proof would need to show that
`LifecycleControlRelated` preserves `quietFiber`, reconstruct the finite target
registry fold from pointwise lookup/domain equivalence, and account for target
references used by `quietFiber`.  Alternatively, the replay producer could
retain checked final quietness at the global envelope construction site, but
that field must be derived from authenticated source/replay semantics rather
than accepted loose.

The following fields were deliberately not attempted after this first final
invariant gap:

- `replayNoFailure`;
- `replayTotal`;
- `replayIndependent`;
- `replayProvenance`;
- protocol and parent ranking;
- precedence acyclicity;
- support well-foundedness; and
- support/active matching.

## 6. Combined interface package status

The exact combined package in
`O6-R21-MOVED-OUTPUT-ALIGNMENT-PRODUCER-AUDIT.md` remains unchanged:

A. erased exact `movedPairAligned` on `LocalRelationalDiamond`;
B. promoted bundle-free sealed suffix spine;
C. opaque nine-plus-two `AdjacentSwapResult`; and
D. retirement of the false generic occurrence-fold hole while
   `adjacentSwapSuffixSpike` stays byte-for-byte unchanged.

Producer alignment is now fully closed after helper retirement, and the R20
consumer demonstrably uses it.  Nevertheless this report does not request the
combined boundary because the authorized whole-bundle checkpoint exposed the
next final-invariant bridge before a complete `ReplayInvariantBundle` exists.

Manifest impact and hole forecast remain prepared, not landed:

```text
current holes                                  21
combined boundary after later approval          20
complete adjacentSwapSuffixSpike                19
```

No replacement hole is permitted. The band remains **21–35 shifts**; quietness
transport is now an explicit 2–4 shift subphase within the whole-bundle segment,
not an increase beyond that band.

## 7. Next narrow authorization

The next declaration-free phase should audit and probe:

1. transport of `quiet` across `ControlEquivalent`/the exact relational replay
   endpoint;
2. whether no-failure has the same lifecycle-control proof shape;
3. concrete R20 source quietness from the authenticated source bundle rather
   than a caller-selected target proof; and
4. target finite-domain reconstruction required by the pointwise control
   relation.

Stop again if the pointwise endpoint relation cannot construct the target fold
without new producer-owned domain evidence.  Do not widen `ReplayInvariantBundle`
or accept desired target quietness as a premise.

## Status

- All genuine moved-alignment producers: passed.
- Zero-consumer fake-shape helper: retired and historically pinned.
- Whole `replayAligned`: passed using exact retained O5 output.
- Whole `replayDiscipline`: passed.
- Initial well-formed/empty and final well-formed: passed.
- `replayQuiet`: stopped at missing constructive endpoint transport.
- Combined interface gate: prepared but not issued.
- Frozen hole count: 21.
