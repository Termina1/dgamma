# O6 operational-occurrence fold evidence audit

Audit coordinate: `cp5-thm73-scoping@40a401b`, immediately after closing the
revision-18 M1 bookkeeping minor. No research declaration or hole body is changed
by this audit.

## Verdict

**STOP-AUDIT-GATE.** `adjacentSwapOperationalOccurrenceFoldSpike` cannot have a
total body at its frozen signature. It accepts an arbitrary `replayedSuffix` and
`swappedTrace`, constrained only by trace decomposition. It receives no action
occurrence correspondence between `suffix` and `replayedSuffix`. Its result,
however, must map every replayed occurrence back to the source and must preserve
all suffix absolute ordinals. With an empty source suffix and a one-step replayed
suffix, those requirements produce a source occurrence at ordinal two in a
source trace containing exactly two nodes. That is structurally impossible.

This is a new evidence gap, distinct from revision 17's controls and revision
18's external order. Those repairs remain ratified.

## Checked counterexample

`research-tests/DGamma/R18OccurrenceFoldArbitrarySuffixImpossibilityPositive.idr`
is total and hole-free. It proves:

```idris
0 arbitraryNonemptyReplayedSuffixMakesFoldVoid :
  (original : Transitions first originalFinal) ->
  (left : Transition first middle) ->
  (right : Transition middle pairFinal) ->
  (diamond : LocalRelationalDiamond ... left right) ->
  (extra : Transition (swappedFinal diamond) replayedFinal) ->
  original = MoreTransitions left (MoreTransitions right NoTransitions) ->
  Void
```

The proof invokes the globally fixed occurrence-fold function exactly at its
current public type with:

- `tracePrefix = NoTransitions`;
- `suffix = NoTransitions`;
- `replayedSuffix = MoreTransitions extra NoTransitions`; and
- the definitionally exact swapped trace.

The target `extra` occurrence has ordinal two. The fold's
`operationalOrdinalRelation` can only classify it as `AdjacentSuffixOrdinal`, so
its `replayActionOrigin` has source ordinal two. Exhaustive inversion of
`LocatedActionOccurrence` for the two-node source proves that no such occurrence
exists.

No action inequality, dictionary identity, endpoint equality, or root/external
classification is used. The contradiction is entirely structural.

## Why current inputs cannot discharge the result

The fold receives:

1. source and swapped decompositions;
2. the local `LocalRelationalDiamond`; and
3. raw `suffix` and `replayedSuffix` traces.

The diamond constrains only the two moved transitions. It has no field about any
suffix action, tag, generated registration, or ordinal. Decomposition equalities
only identify concatenated trace shapes; they do not relate distinct suffix
nodes.

The result requires substantially more:

- `replayActionOrigin` for every action occurrence;
- preservation of the corresponding transition tag;
- a generation bijection for every yielded child registration;
- coherence between specialized generated-registration origins and general
  action origins;
- mapped registration-generation birth ordinals; and
- the four-region absolute ordinal relation.

None of that suffix capital follows from a raw `Transitions` value.

## Genuine call boundary

`swappedOccurrenceFold` currently calls the frozen function using only fields of
an `AdjacentSwapResult`. That result stores `replayedSuffix`, `swappedTrace`, a
RAR `RelationalReplayCorrespondence`, endpoint/external relations, and a replay
bundle. RAR relates effect generators and iterator stages; it is not an
`ActionRegistrationReplayCorrespondence` and cannot recover arbitrary action or
generated-registration occurrence origins.

The future `adjacentSwapSuffixSpike` body must therefore construct the replayed
suffix and occurrence capital simultaneously. It cannot first choose an
arbitrary replayed trace and then invoke the current fold.

## Repair options

### A — add caller-supplied complete correspondence (rejected)

Add `ActionRegistrationReplayCorrespondence original swappedTrace` and the
ordinal law as premises, then package them with the constructor.

This makes the body trivial and circular: the premises are exactly the result's
substantive fields. It also revives the round-8/round-10 detached-map attack,
because a caller can select an internally coherent occurrence map independently
of the operational suffix producer. `AdjacentSwapResult` currently stores no
such authenticated capital for `swappedOccurrenceFold` to pass.

### B — add only suffix correspondence (insufficient alone)

An exact `ActionRegistrationReplayCorrespondence suffix replayedSuffix` repairs
the immediate arbitrary-suffix contradiction, but does not by itself provide:

- the local pair's reversed action/tag origin;
- an absolute generation-birth transposition at
  `transitionCount tracePrefix` and its successor;
- prefix occurrence embedding; or
- proof that the suffix correspondence came from the same replay that produced
  the endpoint, RAR correspondence, and next `ReplayInvariantBundle`.

This can be useful internal capital, but a loose public premise is not an
accepted repair.

### C — sealed simultaneous suffix-replay certificate (recommended)

Introduce a research-only indexed certificate produced by one recursive O6
function. The certificate must own, for one exact source decomposition and local
diamond:

- the existential replayed final state, suffix, and whole swapped trace;
- exact source/swapped decompositions;
- RAR correspondence and relational endpoint;
- next replay invariant bundle;
- prefix/pair/suffix external-order composition;
- one `ActionRegistrationReplayCorrespondence` constructed by that same fold;
- the absolute adjacent ordinal law; and
- any suffix-relative occurrence capital used internally to build the global
  map.

Its constructor must not be caller-accessible independently of the producer.
`AdjacentSwapResult` should be assembled from this sealed certificate, and
`swappedOccurrenceFold` should project the certificate-owned occurrence fold.
The current unrestricted standalone fold must be retired or narrowed to consume
the sealed producer token.

This preserves the accepted requirement that operational authority comes from
the actual source/replay producer rather than a caller-selected map. It also
lets recursion construct action occurrences, generation transposition, RAR,
external order, endpoint, and bundle fields in one pass.

### D — base/nonempty split without sealing (rejected)

A suffix-free base fold is constructible, but a separate generic nonempty case
still needs exact replay-origin capital. Splitting on trace shape alone merely
moves the same gap to the recursive constructor.

## Required gate

Before any declaration change, authorize a revision-19 scoping pass to:

1. trace every `AdjacentSwapResult` constructor/projection and all finite-swap,
   O17, and O19 consumers;
2. design the smallest sealed simultaneous certificate satisfying those exact
   consumers;
3. construct genuine suffix-free and one-step suffix producers before changing
   the interface;
4. retain the tracked arbitrary-suffix impossibility proof as a historical pin;
5. update only the fold/result boundary proven necessary by the audit; and
6. obtain a fresh scoped adversarial review before resuming either O6 body.

Not requested or authorized at this gate: changes to O5/local diamonds, the
revision-18 pair premise, finite derivation operational inputs, `src/`, CP3, or
any other hole declaration/body.

## Opening estimate

After an accepted evidence-boundary repair, the two O6 bodies remain **XL**. The
opening estimate is **15–25 implementation shifts**:

- 4–7 for sealed occurrence/generation/prefix-pair-suffix construction;
- 7–12 for recursive suffix replay threading RAR, endpoint, external, and bundle
  capital; and
- 4–6 for genuine suffix/whole-swap fixtures, adversarial tests, integration,
  and review closure.

The current audit is the first O6 shift and fills zero holes. Re-estimate after
the first genuine one-step suffix certificate and again after the first completed
`adjacentSwapSuffixSpike`.
