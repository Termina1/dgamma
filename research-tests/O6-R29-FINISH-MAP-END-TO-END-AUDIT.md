# O6 revisions 27–29 finish-map retention and end-to-end bundle audit

## 1. Authorized scope

Shift 37 started at `cp5-thm73-scoping@9aaf683`.  It was limited to a
producer-owned test-local finish-map envelope, its definitional consumer audit,
an adversarial forged-map negative, and strict continuation of the target
`ReplayInvariantBundle`.  No frozen declaration, O6 body, manifest, production
source, package, or CP3 edit was made.

## 2. Producer-path finish-map retention

`R27MapRetainedFinishReplay` wraps the exact existing
`R24CheckedEmptyFinishReplay` and adds one erased field:

```idris
0 retainedTargetMapIdentity :
  (state : EffectState Nat R23Key R23Value Unit) ->
  partialEffectMap (replayedTransition baseFinishReplay) state = Just state
```

Population occurs only inside `r27ProduceMapRetainedFinish`, at the same point
where the previous `r24ProduceEmptyFinish` body had already proved
`targetMapIdentity` from its checked target lookup and exact `Reloading []`
lifecycle.  The old producer is now definitionally the `baseFinishReplay`
projection of this core.  No dictionary identity, caller map premise, or
post-hoc transport is used.

This is a refactor of a test-local producer, not a frozen declaration change.
The retained theorem is indexed by the exact checked transition owned by the
base replay.

## 3. Definitional projection audit

The first and second envelopes invoke the same producer core with the same
arguments as the old replay definitions.  All required transfers elaborate as
literal aliases or `Refl`:

- `r27FirstBaseIsR24 = Refl`;
- `r27SecondBaseIsR24 = Refl`;
- `r27FinalEndpointIsR25 = Refl`;
- `r27WholeTargetTrace = r25WholeTargetTrace`;
- `r27WholeAligned = r25WholeAligned`;
- `r27WholeDiscipline = r25WholeDiscipline`;
- `r27InitialWellFormed = r25InitialWellFormed`;
- `r27InitialEmpty = r25InitialEmpty`;
- `r27FinalWellFormed = r25FinalWellFormed`;
- `r27TargetQuiet = r25TargetQuiet`;
- `r27TargetNoFailure = r25TargetNoFailure`; and
- `r27WholeTotal = r25WholeTotal`.

There is no `rewrite`, `replace`, or re-derived theorem in the transfer block.
Thus both replay results, the final endpoint, and fields 1–8 survive the
corrected producer definitionally.

## 4. Forgery guard

`R27FinishMapEnvelopeForgeryNegative` gives a caller a detached map theorem for
the canonical outer-dictionary `Fired` transition and tries to use
`r25CanonicalTransitionExact` to populate the retained field.  It is rejected
at the exact projection index:

```text
Can't solve constraint between:
  Fired ... (LAdvance ?_) LFinishTag (?_ .replayedChecked)
and:
  ?_ .replayedTransition.
```

Therefore the successful field cannot be populated by transporting a
caller-selected canonical theorem.  It is available only because the producer
seals it before projection.

## 5. `replayIndependent` closes

The target trace's two L-Begin maps are definitionally identity.  For each
L-Finish head, `r27ActualMapsTotal` uses only
`retainedTargetMapIdentity` from its exact envelope.  Iterator stages at those
heads are mapped through the authenticated per-step RAR to the known
empty-program source singleton; all other target heads are non-advance actions.
This yields `r27NoIterator` and totality of every target effect transformation.

Because `R23Key` is empty, every pair of defined transformation results is
`EffectStateRelated`, regardless of execution order.  The constructive result
is:

```idris
r28WholeIndependent : TraceIndependent Nat R23Key Unit Unit R23Value
  r23KeyEq r27WholeTargetTrace
```

No independent-map, domain, dictionary, or caller-supplied independence premise
is accepted.

## 6. Remaining bundle fields close in order

Revision 29 continues from independence without skipping a field:

1. `r29Provenance` from `r27WholeDiscipline`;
2. `r29ProtocolRanked` from reached-from-empty plus provenance;
3. `r29ParentRanksIncrease` from the same authenticated capital;
4. `r29PrecedenceAcyclic` from reached discipline;
5. `r29SupportWellFounded` from protocol and parent ranks; and
6. `r29SupportMatchesActive` from the checked trace, initial facts, quietness,
   no-failure, and totality.

These assemble:

```idris
r29TargetBundle : ReplayInvariantBundle Nat R23Key Unit Unit R23Value
  r23Protocol r23NameEq r23KeyEq r27WholeTargetTrace
```

The corrected R23 fixture therefore closes the complete whole-target bundle
end to end.

## 7. Prepared atomic A/B/C/D/E gate

The following frozen package is now prepared for review but is **not landed**.
`adjacentSwapSuffixSpike` remains byte-identical until approval.

### A — moved-pair alignment

Add erased `LocalRelationalDiamond.movedPairAligned`, indexed by the exact two
moved projections.  Populate it at all five genuine O3–O5 producers with the
already checked outer dictionaries.  The R25 envelope is the direct prototype
and consumer proof.

### B — sealed bundle-free suffix spine

Promote the revision-20 `SealedSuffixReplaySpine` into the frozen local-diamond
module as an `export data` type.  Constructors stay hidden from importers.  A
node owns its exact checked source/replayed heads, tails, action/tag equality,
per-step RAR, endpoint, occurrence correspondence, relative ordinal, and the
sealed recursive tail.  It owns no suffix-local `ReplayInvariantBundle`.

### C — opaque nine-plus-two result

Change `AdjacentSwapResult` to an opaque exported record: retain its existing
nine fields, add erased `sealedSuffixReplay` and `sealedOccurrenceFold`, and
hide `MkAdjacentSwapResult`.  The outer result alone retains the exact global
whole-trace bundle.

### D — false fold retirement

Delete `adjacentSwapOperationalOccurrenceFoldSpike` and its false unrestricted
hole.  Define `swappedOccurrenceFold` as the projection
`sealedOccurrenceFold result`.  Keep the public projection type unchanged.
`adjacentSwapSuffixSpike` remains unchanged in this boundary landing.

### E — producer-owned replay-map retention

Extend each `SealedSuffixReplayStep` with producer-owned projection-safe map
capital:

```idris
0 headMapPreserved :
  (state : EffectState name key value world) ->
  partialEffectMap sourceStep state = partialEffectMap replayedStep state
```

This is the generic frozen analogue of revision 27's finish identity.  It must
be constructed at the same checked replay site as `headRAR`, before either
transition is hidden behind a projection.  It is never accepted as a loose
`adjacentSwapSuffixSpike` premise.  For the empty L-Finish fixture, source-map
identity plus this field yields `retainedTargetMapIdentity`.

## 8. Recomputed manifest impact and hole forecast

On approved landing, the immutable manifest must be regenerated once to:

- remove the `adjacentSwapOperationalOccurrenceFoldSpike` hole entry;
- add `LocalRelationalDiamond.movedPairAligned`;
- record `SealedSuffixReplaySpine`, hidden constructors, and
  `SealedSuffixReplayStep.headMapPreserved`;
- add `AdjacentSwapResult.sealedSuffixReplay` and
  `AdjacentSwapResult.sealedOccurrenceFold`;
- record hidden `MkAdjacentSwapResult` visibility; and
- record `swappedOccurrenceFold` as a producer-owned projection.

The forecast is:

- current research holes: **21**;
- atomic A/B/C/D/E landing, retiring D: **20**;
- subsequent separately reviewed `adjacentSwapSuffixSpike` body: **19**.

E adds no hole.  No manifest file is changed before approval.

## 9. Estimate and next action

End-to-end bundle closure reduces the remaining O6 estimate from **26–44** to
**20–35 shifts**.  The lower bound covers atomic promotion, scoped adversarial
review, and the now-prototyped adjacent result body; the upper bound retains
allowance for generic suffix constructors and the later block recursion.

The required next action is the combined A/B/C/D/E frozen-interface review.
No package item may land independently.
