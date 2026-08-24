# Revision-21 moved-output alignment — exhaustive producer stop audit

> **Post-review resolution:** the supervisor accepted this stop audit and
> authorized retirement of the zero-consumer helper. Commit `98dbd09` retires
> it while preserving the historical negative. All remaining genuine producers
> now pass. The R20 chain subsequently closes alignment through final
> well-formedness and stops at `replayQuiet`; see
> `O6-R21-POST-ALIGNMENT-WHOLE-BUNDLE-STOP-AUDIT.md`. The combined boundary is
> still not issued.

Authorized base: `cp5-thm73-scoping@8a92d8e`.

Test-local candidate proof commit: `d943661`.

## Decision

The proposed producer-carried field is correct for all four closed operational
local-diamond implementations and for the complete suffix-free fixture.  The
exhaustive constructor audit nevertheless found one tracked test-local producer
that cannot supply it:

```text
R19SuffixFreeFullAdjacentCertificatePositive.repeatedIterIdentityDiamond
```

That helper reuses two arbitrary `Transition` inputs as its moved pair and
accepts action/tag equality only.  It receives neither source
`AlignedTransitions` nor a `ReplayInvariantBundle`.  Its two transition nodes
may therefore store unrelated executable `DecEq` dictionaries.  The exact
negative fails while trying to align the second reused node:

```text
Mismatch between: storedRightKeyEq and storedLeftKeyEq.
```

The helper has zero consumers.  Its sibling, the actual exported full
suffix-free certificate producer, does receive a whole source bundle and can
project exact alignment.  No live/frozen declaration is changed in this phase.
Because the authorization said to stop if **any** producer cannot supply the
field, the combined interface gate is prepared below but is not requested.

## 1. Exhaustive producer inventory

A tracked-tree search for `MkLocalRelationalDiamond` finds one constructor
declaration and exactly six constructor applications.

### Production-research constructor sites

| Family | Function | Constructor site | Moved-right capital | Moved-left capital | Probe |
|---|---|---:|---|---|---|
| O3 A/A | `activationActivationDiamondSpike` | `CP5ConfluenceLocalDiamondSpike.idr:7982` | input `earlyRightAligned`, then checked/action/tag transported under outer dictionaries | `Fired nameEq keyEq leftAction leftTag movedCheckedLeft` | `activationActivationConstructorMovedAlignment` |
| O4 A/O | `activationOrchestrationDiamondSpike` | line 8209 | `earlyRightTransition = Fired nameEq keyEq rightAction rightTag earlyRightChecked` | `checkedEndpointTransition endpoint`, whose constructor is the outer checked action | `activationOrchestrationConstructorMovedAlignment` |
| O4 O/A | `orchestrationActivationDiamondSpike` | line 8411 | input `earlyRightAligned`, then checked/action/tag transported under outer dictionaries | `Fired nameEq keyEq leftAction leftTag movedCheckedLeft` | `orchestrationActivationConstructorMovedAlignment` |
| O5 O/O | `orchestrationOrchestrationDiamondSpike` | line 8691 | `earlyRightAligned` from exact `safety.earlyRight` | `Fired nameEq keyEq leftAction leftTag movedLeftChecked` | `orchestrationOrchestrationConstructorMovedAlignment` |

All four probe functions elaborate in
`R21MovedOutputAlignmentScopingPositive.idr`.  They construct the literal type:

```idris
AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions movedRight
    (MoreTransitions movedLeft NoTransitions))
```

from exactly the checked equations/singleton alignment held at each constructor
site.  No equality between independently stored dictionaries is assumed.

### O1/O2 families

O1 and O2 produce occurrence, independence, action-origin, and endpoint algebra;
they do not construct or return `LocalRelationalDiamond`.  Exhaustive return-type
and constructor searches find no O1/O2-family diamond producer.  Consequently
there is no O1/O2 migration obligation and no missing proof hidden behind that
label.

### Direct test-local constructor sites

Both remaining applications are in
`R19SuffixFreeFullAdjacentCertificatePositive.idr`.

1. `repeatedIterIdentityDiamond` at line 72 — **blocked**. It accepts arbitrary
   `left`/`right` transitions and only label equations/final well-formedness.
   `R21RepeatedIterProducerAlignmentNegative` restates exactly those premises and
   fails at the mismatch between the stored key dictionaries of the two nodes.
2. `scopedFullSuffixFreeAdjacentCertificateProducer` at line 340 — **passes**.
   It accepts `source : ReplayInvariantBundle ... (left :: right :: [])`, uses
   `left` and `right` literally as the moved pair, and
   `fullSuffixFreeFixtureMovedAlignment = replayAligned` supplies the exact new
   field.

### Wrappers and concrete fixtures

These sites call one of the four operational producers rather than constructing
an independent diamond:

| Module / definition | Underlying producer | Migration result |
|---|---|---|
| `R4OADiamondApplication.applyReverseMixedOrientation` | O4 O/A | inherits producer-owned field |
| `R15O5AlignedProducerPositive.genuineSafetyIndexedO5Application` | O5 O/O | inherits field |
| `R15O5AlignedProducerPositive.genuineSuffixFreeDistinctInsertEndpoint` local `diamond` | O5 O/O | inherits field |
| `R16EndpointControlsImpossibilityPositive.outerProducerCallsO5` | O5 O/O | inherits field |
| `R20WholeBundleAlignmentGapPositive.r20Diamond` | O5 O/O | inherits field and is the motivating whole-bundle consumer |
| R13 O3 endpoint probes | O3 A/A | only consume the returned record; projection remains compatible |
| R14 mixed endpoint probes | corresponding O4 producer | only consume returned record |

No other tracked `.idr` file returns a locally constructed diamond.  Generic
functions accepting a `diamond` parameter are consumers and do not create a
producer obligation.

## 2. Test-local candidate

`CandidateAlignedLocalRelationalDiamond` embeds the unchanged live
`LocalRelationalDiamond` and adds exactly:

```idris
0 movedPairAligned : AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions (movedRight baseDiamond)
    (MoreTransitions (movedLeft baseDiamond) NoTransitions))
```

`sealAlignedLocalRelationalDiamond` requires alignment indexed by the exact
moved projections.  `candidateMovedAlignmentProjection` checks the intended O6
consumer path.

`R21CandidateIndependentDictionaryNegative` pattern matches a legacy diamond,
tries to reuse its stored checked equations under the caller's outer
dictionaries, and is rejected exactly at:

```text
Mismatch between: storedRightKeyEq and keyEq.
```

Thus the candidate seals producer-owned dictionaries and rejects a coherent but
detached legacy value.

## 3. Why the repeated-Iter helper is a real stop

Action/tag equalities establish only:

```idris
transitionAction left = transitionAction right
transitionTag left = transitionTag right
```

They do not establish:

```idris
storedLeftNameEq = nameEq
storedLeftKeyEq = keyEq
storedRightNameEq = nameEq
storedRightKeyEq = keyEq
```

Nor can equality of the two stored dictionaries be inferred.  A `Transition`
constructor stores executable equality dictionaries, including negative
closures. Hedberg/UIP for equality proofs does not identify such dictionaries.

The producer could be migrated only by one of these honest changes:

1. retire the zero-consumer helper; or
2. add exact source-pair `AlignedTransitions` to its test-local signature.

Retirement is preferred: the complete exported fixture producer already owns
and uses the authenticated source bundle, and retaining a weaker duplicate
helper has no consumer value.  Neither change was authorized in this
`declaration-free` phase.

## 4. Prepared combined interface package — BLOCKED, NOT A GATE

The following is the exact package that would be proposed only after the helper
is retired/narrowed under a separate approval and every producer probe passes.

### Delta A — `LocalRelationalDiamond`

Add one erased field immediately after `movedLeft`:

```idris
0 movedPairAligned : AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
```

No existing field changes.  The four research constructors populate it using
the checked probes above; the full suffix-free fixture uses
`replayAligned source`.

### Delta B — corrected sealed suffix spine

Promote the exact test-local `SealedSuffixReplaySpine` from
`R20CorrectedSealedReplayEnvelopeScopingPositive` into the research module with
private constructors.  Its step owns only:

- checked source/replayed heads;
- action/tag equality;
- head RAR and relational endpoint;
- head action/generated occurrence correspondence;
- relative ordinal equality; and
- an already sealed tail.

It owns no `ReplayInvariantBundle`.

### Delta C — opaque `AdjacentSwapResult`

Keep the existing nine fields byte-for-byte and add:

```idris
0 sealedSuffixReplay : SealedSuffixReplaySpine name key world error value
  nameEq keyEq suffix replayedSuffix
0 sealedOccurrenceFold : AdjacentSwapOperationalOccurrenceFold name key world
  error value original tracePrefix left right suffix (movedRight diamond)
  (movedLeft diamond) replayedSuffix swappedTrace
```

Hide `MkAdjacentSwapResult`.  Replace `swappedOccurrenceFold` with the total
projection:

```idris
swappedOccurrenceFold result = sealedOccurrenceFold result
```

`swappedOccurrenceCorrespondence` remains a projection through
`swappedOccurrenceFold`. `adjacentSwapSuffixSpike` remains byte-for-byte
unchanged.

### Delta D — retire the false generic occurrence-fold hole

Remove `adjacentSwapOperationalOccurrenceFoldSpike` and its hole.  It has no
remaining live consumer after Delta C, and the R18 impossibility artifact already
pins its historical unrestricted type locally.

Exactly one frozen hole declaration changes.  No replacement hole is added.

## 5. Recomputed manifest impact

The eventual atomic combined landing would update
`cp5-hole-interface-baseline.json` as follows:

1. remove the `holes[]` entry for
   `adjacentSwapOperationalOccurrenceFoldSpike`;
2. add an `approvedRecordFieldRevisions` entry for
   `LocalRelationalDiamond.movedPairAligned`;
3. add entries for `AdjacentSwapResult.sealedSuffixReplay` and
   `AdjacentSwapResult.sealedOccurrenceFold`;
4. record the `SealedSuffixReplaySpine` type addition and the two hidden
   constructors;
5. record `MkAdjacentSwapResult` constructor sealing;
6. record that `swappedOccurrenceFold` is now the sealed projection; and
7. retain revision-18 `adjacentSwapSuffixSpike` byte-for-byte.

The schema needs explicit `approvedTypeAdditions`,
`approvedConstructorRevisions`, and `approvedProjectionRevisions` arrays rather
than hiding these changes in prose.

Hole forecast:

```text
current                                         21
combined boundary: retire unrestricted fold     20
complete adjacentSwapSuffixSpike                 19
```

The `21 -> 20` forecast remains suspended because the repeated-Iter producer
migration is not approved and the first complete whole bundle has not yet been
constructed.

## 6. Whole-bundle and theorem checkpoints

The revision-20 whole-bundle chain continues to elaborate through:

- authenticated empty prefix;
- genuine O5 pair;
- cross-state checked retire head; and
- the necessary `wholeBundleRequiresExactMovedAlignment` projection.

The candidate field would close that first missing bundle field once carried by
the actual O5 result. No later bundle field is assumed here.
`R16ConfluenceTheoremAssemblyPositive` remains unchanged and elaborates.

## 7. Next authorization requested

This report requests only a choice on the zero-consumer helper:

- authorize retirement of `repeatedIterIdentityDiamond` (preferred); or
- authorize adding erased source-pair alignment to its test-local signature.

After that one migration, rerun every producer probe and the exact R20 whole
fixture. Only if all pass should the combined interface package above be issued
as an exact gate.

No O6 body, frozen interface, manifest, production file, CP3 file, or package
change is requested now.

## Status

- Candidate producer-carried field: checked test-locally.
- O3 A/A constructor: constructible.
- O4 A/O constructor: constructible.
- O4 O/A constructor: constructible.
- O5 O/O constructor: constructible.
- Actual full suffix-free certificate producer: constructible.
- Zero-consumer repeated-Iter helper: blocked by independent stored dictionaries.
- Combined interface package: prepared but blocked; not proposed as a gate.
- Hole count: unchanged at 21.
- Remaining band: unchanged at 21–35 shifts.
