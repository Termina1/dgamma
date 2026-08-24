# O6 sealed replay certificate — revision-19 scoping audit

> **Checkpoint supersession:** the recursive spine and outer sealing decision
> remain accepted, but the test candidate's suffix-local `ReplayInvariantBundle`
> field is rejected by `O6-R19-CROSS-STATE-BUNDLE-MISMATCH-AUDIT.md`.  The
> corrected spine owns local replay capital only; `AdjacentSwapResult` owns the
> whole-trace next bundle.  No boundary implementation is authorized yet.

Scoping coordinate: `cp5-thm73-scoping@8261356` from audited base `ff81eb0`.
This shift changes no frozen declaration, research record, or hole body. The
candidate types exist only in tracked probes under `research-tests/`.

## Decision summary

Revision 19 should make `AdjacentSwapResult` the opaque, producer-owned
certificate for one complete adjacent splice. Its module-private constructor
must own the exact replayed suffix and whole trace, decompositions, RAR,
endpoint, next bundle, external framing, all-action/generated-registration
correspondence, absolute ordinal law, and an internal recursively sealed suffix
spine. Existing public projection names remain the consumer API.

The unrestricted standalone `adjacentSwapOperationalOccurrenceFoldSpike`
function is the only one of the 27 frozen hole declarations that must change: it
should cease to quantify arbitrary replayed suffixes and become a total
projection from the sealed result (or be retired in favor of
`swappedOccurrenceFold`). `adjacentSwapSuffixSpike` keeps its exact revision-18
signature and becomes the sole public producer. No other frozen declaration
changes.

Tracked probes validate both recursive shapes and constructor sealing:

- `scopedSuffixFreeCertificateProducer` constructs the empty base without
  accepting output-shaped capital;
- `scopedOneStepCertificateProducer` consumes an actual checked `Transition`
  and exact replay bundle, creates a genuinely nonempty spine, and derives all
  certificate observations by identity;
- `ScopedReplayStep` accepts only an already sealed recursive tail, never a
  freshly quantified target tail; and
- `R19SealedReplayConstructorNegative` proves importing callers cannot invoke
  the recursive constructor.

The one-step probe validates the certificate boundary and nonempty recursion
shape, not the still-unproved cross-state action replayer. The first genuine
cross-state one-step certificate remains the agreed implementation re-estimate
checkpoint and must precede the boundary-change implementation gate.

## 1. Complete current consumer trace

### 1.1 Construction boundary

The only current `MkAdjacentSwapResult` sites outside its declaration are five
uses in `R11GenericRawPlanRepackagerPositive`:

- the generic `materializeAdjacentSwapResult` at lines 51–54; and
- duplicated supplied-plan fixtures at lines 185, 190, 240, and 245.

That module was deliberately renamed in round 11 as a supplied-capital
*repackager*, not an operational producer. It proves that the accepted public
constructor can package already supplied endpoint/RAR/bundle/external fields.
It is therefore the exact test that must stop constructing the production
research result once the constructor is sealed. It must not be silently deleted:
it should be pinned locally with a retired open record, as with the R16/R17
historical interfaces, or rewritten as a negative constructor-access test.

There is no completed genuine constructor site: `adjacentSwapSuffixSpike` is the
intended producer and remains a hole. O17/O19 consume its result through finite
derivation constructors.

### 1.2 `AdjacentSwapResult` projections

Current fields at `CP5ConfluenceLocalDiamondSpike.idr:840-870` have these
consumers:

| Projection | Direct/derived consumers | Need after sealing |
|---|---|---|
| `replayedFinal` | recursive result indices; R16/R17 historical proofs; R8 negative bridge fixtures | Yes, exact existential replay endpoint. |
| `replayedSuffix` | `swappedOccurrenceFold`; R16/R17 suffix-free pins; malicious-prefix tests | Yes, but produced by the recursive certificate only. |
| `swappedTrace` | tails of `FiniteAdjacentSwapDerivation` and `NonEmptyFiniteAdjacentSwapDerivation`; O19 crossing plans; clone negatives | Yes, exact trace index for recursion. |
| `originalDecomposition` | O19 `adjacentLeftNodeOccurrence` and `adjacentRightNodeOccurrence`; fold packaging | Yes, source-position authentication. |
| `swappedDecomposition` | occurrence fold and R17 external-order pin | Yes, producer-owned equality. |
| `swappedSameExternalInputs` | finite schedule external composition; R17 root-order pin | Yes, built from prefix identity, pair-local R18 capital, and sealed suffix relation. |
| `swappedReplayCorrespondence` | `finiteDerivationReplayCorrespondence` | Yes, recursively composed into O17/O19 RAR. |
| `swappedEndpoint` | O17/O19 endpoint accumulation inside their producer holes | Yes, effects/control/well-formed endpoint. |
| `swappedPremises` | next O17 local-pair selection and O19 recursive step; R16 alignment projection | Yes, the exact next recursive bundle. |
| `swappedOccurrenceFold` | R10 projection test; R16/R17 historical pins | Yes, but it must become a direct sealed field projection. |
| `swappedOccurrenceCorrespondence` | finite derivation composition, O19 position labels, clone negative | Yes, definitionally projected from the sealed fold. |

No consumer needs the current open constructor or the ability to choose any
field independently.

### 1.3 Finite adjacent-swap consumers

`FiniteAdjacentSwapStep` (`LocalDiamondSpike:940-956`) and
`NonEmptyAdjacentSwap` (`:970-985`) store the exact result and index their
recursive tails by `swappedTrace result`. Conversion and node counting inspect
only derivation shape.

Two folds consume result capital:

- `finiteDerivationReplayCorrespondence` (`:1017-1028`) composes each
  `swappedReplayCorrespondence`;
- `finiteDerivationOccurrenceCorrespondence` (`:1031-1041`) composes each
  `swappedOccurrenceCorrespondence`.

Constructor sealing is transparent to both. Their inputs and outputs remain
unchanged if public result projections retain the same names and types.

### 1.4 O17 one-trace sorting

`SortedClosingFreeTrace` (`CP5ConfluenceCanonicalSortSpike.idr:103-154`) stores:

- the final sorted trace;
- `sortingReplayCorrespondence`;
- `sortingAdjacentDerivation`;
- next bundle and same-external witness;
- canonical blocks/placement; and
- endpoint/registration accounting.

`sortingOccurrenceCorrespondence` (`:157-167`) is definitionally
`finiteDerivationOccurrenceCorrespondence (sortingAdjacentDerivation sorted)`.
`sortClosingFreeTraceSpike` (`:196-207`) must repeatedly call the sole
`adjacentSwapSuffixSpike` producer, thread `swappedTrace` and
`swappedPremises`, and accumulate result RAR/endpoint/external fields. It never
constructs or accepts an independent action-origin map. Sealing strengthens this
property without changing the O17 declaration.

### 1.5 O19 whole-block crossing

O19 uses result decomposition and occurrence correspondence more intensively:

- `adjacentLeftNodeOccurrence` and `adjacentRightNodeOccurrence`
  (`CP5ConfluenceCrossTraceSpike.idr:280-322`) locate the selected source nodes
  only from `originalDecomposition`;
- `DerivationCrossesBlockPositions` and `BlockCrossingOriginPlan`
  (`:389-513`) thread a prefix correspondence definitionally extended with
  `swappedOccurrenceCorrespondence result` at every node;
- `WholeBlockSwapDerivation` (`:543-607`) requires a nonempty finite derivation
  and exact Cartesian crossing plan;
- `OperationalAdjacentBlockSwap` (`:643-670`) stores that derivation plus the
  block endpoint, bundle, and external witness;
- `blockSwapReplayCorrespondence` and
  `blockSwapOccurrenceCorrespondence` (`:673-690`) are folds of the exact finite
  derivation; and
- `operationalAdjacentBlockSwapSpike` (`:697-712`) is the genuine O19 caller of
  adjacent splicing.

The later `OperationalActorPermutation` recursively indexes its tail by the
actual `blockSwapTrace`, `blockSwapBlocks`, and `blockSwapPremises`
(`:714-758`). Its RAR and occurrence folds (`:760-796`) compose only sealed
block-step outputs. No O19 consumer needs access to a result/certificate
constructor.

### 1.6 O20 and later consumers

O20 receives O19's sealed `CertifiedOperationalCanonicalPermutation`; it does
not call the local fold. Its replay/occurrence inputs are projections of the
selected operational actor permutation. Therefore the revision-19 boundary must
preserve O19's public block projections, but O20 needs no new certificate field
or operational premise.

### 1.7 R12-accepted full-coverage path

The mandatory path is:

```text
R16ConfluenceTheoremAssemblyPositive.r16ConfluenceTheoremAssembly
  -> R8FullPipeline.fullPipelineFromBundles
  -> deleteAllClosingEpisodesSpike (both traces)
  -> sortClosingFreeTraceSpike (O17, both traces)
  -> independentCanonicalScheduleSpike
  -> canonicalSupportOrdersMatchSpike
  -> selectOperationalCanonicalPermutationSpike (O19)
  -> canonicalSchedulesConvergeSpike (O20)
  -> originalEndpointsConvergeSpike / final theorem result
```

`R8FullPipeline.idr:29-76` fixes that exact call graph. The immutable theorem
probe remains the release boundary, not merely a local import check.

**Implementation rule:** `R16ConfluenceTheoremAssemblyPositive` must elaborate at
every intermediate revision-19 commit. A boundary commit that temporarily
breaks the assembly is not commit-worthy. The constructor/result refactor,
projection compatibility, fold retirement, manifest update, and test pinning
must land together if they cannot individually preserve assembly.

## 2. Smallest sealed simultaneous design

### 2.1 Internal recursive spine

The positive probe validates this shape:

```idris
export data SealedSuffixReplaySpine source replayed where
  End  : SealedSuffixReplaySpine NoTransitions NoTransitions
  Step : (sourceStep : Transition ...)
      -> (replayedStep : Transition ...)
      -> action equality -> tag equality
      -> SealedSuffixReplaySpine sourceTail replayedTail
      -> SealedSuffixReplaySpine
           (MoreTransitions sourceStep sourceTail)
           (MoreTransitions replayedStep replayedTail)
```

The type is externally visible, but constructors are module-private (`export`,
not `public export`). The future Step constructor additionally owns the
per-action checked replay result needed for RAR/effect/control transport. The
recursive tail is a previously produced sealed value, never two raw caller
traces.

### 2.2 Complete adjacent certificate

The smallest production research representation is `AdjacentSwapResult` itself
with a hidden constructor. It retains its current indices and projection API and
adds two producer-owned fields:

```idris
0 sealedSuffixSpine :
  SealedSuffixReplaySpine suffix replayedSuffix

0 sealedOccurrenceFold :
  AdjacentSwapOperationalOccurrenceFold ...
```

Together with its existing fields, the opaque result owns:

1. exact `replayedFinal`, `replayedSuffix`, and `swappedTrace`;
2. source and swapped decompositions;
3. RAR correspondence;
4. relational endpoint;
5. exact next `ReplayInvariantBundle`;
6. whole external relation assembled with `framePairExternalOrderSpike`;
7. all-action/generated-registration occurrence correspondence;
8. the absolute adjacent ordinal law inside `sealedOccurrenceFold`; and
9. internal suffix-relative recursion in `sealedSuffixSpine`.

`swappedOccurrenceFold` becomes `sealedOccurrenceFold`; it no longer calls an
unrestricted function. `swappedOccurrenceCorrespondence` remains its current
projection.

This avoids a second wrapper and preserves every consumer-facing result type and
field name. `adjacentSwapSuffixSpike` is the only module-internal constructor
caller and remains indexed by the exact source decomposition, bundle, local
diamond, and revision-18 pair relation.

### 2.3 Why the certificate is non-circular

No public function accepts the desired whole RAR, endpoint, occurrence map,
ordinal law, or next bundle. The recursive producer obtains them in one pass:

- evaluate one source suffix action at the current swapped state;
- build its exact checked replayed transition;
- recursively produce the sealed tail from the resulting state;
- derive head RAR/effect/control/action/tag/generation capital from the actual
  checked source/replayed step;
- prepend that capital to the sealed tail;
- once the suffix is complete, frame prefix + local pair + suffix into the whole
  result.

The certificate is an output, not an input authority.

## 3. Producer-suppliability by shape

### 3.1 Suffix-free base

For `suffix = NoTransitions`:

- replayed suffix is definitionally `NoTransitions` at `swappedFinal diamond`;
- suffix RAR and action correspondence are identity/empty;
- suffix external relation is `SameExternalOrchestrationEnd`;
- suffix ordinal law is vacuous;
- endpoint is exactly the local diamond endpoint;
- whole RAR/action origins handle prefix identity and the swapped pair;
- whole external relation uses prefix reflexivity, the exact revision-18 pair
  premise, and empty suffix relation;
- next bundle is rebuilt for the exact swapped pair/whole trace from checked
  moved transitions and source invariants.

The tracked `scopedSuffixFreeCertificateProducer` checks the empty sealed shape:
it accepts one exact empty-trace bundle and derives endpoint, RAR, external,
action occurrence, and ordinal fields. It accepts no replayed trace or map.

### 3.2 Nonempty recursive step

For `suffix = MoreTransitions sourceStep sourceTail`:

1. destruct aligned source suffix capital to obtain the actual outer-dictionary
   checked source step;
2. run the same action at the current replay state, yielding exact
   `replayedStep` or use the source-sensitive replay lemma for its action family;
3. derive action and tag equalities from that checked replay branch;
4. construct per-step RAR and endpoint preservation;
5. recurse only on `sourceTail` and the *computed after-state* of
   `replayedStep`;
6. receive one sealed tail certificate;
7. prepend source/replayed step capital to its RAR, external, occurrence,
   generation, ordinal, endpoint, and bundle values; and
8. return one new sealed certificate.

The tracked `scopedOneStepCertificateProducer` is genuinely nonempty: its input
is an actual `Transition` carrying a checked evaluator equation and an exact
one-step replay bundle. It constructs a `ScopedReplayStep`, RAR, endpoint,
external relation, action/generated occurrence map, and ordinal law without
accepting any of those outputs. The current fixture uses identity replay to test
the boundary independently of the not-yet-implemented cross-state per-action
replayer. The first cross-state one-step fixture is mandatory before the design
boundary may land.

### 3.3 Avoiding Option D's arbitrary-tail failure

The Step constructor does **not** have parameters of the form:

```idris
(replayedTail : Transitions arbitraryStart arbitraryFinal) -> ...
```

unless that tail is simultaneously indexed by a constructor-sealed recursive
certificate. The only recursive argument is the sealed tail value. Its replayed
start is definitionally the checked replayed head's after-state, and all maps and
endpoints are projections of that same value.

Consequently a caller cannot instantiate an empty source tail with a nonempty
replayed tail—the exact attack proved by
`R18OccurrenceFoldArbitrarySuffixImpossibilityPositive`. The tracked constructor
negative confirms importing modules cannot invoke `ScopedReplayEnd` directly.

## 4. Frozen declaration and manifest delta — pre-declared

Exactly **one of the 27 frozen hole declarations** changes:

| Frozen declaration | Revision-19 action |
|---|---|
| `adjacentSwapOperationalOccurrenceFoldSpike` | Retire the unrestricted raw-trace hole or narrow it to a total projection from the sealed result/certificate. Its named hole disappears. |
| `adjacentSwapSuffixSpike` | **Byte-for-byte unchanged signature.** It remains the sole producer and eventually receives a body. |
| Other 25 declarations | **Byte-for-byte unchanged.** |

Non-hole research boundary changes requiring explicit manifest/review entries:

- `AdjacentSwapResult` constructor visibility changes from public to hidden;
- it gains sealed spine/fold ownership while preserving public projections;
- `swappedOccurrenceFold` changes from calling the old function to projecting
  the sealed field; and
- the new opaque spine type is introduced in the local-diamond research module.

Expected hole count after the boundary lands: 20 (the false standalone fold hole
is retired by a total projection). Expected hole count after the suffix producer
is eventually proved: 19. No replacement hole name is permitted.

The manifest should gain one `approvedHoleSignatureRevisions` entry for the fold
retirement/narrowing and one approved result-record boundary revision. It must
continue guarding revision-17 record fields and the revision-18 suffix premise.

## 5. Historical pinning and test migration

Before the fold boundary changes,
`R18OccurrenceFoldArbitrarySuffixImpossibilityPositive` must become
self-contained:

1. define local `RetiredUnrestrictedAdjacentSwapOperationalOccurrenceFold` with
   the old decompositions, occurrence correspondence, and ordinal field;
2. restate the theorem against a value of that retired record rather than call
   the changed/retired global function; and
3. retain the exact empty-source/nonempty-replayed ordinal contradiction.

This mirrors `RetiredOrderedReplayEndpoint` in the R16 historical pin and keeps
the evidence meaningful after repair.

`R17FullResultImpossibility` and the suffix-free part of
`R16EndpointControlsImpossibilityPositive` currently call
`swappedOccurrenceFold`. They should continue unchanged if that name becomes the
sealed projection. Their proofs must elaborate at the boundary commit.

`R11GenericRawPlanRepackagerPositive` was migrated explicitly because it was
the only external result-constructor client.  The chosen treatment is a local
`RetiredOpenAdjacentSwapResult` plus
`materializeRetiredOpenAdjacentSwapResult`; the live `MkAdjacentSwapResult`
constructor is no longer referenced.  This most faithfully preserves the
accepted revision-11 claim—caller-supplied semantic fields can be mechanically
repackaged—while withdrawing its former ability to enter O17/O19.  The larger
supplied recursive wrappers were derivative packaging, had no external consumer,
and were removed rather than being granted a current constructor escape hatch.

Clone/provenance positives and negatives (`R10AdjacentSwapMapCloneNegative`,
`R10ProvenanceProjectionPositive`, `R11AdjacentPrefixMalicePositive`) must retain
their intended boundaries.

## 6. Commit and gate sequence

1. **Historical pins only:** make arbitrary-suffix and raw-repackager tests
   self-contained. R16 theorem assembly must pass.
2. **Genuine cross-state probes only:** suffix-free full adjacent certificate and
   one checked cross-state suffix step, still without declaration changes. Stop
   if any per-action RAR/endpoint/bundle field is not derivable.
3. **Boundary design gate:** present exact declarations/record delta and probe
   results; obtain explicit authorization.
4. **Atomic boundary commit:** opaque result constructor, sealed fields/spine,
   total fold projection, manifest/auditor/test migration. R16 assembly must pass
   in that same commit.
5. **Scoped boundary review:** no O6 body work until ACCEPT.
6. **Base implementation:** suffix-free complete result; fresh suite/audit and
   re-estimate if the producer surface differs from the probe.
7. **One-step/recursive implementation:** cross-state checked replay and sealed
   tail induction; re-estimate at the first genuine one-step certificate.
8. **Complete suffix body:** all action families and arbitrary finite suffix;
   re-estimate at first complete `adjacentSwapSuffixSpike`.
9. **Assembled revision-19 scoped review:** required before O17/O19 work resumes.

Every intermediate commit must elaborate
`R16ConfluenceTheoremAssemblyPositive`. If constructor refactoring cannot preserve
it in smaller commits, step 4 is one reviewed atomic commit rather than a broken
intermediate state.

## 7. Shift banding and checkpoints

The previously accepted **15–25 implementation-shift** opening estimate remains:

| Phase | Shifts |
|---|---:|
| Opaque boundary, projections, manifest, historical migrations | 2–4 |
| Full suffix-free adjacent certificate | 3–5 |
| First checked cross-state step and recursive occurrence/generation capital | 4–7 |
| Complete recursive suffix RAR/endpoint/bundle/external integration | 4–6 |
| Adversarial fixtures and review closure | 2–3 |
| **Total** | **15–25** |

This scoping shift changes no implementation declaration and is not subtracted
from that band. Mandatory re-estimation checkpoints:

1. first genuine checked **cross-state one-step** certificate; and
2. first complete `adjacentSwapSuffixSpike` for arbitrary finite suffix.

## Status

- Revision-17 controls: ratified.
- Revision-18 external-order narrowing: ratified.
- Revision-19 consumer trace/design: scoped in this audit.
- Candidate base/nonempty recursion and constructor hiding: tracked and checked.
- Cross-state one-step producer: not yet proved; mandatory before boundary gate.
- Frozen declaration changes this shift: none.
- O6 bodies: stopped.
