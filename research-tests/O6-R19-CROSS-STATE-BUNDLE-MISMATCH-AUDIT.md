# Revision-19 cross-state replay bundle mismatch — stop audit

> **Revision-20 checkpoint:** the corrected local/global bundle split is now
> checked, but whole-bundle production stops earlier at moved-transition
> dictionary alignment.  See `O6-R20-WHOLE-BUNDLE-ALIGNMENT-GAP-AUDIT.md`.
> No adjacent-result boundary gate is currently active.

Coordinate: `cp5-thm73-scoping@2454b78` from the accepted revision-19 scoping
coordinate `c76b521`.

## Stop decision

The first genuine checked cross-state suffix head succeeds for `O-Retire`,
including its checked transition, per-step RAR, relational endpoint,
action/generated occurrence correspondence, and relative ordinal law.  The
probe then exposes a mismatch in the scoping candidate's bundle field:
`ReplayInvariantBundle` is a global-from-empty **whole trace** package and cannot
be recursively indexed by a bare suffix beginning at the swapped pair endpoint.

No frozen declaration, research result record, manifest entry, or O6 hole body
changes in this phase.  Under the authorized stop rule, boundary implementation
is not requested and O6 remains stopped.

## 1. Historical pins completed first

### 1.1 Retired unrestricted occurrence fold

`R18OccurrenceFoldArbitrarySuffixImpossibilityPositive` now defines the local
historical record
`RetiredUnrestrictedAdjacentSwapOperationalOccurrenceFold`.  Its Void theorem
quantifies an inhabitant of the old unrestricted producer signature and no
longer invokes `adjacentSwapOperationalOccurrenceFoldSpike`.  The pin therefore
survives retirement of the false global hole.

### 1.2 Retired open result repackager

`R11GenericRawPlanRepackagerPositive` now defines only
`RetiredOpenAdjacentSwapResult` and
`materializeRetiredOpenAdjacentSwapResult`.  It has no live
`MkAdjacentSwapResult` constructor call and cannot enter finite derivations,
O17, or O19.

A local retired record was chosen instead of turning the module into a negative
because it preserves the exact accepted revision-11 claim: supplied semantic
fields can be mechanically repackaged.  The former recursive wrappers were
derivative packaging with no external consumer; retaining them would require a
live result-constructor escape hatch and was therefore rejected.

## 2. Full suffix-free fixture succeeded

`R19SuffixFreeFullAdjacentCertificatePositive` constructs a complete test-local
suffix-free envelope.  It uses two actual aligned, checked `L-Iter` transitions
for the same actor.  Their action/tag labels coincide, so the checked source
transitions themselves form a trace-preserving semantic transposition, while
the exhaustive occurrence map genuinely exchanges ordinal zero and one.

The producer derives, rather than accepts:

- the local diamond and moved checked transitions;
- empty replayed suffix and exact whole trace/decompositions;
- same-external relation;
- RAR;
- relational endpoint;
- exact next whole-trace `ReplayInvariantBundle`;
- all-action/generated-registration occurrence correspondence;
- absolute adjacent ordinal law;
- sealed empty suffix spine.

It accepts only the checked source bundle and the two action/tag classification
equalities.  The source bundle's `AlignedTransitions` field authenticates the
runtime evaluator dictionaries.

This fixture is deliberately trace-preserving and is not the cross-state
checkpoint.

## 3. Genuine checked cross-state step succeeded

`R19CrossStateRetireReplayProbePositive` proves
`checkedRetireReplayAcrossLocalSwap`.

Its source head is an actual checked

```idris
Fired nameEq keyEq (ORetire actor) ORetireTag sourceChecked
```

from `originalFinal`.  It re-evaluates that action at the exact distinct state
index `swappedFinal diamond`; no moved evaluator equation, moved state, output
endpoint, RAR, map, or ordinal proof is an input.

### 3.1 Derived applicability

The producer:

1. obtains the source retire fiber and exact source replacement shape from
   `checkedActionProjects` and `retireSuccessView`;
2. uses only `swappedControlEquivalent diamond` to derive a related fiber at
   `swappedFinal diamond`;
3. constructs the concrete retired target fiber/registry;
4. proves raw application at the swapped state;
5. derives target well-formedness through `preservationTheoremProof`; and
6. reconstructs the exact checked `Transition` from the raw equation and target
   well-formedness.

This is a true cross-state operational replay.  It does not reuse the source
transition or accept a checked moved transition.

### 3.2 Derived per-step RAR

`singletonRetireRAR` maps every target generator to the exact source singleton.
The only actual generator is the checked retire occurrence; all retire maps are
executable identity maps on effect state.  Iterator-forward/yielded generators
are eliminated because a singleton `O-Retire` trace contains no `L-Advance`
occurrence.  No dictionary identity is assumed: exact `OccursIn` equality
connects the stored checked transition to the selected singleton.

### 3.3 Derived endpoint

- `retireActualEffectFrame` supplies source and moved control-only effect
  frames;
- these compose with `swappedEffects diamond`;
- `controlEquivalentLookupFound` derives the exact moved actor fiber;
- `controlEquivalentAfterRelatedRetire` proves pointwise lookup equivalence
  after replacing both related fibers by their retired forms; and
- target well-formedness is the checked preservation result.

The output is an actual `RelationalReplayEndpoint sourceAfter replayedAfter`.

### 3.4 Derived occurrence and ordinal capital

`singletonRetireOccurrenceCorrespondence` maps the exact replayed occurrence to
the exact checked source occurrence, proves tag equality, and eliminates
impossible generated-registration occurrences.  The relative ordinal law is
proved by exhaustive singleton inversion: both ordinals are zero.

Thus per-action applicability, RAR, endpoint, occurrence, and ordinal capital
all pass the first cross-state checkpoint.

## 4. Bundle mismatch

The scoping probe currently places this field on its recursive suffix
certificate:

```idris
nextBundle : ReplayInvariantBundle ... replayedSuffix
```

That index is incorrect.  `ReplayInvariantBundle` contains, among other fields:

```idris
replayInitialEmpty : bindings (registry initial) = []
```

The recursive suffix begins at `swappedFinal diamond`, not at the system's
original empty state.  In the base case, the candidate therefore requires:

```idris
ReplayInvariantBundle ...
  (the (Transitions swappedFinal swappedFinal) NoTransitions)
```

which immediately forces `bindings (registry swappedFinal) = []`.
`emptySuffixReplayBundleRequiresEmptyRegistry` is the checked projection of this
contradiction.  Normal adjacent swaps occur after registrations and cannot
supply it.

This is not a failure of the checked retire replayer.  It is an indexing error at
the recursive certificate boundary.  Passing a suffix-local bundle as a caller
premise would merely reproduce the output-shaped-capital flaw.

## 5. Corrected certificate split required before the boundary gate

The smallest corrected design retains one opaque outer certificate/result but
separates local recursive and global capital.

### 5.1 Recursive suffix spine

`SealedSuffixReplaySpine sourceSuffix replayedSuffix` owns only capital that is
actually suffix-relative and recursively producer-suppliable:

- exact source and replayed head checked transitions;
- action/tag equality;
- per-step RAR and relational endpoint;
- per-step action/generated occurrence correspondence;
- relative ordinal equality/offset law;
- exact replayed after-state; and
- an already sealed recursive tail.

It must **not** own `ReplayInvariantBundle`.

### 5.2 Outer adjacent envelope

The hidden `AdjacentSwapResult` constructor (or one private adjacent envelope
from which it is assembled) owns the global values:

- exact whole source/replayed traces and decompositions;
- the sealed suffix spine;
- whole RAR composed from prefix, pair, and suffix;
- whole endpoint;
- whole same-external relation;
- whole action/generated occurrence correspondence;
- absolute adjacent ordinal law;
- `sealedOccurrenceFold`; and
- `swappedPremises : ReplayInvariantBundle ... swappedTrace`, indexed by the
  **whole trace from the original empty initial state**.

The outer producer derives `swappedPremises` only after prefix, local pair, and
sealed suffix are assembled.  Recursive Step never asks for a fresh arbitrary
tail or a suffix-local global bundle.

## 6. Provisional field-by-field boundary delta

This is a stop-audit proposal, **not authorization to implement**.

Existing `AdjacentSwapResult` fields remain with their current types:

1. `replayedFinal`;
2. `replayedSuffix`;
3. `swappedTrace`;
4. `originalDecomposition`;
5. `swappedDecomposition`;
6. `swappedSameExternalInputs`;
7. `swappedReplayCorrespondence`;
8. `swappedEndpoint`;
9. `swappedPremises` — explicitly whole-trace only.

Add erased producer-owned fields:

10. `sealedSuffixReplay : SealedSuffixReplaySpine suffix replayedSuffix`;
11. `sealedOccurrenceFold : AdjacentSwapOperationalOccurrenceFold ...`.

Constructor visibility becomes module-private.  `swappedOccurrenceFold` becomes
`sealedOccurrenceFold`; `swappedOccurrenceCorrespondence` remains its projection.

The frozen-declaration forecast remains:

- retire/narrow exactly
  `adjacentSwapOperationalOccurrenceFoldSpike` to the total sealed projection;
- keep `adjacentSwapSuffixSpike` byte-identical;
- keep the other 25 frozen declarations byte-identical;
- hole count `21 -> 20` at boundary retirement; and
- no replacement hole.

This delta may be gated only after a corrected test-local one-step envelope proves
that the **whole** next bundle is producer-suppliable.

## 7. Required next probe before any boundary gate

A new test-local corrected envelope must:

1. use the successful checked retire replay above as its sealed nonempty suffix
   head;
2. carry no suffix-local `ReplayInvariantBundle`;
3. assemble the exact whole replay trace from an authenticated from-empty prefix,
   genuine local pair, and replayed retire head;
4. derive the whole `ReplayInvariantBundle` for that exact trace; and
5. keep `R16ConfluenceTheoremAssemblyPositive` elaborating.

Any requirement to accept the desired whole bundle, aligned trace, discipline,
provenance, or final invariant fields as unrelated caller premises is another
stop condition.

## 8. Checkpoint re-estimate

The first checked cross-state per-action checkpoint lowers operational replay
risk for control-only orchestration heads, but the bundle-indexing defect adds a
new global transport phase.  Remaining estimate is revised from **15–25** to
**18–30 implementation shifts**:

| Remaining phase | Shifts |
|---|---:|
| Corrected test-only spine/envelope and genuine whole-bundle fixture | 3–5 |
| Opaque boundary, fold retirement, manifest and compatibility migration | 2–4 |
| Suffix-free complete producer after the boundary | 2–4 |
| Remaining action families plus recursive whole-bundle transport | 6–10 |
| Complete arbitrary suffix integration | 3–5 |
| Adversarial fixtures and scoped review closure | 2–3 |
| **Total** | **18–30** |

The next checkpoint remains the first complete `adjacentSwapSuffixSpike`.

## Status

- Historical pins: complete and checked.
- Full suffix-free envelope: complete and checked.
- Cross-state checked `O-Retire` replay: complete through RAR, endpoint,
  occurrence, and relative ordinal fields.
- Whole next bundle: blocked by corrected global indexing/transport boundary.
- Frozen changes: none.
- O6 bodies: unchanged and stopped.
