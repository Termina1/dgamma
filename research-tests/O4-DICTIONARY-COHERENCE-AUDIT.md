# O4 dictionary-coherence audit-lite

Audit date: 2026-08-23  
Audit base: `cp5-thm73-scoping@3ead7d08887f2529a59ff2d45b67a4d52af9b636`  
Scope: the two still-open mixed local-diamond bodies
`activationOrchestrationDiamondSpike_rhs` and
`orchestrationActivationDiamondSpike_rhs`. No declaration, frozen manifest,
hole, production file, package file, or test interface is changed by this audit.

## Verdict and gate request

O4 hits the same executable-dictionary boundary independently found and repaired
for O3. The revision-13 authorization was expressly O3-only, so proof work stops
here before either O4 declaration is changed.

The narrow producer-authenticated premise specification is:

1. add to `activationOrchestrationDiamondSpike` one erased source-pair premise

   ```idris
   (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
     (MoreTransitions left (MoreTransitions right NoTransitions))) ->
   ```

2. add to `orchestrationActivationDiamondSpike` that same erased source-pair
   premise and one erased singleton-applicability premise

   ```idris
   (0 earlyRightAligned : AlignedTransitions name key world error value
     nameEq keyEq (MoreTransitions earlyRight NoTransitions)) ->
   ```

This is the exact O4 analogue of revision 13. It does not add raw dictionary
equalities, caller-selected maps, evaluator outputs, effects, controls, or
applicability assertions. It only authenticates the dictionaries already stored
in the exact transitions accepted by the two declarations.

**Gate request:** authorize only those three erased premise occurrences, followed
by an O4-specific positive producer probe and independent-dictionary negative.
If authorized, the existing tracked shape caller
`research-tests/DGamma/R4OADiamondApplication.idr` must be repaired to receive
producer-owned alignment rather than manufacture it.

## 1. Reproduced blocker

`Transition` stores unrestricted executable dictionaries in every `Fired`
constructor (`src/DGamma/Calculus.idr:5841-5847`). A bare transition cannot
project its checked equation under separately supplied outer dictionaries. The
following total diagnostic probe was checked against this audit base:

```idris
0 outerCheckedEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  checkedApplyAction @{nameEq} @{keyEq} (transitionAction transition) first =
    Just (transitionTag transition, middle)
outerCheckedEquation nameEq keyEq
  (Fired storedNameEq storedKeyEq action tag fires) = fires
```

Idris 2 0.8.0 rejects the final line at `fires` with:

```text
Mismatch between: storedKeyEq and keyEq.
```

The failure is at the executable `checkedApplyAction` evaluator, not at an
irrelevant proof field. Hedberg/UIP cannot identify arbitrary `DecEq` records or
the `No` functions stored by their `Dec` results.

Both mixed proofs need the rejected projection immediately:

- A/O must invert the checked source activation and checked later orchestration
  under the outer dictionaries, reconstruct the orchestration at `first`, and
  replay the activation after that foreign registry update.
- O/A must invert both source nodes under the outer dictionaries and also invert
  the supplied `earlyRight` activation at `first` before replaying the
  orchestration after it.

Pattern matching `PaperActivationStep` or `PaperOrchestrationStep` reveals only
action/tag shape. It does not constrain the dictionaries stored by `Fired`.
`TraceIndependent` and source well-formedness likewise do not refine those
indices. Therefore the current standalone signatures do not supply the first
operational equations needed by an outer-dictionary proof.

## 2. Consumer trace

The immutable theorem is not the source of arbitrary dictionaries. Its two
statement-input traces are accompanied by
`AlignedTransitions ... nameEq keyEq` (`src/DGamma/CP3.idr:3785-3810`). The
`AlignedStep` result index is literally a transition constructed as
`Fired nameEq keyEq ...` (`src/DGamma/Metatheory.idr:897-913`).

Every sorting/block consumer retains this authority:

- `ReplayInvariantBundle.replayAligned` stores exact alignment for the current
  replay trace
  (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:430-450`).
- `adjacentSwapSuffixSpike` consumes that exact bundle together with an exact
  prefix/pair/suffix decomposition. The existing immutable
  `alignedAppendSplit` (`src/DGamma/CP3.idr:4793-4805`) splits the bundle first
  at the prefix and then after the two-node pair.
- O17's `sortClosingFreeTraceSpike` must produce a
  `FiniteAdjacentSwapDerivation`; every derivation step stores its exact source
  pair and the resulting `AdjacentSwapResult` stores the next
  `ReplayInvariantBundle`.
- O6/O19 block producers receive `AdjacentActorSwapSafety.sourcePremises`, and
  `OperationalAdjacentBlockSwap.blockSwapPremises` supplies the recursively
  moved source (`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:114-142,
  643-669`). O19's sealed realization starts at
  `canonicalReplayPremises leftCapital` and retains
  `operationalTargetPremises` (`CP5ConfluenceCrossTraceSpike.idr:887-893`).

Thus every genuine A/O or O/A current pair is selected from a trace whose
producer owns the proposed source-pair premise. The only tracked direct O4 call,
`R4OADiamondApplication`, is an interface-shape probe accepting arbitrary
`earlyRight`; it is not a theorem producer and cannot justify leaving the
standalone signature unauthenticated.

## 3. Producer-suppliability

### 3.1 Exact current pair

The already checked tracked producer
`research-tests/DGamma/R13O3AlignedProducerPositive.idr` defines
`alignedPairFromReplayBundle`. It pattern matches `replayAligned` and constructs
exactly:

```idris
AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions left (MoreTransitions right NoTransitions))
```

Its type is orientation-agnostic: neither the proof nor `AlignedTransitions`
depends on whether the two nodes are A/A, A/O, O/A, or O/O. Therefore the same
checked producer supplies the proposed O4 source-pair premise without any new
capital.

### 3.2 Early O/A activation

`earlyRight` is operational applicability at `first`, not an independently
selected immutable-input occurrence. A genuine O/A producer must evaluate the
right activation at `first`. Once it obtains

```idris
earlyChecked : checkedApplyAction @{nameEq} @{keyEq} earlyAction first =
  Just (earlyTag, earlyRightFinal)
```

it constructs both the transition and alignment definitionally:

```idris
earlyRight = Fired nameEq keyEq earlyAction earlyTag earlyChecked

earlyRightAligned =
  AlignedStep earlyAction earlyTag earlyChecked NoTransitions AlignedEnd
```

The same construction is typechecked by
`genuineO3AlignmentsPositive` in the tracked R13 positive module. Again its type
is independent of the other node's orientation. Requiring the singleton
alignment rejects arbitrary caller-provided `earlyRight` while accepting every
genuine checked reconstruction.

### 3.3 Negative boundary

The tracked `R13O3IndependentDictionaryNegative` already checks the same indexed
boundary: a `Transition` built with an alternate `keyEq` cannot inhabit an
`AlignedTransitions ... nameEq keyEq` premise and fails with
`Mismatch between: alternateKeyEq and keyEq.` This is not O3-specific; it is the
constructor index O4 must authenticate too.

## 4. Premise minimality and consumer need

The A/O declaration does not need a separate `earlyRightAligned` argument because
it does not currently accept an `earlyRight`; the proof must reconstruct the
moved orchestration itself under `nameEq`/`keyEq`. The one source alignment
exposes both original checked equations.

The O/A declaration does accept `earlyRight`, so source alignment alone says
nothing about that third independently stored transition. Its singleton
alignment is separately consumer-needed and producer-suppliable. Conversely,
adding six `DecEq` equalities, arbitrary checked equations, raw evaluator
outputs, or a caller-selected moved transition would be wider and less
source-authenticated than the proposed indexed premises.

No claim is made here that the remaining O4 operational commutation is proved.
After a gate, A/O and O/A still require rule-by-rule insert/retire/remove framing,
activation target/applicability preservation, effect commutation, ordered
control comparison, and checked endpoint assembly. This audit establishes only
the minimal dictionary capital needed to begin those constructive proofs.

## Status

- F1 plan-count/release prose repair: committed separately at `91118c7`.
- F2 `unsafePerformIO` escape-guard repair: committed separately at `3ead7d0`.
- O4 declarations and manifest: unchanged.
- O4 holes: unchanged (two).
- Production `src/`, `dgamma.ipkg`, and immutable CP3: unchanged.
- Proof work: stopped pending an explicit O4 interface gate.
