# O6 revision 73: retirement/recovery safety classification campaign

## Scope

Design-only shift #81 (overall #135) started from `0a42210`. It investigated
the revision-72 claim that the landed registration-swap safety permits
`ORetire child ; LLeave parent`. No research implementation, public record,
producer, hole declaration, adjacent body, production module, or package file
was changed.

The make-or-break result reverses revision 72's classification: the operational
countershape is checked, independent, and effect-commuting, but **cannot inhabit
`CandidateRegistrationSwapSafety` at all**. Every safety constructor already
classifies the right transition as either `PaperActivationStep` or
`PaperOrchestrationStep`; every `ParentRecoveryStep` is constructively disjoint
from both classes. The proposed extra exclusion is therefore derivable from the
landed field and redundant.

## 1. Total checked operational countershape

`DGamma.R46RetirementRecoverySwapSafetyDesignPositive` constructs concrete
empty-effect fibers:

- actor `0`: a retired active root parent;
- actor `1`: an inactive child of actor `0`.

It checks both orders:

```text
ORetire 1 ; LLeave 0
LLeave 0  ; ORetire 1
```

The module retains exact source, intermediate, early-right, and target states,
all four checked transitions, both aligned two-step traces, and:

```idris
0 r46OperationalEndpointsEqual : r46SourceFinal = r46TargetFinal
```

Thus the operational/effect diamond shape itself is real.

The source temporal evidence is total:

```idris
0 r46SourceRetirementProvenance :
  ChildRetirementProvenance 0 1 r46SourcePair
```

through `ChildRetiresNow`. The swapped provenance is constructively impossible:

```idris
0 r46TargetRetirementProvenanceImpossible :
  ChildRetirementProvenance 0 1 r46TargetPair -> Void
```

because the target head is `ParentLeaves`. This validates revision 72's claim
about the *order-sensitive proposition itself*.

The requested stronger object—this pair together with landed revision-21
safety—is uninhabitable. That part of the requested counterexample cannot be
pinned positively without contradiction. Instead, the campaign pins its exact
negation both as a total theorem and an expected compiler failure.

## 2. Landed safety already excludes every right recovery

The campaign proves the generic theorem:

```idris
0 candidateSafetyExcludesParentRecovery :
  CandidateRegistrationSwapSafety left right ->
  (child, parent : name) ->
  transitionAction left = ORetire child ->
  ParentRecoveryStep parent right -> Void
```

The left-retirement equality is intentionally not needed. Case analysis on the
four safety constructors exposes one of two right classifiers:

| Safety constructor | Right classifier |
|---|---|
| A/A | `PaperActivationStep right` |
| A/O | `PaperOrchestrationStep right` |
| O/A | `PaperActivationStep right` |
| O/O | `PaperOrchestrationStep right` |

`activationCannotRecover` proves disjointness with all recovery constructors:

- `ParentLeaves`: action `LLeave`, not `LBegin`/`LAdvance`;
- `ParentDivertsBefore`: action `LDivert`;
- `ParentDivertsAfter`: action `LAdvance`, but tag `LDivertTag`, not
  `LIterTag`/`LFinishTag`;
- `ParentRaises`: action `LAdvance`, but tag `LRaiseTag`.

`orchestrationCannotRecover` eliminates the same recovery constructors because
O-Insert/O-Retire/O-Remove actions are never lifecycle actions.

The concrete consequences are:

```idris
0 r46NoLandedSafety :
  CandidateRegistrationSwapSafety r46RetireChild r46LeaveParent -> Void

0 r46NoLiveDiamond :
  LocalRelationalDiamond ... r46RetireChild r46LeaveParent -> Void
```

`R46RetirementRecoveryLiveSafetyNegative` independently pins direct constructor
rejection at the right classifier:

```text
Mismatch between: LAdvance ?actor and LLeave 0.
```

## 3. Make-or-break genuine-chain result

The checked fixture supplies every operational O/A producer premise that is
meaningful before the right classifier:

- exact source pair alignment;
- exact early-right alignment;
- source registry well-formedness;
- distinct actors;
- `PaperOrchestrationStep` for the left O-Retire;
- both O/A insertion exclusions, vacuously but totally; and
- a constructive `TraceIndependent` for the exact pair.

`r46PairIndependent` is not assumed. Every actual generator is identity on the
empty effect state, no iterator stage can occur because neither pair action is
`LAdvance`, and arbitrary generated transformations reduce recursively to the
identity. Therefore Definition 60 does **not** exclude the operational pair.

The sole missing genuine-producer premise is precisely:

```idris
PaperActivationStep r46LeaveParent
```

and the total theorem

```idris
0 r46LeaveCannotReachGenuineOAProducer :
  PaperActivationStep r46LeaveParent -> Void
```

eliminates it. Consequently no genuine `orchestrationActivationDiamondSpike`
can contain this pair, and no R16-chain adjacent call can receive it: the
byte-frozen adjacent function requires a `LocalRelationalDiamond`, whose landed
`registrationSwapSafety` projection already entails the exclusion.

### Classification

This is **not** a reachable theorem-level counterexample and not a
representation-loss gap. It is a proof-discovery gap in revision 72: the exact
needed exclusion was latent in the landed classifiers. The paper's Theorem 73
is not challenged by this shape.

## 4. Producer and selector capital inventory

### Four genuine diamond producers

All four central producers already require and retain exhaustive right-step
classification:

- `activationActivationDiamondSpike`: right activation;
- `activationOrchestrationDiamondSpike`: right orchestration;
- `orchestrationActivationDiamondSpike`: right activation;
- `orchestrationOrchestrationDiamondSpike`: right orchestration.

Revision 21 copies those classifiers into
`CandidateRegistrationSwapSafety`. No additional construction-site evidence is
needed.

### Adjacent boundary

`adjacentSwapSuffixSpike` accepts a `LocalRelationalDiamond`, not raw checked
transitions. The erased `registrationSwapSafety` field therefore supplies the
classification theorem at bundle field 2 without changing the frozen adjacent
signature.

### Sorting selector

`SameExternalOrchestration` and `TraceIndependent` are not the relevant
exclusion: internal lifecycle/orchestration noise may satisfy the external
projection, and the concrete pair is independently effect-commuting. The
selector cannot call adjacent replay until it has constructed one of the four
genuine local diamonds. That producer choice is the effective restriction and
already rejects recovery rules outside Lemma 71's activation class.

## 5. Cure comparison, both directions

### Cure A: extend revision-21 safety

The test-local `CandidateRetirementRecoverySafe` stores the proposed field:

```idris
(child, parent : name) ->
transitionAction left = ORetire child ->
ParentRecoveryStep parent right -> Void
```

Forward probe:

```idris
retainCandidateRetirementRecoverySafety :
  CandidateRegistrationSwapSafety left right ->
  CandidateRetirementRecoverySafe left right
```

is total via `candidateSafetyExcludesParentRecovery`.

Reverse use is unnecessary: a wrapper carrying both the base safety and the new
field projects the base unchanged, while the new field adds no inhabitants and
no downstream fact. Appending it to each safety constructor or to
`LocalRelationalDiamond` would duplicate derivable capital and change a frozen
surface for no semantic gain.

### Cure B: selector restriction

`CandidateSelectorRestrictedDiamond` is a test-local wrapper around a live
diamond plus the proposed exact exclusion.

Both directions are total:

```idris
restrictExistingDiamond :
  LocalRelationalDiamond ... left right ->
  CandidateSelectorRestrictedDiamond ... left right

projectRestrictedDiamond :
  CandidateSelectorRestrictedDiamond ... left right ->
  LocalRelationalDiamond ... left right
```

The forward direction derives the restriction from the existing safety field;
the reverse is direct projection. Changing selector or adjacent interfaces is
therefore also redundant and would reintroduce detached caller capital if the
restriction were passed separately.

## 6. Revision-22 manifest result

`research-tests/cp5-r22-proposed-manifest-delta.json` records:

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

It proposes no type, record-field, constructor, or hole-signature revisions.
The only next implementation is a private lemma equivalent to
`candidateSafetyExcludesParentRecovery`, followed by the structural
`ChildRetirementProvenance` transport inside bundle field 2. That private lemma
is not yet authorized or landed.

## 7. Recommendation

1. Do **not** revise `CandidateRegistrationSwapSafety`,
   `LocalRelationalDiamond`, the selector, or `adjacentSwapSuffixSpike`.
2. Authorize promotion of the test-local classifier theorem as a private CP5
   helper.
3. Transport `NoParentRecovery` and `ChildRetiresBeforeRecovery` through the
   sealed suffix spine by action/tag preservation.
4. At the moved pair boundary, use the classifier theorem to discharge the only
   dangerous orientation: a source-left retirement cannot cross a right parent
   recovery.
5. Resume field 2, then fields 3–15 and assembly under the existing stop rules.

The design campaign resolves the apparent semantic wall without widening the
implementation surface. The honest O6 remainder is re-estimated at **3–15
implementation shifts**: the lower bound rises from 1 because retirement
provenance now requires a structural suffix theorem, a moved-pair theorem, and
prefix reconstruction; the prior upper bound remains 15 because no frozen
revision or producer campaign is needed.

## Frozen-capital audit

This design-only shift does not change:

- `CandidateRegistrationSwapSafety` or `LocalRelationalDiamond`;
- any genuine producer;
- `ReplayInvariantBundle`, RAR, revision-20 maps, or adjacent result;
- joint generator, generator origin, RAR chain, conversion, ordinals,
  correspondence, or alignment;
- the 1183-byte `adjacentSwapSuffixSpike` declaration, SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- `src/`, `dgamma.ipkg`, or CP3 blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.

## Status

- checked operational retirement/recovery countershape: **proved**;
- source retirement provenance: **proved**;
- swapped retirement provenance impossibility: **proved**;
- pair independence: **proved**;
- landed safety exclusion theorem: **proved in test-local probe**;
- genuine R16-chain reachability: **constructively rejected**;
- theorem-level counterexample: **none**;
- frozen revision 22: **not needed**;
- field 2 implementation: **not started in this design-only shift**;
- fields 3–15 and assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 implementation band: **3–15 shifts**.
