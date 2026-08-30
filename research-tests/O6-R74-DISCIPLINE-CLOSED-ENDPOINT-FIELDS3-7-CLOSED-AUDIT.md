# O6 revision 74: discipline closed; endpoint bundle fields 3–7 closed

## Scope

Grind shift #82 (overall #136) resumed from accepted design boundary `c5d27cd`.
The authorized implementation was private CP5 proof work only. This shift did
not change any public/frozen declaration, producer signature, revision-21
surface, test interface, production source, or package file.

The shift closes `ReplayInvariantBundle` field 2 completely and then closes
fields 3–7 in strict record order. Field 8 (`TraceComponentsTotal`) was not
opened: its moved-pair intermediate-state proof is a separate substantial unit,
and this shift stops at a clean committed boundary before dependent context
quality degrades. This is not classified as a new semantic wall.

## 1. Classifier exclusion promoted privately

The accepted R73 theorem is now private CP5 implementation capital:

```idris
0 candidateSafetyExcludesParentRecovery :
  CandidateRegistrationSwapSafety left right ->
  (child, parent : name) ->
  transitionAction left = ORetire child ->
  ParentRecoveryStep parent right -> Void
```

The proof exhausts all four safety constructors. Their right transition is a
paper activation or paper orchestration; both families are constructively
disjoint from all four parent-recovery constructors.

The R46 positive and expected-failure modules remain permanent tracked tests.
They were not weakened or replaced.

## 2. Structural retirement provenance transport

Three layers are now total:

1. **Pointwise suffix replay**
   - `replayedParentRecoveryToSource` transports a replayed recovery witness
     backward using exact action/tag equality;
   - `sealedSuffixNoParentRecovery`;
   - `sealedSuffixChildRetiresBeforeRecovery`;
   - `sealedSuffixChildRetirementProvenance`.

2. **Adjacent pair and unchanged prefix**
   - `adjacentNoParentRecovery`;
   - `adjacentChildRetiresBeforeRecovery`;
   - `adjacentChildRetirementProvenance`.

   The only dangerous source case is `ChildRetiresNow left`: after swapping,
   the retirement occurs at moved-left, so moved-right must be shown not to be
   a parent recovery. This is discharged exactly by
   `candidateSafetyExcludesParentRecovery` and the diamond-owned action/tag
   equations.

3. **Moved insertion tails**
   - `movedRightTailRetirementProvenance` replays the suffix and prepends
     moved-left under its paper-step non-recovery proof;
   - `movedLeftTailRetirementProvenance` drops original right and replays the
     suffix;
   - `movedRetireBeforeInsertedChildImpossible` eliminates the sole false
     orientation, where original right retires the just-inserted child. A
     checked moved-right retirement would require the child present in the
     same source registry in which checked original left insertion proves it
     absent.

No detached provenance, selector promise, or output-shaped premise is added.

## 3. Parent-yield transport across all three boundaries

The accepted `LocatedTransportedParentYield` package remains byte-preserved and
is consumed for the pointwise suffix.

The moved pair needs two additional operational frames:

- `foreignCheckedParentYieldForward` and
  `foreignCheckedParentYieldBackward` preserve the exact parent lookup across
  an action owned by another name;
- `orchestrationCheckedParentYieldForward` and
  `orchestrationCheckedParentYieldBackward` cover the same-owner orchestration
  cases constructively:
  - same-owner insertion conflicts with source absence or an inactive fresh
    fiber;
  - retirement preserves component, program, and lifecycle while changing
    only the retired flag;
  - removal conflicts with a nonempty reloading yield or deletes the target
    lookup.

The aligned wrappers correlate stored transition dictionaries with the global
bundle dictionaries. `movedRightParentYield` and `movedLeftParentYield` then
select the exact proof from revision-21 safety:

- activation crossings use the retained child/parent exclusion and foreign
  lookup frame;
- orchestration crossings use the exhaustive same/foreign orchestration proof.

## 4. Registration discipline field 2 closed

The transport is factored at four levels:

- `sameActionRegistrationStepDiscipline` and
  `pointwiseRegistrationStepDiscipline` replay one suffix head;
- `sealedSuffixRegistrationDiscipline` recurses over the exact sealed suffix;
- `movedRegistrationStepDiscipline` transports one reordered pair head with
  insertion-indexed parent-yield and retirement callbacks;
- `adjacentPairRegistrationDiscipline` assembles moved-right, moved-left, and
  replayed suffix;
- `adjacentRegistrationDiscipline` recursively preserves the unchanged prefix
  and transports any earlier child insertion's retirement provenance across
  the complete adjacent replacement.

`AdjacentAlignedPointwiseReplay` now owns erased
`alignedReplayDiscipline`. `produceAdjacentAlignedPointwiseReplay` derives it
from the original global bundle and the same sealed suffix producer that owns
the target trace. Bundle field 2 is therefore completely closed without
changing `ReplayInvariantBundle` or the frozen adjacent signature.

## 5. Bundle fields 3–7

The private outer envelope now owns, in exact bundle order:

| Field | Status | Construction |
|---|---|---|
| 1 `replayAligned` | closed earlier | producer-owned prefix + moved pair + suffix alignment |
| 2 `replayDiscipline` | **closed this shift** | complete structural transport above |
| 3 `replayInitialWellFormed` | **closed** | unchanged initial state |
| 4 `replayInitialEmpty` | **closed** | unchanged initial state |
| 5 `replayFinalWellFormed` | **closed** | suffix replay endpoint |
| 6 `replayQuiet` | **closed** | pointwise controls + effects + target well-formedness |
| 7 `replayNoFailure` | **closed** | pointwise lifecycle/outcome preservation |

Quietness is not assumed from endpoint equality. `pointwiseQuietTrue` locates
each target fiber by name, obtains the related source fiber, transports
`targetFiber` resolution through `pointwiseConcreteTargetFiberSame`, and then
handles every lifecycle-control constructor. Failure-freedom similarly
transports the exact inactive outcome and reconstructs the target registry
fold.

All proof-only locals introduced in the outer producer are explicitly quantity
0.

## 6. Field 8 boundary

Field 8 is:

```idris
TraceComponentsTotal nameEq keyEq alignedReplayTrace
```

Pointwise suffix heads have enough capital: each sealed head owns an exact
post-step relational endpoint, and effect-table equality transports
`ActiveFiberProvidesAll`.

The moved pair is a distinct proof unit. `TransitionComponentTotal` samples the
acting fiber at each **intermediate post-state**, whereas
`LocalRelationalDiamond` retains only the moved pair and final relational
endpoint. The proof must constructively frame totality through the other moved
step, including same-actor repeated activation cases, without adding an
intermediate relation to the frozen diamond. Existing checked transitions and
source totality appear sufficient; no counterexample or missing premise was
found. The unit was deliberately left unopened rather than spending a fresh
three-attempt budget at the end of a long context.

Classification: **tractable implementation boundary, not a semantic wall**.

## 7. Frozen-capital audit

Unchanged:

- `CandidateRegistrationSwapSafety` and erased
  `LocalRelationalDiamond.registrationSwapSafety`;
- all four genuine producer signatures and fields;
- `ReplayInvariantBundle` and `AdjacentSwapResult` public surfaces;
- revision-20 maps/RAR, iterator outcomes, and R27 identity;
- `JointLocatedConsTargetGenerator`, generator-origin section, RAR chain,
  occurrence correspondence, ordinals, suffix alignment, and outer alignment;
- transported-yield package from `9039970`;
- 1183-byte `adjacentSwapSuffixSpike`, SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- `src/`, `dgamma.ipkg`, and CP3 blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.

No escape hatch, postulate, partial default, or new hole was introduced.

## Recommendation and estimate

Next shift:

1. prove relational transport of `ActiveFiberProvidesAll`;
2. transport totality down the sealed suffix;
3. prove moved-pair totality using the checked same/foreign actor split;
4. close bundle field 8;
5. continue fields 9–15 in strict order;
6. stop at a new semantic wall or complete private assembly only with clear
   remaining budget.

One implementation shift of the accepted **3–15** band is consumed. The honest
remaining band is **2–14 shifts**.

## Status

- private classifier exclusion: **proved**;
- suffix retirement provenance: **proved**;
- whole-adjacent retirement provenance: **proved**;
- pointwise/moved parent-yield transport: **proved**;
- bundle field 2: **closed**;
- bundle fields 3–7: **closed**;
- bundle field 8: **unopened at a tractable intermediate-totality boundary**;
- bundle fields 9–15: **unopened**;
- final private bundle/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- remaining O6 band: **2–14 shifts**.
