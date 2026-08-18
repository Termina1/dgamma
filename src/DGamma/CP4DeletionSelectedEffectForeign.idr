module DGamma.CP4DeletionSelectedEffectForeign

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RecoveryForeignCommute
import DGamma.CP4RecoveryTrace
import Decidable.Equality

%default total

0 partialJustNothingImpossible :
  PartialRelated state rel (Just left) Nothing -> Void
partialJustNothingImpossible relation impossible

0 partialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewrite Refl Refl related = related

record RelatedRightOutput
  (keyEq : DecEq key) (effectMap : PartialEffectMap name key value world)
  (left, right, leftOutput : EffectState name key value world) where
  constructor MkRelatedRightOutput
  0 relatedRightOutput : EffectState name key value world
  0 relatedRightRuns : effectMap right = Just relatedRightOutput
  0 relatedOutputs : EffectStateRelated keyEq leftOutput relatedRightOutput

0 effectMapRunsOnRelatedRight :
  (keyEq : DecEq key) ->
  (effectMap : PartialEffectMap name key value world) ->
  EffectPartialMapRespects keyEq effectMap ->
  (left, right, leftOutput : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  effectMap left = Just leftOutput ->
  RelatedRightOutput keyEq effectMap left right leftOutput
effectMapRunsOnRelatedRight keyEq effectMap respects left right leftOutput
  related leftRuns with (effectMap right) proof rightResult
  effectMapRunsOnRelatedRight keyEq effectMap respects left right leftOutput
    related leftRuns | Nothing =
      let 0 contradiction : PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq) (Just leftOutput) Nothing
          contradiction = partialRelatedRewrite leftRuns rightResult
            (respects left right related)
      in void (partialJustNothingImpossible contradiction)
  effectMapRunsOnRelatedRight keyEq effectMap respects left right leftOutput
    related leftRuns | Just rightOutput =
      let 0 outputs : EffectStateRelated keyEq leftOutput rightOutput
          outputs = case partialRelatedRewrite leftRuns rightResult
            (respects left right related) of
              PartialDefined relation => relation
      in MkRelatedRightOutput rightOutput rightResult outputs

||| Effect-level Lemma-71 diamond for one foreign checked transition.  The
||| original transition's corrected Definition-60 map is proved to run on the
||| survivor projection, and its output is related to the target's accumulated
||| recovery.  Control applicability is intentionally a separate consumer: for
||| L-Advance its raw map still carries the original fiber/control origin.
public export
record ForeignSelectedEffectStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (before, afterState, survivor : SystemState name key value world error)
  (transition : Transition before afterState)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast) where
  constructor MkForeignSelectedEffectStep
  0 foreignTargetModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole afterState
  0 foreignTargetRecovered : EffectState name key value world
  0 foreignTargetRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle foreignTargetModel) (projectEffectState @{nameEq} afterState) =
    Just foreignTargetRecovered
  0 foreignSurvivorOutput : EffectState name key value world
  0 foreignMapRunsOnSurvivor : partialEffectMap transition
    (projectEffectState @{nameEq} survivor) = Just foreignSurvivorOutput
  0 foreignOutputMatchesTarget : EffectStateRelated keyEq foreignSurvivorOutput
    foreignTargetRecovered

0 foreignEffectStepFromAccumulator :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) ->
  (commuted : ForeignAccumulatorStep name key world error value nameEq keyEq
    selected (Fired nameEq keyEq action tag checked) whole sourceModel) ->
  (nextModel : AccumulatorModel name key world error value nameEq keyEq selected
    whole afterState) ->
  accumulatorEffectMap nameEq keyEq selected (modelHandle nextModel)
    (projectEffectState @{nameEq} afterState) =
      Just (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered
        commuted) ->
  EffectStateRelated keyEq
    (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceRecovered
      commuted)
    (projectEffectState @{nameEq} survivor) ->
  ForeignSelectedEffectStep name key world error value nameEq keyEq selected
    before afterState survivor
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole
foreignEffectStepFromAccumulator
  {name} {key} {world} {error} {value}
  nameEq keyEq selected action tag before afterState checked whole survivor
  sourceModel commuted nextModel nextRuns sourceToSurvivor =
    let 0 transferred = effectMapRunsOnRelatedRight keyEq
          (partialEffectMap
            (Fired {before = before} {afterState = afterState} nameEq keyEq
              action tag checked))
          (partialEffectMapRespects nameEq keyEq action tag before afterState
            checked)
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceRecovered
            commuted)
          (projectEffectState @{nameEq} survivor)
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.foreignRecovered
            commuted)
          sourceToSurvivor
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.foreignRecoveredRuns
            commuted)
    in case transferred of
      MkRelatedRightOutput survivorOutput survivorRuns foreignToSurvivor =>
        let 0 survivorToTarget : EffectStateRelated keyEq survivorOutput
              (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered
                commuted)
            survivorToTarget = transitive (EffectStateEquivalence keyEq)
              (symmetric (EffectStateEquivalence keyEq) foreignToSurvivor)
              (symmetric (EffectStateEquivalence keyEq)
                (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecoveredRelated
                  commuted))
        in MkForeignSelectedEffectStep nextModel
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered
            commuted)
          nextRuns survivorOutput survivorRuns survivorToTarget

||| Transpose one foreign actual generator across the selected accumulator.
||| `foreignAccumulatorStep` supplies the commuting diamond at the recovered
||| source; congruence of the exact ordered-table relation transports that map
||| to the independently constructed survivor projection.
public export
0 foreignStepTransposesSelectedEffectBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  (independent : TraceIndependent name key world error value keyEq whole) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole before survivor) ->
  (distinct : Not (selected = actionOwner action)) ->
  ForeignSelectedEffectStep name key world error value nameEq keyEq selected
    before afterState survivor
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole
foreignStepTransposesSelectedEffectBoundary
  {name} {key} {world} {error} {value}
  nameEq keyEq selected action tag before afterState checked whole occurs
  independent survivor
  (MkSelectedEffectReplayBoundary sourceModel boundaryRecovered boundaryRuns
    survivorToBoundary)
  distinct =
    let 0 commuted = foreignAccumulatorStep nameEq keyEq selected action tag
          before afterState checked distinct whole occurs independent sourceModel
        0 sourceSame = justInjective (trans (sym boundaryRuns)
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceAccumulatorRuns
            commuted))
        0 survivorToSource : EffectStateRelated keyEq
          (projectEffectState @{nameEq} survivor)
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceRecovered
            commuted)
        survivorToSource = replace
          {p = \observed => EffectStateRelated keyEq
            (projectEffectState @{nameEq} survivor) observed}
          sourceSame survivorToBoundary
        0 sourceToSurvivor : EffectStateRelated keyEq
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceRecovered
            commuted)
          (projectEffectState @{nameEq} survivor)
        sourceToSurvivor = symmetric (EffectStateEquivalence keyEq)
          survivorToSource
        0 nextModel : AccumulatorModel name key world error value nameEq keyEq
          selected whole afterState
        nextModel = foreignStepPreservesAccumulatorModel nameEq keyEq selected
          action tag before afterState whole checked distinct sourceModel
        0 nextRuns : accumulatorEffectMap nameEq keyEq selected
            (modelHandle nextModel) (projectEffectState @{nameEq} afterState) =
          Just
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered
              commuted)
        nextRuns = trans
          (foreignStepPreservesAccumulatorMap nameEq keyEq selected action tag
            before afterState whole checked distinct sourceModel
            (projectEffectState @{nameEq} afterState))
          (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetAccumulatorRuns
            commuted)
    in foreignEffectStepFromAccumulator nameEq keyEq selected action tag before
      afterState checked whole survivor sourceModel commuted nextModel nextRuns
      sourceToSurvivor

||| Once the control half has rebuilt a concrete survivor target and related its
||| actual effect projection to the transported map output, the next selected
||| replay boundary follows without re-running any commutation argument.
public export
0 foreignEffectStepGivesNextBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {before, afterState, survivor, survivorAfter :
    SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (step : ForeignSelectedEffectStep name key world error value nameEq keyEq
    selected before afterState survivor transition whole) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} survivorAfter)
    (foreignSurvivorOutput step) ->
  SelectedEffectReplayBoundary name key world error value nameEq keyEq selected
    whole afterState survivorAfter
foreignEffectStepGivesNextBoundary nameEq keyEq selected transition whole
  (MkForeignSelectedEffectStep targetModel targetRecovered targetRuns
    survivorOutput mapRuns survivorToTarget)
  actualToOutput =
    MkSelectedEffectReplayBoundary targetModel targetRecovered targetRuns
      (transitive (EffectStateEquivalence keyEq) actualToOutput survivorToTarget)
