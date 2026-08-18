module DGamma.CP4RecoverySelectedReplayStep

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionFrameRetire
import DGamma.CP4DeletionFrameDivert
import DGamma.CP4DeletionFrameLeave
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoverySelectedRetire
import DGamma.CP4RecoverySelectedDivert
import DGamma.CP4RecoverySelectedLeave
import DGamma.CP4RecoverySelectedAdvance
import DGamma.CP4RecoverySelectedStep
import DGamma.CP4RecoverySelectedEffect
import DGamma.Unified
import Decidable.Equality

%default total

0 partialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewrite Refl Refl related = related

public export
record SelectedAccumulatorStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {before, afterState : SystemState name key value world error}
  (transition : Transition before afterState)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) where
  constructor MkSelectedAccumulatorStep
  targetModel : AccumulatorModel name key world error value nameEq keyEq selected
    whole afterState
  0 sourceRecovered : EffectState name key value world
  0 targetRecovered : EffectState name key value world
  0 sourceAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle sourceModel) (projectEffectState @{nameEq} before) =
    Just sourceRecovered
  0 targetAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle targetModel) (projectEffectState @{nameEq} afterState) =
    Just targetRecovered
  0 recoveredRelated : EffectStateRelated keyEq sourceRecovered targetRecovered

accumulatorResult :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  AccumulatorHandle key value world -> EffectState name key value world ->
  EffectState name key value world
accumulatorResult nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator) state =
    let restored = accumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder provision
              (effectTables state selected)))
    in setEffectTable @{nameEq} selected (ownedValues (localTable restored))
      (setEffectAmbient (localWorld restored) state)

0 accumulatorResultRuns :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (handle : AccumulatorHandle key value world) ->
  (state : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected handle state =
    Just (accumulatorResult nameEq keyEq selected handle state)
accumulatorResultRuns nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator)
  (MkEffectState ambient tables) = Refl

0 sameAccumulatorControlStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {before, afterState : SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) ->
  (targetModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole afterState) ->
  ((state : EffectState name key value world) ->
    accumulatorEffectMap nameEq keyEq selected (modelHandle targetModel) state =
    accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel) state) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState) ->
  SelectedAccumulatorStep name key world error value nameEq keyEq selected
    transition whole sourceModel
sameAccumulatorControlStep nameEq keyEq selected transition whole sourceModel
  targetModel mapsSame projectedRelated =
    let 0 sourceRuns = accumulatorResultRuns nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before)
        0 targetRuns = accumulatorResultRuns nameEq keyEq selected
          (modelHandle targetModel) (projectEffectState @{nameEq} afterState)
        0 respected = accumulatorEffectMapRespects nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState) projectedRelated
        0 atOutputs : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (Just (accumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before)))
          (Just (accumulatorResult nameEq keyEq selected
            (modelHandle targetModel)
            (projectEffectState @{nameEq} afterState)))
        atOutputs = partialRelatedRewrite sourceRuns targetRuns
          (rewrite mapsSame (projectEffectState @{nameEq} afterState) in respected)
        0 related : EffectStateRelated keyEq
          (accumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before))
          (accumulatorResult nameEq keyEq selected
            (modelHandle targetModel) (projectEffectState @{nameEq} afterState))
        related = case atOutputs of PartialDefined relation => relation
    in MkSelectedAccumulatorStep targetModel
      (accumulatorResult nameEq keyEq selected (modelHandle sourceModel)
        (projectEffectState @{nameEq} before))
      (accumulatorResult nameEq keyEq selected (modelHandle targetModel)
        (projectEffectState @{nameEq} afterState))
      sourceRuns targetRuns related

public export
0 selectedAdvanceAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq
      (LAdvance selected) tag checked) whole) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq (LAdvance selected) tag checked) whole model
selectedAdvanceAccumulatorStep nameEq keyEq selected before afterState tag checked
  whole occurs model =
    case selectedAdvanceAccumulatorRecovery nameEq keyEq selected before
      afterState tag checked whole occurs model of
      MkSelectedAdvanceRecovery target targetRetired sourceRecovered
        targetRecovered sourceRuns targetRuns related =>
          MkSelectedAccumulatorStep target sourceRecovered
          targetRecovered sourceRuns targetRuns related

public export
0 selectedRetireAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (ORetireTag, afterState)) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq (ORetire selected) ORetireTag checked) whole model
selectedRetireAccumulatorStep nameEq keyEq selected before afterState whole checked
  model =
    let raw = checkedActionProjects nameEq keyEq (ORetire selected) before
          afterState ORetireTag checked
        0 projectedRelated : EffectStateRelated keyEq
          (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState)
        projectedRelated = case retireActualEffectFrame nameEq keyEq selected
          before afterState ORetireTag raw of
          MkActualEffectFrame (PartialDefined related) => related
    in sameAccumulatorControlStep nameEq keyEq selected
      (Fired nameEq keyEq (ORetire selected) ORetireTag checked) whole model
      (selectedRetirePreservesAccumulatorModel nameEq keyEq selected before
        afterState whole checked model)
      (selectedRetirePreservesAccumulatorMap nameEq keyEq selected before
        afterState whole checked model)
      projectedRelated

public export
0 selectedDivertAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (LDivertTag, afterState)) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq (LDivert selected) LDivertTag checked) whole model
selectedDivertAccumulatorStep nameEq keyEq selected before afterState whole
  checked model =
    let raw = checkedActionProjects nameEq keyEq (LDivert selected) before
          afterState LDivertTag checked
        0 projectedRelated : EffectStateRelated keyEq
          (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState)
        projectedRelated = case divertActualEffectFrame nameEq keyEq selected
          before afterState LDivertTag raw of
          MkActualEffectFrame (PartialDefined related) => related
    in sameAccumulatorControlStep nameEq keyEq selected
      (Fired nameEq keyEq (LDivert selected) LDivertTag checked) whole model
      (selectedDivertPreservesAccumulatorModel nameEq keyEq selected before
        afterState whole checked model)
      (selectedDivertPreservesAccumulatorMap nameEq keyEq selected before
        afterState whole checked model)
      projectedRelated

0 selectedDivertAccumulatorStepRetired :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (LDivertTag, afterState)) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  retired (modelFiber (targetModel (selectedDivertAccumulatorStep nameEq keyEq
    selected before afterState whole checked model))) = retired (modelFiber model)
selectedDivertAccumulatorStepRetired nameEq keyEq selected before afterState whole
  checked model = selectedDivertPreservesRetired nameEq keyEq selected before
    afterState whole checked model

public export
0 selectedLeaveAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (LLeaveTag, afterState)) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq (LLeave selected) LLeaveTag checked) whole model
selectedLeaveAccumulatorStep nameEq keyEq selected before afterState whole
  checked model =
    let raw = checkedActionProjects nameEq keyEq (LLeave selected) before
          afterState LLeaveTag checked
        0 projectedRelated : EffectStateRelated keyEq
          (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState)
        projectedRelated = case leaveActualEffectFrame nameEq keyEq selected
          before afterState LLeaveTag raw of
          MkActualEffectFrame (PartialDefined related) => related
    in sameAccumulatorControlStep nameEq keyEq selected
      (Fired nameEq keyEq (LLeave selected) LLeaveTag checked) whole model
      (selectedLeavePreservesAccumulatorModel nameEq keyEq selected before
        afterState whole checked model)
      (selectedLeavePreservesAccumulatorMap nameEq keyEq selected before
        afterState whole checked model)
      projectedRelated


public export
record SelectedStableAccumulatorStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {before, afterState : SystemState name key value world error}
  (transition : Transition before afterState)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) where
  constructor MkSelectedStableAccumulatorStep
  stableAccumulatorStep : SelectedAccumulatorStep name key world error value
    nameEq keyEq selected transition whole sourceModel
  0 stableRetiredSame : retired (modelFiber (targetModel stableAccumulatorStep)) =
    retired (modelFiber sourceModel)
0 selectedLeaveAccumulatorStepRetired :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (LLeaveTag, afterState)) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  retired (modelFiber (targetModel (selectedLeaveAccumulatorStep nameEq keyEq
    selected before afterState whole checked model))) = retired (modelFiber model)
selectedLeaveAccumulatorStepRetired nameEq keyEq selected before afterState whole
  checked model = selectedLeavePreservesRetired nameEq keyEq selected before
    afterState whole checked model

public export
0 selectedInstalledAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  actionOwner action = selected ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  installedAt @{nameEq} selected afterState = True ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq action tag checked) whole model
selectedInstalledAccumulatorStep nameEq keyEq selected action tag before afterState
  checked owner whole occurs targetInstalled model =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 sourceInstalled = accumulatorModelInstalledAt model
    in case action of
      OInsert actor parent component => case owner of
        Refl => void (insertCannotExisting nameEq keyEq selected parent component
          before afterState tag raw (modelFiber model) (modelFound model))
      ORetire actor => case owner of
        Refl => case successfulRetireTag nameEq keyEq selected before afterState
          tag raw of
          Refl => selectedRetireAccumulatorStep nameEq keyEq selected before
            afterState whole checked model
      ORemove actor => case owner of
        Refl => void (removeCannotInstalled nameEq keyEq selected before afterState
          tag raw sourceInstalled)
      LBegin actor => case owner of
        Refl => void (beginCannotInstalled nameEq keyEq selected before afterState
          tag raw sourceInstalled)
      LAdvance actor => case owner of
        Refl => selectedAdvanceAccumulatorStep nameEq keyEq selected before
          afterState tag checked whole occurs model
      LDivert actor => case owner of
        Refl => case successfulLDivertTag nameEq keyEq selected before afterState
          tag raw of
          Refl => selectedDivertAccumulatorStep nameEq keyEq selected before
            afterState whole checked model
      LLeave actor => case owner of
        Refl => case successfulLeaveTag nameEq keyEq selected before afterState tag
          raw of
          Refl => selectedLeaveAccumulatorStep nameEq keyEq selected before
            afterState whole checked model
      LUnload actor => case owner of
        Refl => void (unloadCannotEndInstalled nameEq keyEq selected before
          afterState tag raw targetInstalled)

||| Lifecycle-only selected dispatcher with the additional static retirement
||| frame needed by the ordered selected-exempt deletion boundary.
public export
0 selectedInstalledStableAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  actionOwner action = selected ->
  isLifecycleAction action = True ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  installedAt @{nameEq} selected afterState = True ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedStableAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq action tag checked) whole model
selectedInstalledStableAccumulatorStep nameEq keyEq selected action tag before
  afterState checked owner lifecycle whole occurs targetInstalled model =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 sourceInstalled = accumulatorModelInstalledAt model
    in case action of
      OInsert actor parent component => void (case lifecycle of Refl impossible)
      ORetire actor => void (case lifecycle of Refl impossible)
      ORemove actor => void (case lifecycle of Refl impossible)
      LBegin actor => case owner of
        Refl => void (beginCannotInstalled nameEq keyEq selected before afterState
          tag raw sourceInstalled)
      LAdvance actor => case owner of
        Refl => case selectedAdvanceAccumulatorRecovery nameEq keyEq selected
          before afterState tag checked whole occurs model of
          MkSelectedAdvanceRecovery target retiredSame sourceRecovered
            targetRecovered sourceRuns targetRuns related =>
              MkSelectedStableAccumulatorStep
                (MkSelectedAccumulatorStep target sourceRecovered targetRecovered
                  sourceRuns targetRuns related)
                retiredSame
      LDivert actor => case owner of
        Refl => case successfulLDivertTag nameEq keyEq selected before afterState
          tag raw of
          Refl => MkSelectedStableAccumulatorStep
            (selectedDivertAccumulatorStep nameEq keyEq selected before
              afterState whole checked model)
            (selectedDivertAccumulatorStepRetired nameEq keyEq selected before
              afterState whole checked model)
      LLeave actor => case owner of
        Refl => case successfulLeaveTag nameEq keyEq selected before afterState
          tag raw of
          Refl => MkSelectedStableAccumulatorStep
            (selectedLeaveAccumulatorStep nameEq keyEq selected before
              afterState whole checked model)
            (selectedLeaveAccumulatorStepRetired nameEq keyEq selected before
              afterState whole checked model)
      LUnload actor => case owner of
        Refl => void (unloadCannotEndInstalled nameEq keyEq selected before
          afterState tag raw targetInstalled)

