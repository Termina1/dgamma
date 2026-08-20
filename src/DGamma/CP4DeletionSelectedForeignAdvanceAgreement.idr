module DGamma.CP4DeletionSelectedForeignAdvanceAgreement

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome
import DGamma.CP4RecoveryEffectRespect
import Decidable.Equality

%default total

0 systemStateEta : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
systemStateEta (MkSystemState ambient fibers) = Refl

0 outcomeAgreementTransport :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  IteratorOutcomeAgreement name key value world error keyEq leftBefore
    rightBefore ->
  IteratorOutcomeAgreement name key value world error keyEq leftAfter rightAfter
outcomeAgreementTransport Refl Refl agreement = agreement

record LocatedAdvanceStage
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (component : Component key value world error)
  (leftParent : Parent name) (retiredFlag : Bool)
  (leftTable : OwnedTable key value (componentProvisions component))
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)))
  (leftAccumulator : LocalState key value world
    (componentProvisions component) ->
    LocalState key value world (componentProvisions component))
  (view : View name (dependencies (componentDependencies component)))
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast) where
  constructor MkLocatedAdvanceStage
  locatedAdvanceStage : IteratorStage name key world error value actor whole
  0 locatedStageData : (state : EffectState name key value world) ->
    iteratorStageOutcome locatedAdvanceStage state =
    iteratorStageOutcomeComponentData nameEq keyEq actor component view step
      rest state

0 locateAdvanceStage :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) ->
  (leftParent : Parent name) -> (retiredFlag : Bool) ->
  (leftTable : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (leftAccumulator : LocalState key value world
    (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (tag : RuleTag) -> (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq (LAdvance actor) tag checked) whole) ->
  (found : lookupFiber @{nameEq} actor (registry before) = Just
    (MkFiber component leftParent retiredFlag leftTable
      (Reloading (step :: rest) leftAccumulator view))) ->
  LocatedAdvanceStage name key world error value nameEq keyEq actor component
    leftParent retiredFlag leftTable step rest leftAccumulator view whole
locateAdvanceStage nameEq keyEq actor component leftParent retiredFlag leftTable
  step rest leftAccumulator view tag before afterState checked whole occurs found =
    MkLocatedAdvanceStage
      (StageFromAdvance nameEq keyEq actor tag checked occurs
        (MkFiber component leftParent retiredFlag leftTable
          (Reloading (step :: rest) leftAccumulator view)) found
        (step :: rest) leftAccumulator view Refl step rest SuffixHere)
      (\state => Refl)

||| Repaired Equation 55 at the exact plan/survivor sources used by retained
||| selected-episode L-Advance replay.  Empty current-R leaves preserve the
||| original projection, and global Definition-60 independence supplies the
||| survivor-to-original leg.
public export
0 selectedForeignAdvanceOutcomeProvider :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (whole : Transitions wholeFirst wholeLast) ->
  TraceIndependent name key world error value keyEq whole ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq (LAdvance actor) tag checked) whole) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  ((fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} actor
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just fiber ->
    lookupFiber @{nameEq} actor (registry before) = Just fiber) ->
  (component : Component key value world error) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (leftParent, rightParent : Parent name) -> (retiredFlag : Bool) ->
  (leftAccumulator, rightAccumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  lookupFiber @{nameEq} actor
    (planTarget (completePlanResult (selectedBoundaryPlan boundary))) = Just
    (MkFiber component leftParent retiredFlag leftTable
      (Reloading (step :: rest) leftAccumulator view)) ->
  lookupFiber @{nameEq} actor (registry survivor) = Just
    (MkFiber component rightParent retiredFlag rightTable
      (Reloading (step :: rest) rightAccumulator view)) ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcomeComponentData nameEq keyEq actor component view step
      rest (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState (worldState survivor) (registry survivor)))))
    (iteratorStageOutcomeComponentData nameEq keyEq actor component view step
      rest (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState (worldState before)
            (planTarget (completePlanResult
              (selectedBoundaryPlan boundary)))))))

selectedForeignAdvanceOutcomeProvider {name} {key} {world} {error} {value}
  nameEq keyEq selected actor distinct whole
  independent before afterState survivor tag checked occurs boundary emptyPlan
  planFoundOriginal component leftTable rightTable step rest view leftParent
  rightParent retiredFlag leftAccumulator rightAccumulator planFound
  survivorFound =
    let originalFound = planFoundOriginal
          (MkFiber component leftParent retiredFlag leftTable
            (Reloading (step :: rest) leftAccumulator view)) planFound
        stagePackage = locateAdvanceStage nameEq keyEq actor component
          leftParent retiredFlag leftTable step rest leftAccumulator view tag
          before afterState checked whole occurs originalFound
    in case stagePackage of
      MkLocatedAdvanceStage stage stageData =>
        let originalToPlanConcrete = emptyInactivePlanPreservesEffects nameEq
              keyEq (worldState before) (registry before)
              (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
              (inactiveLeafPlan (completePlanResult
                (selectedBoundaryPlan boundary))) emptyPlan
            0 originalToPlan : EffectStateRelated keyEq
              (projectEffectState @{nameEq} before)
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState (worldState before)
                    (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary))))))
            originalToPlan = replace
              {p = \observed => EffectStateRelated keyEq
                (projectEffectState @{nameEq} observed)
                (projectEffectState @{nameEq}
                  (MkSystemState (worldState before)
                    (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary)))))}
              (systemStateEta before) originalToPlanConcrete
            0 survivorToOriginal : IteratorOutcomeAgreement name key value
              world error keyEq
              (iteratorStageOutcome stage
                (projectEffectState @{nameEq} survivor))
              (iteratorStageOutcome stage
                (projectEffectState @{nameEq} before))
            survivorToOriginal = foreignAdvanceOutcomeAgreement nameEq keyEq
              selected actor distinct whole independent
              (selectedBoundaryEffects boundary) stage
            0 originalToPlanOutcomes : IteratorOutcomeAgreement name key value
              world error keyEq
              (iteratorStageOutcome stage
                (projectEffectState @{nameEq} before))
              (iteratorStageOutcome stage
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState (worldState before)
                      (planTarget (completePlanResult
                        (selectedBoundaryPlan boundary)))))))
            originalToPlanOutcomes = iteratorStageOutcomeRelated keyEq stage
              (projectEffectState @{nameEq} before)
              (projectEffectState @{nameEq}
                (MkSystemState (worldState before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary))))) originalToPlan
            0 survivorToPlan : IteratorOutcomeAgreement name key value world
              error keyEq
              (iteratorStageOutcome stage
                (projectEffectState @{nameEq} survivor))
              (iteratorStageOutcome stage
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState (worldState before)
                      (planTarget (completePlanResult
                        (selectedBoundaryPlan boundary)))))))
            survivorToPlan = iteratorOutcomeAgreementTransitive
              survivorToOriginal originalToPlanOutcomes
            0 survivorEtaEffects : projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState (worldState survivor) (registry survivor))) =
              projectEffectState @{nameEq} survivor
            survivorEtaEffects = cong (projectEffectState @{nameEq})
              (systemStateEta survivor)
            0 survivorDataTransport :
              iteratorStageOutcomeComponentData nameEq keyEq actor component
                view step rest (projectEffectState @{nameEq} survivor) =
              iteratorStageOutcomeComponentData nameEq keyEq actor component
                view step rest
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                (MkSystemState (worldState survivor) (registry survivor))))
            survivorDataTransport = cong
              (iteratorStageOutcomeComponentData nameEq keyEq actor component
                view step rest) (sym survivorEtaEffects)
            0 survivorStage : iteratorStageOutcome stage
              (projectEffectState @{nameEq} survivor) =
              iteratorStageOutcomeComponentData nameEq keyEq actor component
                view step rest
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState (worldState survivor) (registry survivor))))
            survivorStage = trans
              (stageData (projectEffectState @{nameEq} survivor))
              survivorDataTransport
            0 planStage : iteratorStageOutcome stage
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState (worldState before)
                    (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary)))))) =
              iteratorStageOutcomeComponentData nameEq keyEq actor component
                view step rest
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState (worldState before)
                      (planTarget (completePlanResult
                        (selectedBoundaryPlan boundary))))))
            planStage = stageData (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState (worldState before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary))))))
        in outcomeAgreementTransport survivorStage planStage
          survivorToPlan
