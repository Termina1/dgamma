module DGamma.CP4DeletionSelectedForeignLifecycleReplay

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4DeletionSelectedForeignAdvanceAgreement
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignLifecycleDispatch
import DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import DGamma.CP4DeletionSelectedForeignLifecycleStep
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedForeignTables
import DGamma.CP4RecoveryTrace
import Data.List.Elem
import Decidable.Equality

%default total

0 systemStateEta : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
systemStateEta (MkSystemState ambient fibers) = Refl

0 lifecycleControlTransportBefore :
  leftBefore = rightBefore ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq selected
    action tag planAfter leftBefore ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq selected
    action tag planAfter rightBefore
lifecycleControlTransportBefore Refl replay = replay

||| Full retained foreign lifecycle head at the selected quotient.  Trace
||| classification supplies only the occurrence-local provider evidence; all
||| owner lookup, table agreement, Equation-55 outcomes, concrete control replay,
||| and effect-frame joining are assembled here.
public export
0 retainedForeignLifecyclePreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (distinct : Not (actionOwner action = selected)) ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  TraceIndependent name key world error value keyEq whole ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  (selectedOutsidePlan : ActorOutsideDeletionPlan selected
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (ownerOutsidePlan : ActorOutsideDeletionPlan (actionOwner action)
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary)))) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) action tag
    afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) ->
  ((leftSelected, leftOwner, rightOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftOwner ->
    lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
      Just rightOwner ->
    FiberControlRelated leftOwner rightOwner ->
    ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
      global selected (actionOwner action)
      (MkSystemState (worldState before)
        (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
      leftSelected leftOwner) ->
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
retainedForeignLifecyclePreservesEpisodeBoundary
  {name} {key} {world} {error} {value}
  nameEq keyEq selected registered ordinal live action lifecycle distinct global
  noDependent whole before afterState survivor tag checked occurs independent
  boundary emptyPlan selectedOutsidePlan ownerOutsidePlan exactStep evidence =
    let planRaw = namedFireProjectsRaw nameEq keyEq action (MkSystemState (worldState before) (planTarget (completePlanResult (selectedBoundaryPlan boundary)))) (retainedBoundaryNamed exactStep)
          (retainedBoundaryFires exactStep)
        (leftOwner ** leftFound) = lifecycleOwnerPresent nameEq keyEq action
          lifecycle (MkSystemState (worldState before) (planTarget (completePlanResult (selectedBoundaryPlan boundary)))) (namedAfter (retainedBoundaryNamed exactStep)) (namedTag (retainedBoundaryNamed exactStep)) planRaw
        ownerLookup = lookupOutsideInactivePlan nameEq (actionOwner action)
          (registry before) (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
          (inactiveLeafPlan (completePlanResult
            (selectedBoundaryPlan boundary))) ownerOutsidePlan
        0 originalFound : (lookupFiber @{nameEq} (actionOwner action)
          (registry before) = Just leftOwner)
        originalFound = trans (sym ownerLookup) leftFound
        0 maybeControls : FiberControlMaybeRelated
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} (actionOwner action) (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} (actionOwner action)
            (registry survivor))
        maybeControls = selectedOrderedForeignLookupControls nameEq selected
          (actionOwner action) distinct (planTarget (completePlanResult (selectedBoundaryPlan boundary))) (registry survivor)
          (selectedBoundaryOrderedControls boundary)
    in case foreignControlLookupFound nameEq (actionOwner action) (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
      (registry survivor) leftOwner leftFound maybeControls of
      MkForeignRelatedFiberFound rightOwner rightFound ownersRelated =>
        let 0 selectedModel : AccumulatorModel name key world error value
              nameEq keyEq selected whole before
            selectedModel = selectedBoundaryModel
              (selectedBoundaryEffects boundary)
            0 selectedLookup : lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} selected
              (planTarget (completePlanResult
                (selectedBoundaryPlan boundary))) =
              lookupFiber @{nameEq} selected (registry before)
            selectedLookup = lookupOutsideInactivePlan nameEq selected
              (registry before) (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
              (inactiveLeafPlan (completePlanResult
                (selectedBoundaryPlan boundary))) selectedOutsidePlan
            0 selectedFound : (lookupFiber @{nameEq} selected (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
              Just (modelFiber selectedModel))
            selectedFound = trans selectedLookup (modelFound selectedModel)
            0 providerEvidence : ForeignLifecycleProviderFrameEvidence name key
              world error value nameEq keyEq global selected
              (actionOwner action)
              (MkSystemState (worldState before)
                (planTarget (completePlanResult
                  (selectedBoundaryPlan boundary))))
              (modelFiber selectedModel) leftOwner
            providerEvidence = evidence (modelFiber selectedModel) leftOwner
              rightOwner selectedFound leftFound rightFound ownersRelated
            0 foreignTables : (current : name) ->
              Not (current = selected) ->
              {leftFiber, rightFiber : Fiber name key value world error} ->
              Elem (Bind current leftFiber)
                (bindings (planTarget (completePlanResult
                  (selectedBoundaryPlan boundary)))) ->
              Elem (Bind current rightFiber) (bindings (registry survivor)) ->
              FiberControlRelated leftFiber rightFiber ->
              bindings (ownedValues (fiberTable leftFiber)) =
                bindings (ownedValues (fiberTable rightFiber))
            foreignTables = selectedBoundaryForeignLocatedTablesSame nameEq
              keyEq selected boundary
            0 outcomes : ForeignAdvanceOutcomeProvider name key world error value
              nameEq keyEq action (worldState before) (worldState survivor)
              (planTarget (completePlanResult (selectedBoundaryPlan boundary))) (registry survivor)
            outcomes = lifecycleOutcomes action leftOwner originalFound
              ownerLookup Refl
            0 cleanEta : SelectedSurvivorCleanInactive name key world error
              value nameEq selected
              (MkSystemState (worldState survivor) (registry survivor))
            cleanEta = replace
              {p = \observed => SelectedSurvivorCleanInactive name key world error
                value nameEq selected observed}
              (sym (systemStateEta survivor))
              (selectedBoundarySurvivorCleanInactive boundary)
            0 controlEta : ForeignLifecycleControlReplay name key world error
              value nameEq keyEq selected action
              (namedTag (retainedBoundaryNamed exactStep))
              (namedAfter (retainedBoundaryNamed exactStep))
              (MkSystemState (worldState survivor) (registry survivor))
            controlEta = replayForeignLifecycleControlsFromProviderEvidence nameEq
              keyEq selected action distinct lifecycle global noDependent
              (worldState before) (worldState survivor) (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
              (registry survivor) leftOwner rightOwner (modelFiber selectedModel) selectedFound
              leftFound rightFound providerEvidence cleanEta
              (selectedBoundaryOrderedControls boundary) foreignTables
              (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
              (selectedSurvivorWellFormed boundary) outcomes
            0 control : ForeignLifecycleControlReplay name key world error value
              nameEq keyEq selected action
              (namedTag (retainedBoundaryNamed exactStep))
              (namedAfter (retainedBoundaryNamed exactStep)) survivor
            control = lifecycleControlTransportBefore (systemStateEta survivor)
              controlEta
        in packageForeignLifecycleEpisodeStep nameEq keyEq selected registered
          ordinal live action lifecycle distinct whole before afterState survivor
          tag checked occurs independent boundary exactStep leftOwner rightOwner
          originalFound rightFound ownersRelated control
  where
  lifecycleOutcomes :
    (observed : Action name key value world error) ->
    (originalOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner observed) (registry before) =
      Just originalOwner ->
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner observed)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner observed) (registry before) ->
    observed = action ->
    ForeignAdvanceOutcomeProvider name key world error value nameEq keyEq
      observed (worldState before) (worldState survivor)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
      (registry survivor)
  lifecycleOutcomes (OInsert actor parent component) originalOwner originalFound
    ownerLookup same = ()
  lifecycleOutcomes (ORetire actor) originalOwner originalFound ownerLookup
    same = ()
  lifecycleOutcomes (ORemove actor) originalOwner originalFound ownerLookup
    same = ()
  lifecycleOutcomes (LBegin actor) originalOwner originalFound ownerLookup
    same = ()
  lifecycleOutcomes (LAdvance actor) originalOwner originalFound ownerLookup
    same = case same of
      Refl => selectedForeignAdvanceOutcomeProvider nameEq keyEq selected actor
        distinct whole independent before afterState survivor tag checked occurs
        boundary emptyPlan
        (\fiber, planFound => trans (sym ownerLookup) planFound)
  lifecycleOutcomes (LDivert actor) originalOwner originalFound ownerLookup
    same = ()
  lifecycleOutcomes (LLeave actor) originalOwner originalFound ownerLookup
    same = ()
  lifecycleOutcomes (LUnload actor) originalOwner originalFound ownerLookup
    same = ()
