module DGamma.CP4DeletionSelectedOwn

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanCommute
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoverySelectedReplayStep
import DGamma.CP4RecoveryTrace
import Data.List.Elem
import Decidable.Equality

%default total

0 lookupNotElemNothing : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) -> lookupEntries wanted entries = Nothing
lookupNotElemNothing wanted [] absent = Refl
lookupNotElemNothing wanted (Bind current value :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothing current (Bind current value :: rest) absent | Yes Refl =
    void (absent Here)
  lookupNotElemNothing wanted (Bind current value :: rest) absent |
    No distinct = lookupNotElemNothing wanted rest
      (\later => absent (There later))

0 lookupDeleteSelf : DecEq key => (removed : key) ->
  (table : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed table) = Nothing
lookupDeleteSelf removed (MkCoeffectContext entries unique) =
  lookupNotElemNothing removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

0 registryReplacementPreservesCompletePlan :
  (nameEq : DecEq name) -> (actor : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (source, target : Registry name key value world error) ->
  (oldPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live source) ->
  ActorOutsideDeletionPlan actor
    (inactiveLeafPlan (completePlanResult oldPlan)) ->
  (sourceFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor source = Just sourceFiber ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor target = Just targetFiber ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live target
registryReplacementPreservesCompletePlan nameEq actor registered live source
  _ oldPlan outside sourceFiber sourceFound targetFiber targetFound
  (LocalInsert inserted absent) =
    void (nothingIsNotJust (trans (sym absent) sourceFound))
registryReplacementPreservesCompletePlan nameEq actor registered live source
  _ oldPlan outside sourceFiber sourceFound targetFiber targetFound
  (LocalReplace next {oldFiber} @{oldFound} @{staticComponent}
    @{staticParent}) =
      let 0 commuted = replaceOutsideThroughInactivePlan nameEq actor oldFiber
            next source (planTarget (completePlanResult oldPlan))
            (inactiveLeafPlan (completePlanResult oldPlan)) outside oldFound
            staticParent
      in completePlanAfterPreservingReplacement registered live oldPlan commuted
registryReplacementPreservesCompletePlan nameEq actor registered live source
  _ oldPlan outside sourceFiber sourceFound targetFiber targetFound
  (LocalDelete {oldFiber} @{oldFound}) =
    void (nothingIsNotJust (trans
      (sym (lookupDeleteSelf actor source)) targetFound))

||| Scanner stamp coherence turns the public generation-name exclusion into the
||| strong pointwise condition expected by the executable deletion plan.
public export
0 selectedOutsideCurrentRegistered :
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  ActorOutsideCurrentRegistered selected registered live
selectedOutsideCurrentRegistered selected registered live stamped
  selectedOutside actor generation present member same =
    selectedOutside generation member
      (trans (stamped actor generation present) (sym same))

||| The selected fiber is consequently outside every leaf of the complete
||| current-R plan at an intermediate episode boundary.
public export
0 selectedOutsideBoundaryPlan :
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  ActorOutsideDeletionPlan selected
    (inactiveLeafPlan (completePlanResult plan))
selectedOutsideBoundaryPlan selected registered live stamped selectedOutside
  plan = actorOutsidePlan (completePlanResult plan) selected
    (selectedOutsideCurrentRegistered selected registered live stamped
      selectedOutside)

0 selectedReplacementPreservesCompletePlan :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  actionOwner action = selected ->
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) ->
  (targetModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole afterState) ->
  (oldPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live (registry before)) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry afterState)
selectedReplacementPreservesCompletePlan
  {name} {key} {world} {error} {value}
  nameEq keyEq selected registered live stamped selectedOutside action tag before
  afterState checked owner sourceModel targetModel oldPlan =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 update = applyActionLocalUpdate nameEq keyEq action before afterState
          tag raw
        0 selectedPlanOutside = selectedOutsideBoundaryPlan selected registered
          live stamped selectedOutside oldPlan
        0 outside : ActorOutsideDeletionPlan (actionOwner action)
          (inactiveLeafPlan (completePlanResult oldPlan))
        outside = replace
          {p = \observed => ActorOutsideDeletionPlan observed
            (inactiveLeafPlan (completePlanResult oldPlan))}
          (sym owner) selectedPlanOutside
        0 sourceFoundAtOwner : lookupFiber @{nameEq} (actionOwner action)
              (registry before) = Just (modelFiber sourceModel)
        sourceFoundAtOwner = replace
          {p = \observed => lookupFiber @{nameEq} observed (registry before) =
            Just (modelFiber sourceModel)}
          (sym owner) (modelFound sourceModel)
        0 targetFoundAtOwner : lookupFiber @{nameEq} (actionOwner action)
              (registry afterState) = Just (modelFiber targetModel)
        targetFoundAtOwner = replace
          {p = \observed => lookupFiber @{nameEq} observed
            (registry afterState) = Just (modelFiber targetModel)}
          (sym owner) (modelFound targetModel)
    in registryReplacementPreservesCompletePlan nameEq (actionOwner action)
      registered live (registry before) (registry afterState) oldPlan outside
      (modelFiber sourceModel) sourceFoundAtOwner (modelFiber targetModel)
      targetFoundAtOwner (systemRegistryUpdate update)

||| Complete selected-owner quotient step.  The selected accumulator theorem
||| supplies the effect cancellation, scanner coherence transports the exact-R
||| plan through the checked replacement, and the shared boundary lemma keeps
||| every foreign control unchanged while the survivor skips the action.
public export
0 skippedSelectedAccumulatorStepPreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  actionOwner action = selected ->
  (step : SelectedAccumulatorStep name key world error value nameEq keyEq
    selected (Fired nameEq keyEq action tag checked) whole
      (selectedBoundaryModel (selectedBoundaryEffects boundary))) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole afterState survivor
skippedSelectedAccumulatorStepPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live stamped selectedOutside action tag before afterState
  checked whole survivor boundary owner step =
    let 0 nextEffects = selectedStepPreservesEffectReplayBoundary nameEq keyEq
          selected (Fired nameEq keyEq action tag checked) whole
          (selectedBoundaryEffects boundary) step
        0 nextPlan = selectedReplacementPreservesCompletePlan nameEq keyEq
          selected registered live stamped selectedOutside action tag before
          afterState checked owner (selectedBoundaryModel
            (selectedBoundaryEffects boundary)) (targetModel step)
          (selectedBoundaryPlan boundary)
    in skippedSelectedStepPreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live action tag before afterState checked whole survivor
      boundary owner nextEffects nextPlan
