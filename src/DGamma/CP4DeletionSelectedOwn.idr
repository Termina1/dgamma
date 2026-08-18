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

0 fiberStaticFromEqualFields :
  (left, right : Fiber name key value world error) ->
  fiberComponent left = fiberComponent right ->
  fiberParent left = fiberParent right ->
  retired left = retired right ->
  FiberStaticRelated name key world error value left right
fiberStaticFromEqualFields
  (MkFiber leftComponent leftParent leftRetired leftTable leftLifecycle)
  (MkFiber rightComponent rightParent rightRetired rightTable rightLifecycle)
  componentSame parentSame retiredSame = case componentSame of
    Refl => FibersStaticRelated leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame

record SelectedReplacementPlanStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name) (actor : name)
  (source, target : Registry name key value world error)
  (oldPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live source)
  (sourceFiber, targetFiber : Fiber name key value world error) where
  constructor MkSelectedReplacementPlanStep
  selectedReplacementPlan : CompleteCurrentRegisteredPlanResult name key world
    error value nameEq registered live target
  0 selectedReplacementTargetBindings :
    bindings (planTarget (completePlanResult selectedReplacementPlan)) =
    replaceEntries @{nameEq} actor targetFiber
      (bindings (planTarget (completePlanResult oldPlan)))
  0 selectedReplacementStatic : FiberStaticRelated name key world error value
    targetFiber sourceFiber

0 registryReplacementPreservesPlanAndControls :
  (nameEq : DecEq name) -> (actor : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (source, target : Registry name key value world error) ->
  (oldPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live source) ->
  ActorOutsideDeletionPlan actor
    (inactiveLeafPlan (completePlanResult oldPlan)) ->
  (sourceFiber : Fiber name key value world error) ->
  (sourceFound : lookupFiber @{nameEq} actor source = Just sourceFiber) ->
  (targetFiber : Fiber name key value world error) ->
  (targetFound : lookupFiber @{nameEq} actor target = Just targetFiber) ->
  retired targetFiber = retired sourceFiber ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  SelectedReplacementPlanStep name key world error value nameEq registered live
    actor source target oldPlan sourceFiber targetFiber
registryReplacementPreservesPlanAndControls nameEq actor registered live source
  _ oldPlan outside sourceFiber sourceFound targetFiber targetFound
  retiredSame (LocalInsert inserted absent) =
    void (nothingIsNotJust (trans (sym absent) sourceFound))
registryReplacementPreservesPlanAndControls nameEq actor registered live source
  _
  oldPlan@(MkCompleteCurrentRegisteredPlanResult
    oldResult@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
    oldComplete)
  outside sourceFiber sourceFound targetFiber targetFound retiredSame
  (LocalReplace next {oldFiber} {oldFound} {staticComponent} {staticParent}) =
    let 0 oldIsSource : (oldFiber = sourceFiber)
        oldIsSource = justInjective (trans (sym oldFound) sourceFound)
        0 nextFound : (lookupFiber @{nameEq} actor
              (replaceBinding @{nameEq} actor next source) = Just next)
        nextFound = lookupReplacedFiber actor oldFiber next source oldFound
        0 nextIsTarget : (next = targetFiber)
        nextIsTarget = justInjective (trans (sym nextFound) targetFound)
    in case oldIsSource of
      Refl => case nextIsTarget of
        Refl => case replaceOutsideThroughInactivePlan nameEq actor sourceFiber
          targetFiber source oldTarget oldInactive outside sourceFound
          staticParent of
          MkInactivePlanPreservingUpdateCommute
            (MkInactivePlanUpdateCommute nextTarget nextInactive targetBindings
              nextOutside) actorsSame =>
                let nextResult : CurrentRegisteredPlanResult name key world error
                      value nameEq registered live
                      (replaceBinding @{nameEq} actor targetFiber source)
                    nextResult = MkCurrentRegisteredPlanResult nextTarget
                      nextInactive
                      (\observed, outsideCurrent => nextOutside observed
                        (oldOutside observed outsideCurrent))
                    0 nextComplete : CurrentRegisteredPlanComplete name key world
                      error value nameEq registered live nextResult
                    nextComplete observed generation present member =
                      replace {p = Elem observed} (sym actorsSame)
                        (oldComplete observed generation present member)
                    0 static : FiberStaticRelated name key world error value
                      targetFiber sourceFiber
                    static = fiberStaticFromEqualFields targetFiber sourceFiber
                      staticComponent staticParent retiredSame
                in MkSelectedReplacementPlanStep
                  (MkCompleteCurrentRegisteredPlanResult nextResult nextComplete)
                  targetBindings static
registryReplacementPreservesPlanAndControls nameEq actor registered live source
  _ oldPlan outside sourceFiber sourceFound targetFiber targetFound
  retiredSame (LocalDelete {oldFiber} {oldFound}) =
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
  retired (modelFiber (targetModel step)) =
    retired (modelFiber
      (selectedBoundaryModel (selectedBoundaryEffects boundary))) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole afterState survivor
skippedSelectedAccumulatorStepPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live stamped selectedOutside action tag before afterState
  checked whole survivor
  boundary@(MkSelectedEpisodeReplayBoundary
    boundaryEffects@(MkSelectedEffectReplayBoundary sourceModel
      boundaryRecovered boundaryRuns survivorToRecovered)
    boundaryComplete oldOrdered survivorCleanInactive beforeWellFormed
      survivorWellFormed)
  owner
  step@(MkSelectedAccumulatorStep nextModel sourceRecovered targetRecovered
    sourceRuns targetRuns recoveredRelated)
  retiredSame =
    let 0 nextEffects = selectedStepPreservesEffectReplayBoundary nameEq keyEq
          selected (Fired nameEq keyEq action tag checked) whole
          boundaryEffects step
        0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 update = applyActionLocalUpdate nameEq keyEq action before afterState
          tag raw
        0 selectedPlanOutside = selectedOutsideBoundaryPlan selected registered
          live stamped selectedOutside boundaryComplete
        0 outsideAtOwner : ActorOutsideDeletionPlan (actionOwner action)
          (inactiveLeafPlan (completePlanResult boundaryComplete))
        outsideAtOwner = replace
          {p = \observed => ActorOutsideDeletionPlan observed
            (inactiveLeafPlan (completePlanResult boundaryComplete))}
          (sym owner) selectedPlanOutside
        0 sourceFoundAtOwner : lookupFiber @{nameEq} (actionOwner action)
              (registry before) = Just (modelFiber sourceModel)
        sourceFoundAtOwner = replace
          {p = \observed => lookupFiber @{nameEq} observed (registry before) =
            Just (modelFiber sourceModel)}
          (sym owner) (modelFound sourceModel)
        0 targetFoundAtOwner : lookupFiber @{nameEq} (actionOwner action)
              (registry afterState) = Just (modelFiber nextModel)
        targetFoundAtOwner = replace
          {p = \observed => lookupFiber @{nameEq} observed
            (registry afterState) = Just (modelFiber nextModel)}
          (sym owner) (modelFound nextModel)
    in case registryReplacementPreservesPlanAndControls nameEq
      (actionOwner action) registered live (registry before)
      (registry afterState) boundaryComplete outsideAtOwner
      (modelFiber sourceModel)
      sourceFoundAtOwner (modelFiber nextModel) targetFoundAtOwner retiredSame
      (systemRegistryUpdate update) of
      MkSelectedReplacementPlanStep nextComplete targetBindings targetStatic =>
        let 0 planSourceFound : (lookupFiber @{nameEq} selected
              (planTarget (completePlanResult boundaryComplete)) =
                Just (modelFiber sourceModel))
            planSourceFound = trans
              (lookupOutsideInactivePlan nameEq selected (registry before)
                (planTarget (completePlanResult boundaryComplete))
                (inactiveLeafPlan (completePlanResult boundaryComplete))
                selectedPlanOutside)
              (modelFound sourceModel)
            0 planEntriesFound : (lookupEntries @{nameEq} selected
                  (bindings (planTarget (completePlanResult boundaryComplete))) =
                Just (modelFiber sourceModel))
            planEntriesFound = trans
              (sym (lookupFiberAsEntries nameEq selected
                (planTarget (completePlanResult boundaryComplete))))
              planSourceFound
            0 replacedSelected : SelectedOrderedRegistryControlsRelated name key
              world error value selected
              (replaceEntries @{nameEq} selected (modelFiber nextModel)
                (bindings (planTarget (completePlanResult boundaryComplete))))
              (bindings (registry survivor))
            replacedSelected = selectedOrderedReplaceSelectedLeft nameEq
              selected (modelFiber sourceModel) (modelFiber nextModel)
              (bindings (planTarget (completePlanResult boundaryComplete)))
              (bindings (registry survivor))
              planEntriesFound targetStatic
              oldOrdered
            0 ownerEntries : replaceEntries @{nameEq} (actionOwner action)
                  (modelFiber nextModel)
                  (bindings (planTarget (completePlanResult boundaryComplete))) =
                replaceEntries @{nameEq} selected (modelFiber nextModel)
                  (bindings (planTarget (completePlanResult boundaryComplete)))
            ownerEntries = cong
              (\observed => replaceEntries @{nameEq} observed
                (modelFiber nextModel)
                (bindings (planTarget (completePlanResult boundaryComplete))))
                owner
            0 replacedOwner : SelectedOrderedRegistryControlsRelated name key
              world error value selected
              (replaceEntries @{nameEq} (actionOwner action)
                (modelFiber nextModel)
                (bindings (planTarget (completePlanResult boundaryComplete))))
              (bindings (registry survivor))
            replacedOwner = replace
              {p = \entries => SelectedOrderedRegistryControlsRelated name key
                world error value selected entries
                (bindings (registry survivor))}
              (sym ownerEntries) replacedSelected
            0 nextOrdered : SelectedOrderedRegistryControlsRelated name key world
              error value selected
              (bindings (planTarget (completePlanResult nextComplete)))
              (bindings (registry survivor))
            nextOrdered = replace
              {p = \entries => SelectedOrderedRegistryControlsRelated name key
                world error value selected entries
                (bindings (registry survivor))}
              (sym targetBindings) replacedOwner
        in skippedSelectedStepPreservesEpisodeBoundary nameEq keyEq selected
          registered ordinal live action tag before afterState checked whole
          survivor boundary owner nextEffects nextComplete nextOrdered
