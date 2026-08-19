module DGamma.CP4DeletionSelectedForeignLifecycleDispatch

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatch
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleDivert
import DGamma.CP4DeletionSelectedForeignLifecycleLeave
import DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import DGamma.CP4DeletionSelectedForeignLifecycleUnload
import Decidable.Equality

%default total

||| Exhaustive five-rule dispatcher after provider/guard saturation.  The
||| repaired outcome callback is demanded only by L-Advance; all other rules
||| consume the same ordered guard frame directly.
public export
0 replayForeignLifecycleControlsFromFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (actionOwner action = selected) ->
  isLifecycleAction action = True ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (leftOwner, rightOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action) plan = Just leftOwner ->
  lookupFiber @{nameEq} (actionOwner action) survivor = Just rightOwner ->
  (frame : ForeignLifecycleGuardFrame name key world error value nameEq keyEq
    selected (actionOwner action) (dependencies
      (componentDependencies (fiberComponent leftOwner)))
    leftOwner rightOwner plan survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ((component : Component key value world error) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (step : StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component)) ->
    (rest : List (StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component))) ->
    (view : View name (dependencies (componentDependencies component))) ->
    IteratorOutcomeAgreement name key value world error keyEq
      (runtimeAdvanceOutcome nameEq keyEq (actionOwner action) component step
        rest view survivorAmbient rightTable survivor)
      (runtimeAdvanceOutcome nameEq keyEq (actionOwner action) component step
        rest view planAmbient leftTable plan)) ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected action tag planAfter (MkSystemState survivorAmbient survivor)
replayForeignLifecycleControlsFromFrame nameEq keyEq selected
  (OInsert actor parent component) distinct Refl planAmbient survivorAmbient plan
  survivor leftOwner rightOwner leftFound rightFound frame tag planAfter planRaw
  survivorWellFormed outcomes impossible
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (ORetire actor)
  distinct Refl planAmbient survivorAmbient plan survivor leftOwner rightOwner
  leftFound rightFound frame tag planAfter planRaw survivorWellFormed outcomes
  impossible
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (ORemove actor)
  distinct Refl planAmbient survivorAmbient plan survivor leftOwner rightOwner
  leftFound rightFound frame tag planAfter planRaw survivorWellFormed outcomes
  impossible
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (LBegin actor)
  distinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
  rightOwner leftFound rightFound frame tag planAfter planRaw survivorWellFormed
  outcomes = replayForeignBeginControls nameEq keyEq selected actor distinct
    planAmbient survivorAmbient plan survivor leftOwner rightOwner leftFound
    rightFound frame tag planAfter planRaw survivorWellFormed
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (LAdvance actor)
  distinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
  rightOwner leftFound rightFound frame tag planAfter planRaw survivorWellFormed
  outcomes = replayForeignAdvanceControlsFromOutcome nameEq keyEq selected actor
    distinct planAmbient survivorAmbient plan survivor leftOwner rightOwner
    leftFound rightFound frame tag planAfter planRaw survivorWellFormed outcomes
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (LDivert actor)
  distinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
  rightOwner leftFound rightFound frame tag planAfter planRaw survivorWellFormed
  outcomes = replayForeignDivertControls nameEq keyEq selected actor distinct
    planAmbient survivorAmbient plan survivor leftOwner rightOwner leftFound
    rightFound frame tag planAfter planRaw survivorWellFormed
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (LLeave actor)
  distinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
  rightOwner leftFound rightFound frame tag planAfter planRaw survivorWellFormed
  outcomes = replayForeignLeaveControls nameEq keyEq selected actor distinct
    planAmbient survivorAmbient plan survivor leftOwner rightOwner leftFound
    rightFound frame tag planAfter planRaw survivorWellFormed
replayForeignLifecycleControlsFromFrame nameEq keyEq selected (LUnload actor)
  distinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
  rightOwner leftFound rightFound frame tag planAfter planRaw survivorWellFormed
  outcomes = replayForeignUnloadControls nameEq keyEq selected actor distinct
    planAmbient survivorAmbient plan survivor leftOwner rightOwner leftFound
    rightFound frame tag planAfter planRaw survivorWellFormed

||| Provider-evidence join used by the selected-episode retained-head fold.  It
||| consumes either a closed/Lemma-70 precedence anchor or the selected-close
||| reliance anchor, saturates the ordered source relation, and immediately
||| dispatches the concrete checked lifecycle rule.  No extra theorem premise is
||| introduced: `ForeignLifecycleProviderFrameEvidence` is the occurrence-local
||| package reconstructed from the public trace premises.
public export
0 replayForeignLifecycleControlsFromProviderEvidence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (actionOwner action = selected) ->
  isLifecycleAction action = True ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq}
    selected global ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (leftOwner, rightOwner, leftSelected : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected plan = Just leftSelected ->
  lookupFiber @{nameEq} (actionOwner action) plan = Just leftOwner ->
  lookupFiber @{nameEq} (actionOwner action) survivor = Just rightOwner ->
  ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
    global selected (actionOwner action) (MkSystemState planAmbient plan)
    leftSelected leftOwner ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    (MkSystemState survivorAmbient survivor) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ((component : Component key value world error) ->
    (leftTable, rightTable : OwnedTable key value
      (componentProvisions component)) ->
    (step : StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component)) ->
    (rest : List (StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component))) ->
    (view : View name (dependencies (componentDependencies component))) ->
    IteratorOutcomeAgreement name key value world error keyEq
      (runtimeAdvanceOutcome nameEq keyEq (actionOwner action) component step
        rest view survivorAmbient rightTable survivor)
      (runtimeAdvanceOutcome nameEq keyEq (actionOwner action) component step
        rest view planAmbient leftTable plan)) ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected action tag planAfter (MkSystemState survivorAmbient survivor)
replayForeignLifecycleControlsFromProviderEvidence nameEq keyEq selected action
  actorDistinct lifecycle global noDependent planAmbient survivorAmbient plan
  survivor leftOwner rightOwner leftSelected selectedFound leftFound rightFound
  evidence cleanInactive ordered foreignTables tag planAfter planRaw
  survivorWellFormed outcomes =
    let 0 frame = foreignLifecycleGuardFrameFromEvidence nameEq keyEq selected
          (actionOwner action) actorDistinct global noDependent planAmbient
          leftOwner rightOwner leftSelected plan survivor selectedFound leftFound
          rightFound evidence cleanInactive ordered foreignTables
    in replayForeignLifecycleControlsFromFrame nameEq keyEq selected action
      actorDistinct lifecycle planAmbient survivorAmbient plan survivor leftOwner
      rightOwner leftFound rightFound frame tag planAfter planRaw
      survivorWellFormed outcomes
