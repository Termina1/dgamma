module DGamma.CP4DeletionSelectedDeletedOrchestration

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanCommute
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionRetainedAction
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedDeletedCore
import DGamma.CP4DeletionSelectedDeletedPlan
import Data.List.Elem
import Decidable.Equality

%default total

0 nothingNotJustDeletedOrchestration : Nothing = Just item -> Void
nothingNotJustDeletedOrchestration Refl impossible

0 noChildFromRemoveGuard :
  (retiredFlag, inactiveFlag, childPresent : Bool) ->
  retiredFlag && inactiveFlag && not childPresent = True ->
  childPresent = False
noChildFromRemoveGuard retiredFlag inactiveFlag False valid = Refl
noChildFromRemoveGuard False inactiveFlag True valid = case valid of Refl impossible
noChildFromRemoveGuard True False True valid = case valid of Refl impossible
noChildFromRemoveGuard True True True valid = case valid of Refl impossible

record RetireSourceView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (source : Registry name key value world error) where
  constructor MkRetireSourceView
  retireSourceFiber : Fiber name key value world error
  0 retireSourceFound : lookupFiber @{nameEq} actor source =
    Just retireSourceFiber

0 retireSourceView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORetire actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  RetireSourceView name key world error value nameEq actor source
retireSourceView nameEq keyEq actor ambient source tag afterState raw
  with (lookupFiber @{nameEq} actor source) proof found
  retireSourceView nameEq keyEq actor ambient source tag afterState raw |
    Nothing = void (nothingNotJustDeletedOrchestration raw)
  retireSourceView nameEq keyEq actor ambient source tag afterState raw |
    Just fiber = MkRetireSourceView fiber found

record RemoveSourceView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (source : Registry name key value world error) where
  constructor MkRemoveSourceView
  removeSourceFiber : Fiber name key value world error
  0 removeSourceFound : lookupFiber @{nameEq} actor source =
    Just removeSourceFiber
  0 removeSourceGuard : retired removeSourceFiber &&
    isInactive (fiberLifecycle removeSourceFiber) &&
    not (hasChild @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor source) = True
  0 removeSourceNoChild : hasChild @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} actor source = False

0 removeSourceView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORemove actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  RemoveSourceView name key world error value nameEq actor source
removeSourceView nameEq keyEq actor ambient source tag afterState raw
  with (lookupFiber @{nameEq} actor source) proof found
  removeSourceView nameEq keyEq actor ambient source tag afterState raw |
    Nothing = void (nothingNotJustDeletedOrchestration raw)
  removeSourceView nameEq keyEq actor ambient source tag afterState raw |
    Just fiber with (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChild @{nameEq} actor source)) proof removable
    removeSourceView nameEq keyEq actor ambient source tag afterState raw |
      Just fiber | False = void (nothingNotJustDeletedOrchestration raw)
    removeSourceView nameEq keyEq actor ambient source tag afterState raw |
      Just fiber | True = MkRemoveSourceView fiber found removable
        (noChildFromRemoveGuard (retired fiber)
          (isInactive (fiberLifecycle fiber)) (hasChild @{nameEq} actor source)
          removable)

record OrchestrationRuntimeObservation
  (name, key, world, error : Type) (value : key -> Type)
  (ambient : world)
  (canonical : Registry name key value world error)
  (afterState : SystemState name key value world error) where
  constructor MkOrchestrationRuntimeObservation
  0 orchestrationObservedWorld : worldState afterState = ambient
  0 orchestrationObservedBindings : bindings (registry afterState) =
    bindings canonical

0 retireRuntimeObservation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (oldFiber : Fiber name key value world error) ->
  (found : lookupFiber @{nameEq} actor source = Just oldFiber) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORetire actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  OrchestrationRuntimeObservation name key world error value ambient
    (replaceBinding @{nameEq} actor (retireFiber oldFiber) source) afterState
retireRuntimeObservation nameEq keyEq actor ambient source oldFiber found tag
  afterState raw =
    let canonical : SystemState name key value world error
        canonical = MkSystemState ambient
          (replaceBinding @{nameEq} actor (retireFiber oldFiber) source)
        0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (ORetire actor))
          (MkSystemState ambient source) = Just (ORetireTag,
            MkSystemState ambient
              (replaceBinding @{nameEq} actor (retireFiber oldFiber) source)))
        reduced = rewrite found in Refl
        0 samePair : ((ORetireTag, canonical) = (tag, afterState))
        samePair = justInjective (trans (sym reduced) raw)
    in MkOrchestrationRuntimeObservation
      (sym (cong (worldState . snd) samePair))
      (sym (cong (bindings . registry . snd) samePair))

0 removeRuntimeObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (oldFiber : Fiber name key value world error) ->
  (found : lookupFiber @{nameEq} actor source = Just oldFiber) ->
  (removable : retired oldFiber && isInactive (fiberLifecycle oldFiber) &&
    not (hasChild @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor source) = True) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORemove actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  OrchestrationRuntimeObservation name key world error value ambient
    (deleteBinding @{nameEq} actor source) afterState
removeRuntimeObservation nameEq keyEq actor ambient source oldFiber found removable
  tag afterState raw =
    let canonical : SystemState name key value world error
        canonical = MkSystemState ambient (deleteBinding @{nameEq} actor source)
        0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (ORemove actor))
          (MkSystemState ambient source) = Just (ORemoveTag,
            MkSystemState ambient (deleteBinding @{nameEq} actor source)))
        reduced = rewrite found in rewrite removable in Refl
        0 samePair : ((ORemoveTag, canonical) = (tag, afterState))
        samePair = justInjective (trans (sym reduced) raw)
    in MkOrchestrationRuntimeObservation
      (sym (cong (worldState . snd) samePair))
      (sym (cong (bindings . registry . snd) samePair))

0 orchestrationIsNotBegin :
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  IsBeginAction action -> Void
orchestrationIsNotBegin (OInsert actor parent component) Refl begin impossible
orchestrationIsNotBegin (ORetire actor) Refl begin impossible
orchestrationIsNotBegin (ORemove actor) Refl begin impossible
orchestrationIsNotBegin (LBegin actor) Refl begin impossible
orchestrationIsNotBegin (LAdvance actor) Refl begin impossible
orchestrationIsNotBegin (LDivert actor) Refl begin impossible
orchestrationIsNotBegin (LLeave actor) Refl begin impossible
orchestrationIsNotBegin (LUnload actor) Refl begin impossible

0 registeredActorDistinctFromSelected :
  (selected, actor : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (generation : RegistrationGeneration name) ->
  lookupCurrentGeneration @{nameEq} actor live = Just generation ->
  Elem generation registered ->
  Not (selected = actor)
registeredActorDistinctFromSelected selected actor registered live stamped
  selectedOutside generation current member same =
    let 0 present = currentGenerationEntryFromLookup nameEq actor generation live
          current
        0 generationActor : (generationName generation = actor)
        generationActor = stamped actor generation present
    in selectedOutside generation member (trans generationActor (sym same))

||| Result of deleting one R orchestration head while keeping the survivor fixed.
||| Empty-table evidence is returned with the boundary so the selected trace fold
||| can continue without strengthening the boundary record itself.
public export
record DeletedRegisteredEpisodeBoundaryStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  (action : Action name key value world error)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (afterState, survivor : SystemState name key value world error) where
  constructor MkDeletedRegisteredEpisodeBoundaryStep
  0 deletedRegisteredBoundary : SelectedEpisodeReplayBoundary name key world
    error value nameEq keyEq selected registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole afterState
    survivor
  0 deletedRegisteredEmptyTables : CurrentRegisteredEmptyTables name key world
    error value nameEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) afterState

||| A fresh R O-Insert is skipped.  The original creates an empty Inactive leaf,
||| the complete plan immediately erases it, and the survivor stays fixed.
public export
0 deletedRegisteredInsertPreservesEpisodeBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert inserted parent component) before = Just (tag, afterState)) ->
  {restFinal : SystemState name key value world error} ->
  (rest : Transitions afterState restFinal) ->
  RegistrationStepDiscipline protocol nameEq (OInsert inserted parent component)
    before rest ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error)
      (OInsert inserted parent component)) ->
  DeletedRegisteredEpisodeBoundaryStep name key world error value nameEq keyEq
    selected registered ordinal live (OInsert inserted parent component) whole
    afterState survivor
deletedRegisteredInsertPreservesEpisodeBoundary
  protocol nameEq keyEq selected registered ordinal live unique selectedOutside
  inserted parent component (MkSystemState ambient source) afterState tag checked
  rest discipline whole survivor boundary oldEmpty
  (generation ** (owned, member)) =
    let before : SystemState name key value world error
        before = MkSystemState ambient source
        0 raw : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error)
            (OInsert inserted parent component)) before = Just (tag, afterState))
        raw = checkedActionProjects nameEq keyEq
          (OInsert inserted parent component) before afterState tag checked
        0 freshSame : (MkRegistrationGeneration inserted ordinal = generation)
        freshSame = justInjective owned
    in case freshSame of
      Refl =>
        let 0 absent = successfulInsertAbsent nameEq keyEq inserted parent component
              before afterState tag raw
            0 parentNotSelf = ownerInsertionParentDifferent protocol nameEq keyEq
              inserted parent component before afterState tag raw discipline
            0 sourceNoChild = wellFormedAbsentHasNoChild nameEq keyEq inserted
              before (selectedOriginalWellFormed boundary) absent
            0 insertedNoChild = hasChildInsertFalse nameEq inserted inserted
              component parent source absent parentNotSelf sourceNoChild
        in case completePlanAfterDeletedInsert nameEq registered ordinal live
          unique inserted parent component source (selectedBoundaryPlan boundary)
          absent member insertedNoChild of
            (canonicalPlan ** canonicalTargetBindings) =>
              let canonicalSource : Registry name key value world error
                  canonicalSource = insertBinding @{nameEq} inserted
                    (freshFiber component parent) source absent
                  0 observation : InsertRuntimeObservation name key world error
                    value inserted component parent ambient source tag afterState
                  observation = insertRuntimeObservation nameEq keyEq inserted
                    parent component ambient source tag afterState raw
                  0 canonicalBindings : (bindings canonicalSource =
                    Bind inserted (freshFiber component parent) :: bindings source)
                  canonicalBindings = insertBindingRuntimeBindings nameEq inserted
                    (freshFiber component parent) source absent
                  0 sourcesSame : (bindings canonicalSource =
                    bindings (registry afterState))
                  sourcesSame = trans canonicalBindings
                    (sym (insertObservedBindings observation))
              in case transportCompletePlanAcrossBindings nameEq registered
                (putCurrentGeneration @{nameEq} inserted
                  (MkRegistrationGeneration inserted ordinal) live)
                canonicalSource (registry afterState) canonicalPlan sourcesSame of
                (nextPlan ** transportedTargetBindings) =>
                  let 0 targetBindings :
                        (bindings (planTarget (completePlanResult nextPlan)) =
                          bindings (planTarget (completePlanResult
                            (selectedBoundaryPlan boundary))))
                      targetBindings = trans transportedTargetBindings
                        canonicalTargetBindings
                      0 nextEmpty : EmptyTableInactivePlan name key world error
                        value nameEq (inactiveLeafPlan
                          (completePlanResult nextPlan))
                      nextEmpty = deletedStepGivesNextEmptyPlan nameEq keyEq
                        registered ordinal live unique
                        (the (Action name key value world error)
                          (OInsert inserted parent component)) before afterState
                        tag raw
                        (\begin, generated => orchestrationIsNotBegin
                          (the (Action name key value world error)
                            (OInsert inserted parent component)) Refl begin)
                        (selectedBoundaryPlan boundary) oldEmpty nextPlan
                      0 insertedNotSelected : Not (inserted = selected)
                      insertedNotSelected = selectedOutside
                        (MkRegistrationGeneration inserted ordinal) member
                      0 selectedDistinct : Not (selected = inserted)
                      selectedDistinct same = insertedNotSelected (sym same)
                      0 nextBoundary : SelectedEpisodeReplayBoundary name key
                        world error value nameEq keyEq selected registered
                        (S ordinal)
                        (advanceGenerationEnvironment @{nameEq} ordinal
                          (the (Action name key value world error)
                            (OInsert inserted parent component)) live)
                        whole afterState survivor
                      nextBoundary = deletedForeignStepPreservesSelectedBoundary
                        nameEq keyEq selected registered ordinal live
                        (the (Action name key value world error)
                          (OInsert inserted parent component)) tag before afterState
                        checked whole survivor boundary selectedDistinct
                        (insertObservedWorld observation) nextPlan targetBindings
                        oldEmpty nextEmpty
                      0 nextEmptyTables : CurrentRegisteredEmptyTables name key
                        world error value nameEq registered
                        (putCurrentGeneration @{nameEq} inserted
                          (MkRegistrationGeneration inserted ordinal) live)
                        afterState
                      nextEmptyTables =
                        completeEmptyPlanGivesCurrentRegisteredEmptyTables nameEq
                          registered
                          (putCurrentGeneration @{nameEq} inserted
                            (MkRegistrationGeneration inserted ordinal) live)
                          afterState nextPlan nextEmpty
                  in MkDeletedRegisteredEpisodeBoundaryStep nextBoundary
                    nextEmptyTables

||| Idempotent O-Retire of a current R leaf is skipped.  The plan updates that
||| leaf in place and still reaches the exact old target bindings.
public export
0 deletedRegisteredRetirePreservesEpisodeBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (tag, afterState)) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORetire actor)) ->
  DeletedRegisteredEpisodeBoundaryStep name key world error value nameEq keyEq
    selected registered ordinal live (ORetire actor) whole afterState survivor
deletedRegisteredRetirePreservesEpisodeBoundary
  nameEq keyEq selected registered ordinal live unique stamped selectedOutside
  actor (MkSystemState ambient source) afterState tag checked whole survivor
  boundary oldEmpty deleted@(generation ** (owned, member)) =
    let before : SystemState name key value world error
        before = MkSystemState ambient source
        0 raw : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (ORetire actor)) before =
            Just (tag, afterState))
        raw = checkedActionProjects nameEq keyEq (ORetire actor) before
          afterState tag checked
        0 oldComplete : CompleteCurrentRegisteredPlanResult name key world error
          value nameEq registered live source
        oldComplete = selectedBoundaryPlan boundary
        0 oldResult : CurrentRegisteredPlanResult name key world error value
          nameEq registered live source
        oldResult = completePlanResult oldComplete
        0 oldTarget : Registry name key value world error
        oldTarget = planTarget oldResult
        0 oldPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq source oldTarget
        oldPlan = inactiveLeafPlan oldResult
        0 currentEntry : Elem (actor, generation) live
        currentEntry = currentGenerationEntryFromLookup nameEq actor generation
          live owned
        0 planMember : Elem actor (inactivePlanActors oldPlan)
        planMember = currentPlanComplete oldComplete actor generation currentEntry
          member
        0 selectedDistinct : Not (selected = actor)
        selectedDistinct = registeredActorDistinctFromSelected selected actor
          registered live stamped selectedOutside generation owned member
    in case retireSourceView nameEq keyEq actor ambient source tag afterState raw of
      MkRetireSourceView oldFiber found =>
        let canonicalSource : Registry name key value world error
            canonicalSource = replaceBinding @{nameEq} actor
              (retireFiber oldFiber) source
            0 commuted : InactivePlanPreservingUpdateCommute name key world error
              value nameEq oldPlan canonicalSource (bindings oldTarget)
            commuted = retireExactActorInInactivePlan nameEq actor oldFiber
              source oldTarget oldPlan planMember found
            0 observation : OrchestrationRuntimeObservation name key world error
              value ambient canonicalSource afterState
            observation = retireRuntimeObservation nameEq keyEq actor ambient
              source oldFiber found tag afterState raw
        in case completePlanAfterPreservingReplacementWithBindings nameEq
          registered live oldComplete commuted of
          (canonicalPlan ** canonicalTargetBindings) =>
            case transportCompletePlanAcrossBindings nameEq registered live
              canonicalSource (registry afterState) canonicalPlan
              (sym (orchestrationObservedBindings observation)) of
              (nextPlan ** transportedTargetBindings) =>
                let 0 targetBindings :
                      (bindings (planTarget (completePlanResult nextPlan)) =
                        bindings oldTarget)
                    targetBindings = trans transportedTargetBindings
                      canonicalTargetBindings
                    0 nextEmpty : EmptyTableInactivePlan name key world error
                      value nameEq (inactiveLeafPlan
                        (completePlanResult nextPlan))
                    nextEmpty = deletedStepGivesNextEmptyPlan nameEq keyEq
                      registered ordinal live unique
                      (the (Action name key value world error) (ORetire actor))
                      before afterState tag raw
                      (\begin, generated => orchestrationIsNotBegin
                        (the (Action name key value world error) (ORetire actor))
                        Refl begin)
                      oldComplete oldEmpty nextPlan
                    0 nextBoundary : SelectedEpisodeReplayBoundary name key world
                      error value nameEq keyEq selected registered (S ordinal) live
                      whole afterState survivor
                    nextBoundary = deletedForeignStepPreservesSelectedBoundary
                      nameEq keyEq selected registered ordinal live
                      (the (Action name key value world error) (ORetire actor)) tag
                      before afterState checked whole survivor boundary
                      selectedDistinct (orchestrationObservedWorld observation)
                      nextPlan targetBindings oldEmpty nextEmpty
                    0 nextEmptyTables : CurrentRegisteredEmptyTables name key
                      world error value nameEq registered live afterState
                    nextEmptyTables =
                      completeEmptyPlanGivesCurrentRegisteredEmptyTables nameEq
                        registered live afterState nextPlan nextEmpty
                in MkDeletedRegisteredEpisodeBoundaryStep nextBoundary
                  nextEmptyTables

||| Exact R O-Remove is skipped because the survivor plan already omitted that
||| leaf.  Completeness is reindexed to the generation environment after removal.
public export
0 deletedRegisteredRemovePreservesEpisodeBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORemove actor) before =
    Just (tag, afterState)) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORemove actor)) ->
  DeletedRegisteredEpisodeBoundaryStep name key world error value nameEq keyEq
    selected registered ordinal live (ORemove actor) whole afterState survivor
deletedRegisteredRemovePreservesEpisodeBoundary
  nameEq keyEq selected registered ordinal live unique stamped selectedOutside
  actor (MkSystemState ambient source) afterState tag checked whole survivor
  boundary oldEmpty deleted@(generation ** (owned, member)) =
    let before : SystemState name key value world error
        before = MkSystemState ambient source
        0 raw : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (ORemove actor)) before =
            Just (tag, afterState))
        raw = checkedActionProjects nameEq keyEq (ORemove actor) before
          afterState tag checked
        0 oldComplete : CompleteCurrentRegisteredPlanResult name key world error
          value nameEq registered live source
        oldComplete = selectedBoundaryPlan boundary
        0 oldResult : CurrentRegisteredPlanResult name key world error value
          nameEq registered live source
        oldResult = completePlanResult oldComplete
        0 oldTarget : Registry name key value world error
        oldTarget = planTarget oldResult
        0 oldPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq source oldTarget
        oldPlan = inactiveLeafPlan oldResult
        0 currentEntry : Elem (actor, generation) live
        currentEntry = currentGenerationEntryFromLookup nameEq actor generation
          live owned
        0 planMember : Elem actor (inactivePlanActors oldPlan)
        planMember = currentPlanComplete oldComplete actor generation currentEntry
          member
        0 selectedDistinct : Not (selected = actor)
        selectedDistinct = registeredActorDistinctFromSelected selected actor
          registered live stamped selectedOutside generation owned member
    in case removeSourceView nameEq keyEq actor ambient source tag afterState raw of
      MkRemoveSourceView oldFiber found removable noChild =>
        let canonicalSource : Registry name key value world error
            canonicalSource = deleteBinding @{nameEq} actor source
            0 commuted : InactivePlanRemovingUpdateCommute name key world error
              value nameEq actor oldPlan canonicalSource (bindings oldTarget)
            commuted = removeExactActorFromInactivePlan nameEq actor source
              oldTarget oldPlan planMember noChild
            0 observation : OrchestrationRuntimeObservation name key world error
              value ambient canonicalSource afterState
            observation = removeRuntimeObservation nameEq keyEq actor ambient
              source oldFiber found removable tag afterState raw
        in case completePlanAfterDeletedRemoveWithBindings nameEq registered live
          unique actor oldComplete commuted of
          (canonicalPlan ** canonicalTargetBindings) =>
            case transportCompletePlanAcrossBindings nameEq registered
              (deleteCurrentGeneration @{nameEq} actor live) canonicalSource
              (registry afterState) canonicalPlan
              (sym (orchestrationObservedBindings observation)) of
              (nextPlan ** transportedTargetBindings) =>
                let 0 targetBindings :
                      (bindings (planTarget (completePlanResult nextPlan)) =
                        bindings oldTarget)
                    targetBindings = trans transportedTargetBindings
                      canonicalTargetBindings
                    0 nextEmpty : EmptyTableInactivePlan name key world error
                      value nameEq (inactiveLeafPlan
                        (completePlanResult nextPlan))
                    nextEmpty = deletedStepGivesNextEmptyPlan nameEq keyEq
                      registered ordinal live unique
                      (the (Action name key value world error) (ORemove actor))
                      before afterState tag raw
                      (\begin, generated => orchestrationIsNotBegin
                        (the (Action name key value world error) (ORemove actor))
                        Refl begin)
                      oldComplete oldEmpty nextPlan
                    0 nextBoundary : SelectedEpisodeReplayBoundary name key world
                      error value nameEq keyEq selected registered (S ordinal)
                      (deleteCurrentGeneration @{nameEq} actor live) whole
                      afterState survivor
                    nextBoundary = deletedForeignStepPreservesSelectedBoundary
                      nameEq keyEq selected registered ordinal live
                      (the (Action name key value world error) (ORemove actor)) tag
                      before afterState checked whole survivor boundary
                      selectedDistinct (orchestrationObservedWorld observation)
                      nextPlan targetBindings oldEmpty nextEmpty
                    0 nextEmptyTables : CurrentRegisteredEmptyTables name key
                      world error value nameEq registered
                      (deleteCurrentGeneration @{nameEq} actor live) afterState
                    nextEmptyTables =
                      completeEmptyPlanGivesCurrentRegisteredEmptyTables nameEq
                        registered (deleteCurrentGeneration @{nameEq} actor live)
                        afterState nextPlan nextEmpty
                in MkDeletedRegisteredEpisodeBoundaryStep nextBoundary
                  nextEmptyTables
