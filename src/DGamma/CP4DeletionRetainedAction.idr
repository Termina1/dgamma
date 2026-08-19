module DGamma.CP4DeletionRetainedAction

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionControlOrchestration
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import Data.List.Elem
import Decidable.Equality

%default total

falseNotTrueRetained : False = True -> Void
falseNotTrueRetained Refl impossible

trueNotFalseRetained : True = False -> Void
trueNotFalseRetained Refl impossible

justInjectiveRetained : Just left = Just right -> left = right
justInjectiveRetained Refl = Refl

||| A successful fresh insertion is outside any plan rooted in its source
||| registry: every deleted leaf is present, while the inserted name is absent.
public export
0 absentActorOutsideDeletionPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Nothing ->
  ActorOutsideDeletionPlan actor plan
absentActorOutsideDeletionPlan nameEq actor source source
  NoInactiveLeafDeletion absent = ActorOutsideDeletionEnd
absentActorOutsideDeletionPlan {name} {key} {world} {error} {value}
  nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) absent =
    let 0 distinct : Not (actor = removed)
        distinct same = case same of
          Refl => nothingIsNotJust (trans (sym absent) found)
        0 tailAbsent : lookupFiber @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor
          (deleteBinding @{nameEq} removed source) = Nothing
        tailAbsent = trans (lookupDeleteOther actor removed distinct source) absent
    in ActorOutsideDeletionStep rest distinct
      (absentActorOutsideDeletionPlan nameEq actor
        (deleteBinding @{nameEq} removed source) target rest tailAbsent)

public export
0 successfulInsertAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (OInsert inserted parent component) before = Just (tag, afterState) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} inserted (registry before) = Nothing
successfulInsertAbsent {name} {key} {world} {error} {value}
  nameEq keyEq inserted parent component (MkSystemState ambient source)
  afterState tag raw
  with (parentPresent @{nameEq} parent source &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers source))
  successfulInsertAbsent nameEq keyEq inserted parent component
    (MkSystemState ambient source) afterState tag raw | False =
      void (nothingIsNotJust raw)
  successfulInsertAbsent nameEq keyEq inserted parent component
    (MkSystemState ambient source) afterState tag raw | True
    with (setFresh @{nameEq} inserted (freshFiber component parent) source)
      proof insertedResult
    successfulInsertAbsent nameEq keyEq inserted parent component
      (MkSystemState ambient source) afterState tag raw | True | Nothing =
        void (nothingIsNotJust raw)
    successfulInsertAbsent nameEq keyEq inserted parent component
      (MkSystemState ambient source) afterState tag raw | True | Just applied =
        setFreshAbsent nameEq inserted (freshFiber component parent) source
          applied insertedResult

0 reloadingAtInactiveFalse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected source =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  reloadingAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected
    (MkSystemState ambient source) = False
reloadingAtInactiveFalse nameEq selected ambient source component parent
  retiredFlag table outcome found = rewrite found in Refl

reloadingMaybe : Maybe (Fiber name key value world error) -> Bool
reloadingMaybe Nothing = False
reloadingMaybe (Just fiber) = case fiberLifecycle fiber of
  Reloading remaining accumulator view => True
  _ => False

0 reloadingAtAsMaybe :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  reloadingAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected (MkSystemState ambient source) =
  reloadingMaybe (lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} selected source)
reloadingAtAsMaybe nameEq selected ambient source
  with (lookupFiber @{nameEq} selected source)
  reloadingAtAsMaybe nameEq selected ambient source | Nothing = Refl
  reloadingAtAsMaybe nameEq selected ambient source | Just fiber
    with (fiberLifecycle fiber)
    reloadingAtAsMaybe nameEq selected ambient source | Just fiber |
      Inactive outcome = Refl
    reloadingAtAsMaybe nameEq selected ambient source | Just fiber |
      Reloading remaining accumulator view = Refl
    reloadingAtAsMaybe nameEq selected ambient source | Just fiber |
      Active accumulator view = Refl
    reloadingAtAsMaybe nameEq selected ambient source | Just fiber |
      Unloading accumulator view outcome = Refl

0 reloadingAtDeleteOther :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected, removed : name) ->
  Not (selected = removed) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  reloadingAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected
    (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
  reloadingAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected (MkSystemState ambient source)
reloadingAtDeleteOther {name} {key} {world} {error} {value}
  nameEq selected removed distinct ambient source =
    let targetEquation : (reloadingAt @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} selected
          (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
          reloadingMaybe (lookupFiber @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} selected
            (deleteBinding @{nameEq} removed source)))
        targetEquation = reloadingAtAsMaybe nameEq selected ambient
          (deleteBinding @{nameEq} removed source)
        sourceEquation : (reloadingAt @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} selected
          (MkSystemState ambient source) =
          reloadingMaybe (lookupFiber @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} selected source))
        sourceEquation = reloadingAtAsMaybe nameEq selected ambient source
    in trans targetEquation (trans
      (cong reloadingMaybe
        (lookupDeleteOther selected removed distinct source))
      (sym sourceEquation))

||| A Reloading actor cannot be one of the Inactive leaves erased by a plan.
||| This is the parent-side fact needed by retained child O-Insert.
public export
0 reloadingActorOutsideDeletionPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (actor : name) -> (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  reloadingAt @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (MkSystemState ambient source) = True ->
  ActorOutsideDeletionPlan actor plan
reloadingActorOutsideDeletionPlan nameEq actor ambient source source
  NoInactiveLeafDeletion reloading = ActorOutsideDeletionEnd
reloadingActorOutsideDeletionPlan {name} {key} {world} {error} {value}
  nameEq actor ambient source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) reloading =
    let 0 distinct : Not (actor = removed)
        distinct same = case same of
          Refl => falseNotTrueRetained (trans
            (sym (reloadingAtInactiveFalse nameEq removed ambient source component
              parent retiredFlag table outcome found)) reloading)
        0 tailReloading : reloadingAt @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor
          (MkSystemState ambient (deleteBinding @{nameEq} removed source)) = True
        tailReloading = trans
          (reloadingAtDeleteOther nameEq actor removed distinct ambient source)
          reloading
    in ActorOutsideDeletionStep rest distinct
      (reloadingActorOutsideDeletionPlan nameEq actor ambient
        (deleteBinding @{nameEq} removed source) target rest tailReloading)

0 yieldReloading :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (parent : name) ->
  (component : Component key value world error) ->
  (before : SystemState name key value world error) ->
  ParentRegistrationYield protocol nameEq parent component before ->
  reloadingAt @{nameEq} parent before = True
yieldReloading protocol nameEq parent component before yielded =
  rewrite parentFoundAtYield yielded in
  rewrite parentAtYield yielded in Refl

0 rootInsertOrchestrationOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {component : Component key value world error} ->
  (inserted : name) ->
  {source, target : Registry name key value world error} ->
  (plan : InactiveLeafDeletionPlan nameEq source target) ->
  ActorOutsideDeletionPlan inserted plan ->
  OrchestrationOutsideDeletionPlan
    (the (Action name key value world error)
      (OInsert inserted Root component)) plan
rootInsertOrchestrationOutside inserted NoInactiveLeafDeletion
  ActorOutsideDeletionEnd = OrchestrationOutsideDeletionEnd
rootInsertOrchestrationOutside inserted
  (DeleteInactiveLeaf removed leafComponent parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest ownerOutside ownerTail) =
    OrchestrationOutsideDeletionStep rest ownerOutside ()
      (rootInsertOrchestrationOutside inserted rest ownerTail)

0 childInsertOrchestrationOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {component : Component key value world error} ->
  (inserted, insertedParent : name) ->
  {source, target : Registry name key value world error} ->
  (plan : InactiveLeafDeletionPlan nameEq source target) ->
  ActorOutsideDeletionPlan inserted plan ->
  ActorOutsideDeletionPlan insertedParent plan ->
  OrchestrationOutsideDeletionPlan
    (the (Action name key value world error)
      (OInsert inserted (ChildOf insertedParent) component)) plan
childInsertOrchestrationOutside inserted insertedParent NoInactiveLeafDeletion
  ActorOutsideDeletionEnd ActorOutsideDeletionEnd =
    OrchestrationOutsideDeletionEnd
childInsertOrchestrationOutside inserted insertedParent
  (DeleteInactiveLeaf removed leafComponent parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest ownerOutside ownerTail) parentPlan =
    case parentPlan of
      ActorOutsideDeletionStep parentRest parentOutside parentTail =>
        OrchestrationOutsideDeletionStep rest ownerOutside parentOutside
          (childInsertOrchestrationOutside inserted insertedParent rest ownerTail
            parentTail)

0 retireOrchestrationOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  (selected : name) ->
  {source, target : Registry name key value world error} ->
  (plan : InactiveLeafDeletionPlan nameEq source target) ->
  ActorOutsideDeletionPlan selected plan ->
  OrchestrationOutsideDeletionPlan
    (the (Action name key value world error) (ORetire selected)) plan
retireOrchestrationOutside selected NoInactiveLeafDeletion
  ActorOutsideDeletionEnd = OrchestrationOutsideDeletionEnd
retireOrchestrationOutside selected
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest ownerOutside ownerTail) =
    OrchestrationOutsideDeletionStep rest ownerOutside ()
      (retireOrchestrationOutside selected rest ownerTail)

0 removeOrchestrationOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  (selected : name) ->
  {source, target : Registry name key value world error} ->
  (plan : InactiveLeafDeletionPlan nameEq source target) ->
  ActorOutsideDeletionPlan selected plan ->
  OrchestrationOutsideDeletionPlan
    (the (Action name key value world error) (ORemove selected)) plan
removeOrchestrationOutside selected NoInactiveLeafDeletion
  ActorOutsideDeletionEnd = OrchestrationOutsideDeletionEnd
removeOrchestrationOutside selected
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest ownerOutside ownerTail) =
    OrchestrationOutsideDeletionStep rest ownerOutside ()
      (removeOrchestrationOutside selected rest ownerTail)

public export
data NonInsertAction : Action name key value world error -> Type where
  NonInsertRetire : NonInsertAction (ORetire actor)
  NonInsertRemove : NonInsertAction (ORemove actor)
  NonInsertBegin : NonInsertAction (LBegin actor)
  NonInsertAdvance : NonInsertAction (LAdvance actor)
  NonInsertDivert : NonInsertAction (LDivert actor)
  NonInsertLeave : NonInsertAction (LLeave actor)
  NonInsertUnload : NonInsertAction (LUnload actor)

||| The complement of generation ownership gives the strong per-environment
||| outside certificate for every non-insertion action.
public export
0 retainedNonInsertOutsideCurrentRegistered :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  NonInsertAction action ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) live -> Elem generation registered ->
  Not (actionOwner action = selected)
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (ORetire actor) NonInsertRetire notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (ORemove actor) NonInsertRemove notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (LBegin actor) NonInsertBegin notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (LAdvance actor) NonInsertAdvance notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (LDivert actor) NonInsertDivert notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (LLeave actor) NonInsertLeave notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))
retainedNonInsertOutsideCurrentRegistered nameEq registered ordinal live unique
  (LUnload actor) NonInsertUnload notOwned candidate generation present member same =
    case same of
      Refl => notOwned (generation **
        (lookupCurrentGenerationFromElem nameEq live unique present, member))

||| Build the complete plan-level certificate for any retained orchestration
||| action at an original boundary. Child insertion obtains parent exclusion
||| from its committed registration-yield provenance and the plan's Inactive
||| source leaves; no raw-name global exclusion is assumed.
public export
0 retainedOrchestrationOutsidePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action before =
    Just (tag, afterState) ->
  {finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  RegistrationStepDiscipline protocol nameEq action before rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  (planResult : CurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry before)) ->
  OrchestrationOutsideDeletionPlan action (inactiveLeafPlan planResult)
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (OInsert inserted Root component) orchestration before afterState tag raw
  rest discipline notOwned planResult =
    let 0 absent = successfulInsertAbsent nameEq keyEq inserted Root component
          before afterState tag raw
        0 ownerPlan = absentActorOutsideDeletionPlan nameEq inserted
          (registry before) (planTarget planResult)
          (inactiveLeafPlan planResult) absent
    in rootInsertOrchestrationOutside inserted (inactiveLeafPlan planResult)
      ownerPlan
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (OInsert inserted (ChildOf parent) component) orchestration
  before@(MkSystemState ambient source) afterState tag raw rest
  (yielded, retirement) notOwned planResult =
    let 0 absent = successfulInsertAbsent nameEq keyEq inserted (ChildOf parent)
          component before afterState tag raw
        0 ownerPlan = absentActorOutsideDeletionPlan nameEq inserted
          (registry before) (planTarget planResult)
          (inactiveLeafPlan planResult) absent
        0 parentPlan = reloadingActorOutsideDeletionPlan nameEq parent
          ambient source (planTarget planResult)
          (inactiveLeafPlan planResult)
          (yieldReloading protocol nameEq parent component before yielded)
    in childInsertOrchestrationOutside inserted parent
      (inactiveLeafPlan planResult) ownerPlan parentPlan
retainedOrchestrationOutsidePlan {name} {key} {world} {error} {value}
  protocol nameEq keyEq registered ordinal live unique (ORetire actor) orchestration before afterState tag raw rest discipline
  notOwned planResult =
    let 0 strongOutside = retainedNonInsertOutsideCurrentRegistered {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq registered
          ordinal live unique (ORetire actor) NonInsertRetire notOwned
        0 ownerPlan = actorOutsidePlan planResult actor strongOutside
    in retireOrchestrationOutside actor (inactiveLeafPlan planResult) ownerPlan
retainedOrchestrationOutsidePlan {name} {key} {world} {error} {value}
  protocol nameEq keyEq registered ordinal live unique (ORemove actor) orchestration before afterState tag raw rest discipline
  notOwned planResult =
    let 0 strongOutside = retainedNonInsertOutsideCurrentRegistered {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq registered
          ordinal live unique (ORemove actor) NonInsertRemove notOwned
        0 ownerPlan = actorOutsidePlan planResult actor strongOutside
    in removeOrchestrationOutside actor (inactiveLeafPlan planResult) ownerPlan
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (LBegin actor) orchestration before afterState tag raw rest discipline
  notOwned planResult = void (trueNotFalseRetained orchestration)
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (LAdvance actor) orchestration before afterState tag raw rest discipline
  notOwned planResult = void (trueNotFalseRetained orchestration)
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (LDivert actor) orchestration before afterState tag raw rest discipline
  notOwned planResult = void (trueNotFalseRetained orchestration)
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (LLeave actor) orchestration before afterState tag raw rest discipline
  notOwned planResult = void (trueNotFalseRetained orchestration)
retainedOrchestrationOutsidePlan protocol nameEq keyEq registered ordinal live
  unique (LUnload actor) orchestration before afterState tag raw rest discipline
  notOwned planResult = void (trueNotFalseRetained orchestration)

||| Retained suffix lifecycle actions automatically satisfy the generation-aware
||| outside premise consumed by the existing checked plan replay theorem.
public export
0 retainedLifecycleCurrentOutside :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  NonInsertAction action ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  CurrentGenerationOutside {nameEq = nameEq} registered live
    (actionOwner action)
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (ORetire actor) NonInsertRetire notOwned generation current member =
    notOwned (generation ** (current, member))
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (ORemove actor) NonInsertRemove notOwned generation current member =
    notOwned (generation ** (current, member))
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (LBegin actor) NonInsertBegin notOwned generation current member =
    notOwned (generation ** (current, member))
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (LAdvance actor) NonInsertAdvance notOwned generation current member =
    notOwned (generation ** (current, member))
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (LDivert actor) NonInsertDivert notOwned generation current member =
    notOwned (generation ** (current, member))
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (LLeave actor) NonInsertLeave notOwned generation current member =
    notOwned (generation ** (current, member))
retainedLifecycleCurrentOutside nameEq registered ordinal live
  (LUnload actor) NonInsertUnload notOwned generation current member =
    notOwned (generation ** (current, member))

||| Checked one-step replay for every retained orchestration action at an
||| original boundary with its current-R deletion plan.
public export
0 checkedRetainedOrchestrationAfterCurrentPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (planResult : CurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  {originalAfter : SystemState name key value world error} ->
  {tag : RuleTag} ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action
    (MkSystemState ambient source) = Just (tag, originalAfter)) ->
  {finalState : SystemState name key value world error} ->
  (rest : Transitions originalAfter finalState) ->
  RegistrationStepDiscipline protocol nameEq action
    (MkSystemState ambient source) rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState ambient source) = True ->
  TransitionResult {name = name} {key = key} {value = value} {world = world}
    {error = error} (MkSystemState ambient (planTarget planResult))
checkedRetainedOrchestrationAfterCurrentPlan protocol nameEq keyEq registered
  ordinal live unique action orchestration ambient source planResult checked rest
  discipline notOwned sourceWellFormed =
    let 0 raw = checkedActionProjects nameEq keyEq action
          (MkSystemState ambient source) _ _ checked
        0 outside = retainedOrchestrationOutsidePlan protocol nameEq keyEq
          registered ordinal live unique action orchestration
          (MkSystemState ambient source) _ _ raw rest discipline notOwned
          planResult
    in checkedOrchestrationAfterInactivePlan nameEq keyEq action orchestration
      ambient source (planTarget planResult) (inactiveLeafPlan planResult)
      outside sourceWellFormed checked

||| Checked one-step replay for every retained lifecycle action. The complement
||| of exact generation ownership supplies `CurrentGenerationOutside` directly;
||| scanner uniqueness then supplies the stronger plan certificate inside the
||| existing lifecycle theorem.
public export
0 checkedRetainedLifecycleAfterCurrentPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (nonInsert : NonInsertAction action) ->
  (lifecycle : isLifecycleAction action = True) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (planResult : CurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState ambient source) = True ->
  {tag : RuleTag} ->
  {originalAfter : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action
    (MkSystemState ambient source) = Just (tag, originalAfter) ->
  TransitionResult {name = name} {key = key} {value = value} {world = world}
    {error = error} (MkSystemState ambient (planTarget planResult))
checkedRetainedLifecycleAfterCurrentPlan nameEq keyEq registered ordinal live
  unique action nonInsert lifecycle ambient source planResult notOwned
  sourceWellFormed checked =
    checkedLifecycleAfterCurrentRegisteredPlan nameEq keyEq registered live unique
      ambient source planResult action lifecycle
      (retainedLifecycleCurrentOutside nameEq registered ordinal live action
        nonInsert notOwned)
      sourceWellFormed checked
