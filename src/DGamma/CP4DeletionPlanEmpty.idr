module DGamma.CP4DeletionPlanEmpty

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import Data.List.Elem
import Decidable.Equality

%default total

||| Constructive witness that an actor is the current carrier of one exact R
||| generation.  It is the finite complement of `ActorOutsideCurrentRegistered`.
public export
record CurrentRegisteredActor
  (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name) (actor : name) where
  constructor MkCurrentRegisteredActor
  currentRegisteredGeneration : RegistrationGeneration name
  0 currentRegisteredPresent : Elem
    (actor, currentRegisteredGeneration) live
  0 currentRegisteredMember : Elem currentRegisteredGeneration registered

0 decCurrentRegisteredActor :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) -> (actor : name) ->
  Dec (CurrentRegisteredActor registered live actor)
decCurrentRegisteredActor nameEq registered [] actor =
  No (\witness => case currentRegisteredPresent witness of
    Here impossible
    There later impossible)
decCurrentRegisteredActor nameEq registered
  ((current, generation) :: rest) actor
  with (decEq @{nameEq} actor current)
  decCurrentRegisteredActor nameEq registered
    ((current, generation) :: rest) current | Yes Refl
    with (isElem generation registered)
    decCurrentRegisteredActor nameEq registered
      ((current, generation) :: rest) current | Yes Refl | Yes member =
        Yes (MkCurrentRegisteredActor generation Here member)
    decCurrentRegisteredActor nameEq registered
      ((current, generation) :: rest) current | Yes Refl | No absent
      with (decCurrentRegisteredActor nameEq registered rest current)
      decCurrentRegisteredActor nameEq registered
        ((current, generation) :: rest) current | Yes Refl | No absent |
        Yes later = Yes (MkCurrentRegisteredActor
          (currentRegisteredGeneration later)
          (There (currentRegisteredPresent later))
          (currentRegisteredMember later))
      decCurrentRegisteredActor nameEq registered
        ((current, generation) :: rest) current | Yes Refl | No absent |
        No noLater = No (\(MkCurrentRegisteredActor observed present member) =>
          case present of
            Here => absent member
            There later => noLater
              (MkCurrentRegisteredActor observed later member))
  decCurrentRegisteredActor nameEq registered
    ((current, generation) :: rest) actor | No distinct
    with (decCurrentRegisteredActor nameEq registered rest actor)
    decCurrentRegisteredActor nameEq registered
      ((current, generation) :: rest) actor | No distinct | Yes later =
        Yes (MkCurrentRegisteredActor
          (currentRegisteredGeneration later)
          (There (currentRegisteredPresent later))
          (currentRegisteredMember later))
    decCurrentRegisteredActor nameEq registered
      ((current, generation) :: rest) actor | No distinct | No noLater =
        No (\(MkCurrentRegisteredActor observed present member) => case present of
          Here => distinct Refl
          There later => noLater (MkCurrentRegisteredActor observed later member))

0 noCurrentWitnessGivesOutside :
  Not (CurrentRegisteredActor registered live actor) ->
  ActorOutsideCurrentRegistered actor registered live
noCurrentWitnessGivesOutside noWitness selected generation present member same =
  noWitness (case same of
    Refl => MkCurrentRegisteredActor generation present member)

0 outsidePlanRejectsHead :
  {plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target} ->
  ActorOutsideDeletionPlan actor plan ->
  plan = DeleteInactiveLeaf actor component parent retiredFlag table outcome
    found noChild rest -> Void
outsidePlanRejectsHead outside Refl = case outside of
  ActorOutsideDeletionStep rest distinct tail => distinct Refl

0 nothingNotJustPlanEmpty : Nothing = Just item -> Void
nothingNotJustPlanEmpty Refl impossible

0 lookupDeleteSelfPlanEmpty :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed : name) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed
    (deleteBinding @{nameEq} removed source) = Nothing
lookupDeleteSelfPlanEmpty nameEq removed
  (MkCoeffectContext entries unique) =
    lookupNothingFromNotElem nameEq removed
      (deleteEntries @{nameEq} removed entries)
      (deletedKeyNotElem removed entries unique)
  where
  0 lookupNothingFromNotElem :
    (nameEq : DecEq name) -> (wanted : name) ->
    (entries : List (Binding name (FiberAt name key value world error))) ->
    Not (Elem wanted (bindingKeys entries)) ->
    lookupEntries @{nameEq} wanted entries = Nothing
  lookupNothingFromNotElem nameEq wanted [] absent = Refl
  lookupNothingFromNotElem nameEq wanted (Bind current fiber :: rest) absent
    with (decEq @{nameEq} wanted current)
    lookupNothingFromNotElem nameEq current
      (Bind current fiber :: rest) absent | Yes Refl = void (absent Here)
    lookupNothingFromNotElem nameEq wanted
      (Bind current fiber :: rest) absent | No distinct =
        lookupNothingFromNotElem nameEq wanted rest
          (\later => absent (There later))

0 emptyTablesAfterDelete :
  (nameEq : DecEq name) -> (removed : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (source : Registry name key value world error) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    (MkSystemState ambient source) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    (MkSystemState ambient (deleteBinding @{nameEq} removed source))
emptyTablesAfterDelete nameEq removed registered live source invariant selected
  generation member current fiber found
  with (decEq @{nameEq} selected removed)
  emptyTablesAfterDelete nameEq selected registered live source invariant selected
    generation member current fiber found | Yes Refl =
      void (nothingNotJustPlanEmpty
        (trans (sym (lookupDeleteSelfPlanEmpty nameEq selected source)) found))
  emptyTablesAfterDelete nameEq removed registered live source invariant selected
    generation member current fiber found | No distinct =
      let 0 sourceFound : (lookupFiber @{nameEq} selected source = Just fiber)
          sourceFound = trans
            (sym (lookupDeleteOther selected removed distinct source)) found
      in invariant selected generation member current fiber sourceFound

||| The plan's outside projection rules out any extra leaf: a head not carrying
||| a current R generation would be outside the whole plan and hence could not
||| be that head.  Therefore the public no-episode empty-table invariant supplies
||| every constructor of `EmptyTableInactivePlan` without strengthening the plan
||| record.
public export
0 currentRegisteredPlanHasEmptyTables :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (ambient : world) ->
  (source : Registry name key value world error) ->
  (planResult : CurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    (MkSystemState ambient source) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan planResult)
currentRegisteredPlanHasEmptyTables nameEq registered live unique ambient source
  (MkCurrentRegisteredPlanResult target plan outside) invariant =
    emptyPlan plan outside invariant
  where
  0 emptyPlan :
    {currentSource, currentTarget : Registry name key value world error} ->
    (currentPlan : InactiveLeafDeletionPlan {name = name} {key = key}
      {value = value} {world = world} {error = error} nameEq currentSource
      currentTarget) ->
    ((actor : name) -> ActorOutsideCurrentRegistered actor registered live ->
      ActorOutsideDeletionPlan actor currentPlan) ->
    CurrentRegisteredEmptyTables name key world error value nameEq registered live
      (MkSystemState ambient currentSource) ->
    EmptyTableInactivePlan name key world error value nameEq currentPlan
  emptyPlan NoInactiveLeafDeletion outside currentInvariant = EmptyTablePlanEnd
  emptyPlan
    plan@(DeleteInactiveLeaf removed component parent retiredFlag table
      outcome found noChild rest)
    outside currentInvariant =
      case decCurrentRegisteredActor nameEq registered live removed of
        No noWitness => void (outsidePlanRejectsHead
          (outside removed (noCurrentWitnessGivesOutside noWitness)) Refl)
        Yes (MkCurrentRegisteredActor generation present member) =>
          let 0 current : (lookupCurrentGeneration @{nameEq} removed live =
                Just generation)
              current = lookupCurrentGenerationFromElem nameEq live unique present
              0 tableEmpty : (bindings (ownedValues table) = [])
              tableEmpty = currentInvariant removed generation member current
                (MkFiber component parent retiredFlag table (Inactive outcome))
                found
              0 tailOutside : (actor : name) ->
                ActorOutsideCurrentRegistered actor registered live ->
                ActorOutsideDeletionPlan actor rest
              tailOutside actor actorOutside = case outside actor actorOutside of
                ActorOutsideDeletionStep rest headDistinct tail => tail
              0 deletedInvariant : CurrentRegisteredEmptyTables name key world
                error value nameEq registered live
                (MkSystemState ambient
                  (deleteBinding @{nameEq} removed currentSource))
              deletedInvariant = emptyTablesAfterDelete {ambient = ambient} nameEq
                removed registered live currentSource currentInvariant
              0 tailEmpty : EmptyTableInactivePlan name key world error value
                nameEq rest
              tailEmpty = emptyPlan rest tailOutside deletedInvariant
          in EmptyTablePlanStep tableEmpty tailEmpty

||| Complete-plan specialization used by selected and suffix replay boundaries.
public export
0 completeCurrentRegisteredPlanHasEmptyTables :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (ambient : world) ->
  (source : Registry name key value world error) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    (MkSystemState ambient source) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult plan))
completeCurrentRegisteredPlanHasEmptyTables nameEq registered live unique ambient
  source plan invariant = currentRegisteredPlanHasEmptyTables nameEq registered
    live unique ambient source (completePlanResult plan) invariant

||| Direct public-premise bridge: exact-generation no-episode evidence supplies
||| empty tables at the reached boundary, and the scanner supplies the unique
||| current-generation environment needed to identify every plan leaf.
public export
0 reachedCompletePlanHasEmptyTables :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (scan : GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered 0 [] trace ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered finalLive (registry finalState)) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult plan))
reachedCompletePlanHasEmptyTables nameEq keyEq registered trace finalOrdinal
  finalLive scan aligned noEpisodes plan =
    completeCurrentRegisteredPlanHasEmptyTables nameEq registered finalLive
      (generationTraceScanPreservesUnique nameEq scan UniqueNil)
      (worldState finalState) (registry finalState) plan
      (reachedCurrentRegisteredEmptyTables nameEq keyEq registered trace
        finalOrdinal finalLive scan aligned noEpisodes)
