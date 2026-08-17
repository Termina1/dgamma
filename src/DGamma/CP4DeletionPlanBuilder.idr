module DGamma.CP4DeletionPlanBuilder

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import Data.List.Elem
import Decidable.Equality

%default total

||| Strong pointwise form of “actor is outside every current R generation”. It
||| deliberately ranges over environment entries, so it remains sound even for
||| arbitrary duplicate environments; scanner uniqueness can later derive it
||| from `CurrentGenerationOutside`.
public export
ActorOutsideCurrentRegistered :
  {name : Type} -> (actor : name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name -> Type
ActorOutsideCurrentRegistered actor registered live =
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) live -> Elem generation registered ->
  Not (actor = selected)

||| Existential result of scanning the exact final generation environment.
||| Besides the projected Inactive-leaf plan it packages the actor-outside
||| projection needed by `checkedLifecycleAfterInactivePlan`.
public export
record CurrentRegisteredPlanResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name)
  (source : Registry name key value world error) where
  constructor MkCurrentRegisteredPlanResult
  planTarget : Registry name key value world error
  inactiveLeafPlan : InactiveLeafDeletionPlan
    {name = name} {key = key} {value = value} {world = world} {error = error}
    nameEq source planTarget
  0 actorOutsidePlan : (actor : name) ->
    ActorOutsideCurrentRegistered actor registered live ->
    ActorOutsideDeletionPlan
      {name = name} {key = key} {value = value} {world = world} {error = error}
      actor inactiveLeafPlan

||| Executable plan construction from the exact final generation environment
||| and runtime registry. Later raw-name reissues are skipped because their
||| generation is not in R; historical removed generations are absent from the
||| live environment. `Nothing` pinpoints a current R residue that is absent,
||| non-Inactive, or has a child.
public export
buildCurrentRegisteredDeletionPlan :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (source : Registry name key value world error) ->
  Maybe (CurrentRegisteredPlanResult name key world error value nameEq
    registered live source)
buildCurrentRegisteredDeletionPlan nameEq registered [] source =
  Just (MkCurrentRegisteredPlanResult source NoInactiveLeafDeletion
    (\actor, outside => ActorOutsideDeletionEnd))
buildCurrentRegisteredDeletionPlan nameEq registered
  ((selected, generation) :: rest) source with (isElem generation registered)
  buildCurrentRegisteredDeletionPlan nameEq registered
    ((selected, generation) :: rest) source | No absent =
      case buildCurrentRegisteredDeletionPlan nameEq registered rest source of
        Nothing => Nothing
        Just (MkCurrentRegisteredPlanResult target tailPlan tailOutside) =>
          let 0 outsideWhole : (actor : name) ->
                ActorOutsideCurrentRegistered actor registered
                  ((selected, generation) :: rest) ->
                ActorOutsideDeletionPlan actor tailPlan
              outsideWhole actor outside = tailOutside actor
                (\tailSelected, tailGeneration, present, member =>
                  outside tailSelected tailGeneration (There present) member)
          in Just (MkCurrentRegisteredPlanResult target tailPlan outsideWhole)
  buildCurrentRegisteredDeletionPlan nameEq registered
    ((selected, generation) :: rest) source | Yes member
    with (lookupFiber @{nameEq} selected source) proof present
    buildCurrentRegisteredDeletionPlan nameEq registered
      ((selected, generation) :: rest) source | Yes member | Nothing = Nothing
    buildCurrentRegisteredDeletionPlan nameEq registered
      ((selected, generation) :: rest) source | Yes member |
      Just (MkFiber component parent retiredFlag table lifecycle)
      with (fiberLifecycle
        (MkFiber component parent retiredFlag table lifecycle)) proof life
      buildCurrentRegisteredDeletionPlan nameEq registered
        ((selected, generation) :: rest) source | Yes member |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Inactive outcome with (hasChild @{nameEq} selected source) proof children
        buildCurrentRegisteredDeletionPlan nameEq registered
          ((selected, generation) :: rest) source | Yes member |
          Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome | False =
            case buildCurrentRegisteredDeletionPlan nameEq registered rest
              (deleteBinding @{nameEq} selected source) of
              Nothing => Nothing
              Just (MkCurrentRegisteredPlanResult target tailPlan tailOutside) =>
                let 0 outsideWhole : (actor : name) ->
                      ActorOutsideCurrentRegistered actor registered
                        ((selected, generation) :: rest) ->
                      ActorOutsideDeletionPlan actor
                        (DeleteInactiveLeaf {fibers = source} {target = target} selected
                          component parent retiredFlag table outcome present
                          children tailPlan)
                    outsideWhole actor outside =
                      ActorOutsideDeletionStep tailPlan
                        (outside selected generation Here member)
                        (tailOutside actor
                          (\tailSelected, tailGeneration, tailPresent, tailMember =>
                            outside tailSelected tailGeneration
                              (There tailPresent) tailMember))
                in Just (MkCurrentRegisteredPlanResult target
                  (DeleteInactiveLeaf {fibers = source} {target = target} selected
                    component parent retiredFlag table outcome present children
                    tailPlan)
                  outsideWhole)
        buildCurrentRegisteredDeletionPlan nameEq registered
          ((selected, generation) :: rest) source | Yes member |
          Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome | True = Nothing
      buildCurrentRegisteredDeletionPlan nameEq registered
        ((selected, generation) :: rest) source | Yes member |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading remaining accumulator view = Nothing
      buildCurrentRegisteredDeletionPlan nameEq registered
        ((selected, generation) :: rest) source | Yes member |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Active accumulator view = Nothing
      buildCurrentRegisteredDeletionPlan nameEq registered
        ((selected, generation) :: rest) source | Yes member |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Unloading accumulator view outcome = Nothing
