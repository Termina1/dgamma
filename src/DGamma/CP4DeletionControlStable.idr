module DGamma.CP4DeletionControlStable

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionControlBegin
import Decidable.Equality

%default total

0 nothingNotJust : Nothing = Just item -> Void
nothingNotJust Refl impossible

public export
0 divertApplicableAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, removed : name) -> Not (actor = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (removedComponent : Component key value world error) ->
  (removedParent : Parent name) -> (removedRetired : Bool) ->
  (removedTable : OwnedTable key value
    (componentProvisions removedComponent)) ->
  (removedOutcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed fibers = Just
    (MkFiber removedComponent removedParent removedRetired removedTable
      (Inactive removedOutcome)) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} (LDivert actor)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LDivert actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq actor removed distinct ambient fibers removedComponent
  removedParent removedRetired removedTable removedOutcome removedFound raw
  with (lookupFiber @{nameEq} actor fibers) proof actorFound
  divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Nothing = void (nothingNotJust raw)
  divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Inactive outcome = void (nothingNotJust raw)
    divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} actorFiber fibers) view) proof matches
      divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Reloading remaining accumulator view | True =
          void (nothingNotJust raw)
      divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Reloading remaining accumulator view | False =
          let replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome fibers removedFound
          in MkRawActionResult LDivertTag
            (MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle actorFiber
                  (Unloading accumulator view Nothing))
                (deleteBinding @{nameEq} removed fibers)))
            (rewrite replayFound in rewrite actorLife in rewrite replayTarget in
              rewrite matches in Refl)
    divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Active accumulator view = void (nothingNotJust raw)
    divertApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Unloading accumulator view outcome = void (nothingNotJust raw)

public export
0 leaveApplicableAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, removed : name) -> Not (actor = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (removedComponent : Component key value world error) ->
  (removedParent : Parent name) -> (removedRetired : Bool) ->
  (removedTable : OwnedTable key value
    (componentProvisions removedComponent)) ->
  (removedOutcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed fibers = Just
    (MkFiber removedComponent removedParent removedRetired removedTable
      (Inactive removedOutcome)) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} (LLeave actor)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LLeave actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq actor removed distinct ambient fibers removedComponent
  removedParent removedRetired removedTable removedOutcome removedFound raw
  with (lookupFiber @{nameEq} actor fibers) proof actorFound
  leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Nothing = void (nothingNotJust raw)
  leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Inactive outcome = void (nothingNotJust raw)
    leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Reloading remaining accumulator view =
        void (nothingNotJust raw)
    leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} actorFiber fibers) view) proof matches
      leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Active accumulator view | True =
          void (nothingNotJust raw)
      leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Active accumulator view | False =
          let replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome fibers removedFound
          in MkRawActionResult LLeaveTag
            (MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle actorFiber
                  (Unloading accumulator view Nothing))
                (deleteBinding @{nameEq} removed fibers)))
            (rewrite replayFound in rewrite actorLife in rewrite replayTarget in
              rewrite matches in Refl)
    leaveApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Unloading accumulator view outcome = void (nothingNotJust raw)
