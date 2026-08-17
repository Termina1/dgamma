module DGamma.CP4DeletionControlUnload

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionControlBegin
import Decidable.Equality

%default total

0 nothingNotJust : Nothing = Just item -> Void
nothingNotJust Refl impossible

||| L-Unload's only global control guard is `not relied`. An Inactive deleted
||| entry contributes no reliance edge, so the guard and accumulator execution
||| remain available at the replay source.
public export
0 unloadApplicableAfterInactiveDelete :
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
  applyAction @{nameEq} @{keyEq} (LUnload actor)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LUnload actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq actor removed distinct ambient fibers removedComponent
  removedParent removedRetired removedTable removedOutcome removedFound raw
  with (lookupFiber @{nameEq} actor fibers) proof actorFound
  unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Nothing = void (nothingNotJust raw)
  unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Inactive outcome = void (nothingNotJust raw)
    unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Reloading remaining accumulator view =
        void (nothingNotJust raw)
    unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Active accumulator view = void (nothingNotJust raw)
    unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Unloading accumulator view outcome
      with (relied @{nameEq} actor fibers) proof sourceRelied
      unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Unloading accumulator view outcome | True =
          void (nothingNotJust raw)
      unloadApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Unloading accumulator view outcome | False =
          let replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayRelied = trans
                (reliedInactiveDelete nameEq actor removed removedComponent
                  removedParent removedRetired removedTable removedOutcome fibers
                  removedFound) sourceRelied
              restored = accumulator
                (MkLocalState ambient
                  (restrictOwnedPreservingOrder @{keyEq}
                    (componentProvisions (fiberComponent actorFiber))
                    (ownedValues (fiberTable actorFiber))))
          in MkRawActionResult LUnloadTag
            (MkSystemState
              (localWorld (accumulator
                (MkLocalState ambient
                  (restrictOwnedPreservingOrder @{keyEq}
                    (componentProvisions (fiberComponent actorFiber))
                    (ownedValues (fiberTable actorFiber))))))
              (replaceBinding @{nameEq} actor
                (setFiberRuntime actorFiber
                  (localTable (accumulator
                    (MkLocalState ambient
                      (restrictOwnedPreservingOrder @{keyEq}
                        (componentProvisions (fiberComponent actorFiber))
                        (ownedValues (fiberTable actorFiber))))))
                  (Inactive outcome))
                (deleteBinding @{nameEq} removed fibers)))
            (rewrite replayFound in rewrite actorLife in rewrite replayRelied in
              Refl)
