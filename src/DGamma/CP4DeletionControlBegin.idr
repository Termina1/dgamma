module DGamma.CP4DeletionControlBegin

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4DeletionControlCore
import Decidable.Equality

%default total

public export
record RawActionResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (before : SystemState name key value world error) where
  constructor MkRawActionResult
  rawResultTag : RuleTag
  rawResultAfter : SystemState name key value world error
  0 rawResultEquation : applyAction @{nameEq} @{keyEq} action before =
    Just (rawResultTag, rawResultAfter)

0 nothingNotJust : Nothing = Just item -> Void
nothingNotJust Refl impossible

||| L-Begin's lifecycle and target guards remain applicable when a distinct
||| Inactive entry is erased. The replay endpoint is produced constructively by
||| the executable evaluator.
public export
0 beginApplicableAfterInactiveDelete :
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
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (LBegin actor)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (LBegin actor))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq actor removed distinct ambient fibers removedComponent
  removedParent removedRetired removedTable removedOutcome removedFound raw
  with (lookupFiber @{nameEq} actor fibers) proof actorFound
  beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Nothing = void (nothingNotJust raw)
  beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
    nameEq keyEq actor removed distinct ambient fibers removedComponent
    removedParent removedRetired removedTable removedOutcome removedFound raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Inactive Nothing
      with (targetFiber @{nameEq} @{keyEq} actorFiber fibers) proof target
      beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Inactive Nothing | Nothing =
          void (nothingNotJust raw)
      beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
        nameEq keyEq actor removed distinct ambient fibers removedComponent
        removedParent removedRetired removedTable removedOutcome removedFound raw |
        Just actorFiber | Inactive Nothing | Just view =
          let replayFound = trans
                (lookupDeleteOther actor removed distinct fibers) actorFound
              replayTarget = trans
                (targetFiberInactiveDelete nameEq keyEq actorFiber removed
                  removedComponent removedParent removedRetired removedTable
                  removedOutcome fibers removedFound) target
          in MkRawActionResult LBeginTag
            (MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle actorFiber
                  (Reloading
                    (componentProgram (fiberComponent actorFiber)) id view))
                (deleteBinding @{nameEq} removed fibers)))
            (rewrite replayFound in rewrite actorLife in
              rewrite replayTarget in Refl)
    beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Inactive (Just failure) = void (nothingNotJust raw)
    beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Reloading remaining accumulator view =
        void (nothingNotJust raw)
    beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Active accumulator view = void (nothingNotJust raw)
    beginApplicableAfterInactiveDelete {name} {key} {world} {error} {value}
      nameEq keyEq actor removed distinct ambient fibers removedComponent
      removedParent removedRetired removedTable removedOutcome removedFound raw |
      Just actorFiber | Unloading accumulator view outcome =
        void (nothingNotJust raw)
