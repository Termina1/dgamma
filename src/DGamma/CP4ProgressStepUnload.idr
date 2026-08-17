module DGamma.CP4ProgressStepUnload

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressPotential
import DGamma.CP4ProgressStepCore
import Data.Nat
import Decidable.Equality

%default total

||| L-Unload spends the final recovery step. A clean recovery moves from the
||| `K + 3` unload budget to at most `K + 2`; a failed recovery moves from one
||| to zero. Both conclusions are independent of the target-stability premise.
public export
0 unloadActorPotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload actor) before =
    Just (tag, afterState) ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    before afterState
unloadActorPotentialStep nameEq keyEq bound actor
  (MkSystemState ambient fibers) afterState tag raw
  with (lookupFiber @{nameEq} actor fibers) proof found
  unloadActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag raw | Nothing =
      void (nothingIsNotJust raw)
  unloadActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag raw |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    unloadActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    unloadActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view = void (nothingIsNotJust raw)
    unloadActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    unloadActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome with
      (relied @{nameEq} actor fibers) proof reliance
      unloadActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Unloading accumulator view outcome | True =
              void (nothingIsNotJust raw)
      unloadActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Unloading accumulator view outcome | False with (outcome)
        unloadActorPotentialStep nameEq keyEq bound actor
          (MkSystemState ambient fibers) afterState tag raw |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Unloading accumulator view outcome | False | Nothing =
          let sourceFiber : Fiber name key value world error
              sourceFiber = MkFiber component parent retiredFlag table
                (Unloading accumulator view Nothing)
              restored : LocalState key value world
                (componentProvisions component)
              restored = accumulator (MkLocalState ambient table)
              newTable : OwnedTable key value (componentProvisions component)
              newTable = localTable restored
              next : Fiber name key value world error
              next = setFiberRuntime sourceFiber newTable (Inactive Nothing)
              0 nextFound :
                (lookupFiber @{nameEq} actor
                  (replaceBinding @{nameEq} actor next fibers) = Just next)
              nextFound = lookupReplacedFiber actor sourceFiber next fibers found
              0 nextShape : next = MkFiber component parent retiredFlag newTable
                (Inactive Nothing)
              nextShape = Refl
              0 targetShape :
                (the (SystemState name key value world error)
                  (MkSystemState (localWorld restored)
                    (replaceBinding @{nameEq} actor next fibers))) =
                (the (SystemState name key value world error)
                  (MkSystemState (localWorld restored)
                    (replaceBinding @{nameEq} actor
                      (setFiberRuntime sourceFiber newTable (Inactive Nothing))
                      fibers)))
              targetShape = Refl
              0 rawReduced :
                Just (LUnloadTag,
                  the (SystemState name key value world error)
                    (MkSystemState (localWorld restored)
                      (replaceBinding @{nameEq} actor
                        (setFiberRuntime sourceFiber newTable (Inactive Nothing))
                        fibers))) = Just (tag, afterState)
              rawReduced = raw
              0 runtimeAfter :
                (the (SystemState name key value world error)
                  (MkSystemState (localWorld restored)
                    (replaceBinding @{nameEq} actor
                      (setFiberRuntime sourceFiber newTable (Inactive Nothing))
                      fibers))) = afterState
              runtimeAfter = cong snd (justInjective rawReduced)
              0 sourcePotentialExact :
                actorTargetPotential @{nameEq} @{keyEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  bound actor (MkSystemState ambient fibers) = bound + 3
              sourcePotentialExact = trans
                (actorTargetPotentialAtLookup nameEq keyEq bound actor
                  (MkSystemState ambient fibers) sourceFiber found)
                (unloadingCleanPotential
                  {target = targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    (MkSystemState ambient fibers)}
                  nameEq bound component parent retiredFlag table accumulator view)
              0 targetState : SystemState name key value world error
              targetState = MkSystemState (localWorld restored)
                (replaceBinding @{nameEq} actor next fibers)
              0 afterPotentialShape :
                actorTargetPotential @{nameEq} @{keyEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  bound actor targetState =
                fiberTargetPotential @{nameEq} bound
                  (MkFiber component parent retiredFlag newTable (Inactive Nothing))
                  (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState)
              afterPotentialShape = trans
                (actorTargetPotentialAtLookup nameEq keyEq bound actor targetState
                  next nextFound)
                (cong (\fiber => fiberTargetPotential @{nameEq} bound fiber
                  (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState)) nextShape)
              0 sourcePositive : LTE 1
                (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} bound actor
                  (MkSystemState ambient fibers))
              sourcePositive = rewrite sourcePotentialExact in
                oneLTEBoundPlusThree bound
              0 stayedDrop :
                sameTarget @{nameEq}
                  (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    (MkSystemState ambient fibers))
                  (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState) = True ->
                LTE (S (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} bound actor
                  targetState))
                  (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} bound actor
                    (MkSystemState ambient fibers))
              stayedDrop stayed = rewrite afterPotentialShape in
                rewrite sourcePotentialExact in
                  inactiveCleanAfterUnload nameEq bound component parent
                    retiredFlag newTable
                    (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState)
          in replace
            {p = \state => ActorPotentialStep name key world error value nameEq
              keyEq bound actor (MkSystemState ambient fibers) state}
            (trans targetShape runtimeAfter)
            (MkActorPotentialStep sourcePositive stayedDrop)
        unloadActorPotentialStep nameEq keyEq bound actor
          (MkSystemState ambient fibers) afterState tag raw |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Unloading accumulator view outcome | False | Just err =
          let sourceFiber : Fiber name key value world error
              sourceFiber = MkFiber component parent retiredFlag table
                (Unloading accumulator view (Just err))
              restored : LocalState key value world
                (componentProvisions component)
              restored = accumulator (MkLocalState ambient table)
              newTable : OwnedTable key value (componentProvisions component)
              newTable = localTable restored
              next : Fiber name key value world error
              next = setFiberRuntime sourceFiber newTable (Inactive (Just err))
              0 nextFound :
                (lookupFiber @{nameEq} actor
                  (replaceBinding @{nameEq} actor next fibers) = Just next)
              nextFound = lookupReplacedFiber actor sourceFiber next fibers found
              0 nextShape : next = MkFiber component parent retiredFlag newTable
                (Inactive (Just err))
              nextShape = Refl
              0 targetState : SystemState name key value world error
              targetState = MkSystemState (localWorld restored)
                (replaceBinding @{nameEq} actor next fibers)
              0 targetShape :
                (the (SystemState name key value world error) targetState) =
                (the (SystemState name key value world error)
                  (MkSystemState (localWorld restored)
                    (replaceBinding @{nameEq} actor
                      (setFiberRuntime sourceFiber newTable (Inactive (Just err)))
                      fibers)))
              targetShape = Refl
              0 rawReduced :
                Just (LUnloadTag,
                  the (SystemState name key value world error)
                    (MkSystemState (localWorld restored)
                      (replaceBinding @{nameEq} actor
                        (setFiberRuntime sourceFiber newTable (Inactive (Just err)))
                        fibers))) = Just (tag, afterState)
              rawReduced = raw
              0 runtimeAfter :
                (the (SystemState name key value world error)
                  (MkSystemState (localWorld restored)
                    (replaceBinding @{nameEq} actor
                      (setFiberRuntime sourceFiber newTable (Inactive (Just err)))
                      fibers))) = afterState
              runtimeAfter = cong snd (justInjective rawReduced)
              0 sourcePotentialExact :
                actorTargetPotential @{nameEq} @{keyEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  bound actor (MkSystemState ambient fibers) = 1
              sourcePotentialExact = trans
                (actorTargetPotentialAtLookup nameEq keyEq bound actor
                  (MkSystemState ambient fibers) sourceFiber found)
                (unloadingFailedPotential
                  {target = targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    (MkSystemState ambient fibers)}
                  nameEq bound component parent retiredFlag table accumulator view err)
              0 afterPotentialExact :
                actorTargetPotential @{nameEq} @{keyEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  bound actor targetState = Z
              afterPotentialExact = trans
                (actorTargetPotentialAtLookup nameEq keyEq bound actor targetState
                  next nextFound)
                (trans
                  (cong (\fiber => fiberTargetPotential @{nameEq} bound fiber
                    (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState))
                    nextShape)
                  (inactiveFailedPotential
                    {target = targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState}
                    nameEq bound component parent retiredFlag newTable err))
              0 sourcePositive : LTE 1
                (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} bound actor
                  (MkSystemState ambient fibers))
              sourcePositive = rewrite sourcePotentialExact in lteRefl 1
              0 stayedDrop :
                sameTarget @{nameEq}
                  (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    (MkSystemState ambient fibers))
                  (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor targetState) = True ->
                LTE (S (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} bound actor
                  targetState))
                  (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} bound actor
                    (MkSystemState ambient fibers))
              stayedDrop stayed = rewrite afterPotentialExact in
                rewrite sourcePotentialExact in lteRefl 1
          in replace
            {p = \state => ActorPotentialStep name key world error value nameEq
              keyEq bound actor (MkSystemState ambient fibers) state}
            (trans targetShape runtimeAfter)
            (MkActorPotentialStep sourcePositive stayedDrop)
