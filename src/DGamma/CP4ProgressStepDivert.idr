module DGamma.CP4ProgressStepDivert

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressPotential
import DGamma.CP4ProgressStepCore
import Data.Nat
import Decidable.Equality

%default total

||| L-Divert is applicable exactly at a stale committed target. It moves the
||| actor from the `K + 4` stale budget to the `K + 3` clean-unload budget.
public export
0 divertActorPotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LDivert actor) before =
    Just (tag, afterState) ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    before afterState
divertActorPotentialStep nameEq keyEq bound actor
  (MkSystemState ambient fibers) afterState tag raw
  with (lookupFiber @{nameEq} actor fibers) proof found
  divertActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag raw | Nothing =
      void (nothingIsNotJust raw)
  divertActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag raw |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    divertActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    divertActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    divertActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust raw)
    divertActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view with
      (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading remaining accumulator view)) fibers) view) proof matches
      divertActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading remaining accumulator view | True =
              void (nothingIsNotJust raw)
      divertActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading remaining accumulator view | False =
        let sourceFiber : Fiber name key value world error
            sourceFiber = MkFiber component parent retiredFlag table
              (Reloading remaining accumulator view)
            next : Fiber name key value world error
            next = setFiberLifecycle sourceFiber
              (Unloading accumulator view Nothing)
            0 nextFound :
              (lookupFiber @{nameEq} actor
                (replaceBinding @{nameEq} actor next fibers) = Just next)
            nextFound = lookupReplacedFiber actor sourceFiber next fibers found
            0 nextShape : next = MkFiber component parent retiredFlag table
              (Unloading accumulator view Nothing)
            nextShape = setFiberLifecycleExact component parent retiredFlag table
              (Reloading remaining accumulator view)
              (Unloading accumulator view Nothing)
            0 runtimeNextShape : next = setFiberLifecycle sourceFiber
              (Unloading accumulator view Nothing)
            runtimeNextShape = Refl
            0 targetShape :
              (the (SystemState name key value world error)
                (MkSystemState ambient
                  (replaceBinding @{nameEq} actor next fibers))) =
              (the (SystemState name key value world error)
                (MkSystemState ambient
                  (replaceBinding @{nameEq} actor
                    (setFiberLifecycle sourceFiber
                      (Unloading accumulator view Nothing)) fibers)))
            targetShape = cong (MkSystemState ambient)
              (cong (\fiber => replaceBinding @{nameEq} actor fiber fibers)
                runtimeNextShape)
            0 rawReduced :
              Just (LDivertTag,
                the (SystemState name key value world error)
                  (MkSystemState ambient
                    (replaceBinding @{nameEq} actor
                      (setFiberLifecycle sourceFiber
                        (Unloading accumulator view Nothing)) fibers))) =
              Just (tag, afterState)
            rawReduced = raw
            0 runtimeAfter :
              (the (SystemState name key value world error)
                (MkSystemState ambient
                  (replaceBinding @{nameEq} actor
                    (setFiberLifecycle sourceFiber
                      (Unloading accumulator view Nothing)) fibers))) = afterState
            runtimeAfter = cong snd (justInjective rawReduced)
            0 sourceNames : Maybe (List name)
            sourceNames = map (\v => DGamma.Calculus.viewProviders v)
              (targetFiber @{nameEq} @{keyEq} sourceFiber fibers)
            0 sourceTarget : targetProvidersAt @{nameEq} @{keyEq}
              {name = name} {key = key} {value = value} {world = world}
              {error = error} actor (MkSystemState ambient fibers) = sourceNames
            sourceTarget = targetProvidersAtLookup nameEq keyEq actor
              (MkSystemState ambient fibers) sourceFiber found
            0 namesStale : sameTarget @{nameEq} sourceNames
              (Just (viewProviders view)) = False
            namesStale = trans
              (sym (targetMatchesSameTarget nameEq
                (targetFiber @{nameEq} @{keyEq} sourceFiber fibers) view)) matches
            0 sourcePotentialExact :
              actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} bound actor
                (MkSystemState ambient fibers) = bound + 4
            sourcePotentialExact = trans
              (actorTargetPotentialAtLookup nameEq keyEq bound actor
                (MkSystemState ambient fibers) sourceFiber found)
              (trans
                (cong (fiberTargetPotential @{nameEq} bound sourceFiber)
                  sourceTarget)
                (reloadingStalePotential nameEq bound component parent
                  retiredFlag table remaining accumulator view sourceNames
                  namesStale))
            0 afterPotentialExact :
              actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} bound actor
                (MkSystemState ambient
                  (replaceBinding @{nameEq} actor next fibers)) = bound + 3
            afterPotentialExact = trans
              (actorTargetPotentialAtLookup nameEq keyEq bound actor
                (MkSystemState ambient
                  (replaceBinding @{nameEq} actor next fibers)) next nextFound)
              (trans
                (cong (\fiber => fiberTargetPotential @{nameEq} bound fiber
                  (targetProvidersAt @{nameEq} @{keyEq} actor
                    (MkSystemState ambient
                      (replaceBinding @{nameEq} actor next fibers)))) nextShape)
                (unloadingCleanPotential
                  {target = targetProvidersAt @{nameEq} @{keyEq} actor
                    (MkSystemState ambient
                      (replaceBinding @{nameEq} actor next fibers))}
                  nameEq bound component parent retiredFlag table accumulator view))
            0 sourcePositive : LTE 1
              (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} bound actor
                (MkSystemState ambient fibers))
            sourcePositive = rewrite sourcePotentialExact in
              oneLTEBoundPlusFour bound
            0 stayedDrop :
              sameTarget @{nameEq}
                (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor
                  (MkSystemState ambient fibers))
                (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor
                  (MkSystemState ambient
                    (replaceBinding @{nameEq} actor next fibers))) = True ->
              LTE (S (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} bound actor
                (MkSystemState ambient
                  (replaceBinding @{nameEq} actor next fibers))))
                (actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} bound actor
                  (MkSystemState ambient fibers))
            stayedDrop stayed = rewrite afterPotentialExact in
              rewrite sourcePotentialExact in boundPlusThreeStep bound
        in replace
          {p = \state => ActorPotentialStep name key world error value nameEq
            keyEq bound actor (MkSystemState ambient fibers) state}
          (trans targetShape runtimeAfter)
          (MkActorPotentialStep sourcePositive stayedDrop)
