module DGamma.CP4ProgressStepBegin

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressBound
import DGamma.CP4ProgressPotential
import DGamma.CP4ProgressStepCore
import Data.Nat
import Decidable.Equality

%default total

||| L-Begin consumes one same-target potential unit after charging the bounded
||| declared iterator. The direct evaluator split also proves source positivity.
public export
0 beginActorPotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState) ->
  programsBoundedBy bound before = True ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    before afterState
beginActorPotentialStep nameEq keyEq bound actor
  (MkSystemState ambient fibers) afterState tag checked programs
  with (lookupFiber @{nameEq} actor fibers) proof found
  beginActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag checked programs |
      Nothing = void (nothingIsNotJust checked)
  beginActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag checked programs |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    beginActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag checked programs |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive Nothing with
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table (Inactive Nothing)) fibers)
          proof targetFound
      beginActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag checked programs |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Inactive Nothing | Nothing =
              void (nothingIsNotJust checked)
      beginActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag checked programs |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Inactive Nothing | Just view =
              let sourceFiber : Fiber name key value world error
                  sourceFiber = MkFiber component parent retiredFlag table
                    (Inactive Nothing)
                  next : Fiber name key value world error
                  next = setFiberLifecycle sourceFiber
                    (Reloading (componentProgram component) (\local => local) view)
                  0 nextFound :
                    (lookupFiber @{nameEq} actor
                      (replaceBinding @{nameEq} actor next fibers) = Just next)
                  nextFound = lookupReplacedFiber actor
                    (MkFiber component parent retiredFlag table (Inactive Nothing))
                    next fibers found
                  0 sourceTarget : targetProvidersAt @{nameEq} @{keyEq}
                    {name = name} {key = key} {value = value} {world = world}
                    {error = error} actor (MkSystemState ambient fibers) =
                      Just (viewProviders view)
                  sourceTarget = trans
                    (targetProvidersAtLookup nameEq keyEq actor
                      (MkSystemState ambient fibers)
                      (MkFiber component parent retiredFlag table
                        (Inactive Nothing)) found)
                    (cong (map (\v => DGamma.Calculus.viewProviders v))
                      targetFound)
                  0 boundedProgram : length (componentProgram component) <=
                    bound = True
                  boundedProgram = selectedProgramBounded nameEq bound
                    (MkSystemState ambient fibers)
                    programs actor
                      (MkFiber component parent retiredFlag table
                        (Inactive Nothing)) found
                  0 nextShape : next = MkFiber component parent retiredFlag
                    table (Reloading (componentProgram component) (\local => local) view)
                  nextShape = setFiberLifecycleExact component parent
                    retiredFlag table (Inactive Nothing)
                    (Reloading (componentProgram component)
                      (\local => local) view)
                  0 runtimeNextShape : next = setFiberLifecycle
                    (MkFiber component parent retiredFlag table
                      (Inactive Nothing))
                    (Reloading (componentProgram component)
                      (\local => local) view)
                  runtimeNextShape = trans nextShape
                    (sym (setFiberLifecycleExact component parent retiredFlag
                      table (Inactive Nothing)
                      (Reloading (componentProgram component)
                        (\local => local) view)))
                  0 targetShape :
                    (the (SystemState name key value world error)
                      (MkSystemState ambient
                        (replaceBinding @{nameEq} actor next fibers))) =
                    (the (SystemState name key value world error)
                      (MkSystemState ambient
                        (replaceBinding @{nameEq} actor
                          (setFiberLifecycle
                            (MkFiber component parent retiredFlag table
                              (Inactive Nothing))
                            (Reloading (componentProgram component)
                              (\local => local) view)) fibers)))
                  targetShape = cong (MkSystemState ambient)
                    (cong (\fiber => replaceBinding @{nameEq} actor fiber fibers)
                      runtimeNextShape)
                  0 checkedReduced :
                    Just (LBeginTag,
                      the (SystemState name key value world error)
                        (MkSystemState ambient
                          (replaceBinding @{nameEq} actor
                            (setFiberLifecycle
                              (MkFiber component parent retiredFlag table
                                (Inactive Nothing))
                              (Reloading (componentProgram component)
                                (\local => local) view)) fibers))) =
                    Just (tag, afterState)
                  checkedReduced = checked
                  0 runtimeAfter :
                    (the (SystemState name key value world error)
                      (MkSystemState ambient
                        (replaceBinding @{nameEq} actor
                          (setFiberLifecycle
                            (MkFiber component parent retiredFlag table
                              (Inactive Nothing))
                            (Reloading (componentProgram component)
                              (\local => local) view)) fibers))) = afterState
                  runtimeAfter = cong snd (justInjective checkedReduced)
                  0 sourcePotentialExact :
                    actorTargetPotential @{nameEq} @{keyEq} {name = name}
                      {key = key} {value = value} {world = world}
                      {error = error} bound actor
                      (MkSystemState ambient fibers) = bound + 2
                  sourcePotentialExact = trans
                    (actorTargetPotentialAtLookup nameEq keyEq bound actor
                      (MkSystemState ambient fibers)
                      (MkFiber component parent retiredFlag table
                        (Inactive Nothing)) found)
                    (trans
                      (cong (fiberTargetPotential @{nameEq} bound
                        (MkFiber component parent retiredFlag table
                          (Inactive Nothing))) sourceTarget)
                      (inactiveAvailablePotential nameEq bound component parent
                        retiredFlag table (viewProviders view)))
                  0 sourcePositive : LTE 1
                    (actorTargetPotential @{nameEq} @{keyEq} {name = name}
                      {key = key} {value = value} {world = world}
                      {error = error} bound actor
                      (MkSystemState ambient fibers))
                  sourcePositive = rewrite sourcePotentialExact in
                    oneLTEBoundPlusTwo bound
                  0 stayedDrop :
                    sameTarget @{nameEq}
                      (targetProvidersAt @{nameEq} @{keyEq}
                        {name = name} {key = key} {value = value}
                        {world = world} {error = error} actor
                        (MkSystemState ambient fibers))
                      (targetProvidersAt @{nameEq} @{keyEq}
                        {name = name} {key = key} {value = value}
                        {world = world} {error = error} actor
                        (MkSystemState ambient
                          (replaceBinding @{nameEq} actor next fibers))) = True ->
                    LTE (S (actorTargetPotential @{nameEq} @{keyEq}
                      {name = name} {key = key} {value = value}
                      {world = world} {error = error} bound actor
                      (MkSystemState ambient
                        (replaceBinding @{nameEq} actor next fibers))))
                      (actorTargetPotential @{nameEq} @{keyEq}
                        {name = name} {key = key} {value = value}
                        {world = world} {error = error} bound actor
                        (MkSystemState ambient fibers))
                  stayedDrop stayed =
                    let targetEqual = sameTargetTrueEqual nameEq
                          (targetProvidersAt @{nameEq} @{keyEq}
                            {name = name} {key = key} {value = value}
                            {world = world} {error = error} actor
                            (MkSystemState ambient fibers))
                          (targetProvidersAt @{nameEq} @{keyEq}
                            {name = name} {key = key} {value = value}
                            {world = world} {error = error} actor
                            (MkSystemState ambient
                              (replaceBinding @{nameEq} actor next fibers)))
                          stayed
                        0 afterTarget :
                          (targetProvidersAt @{nameEq} @{keyEq}
                            {name = name} {key = key} {value = value}
                            {world = world} {error = error} actor
                            (MkSystemState ambient
                              (replaceBinding @{nameEq} actor next fibers)) =
                              Just (viewProviders view))
                        afterTarget = trans (sym targetEqual) sourceTarget
                        0 afterPotentialExact :
                          actorTargetPotential @{nameEq} @{keyEq}
                            {name = name} {key = key} {value = value}
                            {world = world} {error = error} bound actor
                            (MkSystemState ambient
                              (replaceBinding @{nameEq} actor next fibers)) =
                              S (length (componentProgram component))
                        afterPotentialExact = trans
                          (actorTargetPotentialAtLookup nameEq keyEq bound
                            actor (MkSystemState ambient
                              (replaceBinding @{nameEq} actor next fibers))
                            next nextFound)
                          (trans
                            (cong (fiberTargetPotential @{nameEq} bound next)
                              afterTarget)
                            (rewrite nextShape in
                              reloadingCommittedPotential nameEq bound
                                component parent retiredFlag table
                                (componentProgram component) (\local => local) view))
                    in rewrite afterPotentialExact in
                       rewrite sourcePotentialExact in
                         successorSuccessorLTEPlusTwo
                           (length (componentProgram component)) bound
                           (boolLTEToLTE
                             (length (componentProgram component)) bound
                             boundedProgram)
              in replace
                {p = \state => ActorPotentialStep name key world error value
                  nameEq keyEq bound actor (MkSystemState ambient fibers) state}
                (trans targetShape runtimeAfter)
                (MkActorPotentialStep sourcePositive stayedDrop)
    beginActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag checked programs |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive (Just err) =
          void (nothingIsNotJust checked)
    beginActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag checked programs |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view =
            void (nothingIsNotJust checked)
    beginActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag checked programs |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view =
          void (nothingIsNotJust checked)
    beginActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag checked programs |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome =
            void (nothingIsNotJust checked)
