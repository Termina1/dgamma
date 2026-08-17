module DGamma.CP4ProgressStepAdvanceExit

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressPotential
import DGamma.CP4ProgressStepCore
import Data.Nat
import Decidable.Equality

%default total

0 staleSourceNames :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} fiber (registry state)) view = False ->
  sameTarget @{nameEq}
    (targetProvidersAt @{nameEq} @{keyEq} actor state)
    (Just (viewProviders view)) = False
staleSourceNames nameEq keyEq actor state fiber view found stale =
  let sourceMap = targetProvidersAtLookup nameEq keyEq actor state fiber found
      mapStale = trans
        (sym (targetMatchesSameTarget nameEq
          (targetFiber @{nameEq} @{keyEq} fiber (registry state)) view)) stale
  in rewrite sourceMap in mapStale

||| The stale-target LAdvance branch has the same potential transition as the
||| explicit L-Divert rule.
public export
0 divertAdvancePotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (sourceState, targetState : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (sourceTable, targetTable : OwnedTable key value
    (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (sourceAccumulator, targetAccumulator :
    LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceFound : lookupFiber @{nameEq} actor (registry sourceState) =
    Just (MkFiber component parent retiredFlag sourceTable
      (Reloading remaining sourceAccumulator view))) ->
  (targetFound : lookupFiber @{nameEq} actor (registry targetState) =
    Just (MkFiber component parent retiredFlag targetTable
      (Unloading targetAccumulator view Nothing))) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag sourceTable
        (Reloading remaining sourceAccumulator view))
      (registry sourceState)) view = False ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    sourceState targetState
divertAdvancePotentialStep nameEq keyEq bound actor sourceState targetState
  component parent retiredFlag sourceTable targetTable remaining
  sourceAccumulator targetAccumulator view sourceFound targetFound stale =
  let sourceFiber = MkFiber component parent retiredFlag sourceTable
        (Reloading remaining sourceAccumulator view)
      targetFiberValue = MkFiber component parent retiredFlag targetTable
        (Unloading targetAccumulator view Nothing)
      0 namesStale = staleSourceNames nameEq keyEq actor sourceState
        (MkFiber component parent retiredFlag sourceTable
          (Reloading remaining sourceAccumulator view))
        view sourceFound stale
      0 sourcePotentialExact :
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState =
          bound + 4)
      sourcePotentialExact = trans
        (actorTargetPotentialAtLookup nameEq keyEq bound actor sourceState
          (MkFiber component parent retiredFlag sourceTable
            (Reloading remaining sourceAccumulator view)) sourceFound)
        (reloadingStalePotential nameEq bound component parent retiredFlag
          sourceTable remaining sourceAccumulator view
          (targetProvidersAt @{nameEq} @{keyEq} actor sourceState) namesStale)
      0 afterPotentialExact :
        (actorTargetPotential @{nameEq} @{keyEq} bound actor targetState =
          bound + 3)
      afterPotentialExact = trans
        (actorTargetPotentialAtLookup nameEq keyEq bound actor targetState
          (MkFiber component parent retiredFlag targetTable
            (Unloading targetAccumulator view Nothing)) targetFound)
        (unloadingCleanPotential
          {target = targetProvidersAt @{nameEq} @{keyEq} actor targetState}
          nameEq bound component parent retiredFlag targetTable targetAccumulator
          view)
      0 sourcePositive : LTE 1
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      sourcePositive = rewrite sourcePotentialExact in oneLTEBoundPlusFour bound
      0 stayedDrop : sameTarget @{nameEq}
        (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
        (targetProvidersAt @{nameEq} @{keyEq} actor targetState) = True ->
        LTE (S (actorTargetPotential @{nameEq} @{keyEq} bound actor targetState))
          (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      stayedDrop stayed = rewrite afterPotentialExact in
        rewrite sourcePotentialExact in boundPlusThreeStep bound
  in MkActorPotentialStep sourcePositive stayedDrop

||| A raised iterator step has at least two units of source potential (the
||| current nonempty step) and lands at failed-unload potential one.
public export
0 raiseAdvancePotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (sourceState, targetState : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (sourceTable, targetTable : OwnedTable key value
    (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (sourceAccumulator, targetAccumulator :
    LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (err : error) ->
  (sourceFound : lookupFiber @{nameEq} actor (registry sourceState) =
    Just (MkFiber component parent retiredFlag sourceTable
      (Reloading (step :: rest) sourceAccumulator view))) ->
  (targetFound : lookupFiber @{nameEq} actor (registry targetState) =
    Just (MkFiber component parent retiredFlag targetTable
      (Unloading targetAccumulator view (Just err)))) ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    sourceState targetState
raiseAdvancePotentialStep nameEq keyEq bound actor sourceState targetState
  component parent retiredFlag sourceTable targetTable step rest sourceAccumulator
  targetAccumulator view err sourceFound targetFound =
  let sourceFiber = MkFiber component parent retiredFlag sourceTable
        (Reloading (step :: rest) sourceAccumulator view)
      targetFiberValue = MkFiber component parent retiredFlag targetTable
        (Unloading targetAccumulator view (Just err))
      0 sourcePotentialShape :
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState =
          fiberTargetPotential @{nameEq} bound
            (MkFiber component parent retiredFlag sourceTable
              (Reloading (step :: rest) sourceAccumulator view))
            (targetProvidersAt @{nameEq} @{keyEq} actor sourceState))
      sourcePotentialShape = actorTargetPotentialAtLookup nameEq keyEq bound actor
        sourceState
        (MkFiber component parent retiredFlag sourceTable
          (Reloading (step :: rest) sourceAccumulator view)) sourceFound
      0 sourceAtLeastTwoActual : LTE 2
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      sourceAtLeastTwoActual = rewrite sourcePotentialShape in
        nonemptyReloadingPotentialAtLeastTwo nameEq bound component parent
          retiredFlag sourceTable step rest sourceAccumulator view
          (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
      0 afterPotentialExact :
        (actorTargetPotential @{nameEq} @{keyEq} bound actor targetState = 1)
      afterPotentialExact = trans
        (actorTargetPotentialAtLookup nameEq keyEq bound actor targetState
          (MkFiber component parent retiredFlag targetTable
            (Unloading targetAccumulator view (Just err))) targetFound)
        (unloadingFailedPotential
          {target = targetProvidersAt @{nameEq} @{keyEq} actor targetState}
          nameEq bound component parent retiredFlag targetTable targetAccumulator
          view err)
      0 sourcePositive : LTE 1
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      sourcePositive = lteTransitive (LTESucc LTEZero) sourceAtLeastTwoActual
      0 stayedDrop : sameTarget @{nameEq}
        (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
        (targetProvidersAt @{nameEq} @{keyEq} actor targetState) = True ->
        LTE (S (actorTargetPotential @{nameEq} @{keyEq} bound actor targetState))
          (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      stayedDrop stayed = rewrite afterPotentialExact in sourceAtLeastTwoActual
  in MkActorPotentialStep sourcePositive stayedDrop
