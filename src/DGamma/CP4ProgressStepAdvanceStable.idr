module DGamma.CP4ProgressStepAdvanceStable

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressPotential
import DGamma.CP4ProgressStepCore
import Data.Nat
import Decidable.Equality

%default total

0 matchedSourceTarget :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} fiber (registry state)) view = True ->
  targetProvidersAt @{nameEq} @{keyEq} actor state =
    Just (viewProviders view)
matchedSourceTarget nameEq keyEq actor state fiber view found matches =
  let sourceMap = targetProvidersAtLookup nameEq keyEq actor state fiber found
      mapMatched = trans
        (sym (targetMatchesSameTarget nameEq
          (targetFiber @{nameEq} @{keyEq} fiber (registry state)) view)) matches
      0 targetMatched : (sameTarget @{nameEq}
        (targetProvidersAt @{nameEq} @{keyEq} actor state)
        (Just (viewProviders view)) = True)
      targetMatched = rewrite sourceMap in mapMatched
  in sameTargetTrueEqual nameEq
    (targetProvidersAt @{nameEq} @{keyEq} actor state)
    (Just (viewProviders view)) targetMatched

||| A matched L-Finish endpoint consumes the last same-target control step.
public export
0 finishAdvancePotentialStep :
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
      (Active targetAccumulator view))) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag sourceTable
        (Reloading remaining sourceAccumulator view))
      (registry sourceState)) view = True ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    sourceState targetState
finishAdvancePotentialStep nameEq keyEq bound actor sourceState targetState
  component parent retiredFlag sourceTable targetTable remaining
  sourceAccumulator targetAccumulator view sourceFound targetFound matches =
  let sourceFiber = MkFiber component parent retiredFlag sourceTable
        (Reloading remaining sourceAccumulator view)
      targetFiberValue = MkFiber component parent retiredFlag targetTable
        (Active targetAccumulator view)
      0 sourceTarget = matchedSourceTarget nameEq keyEq actor sourceState
        (MkFiber component parent retiredFlag sourceTable
          (Reloading remaining sourceAccumulator view))
        view sourceFound matches
      0 sourcePotentialExact :
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState =
          S (length remaining))
      sourcePotentialExact = trans
        (actorTargetPotentialAtLookup nameEq keyEq bound actor sourceState
          (MkFiber component parent retiredFlag sourceTable
            (Reloading remaining sourceAccumulator view)) sourceFound)
        (trans (cong (fiberTargetPotential @{nameEq} bound
          (MkFiber component parent retiredFlag sourceTable
            (Reloading remaining sourceAccumulator view))) sourceTarget)
          (reloadingCommittedPotential nameEq bound component parent retiredFlag
            sourceTable remaining sourceAccumulator view))
      0 sourcePositive : LTE 1
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      sourcePositive = rewrite sourcePotentialExact in LTESucc LTEZero
      0 stayedDrop : sameTarget @{nameEq}
        (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
        (targetProvidersAt @{nameEq} @{keyEq} actor targetState) = True ->
        LTE (S (actorTargetPotential @{nameEq} @{keyEq} bound actor targetState))
          (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      stayedDrop stayed =
        let targetEqual = sameTargetTrueEqual nameEq
              (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
              (targetProvidersAt @{nameEq} @{keyEq} actor targetState) stayed
            targetTarget = trans (sym targetEqual) sourceTarget
            afterExact = trans
              (actorTargetPotentialAtLookup nameEq keyEq bound actor targetState
                (MkFiber component parent retiredFlag targetTable
                  (Active targetAccumulator view)) targetFound)
              (trans
                (cong (fiberTargetPotential @{nameEq} bound
                  (MkFiber component parent retiredFlag targetTable
                    (Active targetAccumulator view))) targetTarget)
                (activeCommittedPotential nameEq bound component parent retiredFlag
                  targetTable targetAccumulator view))
        in rewrite afterExact in rewrite sourcePotentialExact in
          LTESucc LTEZero
  in MkActorPotentialStep sourcePositive stayedDrop

||| A matched L-Iter removes exactly one head from the continuation, hence one
||| unit from the same-target potential.
public export
0 iterAdvancePotentialStep :
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
  (nextStep : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (more : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (sourceAccumulator, targetAccumulator :
    LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceFound : lookupFiber @{nameEq} actor (registry sourceState) =
    Just (MkFiber component parent retiredFlag sourceTable
      (Reloading (step :: nextStep :: more) sourceAccumulator view))) ->
  (targetFound : lookupFiber @{nameEq} actor (registry targetState) =
    Just (MkFiber component parent retiredFlag targetTable
      (Reloading (nextStep :: more) targetAccumulator view))) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag sourceTable
        (Reloading (step :: nextStep :: more) sourceAccumulator view))
      (registry sourceState)) view = True ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    sourceState targetState
iterAdvancePotentialStep nameEq keyEq bound actor sourceState targetState
  component parent retiredFlag sourceTable targetTable step nextStep more
  sourceAccumulator targetAccumulator view sourceFound targetFound matches =
  let sourceFiber = MkFiber component parent retiredFlag sourceTable
        (Reloading (step :: nextStep :: more) sourceAccumulator view)
      targetFiberValue = MkFiber component parent retiredFlag targetTable
        (Reloading (nextStep :: more) targetAccumulator view)
      0 sourceTarget = matchedSourceTarget nameEq keyEq actor sourceState
        (MkFiber component parent retiredFlag sourceTable
          (Reloading (step :: nextStep :: more) sourceAccumulator view))
        view sourceFound matches
      0 sourcePotentialExact :
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState =
          S (S (length (nextStep :: more))))
      sourcePotentialExact = trans
        (actorTargetPotentialAtLookup nameEq keyEq bound actor sourceState
          (MkFiber component parent retiredFlag sourceTable
            (Reloading (step :: nextStep :: more) sourceAccumulator view))
          sourceFound)
        (trans (cong (fiberTargetPotential @{nameEq} bound
          (MkFiber component parent retiredFlag sourceTable
            (Reloading (step :: nextStep :: more) sourceAccumulator view)))
          sourceTarget)
          (reloadingCommittedPotential nameEq bound component parent retiredFlag
            sourceTable (step :: nextStep :: more) sourceAccumulator view))
      0 sourcePositive : LTE 1
        (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      sourcePositive = rewrite sourcePotentialExact in
        LTESucc LTEZero
      0 stayedDrop : sameTarget @{nameEq}
        (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
        (targetProvidersAt @{nameEq} @{keyEq} actor targetState) = True ->
        LTE (S (actorTargetPotential @{nameEq} @{keyEq} bound actor targetState))
          (actorTargetPotential @{nameEq} @{keyEq} bound actor sourceState)
      stayedDrop stayed =
        let targetEqual = sameTargetTrueEqual nameEq
              (targetProvidersAt @{nameEq} @{keyEq} actor sourceState)
              (targetProvidersAt @{nameEq} @{keyEq} actor targetState) stayed
            targetTarget = trans (sym targetEqual) sourceTarget
            afterExact = trans
              (actorTargetPotentialAtLookup nameEq keyEq bound actor targetState
                (MkFiber component parent retiredFlag targetTable
                  (Reloading (nextStep :: more) targetAccumulator view))
                targetFound)
              (trans
                (cong (fiberTargetPotential @{nameEq} bound
                  (MkFiber component parent retiredFlag targetTable
                    (Reloading (nextStep :: more) targetAccumulator view)))
                  targetTarget)
                (reloadingCommittedPotential nameEq bound component parent retiredFlag
                  targetTable (nextStep :: more) targetAccumulator view))
        in rewrite afterExact in rewrite sourcePotentialExact in
          lteRefl (S (S (length (nextStep :: more))))
  in MkActorPotentialStep sourcePositive stayedDrop
