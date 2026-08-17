module DGamma.CP4ProgressStepAdvance

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressStepCore
import DGamma.CP4ProgressStepAdvanceStable
import DGamma.CP4ProgressStepAdvanceExit
import Data.Nat
import Decidable.Equality

%default total

||| Exhaustive L-Advance potential theorem. Each evaluator outcome is delegated
||| to its saturated same-module arithmetic helper, then transported along the
||| raw evaluator endpoint equality.
public export
0 advanceActorPotentialStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState) ->
  ActorPotentialStep name key world error value nameEq keyEq bound actor
    before afterState
advanceActorPotentialStep nameEq keyEq bound actor
  (MkSystemState ambient fibers) afterState tag raw
  with (lookupFiber @{nameEq} actor fibers) proof found
  advanceActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag raw | Nothing =
      void (nothingIsNotJust raw)
  advanceActorPotentialStep nameEq keyEq bound actor
    (MkSystemState ambient fibers) afterState tag raw |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    advanceActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    advanceActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    advanceActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust raw)
    advanceActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading [] accumulator view with
      (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading [] accumulator view)) fibers) view) proof matches
      advanceActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading [] accumulator view | True =
        let sourceFiber = MkFiber component parent retiredFlag table
              (Reloading [] accumulator view)
            targetFiberValue : Fiber name key value world error
            targetFiberValue = MkFiber component parent retiredFlag table
              (Active accumulator view)
            targetState : SystemState name key value world error
            targetState = MkSystemState ambient
              (replaceBinding @{nameEq} actor targetFiberValue fibers)
            0 targetFound : lookupFiber @{nameEq} actor (registry targetState) =
              Just targetFiberValue
            targetFound = lookupReplacedFiber actor
              (MkFiber component parent retiredFlag table
                (Reloading [] accumulator view)) targetFiberValue fibers found
            0 rawReduced : Just (LFinishTag, targetState) = Just (tag, afterState)
            rawReduced = raw
            0 exactStep : ActorPotentialStep name key world error value
              nameEq keyEq bound actor (MkSystemState ambient fibers) targetState
            exactStep = finishAdvancePotentialStep nameEq keyEq bound actor
              (MkSystemState ambient fibers) targetState component parent retiredFlag
              table table [] accumulator accumulator view found targetFound matches
        in transportActorPotentialTarget exactStep
          (cong snd (justInjective rawReduced))
      advanceActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading [] accumulator view | False =
        let sourceFiber = MkFiber component parent retiredFlag table
              (Reloading [] accumulator view)
            targetFiberValue : Fiber name key value world error
            targetFiberValue = MkFiber component parent retiredFlag table
              (Unloading accumulator view Nothing)
            targetState : SystemState name key value world error
            targetState = MkSystemState ambient
              (replaceBinding @{nameEq} actor targetFiberValue fibers)
            0 targetFound : lookupFiber @{nameEq} actor (registry targetState) =
              Just targetFiberValue
            targetFound = lookupReplacedFiber actor
              (MkFiber component parent retiredFlag table
                (Reloading [] accumulator view)) targetFiberValue fibers found
            0 rawReduced : Just (LDivertTag, targetState) = Just (tag, afterState)
            rawReduced = raw
            0 exactStep : ActorPotentialStep name key world error value
              nameEq keyEq bound actor (MkSystemState ambient fibers) targetState
            exactStep = divertAdvancePotentialStep nameEq keyEq bound actor
              (MkSystemState ambient fibers) targetState component parent retiredFlag
              table table [] accumulator accumulator view found targetFound matches
        in transportActorPotentialTarget exactStep
          (cong snd (justInjective rawReduced))
    advanceActorPotentialStep nameEq keyEq bound actor
      (MkSystemState ambient fibers) afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading (step :: rest) accumulator view with
      (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view fibers)
      advanceActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Nothing =
              void (nothingIsNotJust raw)
      advanceActorPotentialStep nameEq keyEq bound actor
        (MkSystemState ambient fibers) afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Just capability with
        (runStepEffect step capability (MkLocalState ambient table))
        advanceActorPotentialStep nameEq keyEq bound actor
          (MkSystemState ambient fibers) afterState tag raw |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Left err =
          let sourceFiber = MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)
              targetFiberValue : Fiber name key value world error
              targetFiberValue = MkFiber component parent retiredFlag table
                (Unloading accumulator view (Just err))
              targetState : SystemState name key value world error
              targetState = MkSystemState ambient
                (replaceBinding @{nameEq} actor targetFiberValue fibers)
              0 targetFound : lookupFiber @{nameEq} actor (registry targetState) =
                Just targetFiberValue
              targetFound = lookupReplacedFiber actor
                (MkFiber component parent retiredFlag table
                  (Reloading (step :: rest) accumulator view))
                targetFiberValue fibers found
              0 rawReduced : Just (LRaiseTag, targetState) = Just (tag, afterState)
              rawReduced = raw
              0 exactStep : ActorPotentialStep name key world error value
                nameEq keyEq bound actor (MkSystemState ambient fibers) targetState
              exactStep = raiseAdvancePotentialStep nameEq keyEq bound actor
                (MkSystemState ambient fibers) targetState component parent
                retiredFlag table table step rest accumulator accumulator view err
                found targetFound
          in transportActorPotentialTarget exactStep
            (cong snd (justInjective rawReduced))
        advanceActorPotentialStep nameEq keyEq bound actor
          (MkSystemState ambient fibers) afterState tag raw |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Right (localAfter, undo) with
          (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)) fibers) view)
            proof matches
          advanceActorPotentialStep nameEq keyEq bound actor
            (MkSystemState ambient fibers) afterState tag raw |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: rest) accumulator view | Just capability |
                  Right (localAfter, undo) | False =
            let nextAccumulator = accumulator . undo
                nextTable : OwnedTable key value (componentProvisions component)
                nextTable = localTable localAfter
                sourceFiber = MkFiber component parent retiredFlag table
                  (Reloading (step :: rest) accumulator view)
                targetFiberValue : Fiber name key value world error
                targetFiberValue = MkFiber component parent retiredFlag (localTable localAfter)
                  (Unloading (accumulator . undo) view Nothing)
                targetState : SystemState name key value world error
                targetState = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} actor targetFiberValue fibers)
                0 targetFound : lookupFiber @{nameEq} actor
                  (registry targetState) = Just targetFiberValue
                targetFound = lookupReplacedFiber actor
                  (MkFiber component parent retiredFlag table
                    (Reloading (step :: rest) accumulator view))
                  targetFiberValue fibers found
                0 rawReduced : Just (LDivertTag, targetState) =
                  Just (tag, afterState)
                rawReduced = raw
                0 exactStep : ActorPotentialStep name key world error value
                  nameEq keyEq bound actor (MkSystemState ambient fibers) targetState
                exactStep = divertAdvancePotentialStep nameEq keyEq bound actor
                  (MkSystemState ambient fibers) targetState component parent
                  retiredFlag table (localTable localAfter) (step :: rest) accumulator
                  (accumulator . undo) view found targetFound matches
            in transportActorPotentialTarget exactStep
              (cong snd (justInjective rawReduced))
          advanceActorPotentialStep nameEq keyEq bound actor
            (MkSystemState ambient fibers) afterState tag raw |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: []) accumulator view | Just capability |
                  Right (localAfter, undo) | True =
            let nextAccumulator = accumulator . undo
                nextTable : OwnedTable key value (componentProvisions component)
                nextTable = localTable localAfter
                targetFiberValue : Fiber name key value world error
                targetFiberValue = MkFiber component parent retiredFlag (localTable localAfter)
                  (Active (accumulator . undo) view)
                targetState : SystemState name key value world error
                targetState = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} actor targetFiberValue fibers)
                0 targetFound : lookupFiber @{nameEq} actor
                  (registry targetState) = Just targetFiberValue
                targetFound = lookupReplacedFiber actor
                  (MkFiber component parent retiredFlag table
                    (Reloading (step :: []) accumulator view))
                  targetFiberValue fibers found
                0 rawReduced : Just (LFinishTag, targetState) =
                  Just (tag, afterState)
                rawReduced = raw
                0 exactStep : ActorPotentialStep name key world error value
                  nameEq keyEq bound actor (MkSystemState ambient fibers) targetState
                exactStep = finishAdvancePotentialStep nameEq keyEq bound actor
                  (MkSystemState ambient fibers) targetState component parent
                  retiredFlag table (localTable localAfter) (step :: []) accumulator
                  (accumulator . undo) view found targetFound matches
            in transportActorPotentialTarget exactStep
              (cong snd (justInjective rawReduced))
          advanceActorPotentialStep nameEq keyEq bound actor
            (MkSystemState ambient fibers) afterState tag raw |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: nextStep :: more) accumulator view |
                  Just capability | Right (localAfter, undo) | True =
            let nextAccumulator = accumulator . undo
                nextTable : OwnedTable key value (componentProvisions component)
                nextTable = localTable localAfter
                targetFiberValue : Fiber name key value world error
                targetFiberValue = MkFiber component parent retiredFlag (localTable localAfter)
                  (Reloading (nextStep :: more) (accumulator . undo) view)
                targetState : SystemState name key value world error
                targetState = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} actor targetFiberValue fibers)
                0 targetFound : lookupFiber @{nameEq} actor
                  (registry targetState) = Just targetFiberValue
                targetFound = lookupReplacedFiber actor
                  (MkFiber component parent retiredFlag table
                    (Reloading (step :: nextStep :: more) accumulator view))
                  targetFiberValue fibers found
                0 rawReduced : Just (LIterTag, targetState) =
                  Just (tag, afterState)
                rawReduced = raw
                0 exactStep : ActorPotentialStep name key world error value
                  nameEq keyEq bound actor (MkSystemState ambient fibers) targetState
                exactStep = iterAdvancePotentialStep nameEq keyEq bound actor
                  (MkSystemState ambient fibers) targetState component parent
                  retiredFlag table (localTable localAfter) step nextStep more accumulator
                  (accumulator . undo) view found targetFound matches
            in transportActorPotentialTarget exactStep
              (cong snd (justInjective rawReduced))
