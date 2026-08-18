module DGamma.CP4DeletionFrameAdvanceDispatch

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrameAdvance
import DGamma.CP4DeletionFrameRaise
import Decidable.Equality

%default total

0 transportTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {action : Action name key value world error} ->
  {expected, observed : RuleTag} ->
  {before, afterState : SystemState name key value world error} ->
  expected = observed ->
  ActualEffectFrame nameEq keyEq action expected before afterState ->
  ActualEffectFrame nameEq keyEq action observed before afterState
transportTag Refl frame = frame

||| Complete L-Advance dispatcher over L-Iter/L-Finish/L-Raise and both
||| L-Divert landing alternatives.
public export
0 advanceActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) tag before afterState
advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} actor fibers) proof found
  advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust raw)
    advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading [] accumulator view with
      (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading [] accumulator view)) fibers) view) proof matches
      advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading [] accumulator view | True =
        let concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle
                  (MkFiber component parent retiredFlag table
                    (Reloading [] accumulator view))
                  (Active accumulator view)) fibers)
            0 tagShape : LFinishTag = tag
            tagShape = ruleTagFromJust raw
            0 afterShape : concrete = afterState
            afterShape = endpointFromJust raw
            0 frame : ActualEffectFrame nameEq keyEq (LAdvance actor)
              LFinishTag (MkSystemState ambient fibers) concrete
            frame = finishEmptyActualEffectFrame nameEq keyEq actor ambient fibers
              component parent retiredFlag table accumulator view found concrete
              Refl
        in transportTag tagShape
          (replace {p = \state => ActualEffectFrame nameEq keyEq (LAdvance actor)
            LFinishTag (MkSystemState ambient fibers) state} afterShape frame)
      advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading [] accumulator view | False =
        let concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} actor
                (setFiberLifecycle
                  (MkFiber component parent retiredFlag table
                    (Reloading [] accumulator view))
                  (Unloading accumulator view Nothing)) fibers)
            0 tagShape : LDivertTag = tag
            tagShape = ruleTagFromJust raw
            0 afterShape : concrete = afterState
            afterShape = endpointFromJust raw
            0 frame : ActualEffectFrame nameEq keyEq (LAdvance actor)
              LDivertTag (MkSystemState ambient fibers) concrete
            frame = landingDivertEmptyActualEffectFrame nameEq keyEq actor ambient
              fibers component parent retiredFlag table accumulator view found
              concrete Refl
        in transportTag tagShape
          (replace {p = \state => ActualEffectFrame nameEq keyEq (LAdvance actor)
            LDivertTag (MkSystemState ambient fibers) state} afterShape frame)
    advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading (step :: rest) accumulator view with
      (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view fibers) proof resolved
      advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Nothing =
              void (nothingIsNotJust raw)
      advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Just capability with
        (runStepEffect step capability
          (MkLocalState ambient
            (restrictOwnedPreservingOrder (componentProvisions component)
              (ownedValues table)))) proof ran
        advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
          afterState tag raw |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Left err =
          let concrete : SystemState name key value world error
              concrete = MkSystemState ambient
                (replaceBinding @{nameEq} actor
                  (setFiberLifecycle
                    (MkFiber component parent retiredFlag table
                      (Reloading (step :: rest) accumulator view))
                    (Unloading accumulator view (Just err))) fibers)
              0 tagShape : LRaiseTag = tag
              tagShape = ruleTagFromJust raw
              0 afterShape : concrete = afterState
              afterShape = endpointFromJust raw
              0 frame : ActualEffectFrame nameEq keyEq (LAdvance actor)
                LRaiseTag (MkSystemState ambient fibers) concrete
              frame = raiseConcreteActualEffectFrame nameEq keyEq actor ambient
                fibers component parent retiredFlag table step rest accumulator
                view err found concrete Refl
          in transportTag tagShape
            (replace {p = \state => ActualEffectFrame nameEq keyEq
              (LAdvance actor) LRaiseTag (MkSystemState ambient fibers) state}
              afterShape frame)
        advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
          afterState tag raw |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Right (localAfter, undo) with
          (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)) fibers) view)
            proof matches
          advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
            afterState tag raw |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: rest) accumulator view | Just capability |
                  Right (localAfter, undo) | False =
            let concrete : SystemState name key value world error
                concrete = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} actor
                    (setFiberRuntime
                      (MkFiber component parent retiredFlag table
                        (Reloading (step :: rest) accumulator view))
                      (localTable localAfter)
                      (Unloading (pushLocalUndo (componentProvisions component) accumulator undo) view Nothing)) fibers)
                0 tagShape : LDivertTag = tag
                tagShape = ruleTagFromJust raw
                0 afterShape : concrete = afterState
                afterShape = endpointFromJust raw
                0 frame : ActualEffectFrame nameEq keyEq (LAdvance actor)
                  LDivertTag (MkSystemState ambient fibers) concrete
                frame = landingDivertActualEffectFrame nameEq keyEq actor ambient
                  fibers component parent retiredFlag table step rest accumulator
                  view capability resolved localAfter undo ran matches found
                  concrete Refl
            in transportTag tagShape
              (replace {p = \state => ActualEffectFrame nameEq keyEq
                (LAdvance actor) LDivertTag (MkSystemState ambient fibers) state}
                afterShape frame)
          advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
            afterState tag raw |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: []) accumulator view | Just capability |
                  Right (localAfter, undo) | True =
            let concrete : SystemState name key value world error
                concrete = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} actor
                    (setFiberRuntime
                      (MkFiber component parent retiredFlag table
                        (Reloading [step] accumulator view))
                      (localTable localAfter)
                      (Active (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers)
                0 tagShape : LFinishTag = tag
                tagShape = ruleTagFromJust raw
                0 afterShape : concrete = afterState
                afterShape = endpointFromJust raw
                0 frame : ActualEffectFrame nameEq keyEq (LAdvance actor)
                  LFinishTag (MkSystemState ambient fibers) concrete
                frame = finishStepActualEffectFrame nameEq keyEq actor ambient fibers
                  component parent retiredFlag table step accumulator view capability
                  resolved localAfter undo ran matches found concrete Refl
            in transportTag tagShape
              (replace {p = \state => ActualEffectFrame nameEq keyEq
                (LAdvance actor) LFinishTag (MkSystemState ambient fibers) state}
                afterShape frame)
          advanceActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
            afterState tag raw |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: nextStep :: more) accumulator view |
                  Just capability | Right (localAfter, undo) | True =
            let concrete : SystemState name key value world error
                concrete = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} actor
                    (setFiberRuntime
                      (MkFiber component parent retiredFlag table
                        (Reloading (step :: nextStep :: more) accumulator view))
                      (localTable localAfter)
                      (Reloading (nextStep :: more) (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers)
                0 tagShape : LIterTag = tag
                tagShape = ruleTagFromJust raw
                0 afterShape : concrete = afterState
                afterShape = endpointFromJust raw
                0 frame : ActualEffectFrame nameEq keyEq (LAdvance actor)
                  LIterTag (MkSystemState ambient fibers) concrete
                frame = iterActualEffectFrame nameEq keyEq actor ambient fibers
                  component parent retiredFlag table step nextStep more accumulator
                  view capability resolved localAfter undo ran matches found concrete
                  Refl
            in transportTag tagShape
              (replace {p = \state => ActualEffectFrame nameEq keyEq
                (LAdvance actor) LIterTag (MkSystemState ambient fibers) state}
                afterShape frame)
