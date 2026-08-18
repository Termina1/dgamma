module DGamma.CP4DeletionFrameUnload

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrameAdvance
import Decidable.Equality

%default total

||| Saturated L-Unload frame, including the accumulator/recovery effect on both
||| ambient state and the actor's owned table.
public export
0 unloadConcreteActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome))) ->
  (afterState : SystemState name key value world error) ->
  let restored = accumulator
        (MkLocalState ambient
          (restrictOwnedPreservingOrder (componentProvisions component)
            (ownedValues table))) in
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState (localWorld restored)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime
            (MkFiber component parent retiredFlag table
              (Unloading accumulator view outcome))
            (localTable restored) (Inactive outcome)) fibers))) = afterState) ->
  ActualEffectFrame nameEq keyEq (LUnload actor) LUnloadTag
    (MkSystemState ambient fibers) afterState
unloadConcreteActualEffectFrame nameEq keyEq actor ambient fibers component parent
  retiredFlag table accumulator view outcome sourceFound afterState concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)
      normalized : OwnedTable key value (componentProvisions component)
      normalized = restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table)
      restored : LocalState key value world (componentProvisions component)
      restored = accumulator (MkLocalState ambient normalized)
      next : Fiber name key value world error
      next = setFiberRuntime sourceFiber (localTable restored) (Inactive outcome)
      0 tableSame : ownedValues (fiberTable next) =
        ownedValues (localTable restored)
      tableSame = setRuntimeTableExact sourceFiber (localTable restored)
        (Inactive outcome)
      0 mapRuns : partialEffectMapFor nameEq keyEq (LUnload actor) LUnloadTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (setEffectTable @{nameEq} actor
          (ownedValues (localTable restored))
          (setEffectAmbient (localWorld restored)
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)))))
      mapRuns = partialEffectMapUnloadRuns nameEq keyEq actor ambient fibers
        component parent retiredFlag table accumulator view outcome sourceFound
  in runtimeReplaceActualEffectFrame nameEq keyEq (LUnload actor) LUnloadTag
    actor ambient (localWorld restored) sourceFiber next fibers afterState
    sourceFound (ownedValues (localTable restored)) tableSame concreteAfter mapRuns

||| Complete L-Unload actual-effect frame, dispatching the relied guard and all
||| lifecycle shapes before applying the saturated accumulator frame.
public export
0 unloadActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload actor) before =
    Just (tag, afterState) ->
  ActualEffectFrame nameEq keyEq (LUnload actor) tag before afterState
unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} actor fibers) proof found
  unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
    afterState tag raw | Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle (MkFiber component parent retiredFlag table lifecycle))
    unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view = void (nothingIsNotJust raw)
    unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
      afterState tag raw |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome with
      (relied @{nameEq} actor fibers)
      unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Unloading accumulator view outcome | True =
              void (nothingIsNotJust raw)
      unloadActualEffectFrame nameEq keyEq actor (MkSystemState ambient fibers)
        afterState tag raw |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Unloading accumulator view outcome | False =
        let sourceFiber : Fiber name key value world error
            sourceFiber = MkFiber component parent retiredFlag table
              (Unloading accumulator view outcome)
            normalized : OwnedTable key value (componentProvisions component)
            normalized = restrictOwnedPreservingOrder
              (componentProvisions component) (ownedValues table)
            restored : LocalState key value world (componentProvisions component)
            restored = accumulator (MkLocalState ambient normalized)
            concrete : SystemState name key value world error
            concrete = MkSystemState (localWorld restored)
              (replaceBinding @{nameEq} actor
                (setFiberRuntime sourceFiber (localTable restored)
                  (Inactive outcome)) fibers)
            0 rawReduced : Just (LUnloadTag, concrete) = Just (tag, afterState)
            rawReduced = raw
            0 concreteAfter : concrete = afterState
            concreteAfter = cong snd (justInjective rawReduced)
            0 tagShape : LUnloadTag = tag
            tagShape = cong fst (justInjective rawReduced)
        in case tagShape of
          Refl =>
            let next : Fiber name key value world error
                next = setFiberRuntime sourceFiber (localTable restored)
                  (Inactive outcome)
                0 tableSame : ownedValues (fiberTable next) =
                  ownedValues (localTable restored)
                tableSame = setRuntimeTableExact sourceFiber
                  (localTable restored) (Inactive outcome)
                0 mapRuns : partialEffectMapFor nameEq keyEq (LUnload actor)
                  LUnloadTag
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) =
                  Just (setEffectTable @{nameEq} actor
                    (ownedValues (localTable restored))
                    (setEffectAmbient (localWorld restored)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers)))))
                mapRuns = partialEffectMapUnloadRuns nameEq keyEq actor ambient
                  fibers component parent retiredFlag table accumulator view
                  outcome found
                0 framed : ActualEffectFrame nameEq keyEq (LUnload actor)
                  LUnloadTag (MkSystemState ambient fibers) afterState
                framed = runtimeReplaceActualEffectFrame nameEq keyEq
                  (LUnload actor) LUnloadTag actor ambient (localWorld restored)
                  sourceFiber next fibers afterState found
                  (ownedValues (localTable restored)) tableSame concreteAfter
                  mapRuns
            in replace
              {p = \observedTag => ActualEffectFrame nameEq keyEq
                (LUnload actor) observedTag (MkSystemState ambient fibers)
                afterState}
              tagShape framed
