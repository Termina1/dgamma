module DGamma.CP4DeletionFrameAdvance

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import Decidable.Equality

%default total

public export
0 runtimeTableLookup :
  (keyEq : DecEq key) -> (k : key) ->
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value (componentProvisions (fiberComponent fiber))) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  lookupBinding @{keyEq} k
    (ownedValues (fiberTable (setFiberRuntime fiber table life))) =
  lookupBinding @{keyEq} k (ownedValues table)
runtimeTableLookup keyEq k
  (MkFiber component parent retiredFlag oldTable oldLife) table life = Refl

||| Empty-continuation L-Finish changes only lifecycle control.
public export
0 finishEmptyActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading [] accumulator view))) ->
  (afterState : SystemState name key value world error) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor
          (setFiberLifecycle
            (MkFiber component parent retiredFlag table
              (Reloading [] accumulator view))
            (Active accumulator view)) fibers))) = afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) LFinishTag
    (MkSystemState ambient fibers) afterState
finishEmptyActualEffectFrame nameEq keyEq actor ambient fibers component parent
  retiredFlag table accumulator view sourceFound afterState concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Reloading [] accumulator view)
      next : Fiber name key value world error
      next = setFiberLifecycle sourceFiber (Active accumulator view)
      0 nextShape : next = setFiberLifecycle sourceFiber (Active accumulator view)
      nextShape = Refl
      0 tableSame : (k : key) ->
        lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
        lookupBinding @{keyEq} k (ownedValues (fiberTable sourceFiber))
      tableSame k = trans
        (cong (\observed => lookupBinding @{keyEq} k
          (ownedValues (fiberTable observed))) nextShape)
        (setLifecycleTableLookup keyEq k sourceFiber (Active accumulator view))
      0 identityMap : partialEffectMapFor nameEq keyEq (LAdvance actor)
        LFinishTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers)))
      identityMap = rewrite sourceFound in Refl
  in controlReplaceActualEffectFrame nameEq keyEq (LAdvance actor) LFinishTag
    actor ambient sourceFiber next fibers afterState sourceFound tableSame
    concreteAfter identityMap

||| Nonempty L-Finish branch: the final iterator step mutates the effect state
||| and lands Active with the yielded table/accumulator.
public export
0 finishStepActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  (resolved : resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view fibers =
    Just capability) ->
  (localAfter : LocalState key value world (componentProvisions component)) ->
  (undo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (ran : runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table))) = Right (localAfter, undo)) ->
  (matches : targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table
        (Reloading [step] accumulator view)) fibers) view = True) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading [step] accumulator view))) ->
  (afterState : SystemState name key value world error) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState (localWorld localAfter)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime
            (MkFiber component parent retiredFlag table
              (Reloading [step] accumulator view))
            (localTable localAfter) (Active (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers))) =
      afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) LFinishTag
    (MkSystemState ambient fibers) afterState
finishStepActualEffectFrame nameEq keyEq actor ambient fibers component parent
  retiredFlag table step accumulator view capability resolved localAfter undo ran
  matches sourceFound afterState concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Reloading [step] accumulator view)
      next : Fiber name key value world error
      next = setFiberRuntime sourceFiber (localTable localAfter)
        (Active (pushLocalUndo (componentProvisions component) accumulator undo) view)
      0 effectResolved : resolveEffectValues @{keyEq}
        (dependencies (componentDependencies component)) view
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) = Just capability
      effectResolved = trans
        (resolveEffectValuesProjected nameEq keyEq
          (dependencies (componentDependencies component)) view
          (MkSystemState ambient fibers)) resolved
      0 mapRuns : partialEffectMapFor nameEq keyEq (LAdvance actor) LFinishTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (setEffectTable @{nameEq} actor
          (ownedValues (localTable localAfter))
          (setEffectAmbient (localWorld localAfter)
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)))))
      mapRuns = partialEffectMapAdvanceFinishRuns nameEq keyEq actor ambient
        fibers component parent retiredFlag table step [] accumulator view
        capability sourceFound effectResolved localAfter undo ran
      0 tableSame : (k : key) ->
        lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
        lookupBinding @{keyEq} k (ownedValues (localTable localAfter))
      tableSame k = runtimeTableLookup keyEq k sourceFiber
        (localTable localAfter) (Active (pushLocalUndo (componentProvisions component) accumulator undo) view)
  in runtimeReplaceActualEffectFrame nameEq keyEq (LAdvance actor) LFinishTag
    actor ambient (localWorld localAfter) sourceFiber next fibers afterState
    sourceFound (ownedValues (localTable localAfter)) tableSame concreteAfter
    mapRuns

||| L-Iter branch: one successful step mutates effects and retains the nonempty
||| tail continuation.
public export
0 iterActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step, nextStep : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (more : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  (resolved : resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view fibers =
    Just capability) ->
  (localAfter : LocalState key value world (componentProvisions component)) ->
  (undo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (ran : runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table))) = Right (localAfter, undo)) ->
  (matches : targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table
        (Reloading (step :: nextStep :: more) accumulator view)) fibers) view =
    True) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading (step :: nextStep :: more) accumulator view))) ->
  (afterState : SystemState name key value world error) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState (localWorld localAfter)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime
            (MkFiber component parent retiredFlag table
              (Reloading (step :: nextStep :: more) accumulator view))
            (localTable localAfter)
            (Reloading (nextStep :: more) (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers))) =
      afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) LIterTag
    (MkSystemState ambient fibers) afterState
iterActualEffectFrame nameEq keyEq actor ambient fibers component parent
  retiredFlag table step nextStep more accumulator view capability resolved
  localAfter undo ran matches sourceFound afterState concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Reloading (step :: nextStep :: more) accumulator view)
      next : Fiber name key value world error
      next = setFiberRuntime sourceFiber (localTable localAfter)
        (Reloading (nextStep :: more) (pushLocalUndo (componentProvisions component) accumulator undo) view)
      0 effectResolved : resolveEffectValues @{keyEq}
        (dependencies (componentDependencies component)) view
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) = Just capability
      effectResolved = trans
        (resolveEffectValuesProjected nameEq keyEq
          (dependencies (componentDependencies component)) view
          (MkSystemState ambient fibers)) resolved
      0 mapRuns : partialEffectMapFor nameEq keyEq (LAdvance actor) LIterTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (setEffectTable @{nameEq} actor
          (ownedValues (localTable localAfter))
          (setEffectAmbient (localWorld localAfter)
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)))))
      mapRuns = partialEffectMapAdvanceIterRuns nameEq keyEq actor ambient
        fibers component parent retiredFlag table step (nextStep :: more)
        accumulator view capability sourceFound effectResolved localAfter undo ran
      0 tableSame : (k : key) ->
        lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
        lookupBinding @{keyEq} k (ownedValues (localTable localAfter))
      tableSame k = runtimeTableLookup keyEq k sourceFiber
        (localTable localAfter)
        (Reloading (nextStep :: more) (pushLocalUndo (componentProvisions component) accumulator undo) view)
  in runtimeReplaceActualEffectFrame nameEq keyEq (LAdvance actor) LIterTag
    actor ambient (localWorld localAfter) sourceFiber next fibers afterState
    sourceFound (ownedValues (localTable localAfter)) tableSame concreteAfter
    mapRuns

||| Effectful landing-L-Divert branch after a successful iterator step observes
||| a stale target and lands Unloading with the yielded effect state.
public export
0 landingDivertActualEffectFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  (resolved : resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view fibers =
    Just capability) ->
  (localAfter : LocalState key value world (componentProvisions component)) ->
  (undo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (ran : runStepEffect step capability
    (MkLocalState ambient
      (restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table))) = Right (localAfter, undo)) ->
  (matches : targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table
        (Reloading (step :: rest) accumulator view)) fibers) view = False) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view))) ->
  (afterState : SystemState name key value world error) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState (localWorld localAfter)
        (replaceBinding @{nameEq} actor
          (setFiberRuntime
            (MkFiber component parent retiredFlag table
              (Reloading (step :: rest) accumulator view))
            (localTable localAfter)
            (Unloading (pushLocalUndo (componentProvisions component) accumulator undo) view Nothing)) fibers))) = afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) LDivertTag
    (MkSystemState ambient fibers) afterState
landingDivertActualEffectFrame nameEq keyEq actor ambient fibers component parent
  retiredFlag table step rest accumulator view capability resolved localAfter undo
  ran matches sourceFound afterState concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Reloading (step :: rest) accumulator view)
      next : Fiber name key value world error
      next = setFiberRuntime sourceFiber (localTable localAfter)
        (Unloading (pushLocalUndo (componentProvisions component) accumulator undo) view Nothing)
      0 effectResolved : resolveEffectValues @{keyEq}
        (dependencies (componentDependencies component)) view
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) = Just capability
      effectResolved = trans
        (resolveEffectValuesProjected nameEq keyEq
          (dependencies (componentDependencies component)) view
          (MkSystemState ambient fibers)) resolved
      0 iterMapRuns : partialEffectMapFor nameEq keyEq (LAdvance actor) LIterTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (setEffectTable @{nameEq} actor
          (ownedValues (localTable localAfter))
          (setEffectAmbient (localWorld localAfter)
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)))))
      iterMapRuns = partialEffectMapAdvanceIterRuns nameEq keyEq actor ambient
        fibers component parent retiredFlag table step rest accumulator view
        capability sourceFound effectResolved localAfter undo ran
      0 mapRuns : partialEffectMapFor nameEq keyEq (LAdvance actor) LDivertTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (setEffectTable @{nameEq} actor
          (ownedValues (localTable localAfter))
          (setEffectAmbient (localWorld localAfter)
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)))))
      mapRuns = trans
        (advanceDivertMapSameAsIter nameEq keyEq actor
          (MkSystemState ambient fibers)
          (projectEffectState @{nameEq} (MkSystemState ambient fibers))) iterMapRuns
      0 tableSame : (k : key) ->
        lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
        lookupBinding @{keyEq} k (ownedValues (localTable localAfter))
      tableSame k = runtimeTableLookup keyEq k sourceFiber
        (localTable localAfter) (Unloading (pushLocalUndo (componentProvisions component) accumulator undo) view Nothing)
  in runtimeReplaceActualEffectFrame nameEq keyEq (LAdvance actor) LDivertTag
    actor ambient (localWorld localAfter) sourceFiber next fibers afterState
    sourceFound (ownedValues (localTable localAfter)) tableSame concreteAfter
    mapRuns

public export
0 landingDivertEmptyActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceFound : lookupFiber @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading [] accumulator view))) ->
  (afterState : SystemState name key value world error) ->
  (concreteAfter :
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor
          (setFiberLifecycle
            (MkFiber component parent retiredFlag table
              (Reloading [] accumulator view))
            (Unloading accumulator view Nothing)) fibers))) = afterState) ->
  ActualEffectFrame nameEq keyEq (LAdvance actor) LDivertTag
    (MkSystemState ambient fibers) afterState
landingDivertEmptyActualEffectFrame nameEq keyEq actor ambient fibers component
  parent retiredFlag table accumulator view sourceFound afterState concreteAfter =
  let sourceFiber : Fiber name key value world error
      sourceFiber = MkFiber component parent retiredFlag table
        (Reloading [] accumulator view)
      next : Fiber name key value world error
      next = setFiberLifecycle sourceFiber (Unloading accumulator view Nothing)
      0 nextShape : next = setFiberLifecycle sourceFiber
        (Unloading accumulator view Nothing)
      nextShape = Refl
      0 tableSame : (k : key) ->
        lookupBinding @{keyEq} k (ownedValues (fiberTable next)) =
        lookupBinding @{keyEq} k (ownedValues (fiberTable sourceFiber))
      tableSame k = trans
        (cong (\observed => lookupBinding @{keyEq} k
          (ownedValues (fiberTable observed))) nextShape)
        (setLifecycleTableLookup keyEq k sourceFiber
          (Unloading accumulator view Nothing))
      0 identityMap : partialEffectMapFor nameEq keyEq (LAdvance actor)
        LDivertTag
        (the (SystemState name key value world error)
          (MkSystemState ambient fibers))
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers))) =
        Just (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient fibers)))
      identityMap = rewrite sourceFound in Refl
  in controlReplaceActualEffectFrame nameEq keyEq (LAdvance actor) LDivertTag
    actor ambient sourceFiber next fibers afterState sourceFound tableSame
    concreteAfter identityMap
