module DGamma.CP4DeletionRelatedLifecycleEffectMap

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionRelationalActionCore
import DGamma.Unified
import Decidable.Equality

%default total

0 partialRelatedTransport :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state relation leftBefore rightBefore ->
  PartialRelated state relation leftAfter rightAfter
partialRelatedTransport Refl Refl related = related

0 advanceAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just fiber ->
  (state : EffectState name key value world) ->
  advanceRuntimeEffectMap nameEq keyEq actor
    (the (SystemState name key value world error)
      (MkSystemState ambient fibers)) state =
    fiberAdvanceRuntimeEffectMap nameEq keyEq actor fiber state
advanceAtFound nameEq keyEq actor ambient fibers fiber found state =
  rewrite found in Refl

0 unloadAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just fiber ->
  (state : EffectState name key value world) ->
  unloadRuntimeEffectMap nameEq keyEq actor
    (the (SystemState name key value world error)
      (MkSystemState ambient fibers)) state =
    fiberUnloadRuntimeEffectMap nameEq keyEq actor fiber state
unloadAtFound nameEq keyEq actor ambient fibers fiber found state =
  rewrite found in Refl

0 relatedFiberAdvanceOutputs :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (left, right : Fiber name key value world error) ->
  FiberControlRelated left right ->
  (state : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (fiberAdvanceRuntimeEffectMap nameEq keyEq actor left state)
    (fiberAdvanceRuntimeEffectMap nameEq keyEq actor right state)
relatedFiberAdvanceOutputs nameEq keyEq actor left right related state =
  case related of
    FibersControlRelated {component} leftParent rightParent leftRetired
      rightRetired leftTable rightTable leftLifecycle rightLifecycle parentSame
      retiredSame lifecycleSame => advanceByLifecycle lifecycleSame
  where
  0 advanceByLifecycle :
    {component : Component key value world error} ->
    {leftParent, rightParent : Parent name} ->
    {leftRetired, rightRetired : Bool} ->
    {leftTable, rightTable : OwnedTable key value
      (componentProvisions component)} ->
    {leftLifecycle, rightLifecycle : Lifecycle key value world error name
      (dependencies (componentDependencies component))
      (componentProvisions component)} ->
    LifecycleControlRelated leftLifecycle rightLifecycle ->
    PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
      (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
        (MkFiber component leftParent leftRetired leftTable leftLifecycle) state)
      (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
        (MkFiber component rightParent rightRetired rightTable rightLifecycle)
        state)
  advanceByLifecycle (InactiveControls outcomeSame) = PartialUndefined
  advanceByLifecycle (ActiveControls accumulatorsSame viewsSame) =
    PartialUndefined
  advanceByLifecycle (UnloadingControls accumulatorsSame viewsSame outcomesSame) =
    PartialUndefined
  advanceByLifecycle
    (ReloadingControls {leftRemaining} {rightRemaining} {leftView} {rightView}
      remainingSame accumulatorsSame viewsSame) =
        rewrite remainingSame in rewrite viewsSame in
          advanceRemaining rightRemaining rightView
    where
    0 advanceRemaining :
      (remaining : List (StepEffect key value world error
        (dependencies (componentDependencies component))
        (componentProvisions component))) ->
      (view : View name (dependencies (componentDependencies component))) ->
      PartialRelated (EffectState name key value world)
        (EffectStateRelated keyEq)
        (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
          (MkFiber component leftParent leftRetired leftTable
            (Reloading remaining leftAccumulator view)) state)
        (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
          (MkFiber component rightParent rightRetired rightTable
            (Reloading remaining rightAccumulator view)) state)
    advanceRemaining [] view = PartialDefined (effectStateReflexive keyEq state)
    advanceRemaining (step :: rest) view
      with (resolveEffectValues @{keyEq}
        (dependencies (componentDependencies component)) view state)
      advanceRemaining (step :: rest) view | Nothing = PartialUndefined
      advanceRemaining (step :: rest) view | Just capability
        with (runStepEffect step capability
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq}
              (componentProvisions component) (effectTables state actor))))
        advanceRemaining (step :: rest) view | Just capability |
          Left failure = PartialUndefined
        advanceRemaining (step :: rest) view | Just capability |
          Right (after, undo) =
            PartialDefined (effectStateReflexive keyEq
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) state)))

0 relatedAccumulatorOutputs :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (leftAccumulator, rightAccumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  AccumulatorRelated leftAccumulator rightAccumulator ->
  (state : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (accumulatorRuntimeEffectMap nameEq keyEq actor leftAccumulator state)
    (accumulatorRuntimeEffectMap nameEq keyEq actor rightAccumulator state)
relatedAccumulatorOutputs nameEq keyEq actor provision leftAccumulator
  rightAccumulator accumulatorsSame state =
    let restoredRelated = accumulatorsSame
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor)))
        ambientRelated = setRelatedEffectAmbient keyEq
          (localWorld (leftAccumulator
            (MkLocalState (effectAmbient state)
              (restrictOwnedPreservingOrder @{keyEq} provision
                (effectTables state actor)))))
          (localWorld (rightAccumulator
            (MkLocalState (effectAmbient state)
              (restrictOwnedPreservingOrder @{keyEq} provision
                (effectTables state actor)))))
          (localAmbientExact restoredRelated) (effectStateReflexive keyEq state)
        outputRelated = setRelatedEffectTables nameEq keyEq actor
          (ownedValues (localTable (leftAccumulator
            (MkLocalState (effectAmbient state)
              (restrictOwnedPreservingOrder @{keyEq} provision
                (effectTables state actor))))))
          (ownedValues (localTable (rightAccumulator
            (MkLocalState (effectAmbient state)
              (restrictOwnedPreservingOrder @{keyEq} provision
                (effectTables state actor))))))
          (localBindingsExact restoredRelated) ambientRelated
    in PartialDefined outputRelated

0 relatedFiberUnloadOutputs :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (left, right : Fiber name key value world error) ->
  FiberControlRelated left right ->
  (state : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (fiberUnloadRuntimeEffectMap nameEq keyEq actor left state)
    (fiberUnloadRuntimeEffectMap nameEq keyEq actor right state)
relatedFiberUnloadOutputs nameEq keyEq actor left right related state =
  case related of
    FibersControlRelated {component} leftParent rightParent leftRetired
      rightRetired leftTable rightTable leftLifecycle rightLifecycle parentSame
      retiredSame lifecycleSame => unloadByLifecycle lifecycleSame
  where
  0 unloadByLifecycle :
    {component : Component key value world error} ->
    {leftParent, rightParent : Parent name} ->
    {leftRetired, rightRetired : Bool} ->
    {leftTable, rightTable : OwnedTable key value
      (componentProvisions component)} ->
    {leftLifecycle, rightLifecycle : Lifecycle key value world error name
      (dependencies (componentDependencies component))
      (componentProvisions component)} ->
    LifecycleControlRelated leftLifecycle rightLifecycle ->
    PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
      (fiberUnloadRuntimeEffectMap nameEq keyEq actor
        (MkFiber component leftParent leftRetired leftTable leftLifecycle) state)
      (fiberUnloadRuntimeEffectMap nameEq keyEq actor
        (MkFiber component rightParent rightRetired rightTable rightLifecycle)
        state)
  unloadByLifecycle (InactiveControls outcomeSame) = PartialUndefined
  unloadByLifecycle (ActiveControls accumulatorsSame viewsSame) = PartialUndefined
  unloadByLifecycle (ReloadingControls remainingSame accumulatorsSame viewsSame) =
    PartialUndefined
  unloadByLifecycle
    (UnloadingControls {leftAccumulator} {rightAccumulator} accumulatorsSame
      viewsSame outcomesSame) =
      relatedAccumulatorOutputs nameEq keyEq actor
        (componentProvisions component) leftAccumulator rightAccumulator
        accumulatorsSame state

||| Cross-origin Table-1 output relation for two fully related lifecycle owner
||| cells, evaluated at the same effect state.  This is the effect/control join
||| used after the selected accumulator transposition.
public export
0 relatedLifecyclePartialMapOutputs :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (tag : RuleTag) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftOwner, rightOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action) leftRegistry = Just leftOwner ->
  lookupFiber @{nameEq} (actionOwner action) rightRegistry = Just rightOwner ->
  FiberControlRelated leftOwner rightOwner ->
  (state : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (partialEffectMapFor nameEq keyEq action tag
      (MkSystemState leftWorld leftRegistry) state)
    (partialEffectMapFor nameEq keyEq action tag
      (MkSystemState rightWorld rightRegistry) state)
relatedLifecyclePartialMapOutputs nameEq keyEq
  (OInsert actor parent component) Refl tag leftWorld rightWorld leftRegistry
  rightRegistry leftOwner rightOwner leftFound rightFound owners state impossible
relatedLifecyclePartialMapOutputs nameEq keyEq (ORetire actor) Refl tag leftWorld
  rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound rightFound
  owners state impossible
relatedLifecyclePartialMapOutputs nameEq keyEq (ORemove actor) Refl tag leftWorld
  rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound rightFound
  owners state impossible
relatedLifecyclePartialMapOutputs nameEq keyEq (LBegin actor) lifecycle tag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle LRaiseTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle LIterTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = partialRelatedTransport
    (sym (advanceAtFound nameEq keyEq actor leftWorld leftRegistry leftOwner leftFound
      state))
    (sym (advanceAtFound nameEq keyEq actor rightWorld rightRegistry rightOwner
      rightFound state))
    (relatedFiberAdvanceOutputs nameEq keyEq actor leftOwner rightOwner owners state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle
  LFinishTag leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner
  leftFound rightFound owners state = partialRelatedTransport
    (sym (advanceAtFound nameEq keyEq actor leftWorld leftRegistry leftOwner leftFound
      state))
    (sym (advanceAtFound nameEq keyEq actor rightWorld rightRegistry rightOwner
      rightFound state))
    (relatedFiberAdvanceOutputs nameEq keyEq actor leftOwner rightOwner owners state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle
  LDivertTag leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner
  leftFound rightFound owners state = partialRelatedTransport
    (sym (advanceAtFound nameEq keyEq actor leftWorld leftRegistry leftOwner leftFound
      state))
    (sym (advanceAtFound nameEq keyEq actor rightWorld rightRegistry rightOwner
      rightFound state))
    (relatedFiberAdvanceOutputs nameEq keyEq actor leftOwner rightOwner owners state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle OInsertTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle ORetireTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle ORemoveTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle LBeginTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle LLeaveTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LAdvance actor) lifecycle LUnloadTag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LDivert actor) lifecycle tag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LLeave actor) lifecycle tag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = PartialDefined (effectStateReflexive keyEq state)
relatedLifecyclePartialMapOutputs nameEq keyEq (LUnload actor) lifecycle tag
  leftWorld rightWorld leftRegistry rightRegistry leftOwner rightOwner leftFound
  rightFound owners state = partialRelatedTransport
    (sym (unloadAtFound nameEq keyEq actor leftWorld leftRegistry leftOwner leftFound
      state))
    (sym (unloadAtFound nameEq keyEq actor rightWorld rightRegistry rightOwner
      rightFound state))
    (relatedFiberUnloadOutputs nameEq keyEq actor leftOwner rightOwner owners state)
