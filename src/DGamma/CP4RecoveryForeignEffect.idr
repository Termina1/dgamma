module DGamma.CP4RecoveryForeignEffect

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Decidable.Equality

%default total

0 equalEffectStatesPreserveBindings :
  (selected : name) -> (left, right : EffectState name key value world) ->
  left = right ->
  bindings (effectTables left selected) = bindings (effectTables right selected)
equalEffectStatesPreserveBindings selected left right same = cong
  (\state => bindings (effectTables state selected)) same

0 setOtherActorPreservesBindings :
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (selected = actor) -> (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  bindings (effectTables (setEffectTable @{nameEq} actor table state) selected) =
  bindings (effectTables state selected)
setOtherActorPreservesBindings nameEq selected actor distinct table state
  with (decEq @{nameEq} selected actor)
  setOtherActorPreservesBindings nameEq actor actor distinct table state |
    Yes Refl = void (distinct Refl)
  setOtherActorPreservesBindings nameEq selected actor distinct table state |
    No different = Refl

0 stepForwardForeignPreservesBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (selected = actor) ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) ->
  (state, moved : EffectState name key value world) ->
  stepForwardEffectMap nameEq keyEq actor step capability state = Just moved ->
  bindings (effectTables moved selected) = bindings (effectTables state selected)
stepForwardForeignPreservesBindings nameEq keyEq selected actor distinct step
  capability state moved equation
  with (runStepEffect step capability
    (MkLocalState (effectAmbient state)
      (restrictOwnedPreservingOrder @{keyEq} provision
        (effectTables state actor))))
  stepForwardForeignPreservesBindings nameEq keyEq selected actor distinct step
    capability state moved equation | Left err = void (nothingIsNotJust equation)
  stepForwardForeignPreservesBindings nameEq keyEq selected actor distinct step
    capability state moved equation | Right (after, undo) =
      let 0 concreteIsMoved :
            (setEffectTable @{nameEq} actor (ownedValues (localTable after))
               (setEffectAmbient (localWorld after) state) = moved)
          concreteIsMoved = justInjective equation
          0 concretePreserves : bindings (effectTables
            (setEffectTable @{nameEq} actor (ownedValues (localTable after))
              (setEffectAmbient (localWorld after) state)) selected) =
            bindings (effectTables state selected)
          concretePreserves = setOtherActorPreservesBindings nameEq selected actor
            distinct (ownedValues (localTable after))
            (setEffectAmbient (localWorld after) state)
      in replace
        {p = \observed => bindings (effectTables observed selected) =
          bindings (effectTables state selected)}
        concreteIsMoved concretePreserves

0 advanceForeignPreservesBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (selected = actor) ->
  (origin : SystemState name key value world error) ->
  (state, moved : EffectState name key value world) ->
  advanceRuntimeEffectMap nameEq keyEq actor origin state = Just moved ->
  bindings (effectTables moved selected) = bindings (effectTables state selected)
advanceForeignPreservesBindings nameEq keyEq selected actor distinct
  (MkSystemState ambient fibers) state moved equation
  with (lookupFiber @{nameEq} actor fibers)
  advanceForeignPreservesBindings nameEq keyEq selected actor distinct
    (MkSystemState ambient fibers) state moved equation | Nothing =
      void (nothingIsNotJust equation)
  advanceForeignPreservesBindings nameEq keyEq selected actor distinct
    (MkSystemState ambient fibers) state moved equation | Just fiber
    with (fiberLifecycle fiber)
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Reloading [] accumulator view = equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Reloading (step :: rest) accumulator view
      with (resolveEffectValues @{keyEq}
        (dependencies (componentDependencies (fiberComponent fiber))) view state)
      advanceForeignPreservesBindings nameEq keyEq selected actor distinct
        (MkSystemState ambient fibers) state moved equation | Just fiber |
        Reloading (step :: rest) accumulator view | Nothing =
          void (nothingIsNotJust equation)
      advanceForeignPreservesBindings nameEq keyEq selected actor distinct
        (MkSystemState ambient fibers) state moved equation | Just fiber |
        Reloading (step :: rest) accumulator view | Just capability =
          stepForwardForeignPreservesBindings nameEq keyEq selected actor distinct
            step capability state moved equation

public export
0 accumulatorForeignPreservesBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (selected = actor) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (state, moved : EffectState name key value world) ->
  accumulatorRuntimeEffectMap nameEq keyEq actor accumulator state = Just moved ->
  bindings (effectTables moved selected) = bindings (effectTables state selected)
accumulatorForeignPreservesBindings nameEq keyEq selected actor distinct provision
  accumulator state moved equation =
    let owned : OwnedTable key value provision
        owned = restrictOwnedPreservingOrder @{keyEq} provision
          (effectTables state actor)
        restored : LocalState key value world provision
        restored = accumulator (MkLocalState (effectAmbient state) owned)
        0 concreteIsMoved :
          (setEffectTable @{nameEq} actor (ownedValues (localTable restored))
             (setEffectAmbient (localWorld restored) state) = moved)
        concreteIsMoved = justInjective equation
        0 concretePreserves : bindings (effectTables
          (setEffectTable @{nameEq} actor (ownedValues (localTable restored))
            (setEffectAmbient (localWorld restored) state)) selected) =
          bindings (effectTables state selected)
        concretePreserves = setOtherActorPreservesBindings nameEq selected actor
          distinct (ownedValues (localTable restored))
          (setEffectAmbient (localWorld restored) state)
    in replace
      {p = \observed => bindings (effectTables observed selected) =
        bindings (effectTables state selected)}
      concreteIsMoved concretePreserves

public export
0 accumulatorEffectMapForeignPreservesBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (selected = actor) ->
  (handle : AccumulatorHandle key value world) ->
  (state, moved : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq actor handle state = Just moved ->
  bindings (effectTables moved selected) = bindings (effectTables state selected)
accumulatorEffectMapForeignPreservesBindings nameEq keyEq selected actor distinct
  (MkAccumulatorHandle provision captured accumulator) state moved equation =
    accumulatorForeignPreservesBindings nameEq keyEq selected actor distinct
      provision accumulator state moved equation

0 unloadForeignPreservesBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (selected = actor) ->
  (origin : SystemState name key value world error) ->
  (state, moved : EffectState name key value world) ->
  unloadRuntimeEffectMap nameEq keyEq actor origin state = Just moved ->
  bindings (effectTables moved selected) = bindings (effectTables state selected)
unloadForeignPreservesBindings nameEq keyEq selected actor distinct
  (MkSystemState ambient fibers) state moved equation
  with (lookupFiber @{nameEq} actor fibers)
  unloadForeignPreservesBindings nameEq keyEq selected actor distinct
    (MkSystemState ambient fibers) state moved equation | Nothing =
      void (nothingIsNotJust equation)
  unloadForeignPreservesBindings nameEq keyEq selected actor distinct
    (MkSystemState ambient fibers) state moved equation | Just fiber
    with (fiberLifecycle fiber)
    unloadForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    unloadForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    unloadForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    unloadForeignPreservesBindings nameEq keyEq selected actor distinct
      (MkSystemState ambient fibers) state moved equation | Just fiber |
      Unloading accumulator view outcome =
        accumulatorForeignPreservesBindings nameEq keyEq selected actor distinct
          (componentProvisions (fiberComponent fiber)) accumulator state moved
          equation

public export
0 partialEffectMapForForeignPreservesBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (action : Action name key value world error) ->
  Not (selected = actionOwner action) -> (tag : RuleTag) ->
  (origin : SystemState name key value world error) ->
  (state, moved : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq action tag origin state = Just moved ->
  bindings (effectTables moved selected) = bindings (effectTables state selected)
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (OInsert actor parent component) distinct tag origin state moved equation =
    let 0 concreteIsMoved :
          (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value}) state = moved)
        concreteIsMoved = justInjective equation
        0 concretePreserves : bindings (effectTables
          (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value}) state) selected) =
          bindings (effectTables state selected)
        concretePreserves = setOtherActorPreservesBindings nameEq selected actor
          distinct (emptyContext {key = key} {value = value}) state
    in replace
      {p = \observed => bindings (effectTables observed selected) =
        bindings (effectTables state selected)}
      concreteIsMoved concretePreserves
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (ORemove actor) distinct tag origin state moved equation =
    let 0 concreteIsMoved :
          (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value}) state = moved)
        concreteIsMoved = justInjective equation
        0 concretePreserves : bindings (effectTables
          (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value}) state) selected) =
          bindings (effectTables state selected)
        concretePreserves = setOtherActorPreservesBindings nameEq selected actor
          distinct (emptyContext {key = key} {value = value}) state
    in replace
      {p = \observed => bindings (effectTables observed selected) =
        bindings (effectTables state selected)}
      concreteIsMoved concretePreserves
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LRaiseTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LIterTag origin state moved equation =
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct origin
      state moved equation
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LFinishTag origin state moved equation =
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct origin
      state moved equation
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LDivertTag origin state moved equation =
    advanceForeignPreservesBindings nameEq keyEq selected actor distinct origin
      state moved equation
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct OInsertTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct ORetireTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct ORemoveTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LBeginTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LLeaveTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LAdvance actor) distinct LUnloadTag origin state moved equation =
    equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LUnload actor) distinct tag origin state moved equation =
    unloadForeignPreservesBindings nameEq keyEq selected actor distinct origin
      state moved equation
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (ORetire actor) distinct tag origin state moved equation = equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LBegin actor) distinct tag origin state moved equation = equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LDivert actor) distinct tag origin state moved equation = equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
partialEffectMapForForeignPreservesBindings nameEq keyEq selected
  (LLeave actor) distinct tag origin state moved equation = equalEffectStatesPreserveBindings selected moved state (sym (justInjective equation))
