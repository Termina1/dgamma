module DGamma.CP4RecoveryEffectRespect

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Decidable.Equality

%default total

public export
EffectPartialMapRespects :
  {name, key, world : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> PartialEffectMap name key value world -> Type
EffectPartialMapRespects {name} {key} {world} {value} keyEq effectMap =
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (effectMap left) (effectMap right)

0 setActorRuntimeRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (worldValue : world) -> (table : CoeffectContext key value) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor table
      (setEffectAmbient worldValue left))
    (setEffectTable @{nameEq} actor table
      (setEffectAmbient worldValue right))
setActorRuntimeRelated nameEq keyEq actor worldValue table left right related =
  MkEffectStateRelated Refl tables
  where
  0 tables : (selected : name) ->
    effectTables
      (setEffectTable @{nameEq} actor table
        (setEffectAmbient worldValue left)) selected =
    effectTables
      (setEffectTable @{nameEq} actor table
        (setEffectAmbient worldValue right)) selected
  tables selected with (decEq @{nameEq} selected actor) proof decision
    tables selected | Yes same = case same of Refl => Refl
    tables selected | No distinct = tablesExact related selected

0 setActorTableRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (table : CoeffectContext key value) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor table left)
    (setEffectTable @{nameEq} actor table right)
setActorTableRelated nameEq keyEq actor table left right related =
  MkEffectStateRelated (ambientExact related) tables
  where
  0 tables : (selected : name) ->
    effectTables (setEffectTable @{nameEq} actor table left) selected =
    effectTables (setEffectTable @{nameEq} actor table right) selected
  tables selected with (decEq @{nameEq} selected actor) proof decision
    tables selected | Yes same = case same of Refl => Refl
    tables selected | No distinct = tablesExact related selected

public export
0 resolveEffectValuesRelated :
  (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  {left, right : EffectState name key value world} ->
  EffectStateRelated keyEq left right ->
  resolveEffectValues @{keyEq} deps view left =
  resolveEffectValues @{keyEq} deps view right
resolveEffectValuesRelated keyEq [] EmptyView related = Refl
resolveEffectValuesRelated keyEq (k :: ks) (ProviderView provider rest) related
  with (lookupBinding @{keyEq} k (effectTables left provider)) proof leftLookup
  resolveEffectValuesRelated keyEq (k :: ks) (ProviderView provider rest)
    related | Nothing =
      let headSame = cong (lookupBinding @{keyEq} k)
            (tablesExact related provider)
          rightLookup = trans (sym headSame) leftLookup
      in rewrite rightLookup in Refl
  resolveEffectValuesRelated keyEq (k :: ks) (ProviderView provider rest)
    related | Just v =
      let headSame = cong (lookupBinding @{keyEq} k)
            (tablesExact related provider)
          rightLookup = trans (sym headSame) leftLookup
      in rewrite rightLookup in cong (map (OneDepValue v))
        (resolveEffectValuesRelated keyEq ks rest related)

successfulAdvanceMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  Fiber name key value world error -> PartialEffectMap name key value world
successfulAdvanceMap = fiberAdvanceRuntimeEffectMap

0 stepForwardMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (stepForwardEffectMap nameEq keyEq actor step capability left)
    (stepForwardEffectMap nameEq keyEq actor step capability right)
stepForwardMapRespects nameEq keyEq actor step capability left right related =
  let 0 localSame :
        (MkLocalState (effectAmbient left)
           (restrictOwnedPreservingOrder @{keyEq} provision
             (effectTables left actor)) =
         MkLocalState (effectAmbient right)
           (restrictOwnedPreservingOrder @{keyEq} provision
             (effectTables right actor)))
      localSame = rewrite ambientExact related in
        rewrite tablesExact related actor in Refl
  in stepRuns localSame
  where
  0 stepRuns :
    (localSame :
      MkLocalState (effectAmbient left)
          (restrictOwnedPreservingOrder @{keyEq} provision
            (effectTables left actor)) =
      MkLocalState (effectAmbient right)
          (restrictOwnedPreservingOrder @{keyEq} provision
            (effectTables right actor))) ->
    PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
      (stepForwardEffectMap nameEq keyEq actor step capability left)
      (stepForwardEffectMap nameEq keyEq actor step capability right)
  stepRuns localSame
    with (runStepEffect step capability
      (MkLocalState (effectAmbient left)
        (restrictOwnedPreservingOrder @{keyEq} provision
          (effectTables left actor)))) proof leftRan
    stepRuns localSame | Left err =
      let runSame = cong (runStepEffect step capability) localSame
          rightRan = trans (sym runSame) leftRan
      in rewrite rightRan in PartialUndefined
    stepRuns localSame | Right (after, undo) =
      let runSame = cong (runStepEffect step capability) localSame
          rightRan = trans (sym runSame) leftRan
      in rewrite rightRan in
        PartialDefined (setActorRuntimeRelated nameEq keyEq actor
          (localWorld after) (ownedValues (localTable after)) left right related)

0 successfulAdvanceMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (successfulAdvanceMap nameEq keyEq actor fiber left)
    (successfulAdvanceMap nameEq keyEq actor fiber right)
successfulAdvanceMapRespects nameEq keyEq actor fiber left right related
  with (fiberLifecycle fiber)
  successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
    Inactive outcome = PartialUndefined
  successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
    Active accumulator view = PartialUndefined
  successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
    Unloading accumulator view outcome = PartialUndefined
  successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
    Reloading [] accumulator view = PartialDefined related
  successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
    Reloading (step :: rest) accumulator view
    with (resolveEffectValues @{keyEq}
      (dependencies (componentDependencies (fiberComponent fiber))) view left)
      proof leftResolved
    successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
      Reloading (step :: rest) accumulator view | Nothing =
        let resolvedSame = resolveEffectValuesRelated keyEq
              (dependencies (componentDependencies (fiberComponent fiber))) view
              related
            rightResolved = trans (sym resolvedSame) leftResolved
        in rewrite rightResolved in PartialUndefined
    successfulAdvanceMapRespects nameEq keyEq actor fiber left right related |
      Reloading (step :: rest) accumulator view | Just capability =
        let resolvedSame = resolveEffectValuesRelated keyEq
              (dependencies (componentDependencies (fiberComponent fiber))) view
              related
            rightResolved = trans (sym resolvedSame) leftResolved
        in rewrite rightResolved in
          stepForwardMapRespects nameEq keyEq actor step capability left right
            related

0 advanceRuntimeMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (origin : SystemState name key value world error) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (advanceRuntimeEffectMap nameEq keyEq actor origin left)
    (advanceRuntimeEffectMap nameEq keyEq actor origin right)
advanceRuntimeMapRespects nameEq keyEq actor (MkSystemState ambient fibers) left
  right related with (lookupFiber @{nameEq} actor fibers)
  advanceRuntimeMapRespects nameEq keyEq actor (MkSystemState ambient fibers)
    left right related | Nothing = PartialUndefined
  advanceRuntimeMapRespects nameEq keyEq actor (MkSystemState ambient fibers)
    left right related | Just fiber =
      successfulAdvanceMapRespects nameEq keyEq actor fiber left right related

unloadEffectMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  Fiber name key value world error -> PartialEffectMap name key value world
unloadEffectMap = fiberUnloadRuntimeEffectMap

0 unloadMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (unloadEffectMap nameEq keyEq actor fiber left)
    (unloadEffectMap nameEq keyEq actor fiber right)
unloadMapRespects nameEq keyEq actor fiber left right related
  with (fiberLifecycle fiber)
  unloadMapRespects nameEq keyEq actor fiber left right related |
    Inactive outcome = PartialUndefined
  unloadMapRespects nameEq keyEq actor fiber left right related |
    Reloading remaining accumulator view = PartialUndefined
  unloadMapRespects nameEq keyEq actor fiber left right related |
    Active accumulator view = PartialUndefined
  unloadMapRespects nameEq keyEq actor fiber left right related |
    Unloading accumulator view outcome =
      let actorTableSame = tablesExact related actor
          ambientSame = ambientExact related
          0 localSame :
            (MkLocalState (effectAmbient left)
               (restrictOwnedPreservingOrder @{keyEq}
                 (componentProvisions (fiberComponent fiber))
                 (effectTables left actor)) =
             MkLocalState (effectAmbient right)
               (restrictOwnedPreservingOrder @{keyEq}
                 (componentProvisions (fiberComponent fiber))
                 (effectTables right actor)))
          localSame = rewrite ambientSame in rewrite actorTableSame in Refl
          0 restoredSame :
            (accumulator
               (MkLocalState (effectAmbient left)
                 (restrictOwnedPreservingOrder @{keyEq}
                   (componentProvisions (fiberComponent fiber))
                   (effectTables left actor))) =
             accumulator
               (MkLocalState (effectAmbient right)
                 (restrictOwnedPreservingOrder @{keyEq}
                   (componentProvisions (fiberComponent fiber))
                   (effectTables right actor))))
          restoredSame = cong accumulator localSame
      in rewrite sym restoredSame in
        PartialDefined (setActorRuntimeRelated nameEq keyEq actor
          (localWorld (accumulator
            (MkLocalState (effectAmbient left)
              (restrictOwnedPreservingOrder @{keyEq}
                (componentProvisions (fiberComponent fiber))
                (effectTables left actor)))))
          (ownedValues (localTable (accumulator
            (MkLocalState (effectAmbient left)
              (restrictOwnedPreservingOrder @{keyEq}
                (componentProvisions (fiberComponent fiber))
                (effectTables left actor))))))
          left right related)

0 unloadRuntimeMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (origin : SystemState name key value world error) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (unloadRuntimeEffectMap nameEq keyEq actor origin left)
    (unloadRuntimeEffectMap nameEq keyEq actor origin right)
unloadRuntimeMapRespects nameEq keyEq actor (MkSystemState ambient fibers) left
  right related with (lookupFiber @{nameEq} actor fibers)
  unloadRuntimeMapRespects nameEq keyEq actor (MkSystemState ambient fibers)
    left right related | Nothing = PartialUndefined
  unloadRuntimeMapRespects nameEq keyEq actor (MkSystemState ambient fibers)
    left right related | Just fiber =
      unloadMapRespects nameEq keyEq actor fiber left right related

||| Finding #10's central congruence: every Table-1 partial effect map respects
||| exact ordered effect-state equality. No callback respect premise is needed,
||| because related inputs now contain exactly equal ambient values and complete
||| actor tables, hence the executable callback receives equal `LocalState`s.
public export
0 partialEffectMapForRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (origin : SystemState name key value world error) ->
  EffectPartialMapRespects keyEq
    (partialEffectMapFor nameEq keyEq action tag origin)
partialEffectMapForRespects nameEq keyEq (OInsert actor parent component) tag
  origin left right related =
    PartialDefined (setActorTableRelated nameEq keyEq actor emptyContext left
      right related)
partialEffectMapForRespects nameEq keyEq (ORemove actor) tag origin left right
  related = PartialDefined (setActorTableRelated nameEq keyEq actor emptyContext
    left right related)
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LRaiseTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LIterTag origin
  left right related =
    advanceRuntimeMapRespects nameEq keyEq actor origin left right related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LFinishTag origin
  left right related =
    advanceRuntimeMapRespects nameEq keyEq actor origin left right related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LDivertTag origin
  left right related =
    advanceRuntimeMapRespects nameEq keyEq actor origin left right related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) OInsertTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) ORetireTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) ORemoveTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LBeginTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LLeaveTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LAdvance actor) LUnloadTag origin left
  right related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LUnload actor) tag origin left right
  related = unloadRuntimeMapRespects nameEq keyEq actor origin left right related
partialEffectMapForRespects nameEq keyEq (ORetire actor) tag origin left right
  related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LBegin actor) tag origin left right
  related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LDivert actor) tag origin left right
  related = PartialDefined related
partialEffectMapForRespects nameEq keyEq (LLeave actor) tag origin left right
  related = PartialDefined related

public export
0 partialEffectMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  EffectPartialMapRespects keyEq
    (partialEffectMap
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked))
partialEffectMapRespects nameEq keyEq action tag before afterState checked =
  partialEffectMapForRespects nameEq keyEq action tag before
