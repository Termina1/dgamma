module DGamma.R39RelationalHeadProducerPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP4DeletionRelatedLifecycleEffectMap
import DGamma.CP4RecoveryEffectRespect
import DGamma.R39RelationalMapAlgebraPositive
import Decidable.Equality

%default total

||| Definition-only bridge used by all six already-closed head producers.  The
||| exact retained proof is consumed together with the target transition's
||| established respectfulness; no dictionary equality is assumed.
public export
0 r39TransitionExactMapGivesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39TransitionExactMapGivesRelated source target targetRespects exact =
  r39ExactMapsGivePartialMapsRelated (partialEffectMap source)
    (partialEffectMap target) targetRespects exact

public export
0 r39InsertProducerSuppliesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  transitionAction source = OInsert actor parent component ->
  transitionAction target = OInsert actor parent component ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39InsertProducerSuppliesRelated source target sourceAction targetAction =
  r39TransitionExactMapGivesRelated source target

public export
0 r39RetireProducerSuppliesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  transitionAction source = ORetire actor ->
  transitionAction target = ORetire actor ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39RetireProducerSuppliesRelated source target sourceAction targetAction =
  r39TransitionExactMapGivesRelated source target

public export
0 r39RemoveProducerSuppliesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  transitionAction source = ORemove actor ->
  transitionAction target = ORemove actor ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39RemoveProducerSuppliesRelated source target sourceAction targetAction =
  r39TransitionExactMapGivesRelated source target

public export
0 r39BeginProducerSuppliesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  transitionAction source = LBegin actor ->
  transitionAction target = LBegin actor ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39BeginProducerSuppliesRelated source target sourceAction targetAction =
  r39TransitionExactMapGivesRelated source target

public export
0 r39DivertProducerSuppliesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  transitionAction source = LDivert actor ->
  transitionAction target = LDivert actor ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39DivertProducerSuppliesRelated source target sourceAction targetAction =
  r39TransitionExactMapGivesRelated source target

public export
0 r39LeaveProducerSuppliesRelated :
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  transitionAction source = LLeave actor ->
  transitionAction target = LLeave actor ->
  EffectPartialMapRespects keyEq (partialEffectMap target) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
r39LeaveProducerSuppliesRelated source target sourceAction targetAction =
  r39TransitionExactMapGivesRelated source target

0 r39RelatedAccumulatorOutputsSameInput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (sourceAccumulator, targetAccumulator :
    LocalState key value world provision -> LocalState key value world provision) ->
  AccumulatorRelated sourceAccumulator targetAccumulator ->
  (state : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (accumulatorRuntimeEffectMap nameEq keyEq actor sourceAccumulator state)
    (accumulatorRuntimeEffectMap nameEq keyEq actor targetAccumulator state)
r39RelatedAccumulatorOutputsSameInput nameEq keyEq actor provision
  sourceAccumulator targetAccumulator accumulatorsRelated state =
    let restoredRelated = accumulatorsRelated
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor)))
        outputRelated = MkEffectStateRelated
          (localAmbientExact restoredRelated) tablesRelated
    in PartialDefined outputRelated
  where
  0 tablesRelated :
    (selected : name) ->
    bindings (effectTables
      (setEffectTable @{nameEq} actor
        (ownedValues (localTable (sourceAccumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor))))))
        (setEffectAmbient (localWorld (sourceAccumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor))))) state)) selected) =
    bindings (effectTables
      (setEffectTable @{nameEq} actor
        (ownedValues (localTable (targetAccumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor))))))
        (setEffectAmbient (localWorld (targetAccumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor))))) state)) selected)
  tablesRelated selected with (decEq @{nameEq} selected actor)
    tablesRelated selected | Yes same = case same of
      Refl => localBindingsExact
        (accumulatorsRelated
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder @{keyEq} provision
              (effectTables state actor))))
    tablesRelated selected | No distinct = Refl

||| Producer probe for the revision-38 counterexample class.  Runtime-related
||| accumulator functions supply the strong cross-input relation even when
||| their proof-bearing result contexts are not equal.
public export
0 r39RelatedAccumulatorsSupplyRelatedMaps :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (sourceAccumulator, targetAccumulator :
    LocalState key value world provision -> LocalState key value world provision) ->
  AccumulatorRelated sourceAccumulator targetAccumulator ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (accumulatorRuntimeEffectMap nameEq keyEq actor sourceAccumulator)
    (accumulatorRuntimeEffectMap nameEq keyEq actor targetAccumulator)
r39RelatedAccumulatorsSupplyRelatedMaps nameEq keyEq actor provision
  sourceAccumulator targetAccumulator accumulatorsRelated {x} {y} inputs =
    r39EffectPartialTransitive
      (accumulatorRuntimeEffectMapRespects nameEq keyEq actor provision
        sourceAccumulator x y inputs)
      (r39RelatedAccumulatorOutputsSameInput nameEq keyEq actor provision
        sourceAccumulator targetAccumulator accumulatorsRelated y)

||| Generic lifecycle bridge used by both blocked L-Unload and L-Advance actual
||| Table-1 maps.  Same-input producer capital is upgraded with map respect to
||| arbitrary related inputs.
public export
0 r39RelatedLifecycleOwnersSupplyRelatedMaps :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) -> (tag : RuleTag) ->
  (source, target : SystemState name key value world error) ->
  (sourceOwner, targetOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action) (registry source) =
    Just sourceOwner ->
  lookupFiber @{nameEq} (actionOwner action) (registry target) =
    Just targetOwner ->
  FiberControlRelated sourceOwner targetOwner ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMapFor nameEq keyEq action tag source)
    (partialEffectMapFor nameEq keyEq action tag target)
r39RelatedLifecycleOwnersSupplyRelatedMaps nameEq keyEq action lifecycle tag
  source target sourceOwner targetOwner sourceFound targetFound ownersRelated
  {x} {y} inputs =
    r39EffectPartialTransitive
      (partialEffectMapForRespects nameEq keyEq action tag source x y inputs)
      (relatedLifecyclePartialMapOutputsAtStates nameEq keyEq action lifecycle tag
        source target sourceOwner targetOwner sourceFound targetFound
        ownersRelated y)
