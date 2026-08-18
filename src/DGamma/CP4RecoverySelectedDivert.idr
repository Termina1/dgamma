module DGamma.CP4RecoverySelectedDivert

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4RecoveryTrace
import DGamma.Unified
import Decidable.Equality

%default total

0 justPairInjective : Just left = Just right -> left = right
justPairInjective Refl = Refl

0 divertConcreteModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected)
    (MkSystemState ambient fibers) = Just (LDivertTag, afterState) ->
  (modelFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected fibers = Just modelFiber ->
  (modelAccumulator : LocalState key value world
      (componentProvisions (fiberComponent modelFiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent modelFiber))) ->
  InstalledAccumulator modelFiber modelAccumulator ->
  (modelTransformation : TraceEffectTransformation name key world error value
    selected whole) ->
  AccumulatorFactorization nameEq keyEq selected
    (componentProvisions (fiberComponent modelFiber)) modelAccumulator
    modelTransformation ->
  TransformationPreservesConfinement selected
    (componentProvisions (fiberComponent modelFiber)) modelTransformation ->
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
divertConcreteModel {name} {key} {world} {error} {value}
  nameEq keyEq selected ambient fibers afterState whole raw modelFiber modelFound
  modelAccumulator modelInstalled modelTransformation modelFactorization
  modelConfinement with (lookupFiber @{nameEq} selected fibers) proof found
  divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
    modelFiber modelFound modelAccumulator modelInstalled modelTransformation
    modelFactorization modelConfinement | Nothing =
      void (nothingIsNotJust modelFound)
  divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
    modelFiber modelFound modelAccumulator modelInstalled modelTransformation
    modelFactorization modelConfinement |
    Just (MkFiber component parent retiredFlag table lifecycle)
    with (lifecycle)
    divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
      modelFiber modelFound modelAccumulator modelInstalled modelTransformation
      modelFactorization modelConfinement |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Inactive outcome = void (nothingIsNotJust raw)
    divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
      modelFiber modelFound modelAccumulator modelInstalled modelTransformation
      modelFactorization modelConfinement |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Active accumulator view = void (nothingIsNotJust raw)
    divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
      modelFiber modelFound modelAccumulator modelInstalled modelTransformation
      modelFactorization modelConfinement |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Unloading accumulator view outcome = void (nothingIsNotJust raw)
    divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
      modelFiber modelFound modelAccumulator modelInstalled modelTransformation
      modelFactorization modelConfinement |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading remaining accumulator view)) fibers) view)
      divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
        modelFiber modelFound modelAccumulator modelInstalled modelTransformation
        modelFactorization modelConfinement |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading remaining accumulator view | True =
          void (nothingIsNotJust raw)
      divertConcreteModel nameEq keyEq selected ambient fibers afterState whole raw
        modelFiber modelFound modelAccumulator modelInstalled modelTransformation
        modelFactorization modelConfinement |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading remaining accumulator view | False =
          let sourceFiber : Fiber name key value world error
              sourceFiber = MkFiber component parent retiredFlag table
                (Reloading remaining accumulator view)
              targetFiberValue : Fiber name key value world error
              targetFiberValue = setFiberLifecycle sourceFiber
                (Unloading accumulator view Nothing)
              concrete : SystemState name key value world error
              concrete = MkSystemState ambient
                (replaceBinding @{nameEq} selected targetFiberValue fibers)
              0 concreteIsAfter : concrete = afterState
              concreteIsAfter = cong snd (justPairInjective raw)
              0 sameFiber : modelFiber = sourceFiber
              sameFiber = sym (justPairInjective modelFound)
          in case sameFiber of
            Refl => case modelInstalled of
              AccumulatorReloading modelRemaining modelView modelLife =>
                case modelLife of
                  Refl =>
                    let 0 targetFound : (lookupFiber @{nameEq} {name = name}
                          {key = key} {value = value} {world = world}
                          {error = error} selected (registry concrete) =
                          Just targetFiberValue)
                        targetFound = lookupReplacedFiber selected sourceFiber
                          targetFiberValue fibers found
                        concreteModel : AccumulatorModel name key world error value
                          nameEq keyEq selected whole concrete
                        concreteModel = MkAccumulatorModel targetFiberValue
                          targetFound accumulator
                          (AccumulatorUnloading view Nothing Refl)
                          modelTransformation modelFactorization modelConfinement
                    in replace
                      {p = \observed => AccumulatorModel name key world error value
                        nameEq keyEq selected whole observed}
                      concreteIsAfter concreteModel
              AccumulatorActive modelView modelLife =>
                case modelLife of Refl impossible
              AccumulatorUnloading modelView outcome modelLife =>
                case modelLife of Refl impossible

||| The explicit aborting L-Divert changes a selected Reloading lifecycle to
||| Unloading without changing its table, accumulator, or generated inverse
||| transformation.
public export
0 selectedDivertPreservesAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  checkedApplyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (LDivertTag, afterState) ->
  AccumulatorModel name key world error value nameEq keyEq selected whole before ->
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
selectedDivertPreservesAccumulatorModel nameEq keyEq selected
  (MkSystemState ambient fibers) afterState whole checked
  (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
    modelTransformation modelFactorization modelConfinement) =
    divertConcreteModel nameEq keyEq selected ambient fibers afterState whole
      (checkedActionProjects nameEq keyEq (LDivert selected)
        (MkSystemState ambient fibers) afterState LDivertTag checked)
      modelFiber modelFound modelAccumulator modelInstalled modelTransformation
      modelFactorization modelConfinement
