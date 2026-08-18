module DGamma.CP4RecoverySelectedRetire

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

0 retireInstalledAccumulator :
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  InstalledAccumulator
    (MkFiber component parent retired table lifecycle) accumulator ->
  InstalledAccumulator
    (MkFiber component parent True table lifecycle) accumulator
retireInstalledAccumulator component parent retired table lifecycle accumulator
  (AccumulatorReloading remaining view shape) =
    AccumulatorReloading remaining view shape
retireInstalledAccumulator component parent retired table lifecycle accumulator
  (AccumulatorActive view shape) = AccumulatorActive view shape
retireInstalledAccumulator component parent retired table lifecycle accumulator
  (AccumulatorUnloading view outcome shape) =
    AccumulatorUnloading view outcome shape

0 successfulRetireTarget :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  lookupFiber @{nameEq} selected fibers = Just fiber ->
  applyAction @{nameEq} @{keyEq} (ORetire selected)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  afterState = MkSystemState ambient
    (replaceBinding @{nameEq} selected (retireFiber fiber) fibers)
successfulRetireTarget nameEq keyEq selected fiber ambient fibers afterState tag
  found raw with (lookupFiber @{nameEq} selected fibers) proof observed
  successfulRetireTarget nameEq keyEq selected fiber ambient fibers afterState tag
    found raw | Nothing = case found of Refl impossible
  successfulRetireTarget nameEq keyEq selected fiber ambient fibers afterState tag
    found raw | Just actual = case justPairInjective found of
      Refl => case justPairInjective raw of Refl => Refl

||| O-Retire of the selected installed fiber changes only its retirement flag.
||| The concrete accumulator function and generated transformation are retained.
public export
0 selectedRetirePreservesAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (ORetireTag, afterState) ->
  AccumulatorModel name key world error value nameEq keyEq selected whole before ->
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
selectedRetirePreservesAccumulatorModel {name} {key} {world} {error} {value}
  nameEq keyEq selected (MkSystemState ambient fibers) afterState whole checked
  (MkAccumulatorModel fiber sourceFound accumulator installed transformation
    factorization confinement)
  with (fiber)
  selectedRetirePreservesAccumulatorModel nameEq keyEq selected
    (MkSystemState ambient fibers) afterState whole checked
    (MkAccumulatorModel fiber sourceFound accumulator installed transformation
      factorization confinement) |
      (MkFiber component parent retired table lifecycle) =
        let raw = checkedActionProjects nameEq keyEq (ORetire selected)
              (MkSystemState ambient fibers) afterState ORetireTag checked
            concreteFiber : Fiber name key value world error
            concreteFiber = MkFiber component parent True table lifecycle
            concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} selected concreteFiber fibers)
            0 concreteIsAfter : concrete = afterState
            concreteIsAfter = sym (successfulRetireTarget nameEq keyEq selected
              (MkFiber component parent retired table lifecycle) ambient fibers
              afterState ORetireTag sourceFound raw)
            0 concreteFound : lookupFiber @{nameEq} selected
              (registry concrete) = Just concreteFiber
            concreteFound = lookupReplacedFiber selected
              (MkFiber component parent retired table lifecycle) concreteFiber
              fibers sourceFound
            concreteModel : AccumulatorModel name key world error value nameEq
              keyEq selected whole concrete
            concreteModel = MkAccumulatorModel concreteFiber concreteFound
              accumulator
              (retireInstalledAccumulator component parent retired table lifecycle
                accumulator installed)
              transformation factorization confinement
        in replace
          {p = \observed => AccumulatorModel name key world error value nameEq
            keyEq selected whole observed}
          concreteIsAfter concreteModel

||| O-Retire changes neither the provision nor the runtime accumulator callback;
||| the handle's captured table is intentionally irrelevant to its effect map.
public export
0 selectedRetirePreservesAccumulatorMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (ORetireTag, afterState)) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  (state : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected
    (modelHandle (selectedRetirePreservesAccumulatorModel nameEq keyEq selected
      before afterState whole checked model)) state =
  accumulatorEffectMap nameEq keyEq selected (modelHandle model) state
selectedRetirePreservesAccumulatorMap {name} {key} {world} {error} {value}
  nameEq keyEq selected before@(MkSystemState ambient fibers) afterState whole
  checked model@(MkAccumulatorModel fiber sourceFound accumulator installed
    transformation factorization confinement) state
  with (fiber)
  selectedRetirePreservesAccumulatorMap nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState whole checked
    model@(MkAccumulatorModel fiber sourceFound accumulator installed
      transformation factorization confinement) state |
      MkFiber component parent retired table lifecycle =
        let raw = checkedActionProjects nameEq keyEq (ORetire selected)
              (MkSystemState ambient fibers) afterState ORetireTag checked
            concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} selected
                (MkFiber component parent True table lifecycle) fibers)
            0 concreteIsAfter : concrete = afterState
            concreteIsAfter = sym (successfulRetireTarget nameEq keyEq selected
              (MkFiber component parent retired table lifecycle) ambient fibers
              afterState ORetireTag sourceFound raw)
        in case concreteIsAfter of Refl => Refl
