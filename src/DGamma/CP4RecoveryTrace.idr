module DGamma.CP4RecoveryTrace

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryAccumulator
import DGamma.Unified
import Data.List.Elem
import Decidable.Equality

%default total

||| The three installed lifecycle shapes that carry the same concrete
||| accumulator function. Keeping this evidence separate from `installed=True`
||| avoids re-splitting an existential `Fiber` at every temporal step.
public export
data InstalledAccumulator :
  (fiber : Fiber name key value world error) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) -> Type where
  AccumulatorReloading :
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber)))) ->
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    fiberLifecycle fiber = Reloading remaining accumulator view ->
    InstalledAccumulator fiber accumulator
  AccumulatorActive :
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    fiberLifecycle fiber = Active accumulator view ->
    InstalledAccumulator fiber accumulator
  AccumulatorUnloading :
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    (outcome : Maybe error) ->
    fiberLifecycle fiber = Unloading accumulator view outcome ->
    InstalledAccumulator fiber accumulator

||| Strong temporal invariant for Theorem 61. The runtime fiber/accumulator is
||| tied to a generated transformation over the complete episode trace; the
||| factorization field is the Finding-9 algebraic invariant.
public export
record AccumulatorModel
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (state : SystemState name key value world error) where
  constructor MkAccumulatorModel
  modelFiber : Fiber name key value world error
  0 modelFound : lookupFiber @{nameEq} selected (registry state) =
    Just modelFiber
  modelAccumulator : LocalState key value world
      (componentProvisions (fiberComponent modelFiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent modelFiber))
  0 modelInstalled : InstalledAccumulator modelFiber modelAccumulator
  modelTransformation : TraceEffectTransformation name key world error value
    selected whole
  0 modelFactorization : AccumulatorFactorization nameEq keyEq selected
    (componentProvisions (fiberComponent modelFiber)) modelAccumulator
    modelTransformation
  0 modelConfinement : TransformationPreservesConfinement selected
    (componentProvisions (fiberComponent modelFiber)) modelTransformation

public export
modelHandle :
  AccumulatorModel name key world error value nameEq keyEq selected whole state ->
  AccumulatorHandle key value world
modelHandle model = MkAccumulatorHandle
  (componentProvisions (fiberComponent (modelFiber model)))
  (fiberTable (modelFiber model)) (modelAccumulator model)

||| The model exposes the exact handle stored by the runtime lifecycle.
public export
0 modelHandleAt :
  (model : AccumulatorModel name key world error value nameEq keyEq selected
    whole state) ->
  actualAccumulatorAt @{nameEq} selected state = Just (modelHandle model)
modelHandleAt model = rewrite modelFound model in case modelInstalled model of
  AccumulatorReloading remaining view lifecycle => rewrite lifecycle in Refl
  AccumulatorActive view lifecycle => rewrite lifecycle in Refl
  AccumulatorUnloading view outcome lifecycle => rewrite lifecycle in Refl

0 justPairInjective : Just left = Just right -> left = right
justPairInjective Refl = Refl

0 beginConcreteAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (start : SystemState name key value world error) ->
  (whole : Transitions start wholeLast) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected fibers = Just fiber ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  MkSystemState ambient
    (replaceBinding @{nameEq} selected
      (setFiberLifecycle fiber
        (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view)) fibers) =
    start ->
  AccumulatorModel name key world error value nameEq keyEq selected whole start
beginConcreteAccumulatorModel {name} {key} {world} {error} {value}
  nameEq keyEq selected ambient fibers start whole
  fiber@(MkFiber component parent retired table oldLife) found view concreteIsStart =
    let nextFiber : Fiber name key value world error
        nextFiber = MkFiber component parent retired table
          (Reloading (componentProgram component) (\local => local) view)
        concrete : SystemState name key value world error
        concrete = MkSystemState ambient
          (replaceBinding @{nameEq} selected nextFiber fibers)
        0 nextFound : lookupFiber @{nameEq} selected (registry concrete) =
          Just nextFiber
        nextFound = lookupReplacedFiber selected fiber nextFiber fibers found
        concreteModel : AccumulatorModel name key world error value nameEq keyEq
          selected whole concrete
        concreteModel = MkAccumulatorModel nextFiber nextFound id
          (AccumulatorReloading (componentProgram component) view Refl)
          TraceIdentity
          (identityAccumulatorFactorization {name = name} {key = key}
            {world = world} {error = error} {value = value} {trace = whole}
            nameEq keyEq selected (componentProvisions component))
          (identityTransformationPreservesConfinement
            {name = name} {key = key} {world = world} {error = error}
            {value = value} {trace = whole} selected
            (componentProvisions component))
    in replace
      {p = \observed => AccumulatorModel name key world error value nameEq keyEq
        selected whole observed}
      concreteIsStart concreteModel

0 beginAccumulatorModelFromRaw :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (preStart, start : SystemState name key value world error) ->
  (whole : Transitions start wholeLast) ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) preStart =
    Just (LBeginTag, start) ->
  AccumulatorModel name key world error value nameEq keyEq selected whole start
beginAccumulatorModelFromRaw {name} {key} {world} {error} {value}
  nameEq keyEq selected preStart@(MkSystemState ambient fibers) start whole raw
  with (lookupFiber @{nameEq} selected fibers) proof found
  beginAccumulatorModelFromRaw nameEq keyEq selected
    preStart@(MkSystemState ambient fibers) start whole raw | Nothing =
      void (nothingIsNotJust raw)
  beginAccumulatorModelFromRaw nameEq keyEq selected
    preStart@(MkSystemState ambient fibers) start whole raw | Just fiber
    with (fiberLifecycle fiber) proof lifecycle
    beginAccumulatorModelFromRaw nameEq keyEq selected
      preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
        Inactive Nothing
      with (targetFiber @{nameEq} @{keyEq} fiber fibers) proof target
      beginAccumulatorModelFromRaw nameEq keyEq selected
        preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
          Inactive Nothing | Nothing = void (nothingIsNotJust raw)
      beginAccumulatorModelFromRaw nameEq keyEq selected
        preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
          Inactive Nothing | Just view =
            let concrete : SystemState name key value world error
                concrete = MkSystemState ambient
                  (replaceBinding @{nameEq} selected
                    (setFiberLifecycle fiber
                      (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view))
                    fibers)
                0 concreteIsStart : concrete = start
                concreteIsStart = cong snd (justPairInjective raw)
            in beginConcreteAccumulatorModel nameEq keyEq selected ambient fibers
              start whole fiber found view concreteIsStart
    beginAccumulatorModelFromRaw nameEq keyEq selected
      preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
        Inactive (Just err) = void (nothingIsNotJust raw)
    beginAccumulatorModelFromRaw nameEq keyEq selected
      preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
        Reloading remaining accumulator view = void (nothingIsNotJust raw)
    beginAccumulatorModelFromRaw nameEq keyEq selected
      preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
        Active accumulator view = void (nothingIsNotJust raw)
    beginAccumulatorModelFromRaw nameEq keyEq selected
      preStart@(MkSystemState ambient fibers) start whole raw | Just fiber |
        Unloading accumulator view outcome = void (nothingIsNotJust raw)

||| L-Begin establishes the temporal invariant with the identity generated
||| transformation and one trailing order-preserving actor normalization.
public export
0 beginAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {preStart, start : SystemState name key value world error} ->
  (whole : Transitions start wholeLast) ->
  BeginStep nameEq keyEq selected preStart start ->
  AccumulatorModel name key world error value nameEq keyEq selected whole start
beginAccumulatorModel nameEq keyEq selected {preStart} {start} whole opening =
  beginAccumulatorModelFromRaw nameEq keyEq selected preStart start whole
    (checkedActionProjects nameEq keyEq (LBegin selected) preStart start
      LBeginTag (beginEquation opening))

||| A foreign step cannot change the selected fiber object, hence it preserves
||| the exact lifecycle accumulator and its generated-transformation model.
||| Ambient/table commutation is deliberately deferred to the replay invariant;
||| this lemma is only the control-side persistence fact.
public export
0 foreignStepPreservesAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState) ->
  Not (selected = actionOwner action) ->
  AccumulatorModel name key world error value nameEq keyEq selected whole before ->
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
foreignStepPreservesAccumulatorModel {name} {key} {world} {error} {value}
  nameEq keyEq selected action tag before afterState whole checked distinct model =
    let raw = checkedActionProjects nameEq keyEq action before afterState tag checked
        update = applyActionLocalUpdate nameEq keyEq action before afterState tag raw
        targetFound = trans
          (systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
            before afterState update)
          (modelFound model)
    in MkAccumulatorModel (modelFiber model) targetFound
      (modelAccumulator model) (modelInstalled model)
      (modelTransformation model) (modelFactorization model)
      (modelConfinement model)
