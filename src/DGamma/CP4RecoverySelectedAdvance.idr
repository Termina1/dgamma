module DGamma.CP4RecoverySelectedAdvance

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoveryAdvance
import DGamma.Unified
import Decidable.Equality

%default total

0 justPairInjective : Just left = Just right -> left = right
justPairInjective Refl = Refl

%inline
0 advanceRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {before, afterState : SystemState name key value world error} ->
  {tag : RuleTag} ->
  checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)
advanceRaw {nameEq} {keyEq} {selected} {before} {afterState} {tag} checked =
  checkedActionProjects nameEq keyEq (LAdvance selected) before afterState tag
    checked

data AdvanceOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) -> Type where
  MkAdvanceOccurrence :
    (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
      Just (tag, afterState)) ->
    OccursIn
      (Fired {before = before} {afterState = afterState} nameEq keyEq
        (LAdvance selected) tag checked) whole ->
    AdvanceOccurrence name key world error value nameEq keyEq selected before
      afterState tag whole

0 lifecycleAccumulator :
  Lifecycle key value world error name deps provision ->
  Maybe (LocalState key value world provision ->
    LocalState key value world provision)
lifecycleAccumulator (Inactive outcome) = Nothing
lifecycleAccumulator (Reloading remaining accumulator view) = Just accumulator
lifecycleAccumulator (Active accumulator view) = Just accumulator
lifecycleAccumulator (Unloading accumulator view outcome) = Just accumulator

0 controlAdvanceModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceFound : lookupFiber @{nameEq} selected fibers =
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view))) ->
  (targetWorld : world) ->
  (targetTable : OwnedTable key value (componentProvisions component)) ->
  (targetLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  InstalledAccumulator
    (MkFiber component parent retiredFlag targetTable targetLifecycle)
    accumulator ->
  (concrete : SystemState name key value world error) ->
  concrete = MkSystemState targetWorld
    (replaceBinding @{nameEq} selected
      (MkFiber component parent retiredFlag targetTable targetLifecycle) fibers) ->
  concrete = afterState ->
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
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
controlAdvanceModel {name} {key} {world} {error} {value}
  nameEq keyEq selected ambient fibers afterState whole component parent
  retiredFlag table remaining accumulator view sourceFound targetWorld targetTable
  targetLifecycle targetInstalled concrete concreteShape concreteIsAfter modelFiber
  modelFound modelAccumulator modelInstalled modelTransformation
  modelFactorization =
    let sourceFiber : Fiber name key value world error
        sourceFiber = MkFiber component parent retiredFlag table
          (Reloading remaining accumulator view)
        targetFiberValue : Fiber name key value world error
        targetFiberValue = MkFiber component parent retiredFlag targetTable
          targetLifecycle
        0 sameFiber : modelFiber = sourceFiber
        sameFiber = justPairInjective (trans (sym modelFound) sourceFound)
    in case sameFiber of
      Refl => case modelInstalled of
        AccumulatorReloading modelRemaining modelView modelLife =>
          let 0 accumulatorSame : (accumulator = modelAccumulator)
              accumulatorSame = justPairInjective
                (cong lifecycleAccumulator modelLife)
              0 modelFactorActual : AccumulatorFactorization nameEq keyEq
                selected (componentProvisions component) accumulator
                modelTransformation
              modelFactorActual = replace
                {p = \observed => AccumulatorFactorization nameEq keyEq selected
                  (componentProvisions component) observed modelTransformation}
                (sym accumulatorSame) modelFactorization
          in case modelLife of
            Refl =>
              let 0 targetFoundConcrete : (lookupFiber @{nameEq} {name = name}
                    {key = key} {value = value} {world = world} {error = error}
                    selected (registry
                      (the (SystemState name key value world error)
                        (MkSystemState targetWorld
                          (replaceBinding @{nameEq} selected targetFiberValue
                            fibers)))) = Just targetFiberValue)
                  targetFoundConcrete = lookupReplacedFiber selected sourceFiber
                    targetFiberValue fibers sourceFound
                  0 targetFound : (lookupFiber @{nameEq} {name = name}
                    {key = key} {value = value} {world = world} {error = error}
                    selected (registry concrete) = Just targetFiberValue)
                  targetFound = replace
                    {p = \observed => lookupFiber @{nameEq} {name = name}
                      {key = key} {value = value} {world = world} {error = error}
                      selected (registry observed) = Just targetFiberValue}
                    (sym concreteShape) targetFoundConcrete
                  concreteModel : AccumulatorModel name key world error value
                    nameEq keyEq selected whole concrete
                  concreteModel = MkAccumulatorModel targetFiberValue targetFound
                    accumulator targetInstalled modelTransformation
                    modelFactorActual
              in replace
                {p = \observed => AccumulatorModel name key world error value
                  nameEq keyEq selected whole observed}
                concreteIsAfter concreteModel
        AccumulatorActive modelView modelLife =>
          case modelLife of Refl impossible
        AccumulatorUnloading modelView outcome modelLife =>
          case modelLife of Refl impossible

0 successfulAdvanceModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (whole : Transitions wholeFirst wholeLast) ->
  AdvanceOccurrence name key world error value nameEq keyEq selected before
    afterState tag whole ->
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
  (sourceFound : lookupFiber @{nameEq} selected (registry before) =
    Just (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  (resolved : resolveCommittedValues @{nameEq} @{keyEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view (registry before) =
    Just capability) ->
  (localAfter : LocalState key value world (componentProvisions component)) ->
  (undo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (ran : runStepEffect step capability
    (MkLocalState (worldState before)
      (restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table))) = Right (localAfter, undo)) ->
  (targetLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  InstalledAccumulator
    (MkFiber component parent retiredFlag (localTable localAfter)
      targetLifecycle)
    (pushLocalUndo (componentProvisions component) accumulator undo) ->
  (concrete : SystemState name key value world error) ->
  concrete = MkSystemState (localWorld localAfter)
    (replaceBinding @{nameEq} selected
      (MkFiber component parent retiredFlag (localTable localAfter)
        targetLifecycle) (registry before)) ->
  concrete = afterState ->
  (modelFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry before) = Just modelFiber ->
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
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
successfulAdvanceModel {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState tag whole
  (MkAdvanceOccurrence anchoredChecked anchoredOccurs) component parent
  retiredFlag table step rest accumulator view sourceFound capability resolved
  localAfter undo ran targetLifecycle targetInstalled concrete concreteShape
  concreteIsAfter modelFiber modelFound modelAccumulator modelInstalled
  modelTransformation modelFactorization =
    let targetAccumulator : LocalState key value world
          (componentProvisions component) ->
          LocalState key value world (componentProvisions component)
        targetAccumulator = pushLocalUndo (componentProvisions component)
          accumulator undo
        stage : IteratorStage name key world error value selected whole
        stage = StageFromAdvance nameEq keyEq selected tag anchoredChecked
          anchoredOccurs
          (MkFiber component parent retiredFlag table
            (Reloading (step :: rest) accumulator view))
          sourceFound (step :: rest) accumulator view Refl step rest SuffixHere
        generator : TraceEffectGenerator name key world error value selected whole
        generator = IteratorYieldedGenerator stage
          (projectEffectState @{nameEq} before)
        nextTransformation : TraceEffectTransformation name key world error value
          selected whole
        nextTransformation = TraceCompose modelTransformation
          (TraceGenerator generator)
        0 sameFiber : modelFiber = MkFiber component parent retiredFlag table
          (Reloading (step :: rest) accumulator view)
        sameFiber = justPairInjective (trans (sym modelFound) sourceFound)
    in case sameFiber of
      Refl => case modelInstalled of
        AccumulatorReloading modelRemaining modelView modelLife =>
          let 0 accumulatorSame : (accumulator = modelAccumulator)
              accumulatorSame = justPairInjective
                (cong lifecycleAccumulator modelLife)
              0 modelFactorActual : AccumulatorFactorization nameEq keyEq
                selected (componentProvisions component) accumulator
                modelTransformation
              modelFactorActual = replace
                {p = \observed => AccumulatorFactorization nameEq keyEq selected
                  (componentProvisions component) observed modelTransformation}
                (sym accumulatorSame) modelFactorization
              0 nextFactorization : AccumulatorFactorization nameEq keyEq
                selected (componentProvisions component) targetAccumulator
                nextTransformation
              nextFactorization = successfulAdvancePushesAccumulatorFactorization
                nameEq keyEq selected before afterState tag anchoredChecked
                anchoredOccurs
                (MkFiber component parent retiredFlag table
                  (Reloading (step :: rest) accumulator view))
                sourceFound step rest accumulator view Refl capability
                resolved localAfter undo ran modelTransformation modelFactorActual
              concreteTarget : SystemState name key value world error
              concreteTarget = MkSystemState (localWorld localAfter)
                (replaceBinding @{nameEq} selected
                  (MkFiber component parent retiredFlag (localTable localAfter)
                    targetLifecycle) (registry before))
              0 targetFoundConcrete : (lookupFiber @{nameEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                selected (registry concreteTarget) =
                Just (MkFiber component parent retiredFlag
                  (localTable localAfter) targetLifecycle))
              targetFoundConcrete = lookupReplacedFiber selected
                (MkFiber component parent retiredFlag table
                  (Reloading (step :: rest) accumulator view))
                (MkFiber component parent retiredFlag (localTable localAfter)
                  targetLifecycle) (registry before) sourceFound
              0 targetFound : (lookupFiber @{nameEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                selected (registry concrete) =
                Just (MkFiber component parent retiredFlag
                  (localTable localAfter) targetLifecycle))
              targetFound = replace
                {p = \observed => lookupFiber @{nameEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  selected (registry observed) =
                  Just (MkFiber component parent retiredFlag
                    (localTable localAfter) targetLifecycle)}
                (sym concreteShape) targetFoundConcrete
              concreteModel : AccumulatorModel name key world error value
                nameEq keyEq selected whole concrete
              concreteModel = MkAccumulatorModel
                (MkFiber component parent retiredFlag (localTable localAfter)
                  targetLifecycle) targetFound
                targetAccumulator targetInstalled nextTransformation
                nextFactorization
          in replace
            {p = \observed => AccumulatorModel name key world error value
              nameEq keyEq selected whole observed}
            concreteIsAfter concreteModel
        AccumulatorActive modelView modelLife =>
          case modelLife of Refl impossible
        AccumulatorUnloading modelView outcome modelLife =>
          case modelLife of Refl impossible

||| Exhaustive selected L-Advance preservation. Control-only empty, raised, and
||| stale branches keep the transformation; each successful iterator branch
||| extends it by the exact yielded inverse occurrence.
public export
0 selectedAdvanceFromRaw :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  {0 raw : applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq
      (LAdvance selected) tag checked) whole) ->
  {anchor : AdvanceOccurrence name key world error value nameEq keyEq selected
    before afterState tag whole} ->
  AccumulatorModel name key world error value nameEq keyEq selected whole before ->
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
selectedAdvanceFromRaw {name} {key} {world} {error} {value}
  nameEq keyEq selected before@(MkSystemState ambient fibers) afterState tag
  checked whole occurs
  (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
    modelTransformation modelFactorization)
  with (lookupFiber @{nameEq} selected fibers) proof found
  selectedAdvanceFromRaw nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag checked whole occurs
    (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
      modelTransformation modelFactorization) | Nothing =
        void (nothingIsNotJust modelFound)
  selectedAdvanceFromRaw nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag checked whole occurs
    (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
      modelTransformation modelFactorization) |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (lifecycle)
    selectedAdvanceFromRaw nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust checked)
    selectedAdvanceFromRaw nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust checked)
    selectedAdvanceFromRaw nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust checked)
    selectedAdvanceFromRaw nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading [] accumulator view)) fibers) view)
      selectedAdvanceFromRaw nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization) |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading [] accumulator view | True =
        let sourceFiber = MkFiber component parent retiredFlag table
              (Reloading [] accumulator view)
            concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} selected
                (setFiberLifecycle
                  (MkFiber component parent retiredFlag table
                    (Reloading [] accumulator view))
                  (Active accumulator view)) fibers)
            0 concreteShape : concrete = MkSystemState ambient
              (replaceBinding @{nameEq} selected
                (MkFiber component parent retiredFlag table
                  (Active accumulator view)) fibers)
            concreteShape = cong
              (\observed => MkSystemState ambient
                (replaceBinding @{nameEq} selected observed fibers))
              (setFiberLifecycleExact component parent retiredFlag table
                (Reloading [] accumulator view) (Active accumulator view))
            0 concreteIsAfter : concrete = afterState
            concreteIsAfter = cong snd (justPairInjective raw)
        in controlAdvanceModel nameEq keyEq selected ambient fibers afterState whole
          component parent retiredFlag table [] accumulator view found ambient table
          (Active accumulator view) (AccumulatorActive view Refl) concrete
          concreteShape concreteIsAfter modelFiber
          (trans found modelFound) modelAccumulator modelInstalled
          modelTransformation modelFactorization
      selectedAdvanceFromRaw nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization) |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading [] accumulator view | False =
        let sourceFiber = MkFiber component parent retiredFlag table
              (Reloading [] accumulator view)
            concrete : SystemState name key value world error
            concrete = MkSystemState ambient
              (replaceBinding @{nameEq} selected
                (setFiberLifecycle
                  (MkFiber component parent retiredFlag table
                    (Reloading [] accumulator view))
                  (Unloading accumulator view Nothing)) fibers)
            0 concreteShape : concrete = MkSystemState ambient
              (replaceBinding @{nameEq} selected
                (MkFiber component parent retiredFlag table
                  (Unloading accumulator view Nothing)) fibers)
            concreteShape = cong
              (\observed => MkSystemState ambient
                (replaceBinding @{nameEq} selected observed fibers))
              (setFiberLifecycleExact component parent retiredFlag table
                (Reloading [] accumulator view)
                (Unloading accumulator view Nothing))
            0 concreteIsAfter : concrete = afterState
            concreteIsAfter = cong snd (justPairInjective raw)
        in controlAdvanceModel nameEq keyEq selected ambient fibers afterState whole
          component parent retiredFlag table [] accumulator view found ambient table
          (Unloading accumulator view Nothing)
          (AccumulatorUnloading view Nothing Refl) concrete concreteShape
          concreteIsAfter modelFiber (trans found modelFound)
          modelAccumulator modelInstalled modelTransformation modelFactorization
    selectedAdvanceFromRaw nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view fibers) proof resolved
      selectedAdvanceFromRaw nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization) |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Nothing =
              void (nothingIsNotJust checked)
      selectedAdvanceFromRaw nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization) |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Just capability
        with (runStepEffect step capability
          (MkLocalState ambient
            (restrictOwnedPreservingOrder (componentProvisions component)
              (ownedValues table)))) proof ran
        selectedAdvanceFromRaw nameEq keyEq selected
          before@(MkSystemState ambient fibers) afterState tag checked whole occurs
          (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
            modelTransformation modelFactorization) |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Left err =
          let sourceFiber = MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)
              concrete : SystemState name key value world error
              concrete = MkSystemState ambient
                (replaceBinding @{nameEq} selected
                  (setFiberLifecycle
                    (MkFiber component parent retiredFlag table
                      (Reloading (step :: rest) accumulator view))
                    (Unloading accumulator view (Just err))) fibers)
              0 concreteShape : concrete = MkSystemState ambient
                (replaceBinding @{nameEq} selected
                  (MkFiber component parent retiredFlag table
                    (Unloading accumulator view (Just err))) fibers)
              concreteShape = cong
                (\observed => MkSystemState ambient
                  (replaceBinding @{nameEq} selected observed fibers))
                (setFiberLifecycleExact component parent retiredFlag table
                  (Reloading (step :: rest) accumulator view)
                  (Unloading accumulator view (Just err)))
              0 concreteIsAfter : concrete = afterState
              concreteIsAfter = cong snd (justPairInjective raw)
          in controlAdvanceModel nameEq keyEq selected ambient fibers afterState
            whole component parent retiredFlag table (step :: rest) accumulator
            view found ambient table (Unloading accumulator view (Just err))
            (AccumulatorUnloading view (Just err) Refl) concrete concreteShape
            concreteIsAfter modelFiber (trans found modelFound)
            modelAccumulator modelInstalled
            modelTransformation modelFactorization
        selectedAdvanceFromRaw nameEq keyEq selected
          before@(MkSystemState ambient fibers) afterState tag checked whole occurs
          (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
            modelTransformation modelFactorization) |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)) fibers) view)
          selectedAdvanceFromRaw nameEq keyEq selected
            before@(MkSystemState ambient fibers) afterState tag checked whole occurs
            (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
              modelTransformation modelFactorization) |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: rest) accumulator view | Just capability |
                  Right (localAfter, undo) | False =
            let concrete : SystemState name key value world error
                concrete = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} selected
                    (setFiberRuntime
                      (MkFiber component parent retiredFlag table
                        (Reloading (step :: rest) accumulator view))
                      (localTable localAfter)
                      (Unloading
                        (pushLocalUndo (componentProvisions component)
                          accumulator undo) view Nothing)) fibers)
                0 concreteShape : concrete = MkSystemState
                  (localWorld localAfter)
                  (replaceBinding @{nameEq} selected
                    (MkFiber component parent retiredFlag (localTable localAfter)
                      (Unloading
                        (pushLocalUndo (componentProvisions component)
                          accumulator undo) view Nothing)) fibers)
                concreteShape = Refl
                0 concreteIsAfter : concrete = afterState
                concreteIsAfter = cong snd (justPairInjective raw)
            in successfulAdvanceModel nameEq keyEq selected
              (MkSystemState ambient fibers) afterState tag whole anchor component
              parent retiredFlag table step rest
              accumulator view found capability resolved localAfter undo ran
              (Unloading
                (pushLocalUndo (componentProvisions component) accumulator undo)
                view Nothing)
              (AccumulatorUnloading view Nothing Refl) concrete concreteShape
              concreteIsAfter modelFiber (trans found modelFound)
              modelAccumulator modelInstalled
              modelTransformation modelFactorization
          selectedAdvanceFromRaw nameEq keyEq selected
            before@(MkSystemState ambient fibers) afterState tag checked whole occurs
            (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
              modelTransformation modelFactorization) |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: []) accumulator view | Just capability |
                  Right (localAfter, undo) | True =
            let concrete : SystemState name key value world error
                concrete = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} selected
                    (setFiberRuntime
                      (MkFiber component parent retiredFlag table
                        (Reloading [step] accumulator view))
                      (localTable localAfter)
                      (Active
                        (pushLocalUndo (componentProvisions component)
                          accumulator undo) view)) fibers)
                0 concreteShape : concrete = MkSystemState
                  (localWorld localAfter)
                  (replaceBinding @{nameEq} selected
                    (MkFiber component parent retiredFlag (localTable localAfter)
                      (Active
                        (pushLocalUndo (componentProvisions component)
                          accumulator undo) view)) fibers)
                concreteShape = Refl
                0 concreteIsAfter : concrete = afterState
                concreteIsAfter = cong snd (justPairInjective raw)
            in successfulAdvanceModel nameEq keyEq selected
              (MkSystemState ambient fibers) afterState tag whole anchor component
              parent retiredFlag table step []
              accumulator view found capability resolved localAfter undo ran
              (Active
                (pushLocalUndo (componentProvisions component) accumulator undo)
                view)
              (AccumulatorActive view Refl) concrete concreteShape
              concreteIsAfter modelFiber (trans found modelFound)
              modelAccumulator modelInstalled
              modelTransformation modelFactorization
          selectedAdvanceFromRaw nameEq keyEq selected
            before@(MkSystemState ambient fibers) afterState tag checked whole occurs
            (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
              modelTransformation modelFactorization) |
              Just (MkFiber component parent retiredFlag table lifecycle) |
                Reloading (step :: nextStep :: more) accumulator view |
                  Just capability | Right (localAfter, undo) | True =
            let concrete : SystemState name key value world error
                concrete = MkSystemState (localWorld localAfter)
                  (replaceBinding @{nameEq} selected
                    (setFiberRuntime
                      (MkFiber component parent retiredFlag table
                        (Reloading (step :: nextStep :: more) accumulator view))
                      (localTable localAfter)
                      (Reloading (nextStep :: more)
                        (pushLocalUndo (componentProvisions component)
                          accumulator undo) view)) fibers)
                0 concreteShape : concrete = MkSystemState
                  (localWorld localAfter)
                  (replaceBinding @{nameEq} selected
                    (MkFiber component parent retiredFlag (localTable localAfter)
                      (Reloading (nextStep :: more)
                        (pushLocalUndo (componentProvisions component)
                          accumulator undo) view)) fibers)
                concreteShape = Refl
                0 concreteIsAfter : concrete = afterState
                concreteIsAfter = cong snd (justPairInjective raw)
            in successfulAdvanceModel nameEq keyEq selected
              (MkSystemState ambient fibers) afterState tag whole anchor component
              parent retiredFlag table step
              (nextStep :: more) accumulator view found capability resolved
              localAfter undo ran
              (Reloading (nextStep :: more)
                (pushLocalUndo (componentProvisions component) accumulator undo)
                view)
              (AccumulatorReloading (nextStep :: more) view Refl) concrete
              concreteShape
              concreteIsAfter modelFiber (trans found modelFound)
              modelAccumulator modelInstalled
              modelTransformation modelFactorization

||| Public checked-step specialization; the raw evaluator equation is projected
||| once and fed to the exhaustive dispatcher as an erased implicit.
public export
0 selectedAdvancePreservesAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq
      (LAdvance selected) tag checked) whole) ->
  AccumulatorModel name key world error value nameEq keyEq selected whole before ->
  AccumulatorModel name key world error value nameEq keyEq selected whole
    afterState
selectedAdvancePreservesAccumulatorModel nameEq keyEq selected before afterState
  tag checked whole occurs model =
    selectedAdvanceFromRaw nameEq keyEq selected before afterState tag checked
      {raw = advanceRaw checked} whole occurs
      {anchor = MkAdvanceOccurrence checked occurs} model
