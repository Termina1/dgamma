module DGamma.CP4RecoverySelectedAdvance

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoveryAdvance
import DGamma.CP4RecoverySelectedEffect
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionFrameAdvanceDispatch
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

record BuiltAccumulatorModel
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (afterState : SystemState name key value world error)
  (provision : CoeffectSpec key)
  (expectedRetired : Bool)
  (runtimeAccumulator : LocalState key value world provision ->
    LocalState key value world provision) where
  constructor MkBuiltAccumulatorModel
  builtModel : AccumulatorModel name key world error value nameEq keyEq selected
    whole afterState
  0 builtRetired : retired (modelFiber builtModel) = expectedRetired
  0 builtMapRuntime : (state : EffectState name key value world) ->
    accumulatorEffectMap nameEq keyEq selected (modelHandle builtModel) state =
    accumulatorRuntimeEffectMap nameEq keyEq selected runtimeAccumulator state

0 lifecycleAccumulator :
  Lifecycle key value world error name deps provision ->
  Maybe (LocalState key value world provision ->
    LocalState key value world provision)
lifecycleAccumulator (Inactive outcome) = Nothing
lifecycleAccumulator (Reloading remaining accumulator view) = Just accumulator
lifecycleAccumulator (Active accumulator view) = Just accumulator
lifecycleAccumulator (Unloading accumulator view outcome) = Just accumulator

0 reloadingModelMapRuntime :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    state) ->
  lookupFiber @{nameEq} selected (registry state) =
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) ->
  (effectState : EffectState name key value world) ->
  accumulatorRuntimeEffectMap nameEq keyEq selected accumulator effectState =
  accumulatorEffectMap nameEq keyEq selected (modelHandle model) effectState
reloadingModelMapRuntime nameEq keyEq selected component parent retiredFlag table
  remaining accumulator view
  model@(MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
    modelTransformation modelFactorization modelConfinement) found effectState =
    let 0 sameFiber : (modelFiber =
          MkFiber component parent retiredFlag table
            (Reloading remaining accumulator view))
        sameFiber = justPairInjective (trans (sym modelFound) found)
    in case sameFiber of
      Refl => case modelInstalled of
        AccumulatorReloading modelRemaining modelView modelLife =>
          case modelLife of Refl => Refl
        AccumulatorActive modelView modelLife => case modelLife of Refl impossible
        AccumulatorUnloading modelView outcome modelLife =>
          case modelLife of Refl impossible

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
  TransformationPreservesConfinement selected
    (componentProvisions (fiberComponent modelFiber)) modelTransformation ->
  BuiltAccumulatorModel name key world error value nameEq keyEq selected whole
    afterState (componentProvisions component) retiredFlag accumulator
controlAdvanceModel {name} {key} {world} {error} {value}
  nameEq keyEq selected ambient fibers afterState whole component parent
  retiredFlag table remaining accumulator view sourceFound targetWorld targetTable
  targetLifecycle targetInstalled concrete concreteShape concreteIsAfter modelFiber
  modelFound modelAccumulator modelInstalled modelTransformation
  modelFactorization modelConfinement =
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
                    modelFactorActual modelConfinement
                  concreteResult : BuiltAccumulatorModel name key world error
                    value nameEq keyEq selected whole concrete
                    (componentProvisions component) retiredFlag accumulator
                  concreteResult = MkBuiltAccumulatorModel concreteModel Refl
                    (\state => Refl)
              in replace
                {p = \observed => BuiltAccumulatorModel name key world error
                  value nameEq keyEq selected whole observed
                  (componentProvisions component) retiredFlag accumulator}
                concreteIsAfter concreteResult
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
  TransformationPreservesConfinement selected
    (componentProvisions (fiberComponent modelFiber)) modelTransformation ->
  BuiltAccumulatorModel name key world error value nameEq keyEq selected whole
    afterState (componentProvisions component) retiredFlag
    (pushLocalUndo (componentProvisions component) accumulator undo)
successfulAdvanceModel {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState tag whole
  (MkAdvanceOccurrence anchoredChecked anchoredOccurs) component parent
  retiredFlag table step rest accumulator view sourceFound capability resolved
  localAfter undo ran targetLifecycle targetInstalled concrete concreteShape
  concreteIsAfter modelFiber modelFound modelAccumulator modelInstalled
  modelTransformation modelFactorization modelConfinement =
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
        0 stageRuns : iteratorStageEffect stage
          (projectEffectState @{nameEq} before) = Just
          (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before)),
           yieldedInverseEffectMap nameEq keyEq selected
             (componentProvisions component) undo,
           MkIteratorContinuation rest)
        stageRuns = actualIteratorStageYields nameEq keyEq selected before
          afterState tag anchoredChecked anchoredOccurs
          (MkFiber component parent retiredFlag table
            (Reloading (step :: rest) accumulator view))
          sourceFound step rest accumulator view Refl capability resolved
          localAfter undo ran
        0 generatorMap : (state : EffectState name key value world) ->
          traceGeneratorMap generator state = yieldedInverseEffectMap nameEq
            keyEq selected (componentProvisions component) undo state
        generatorMap = yieldedGeneratorMapFromStageRun stage
          (projectEffectState @{nameEq} before)
          (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before)))
          (yieldedInverseEffectMap nameEq keyEq selected
            (componentProvisions component) undo)
          (MkIteratorContinuation rest) stageRuns
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
              0 nextConfinement : TransformationPreservesConfinement selected
                (componentProvisions component) nextTransformation
              nextConfinement = pushTransformationPreservesConfinement nameEq
                keyEq selected (componentProvisions component) undo
                modelTransformation generator modelConfinement generatorMap
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
                nextFactorization nextConfinement
              concreteResult : BuiltAccumulatorModel name key world error value
                nameEq keyEq selected whole concrete
                (componentProvisions component) retiredFlag targetAccumulator
              concreteResult = MkBuiltAccumulatorModel concreteModel Refl
                (\state => Refl)
          in replace
            {p = \observed => BuiltAccumulatorModel name key world error value
              nameEq keyEq selected whole observed
              (componentProvisions component) retiredFlag targetAccumulator}
            concreteIsAfter concreteResult
        AccumulatorActive modelView modelLife =>
          case modelLife of Refl impossible
        AccumulatorUnloading modelView outcome modelLife =>
          case modelLife of Refl impossible

0 partialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewrite Refl Refl related = related

advanceAccumulatorResult :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  AccumulatorHandle key value world -> EffectState name key value world ->
  EffectState name key value world
advanceAccumulatorResult nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator) state =
    let restored = accumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder provision
              (effectTables state selected)))
    in setEffectTable @{nameEq} selected (ownedValues (localTable restored))
      (setEffectAmbient (localWorld restored) state)

0 advanceAccumulatorResultRuns :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (handle : AccumulatorHandle key value world) ->
  (state : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected handle state =
    Just (advanceAccumulatorResult nameEq keyEq selected handle state)
advanceAccumulatorResultRuns nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator)
  (MkEffectState ambient tables) = Refl

public export
record SelectedAdvanceRecovery
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (before, afterState : SystemState name key value world error)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (sourceHandle : AccumulatorHandle key value world)
  (sourceRetired : Bool) where
  constructor MkSelectedAdvanceRecovery
  targetModel : AccumulatorModel name key world error value nameEq keyEq selected
    whole afterState
  0 targetRetiredSame : retired (modelFiber targetModel) = sourceRetired
  0 sourceRecovered : EffectState name key value world
  0 targetRecovered : EffectState name key value world
  0 sourceAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    sourceHandle (projectEffectState @{nameEq} before) =
    Just sourceRecovered
  0 targetAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle targetModel) (projectEffectState @{nameEq} afterState) =
    Just targetRecovered
  0 recoveredRelated : EffectStateRelated keyEq sourceRecovered targetRecovered

0 controlAdvanceRecovery :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
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
  (found : lookupFiber @{nameEq} selected (registry before) =
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view))) ->
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) ->
  (built : BuiltAccumulatorModel name key world error value nameEq keyEq selected
    whole afterState (componentProvisions component) retiredFlag accumulator) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState) ->
  SelectedAdvanceRecovery name key world error value nameEq keyEq selected before
    afterState whole (modelHandle sourceModel) (retired (modelFiber sourceModel))
controlAdvanceRecovery nameEq keyEq selected before afterState whole
  component parent retiredFlag table remaining accumulator view found sourceModel
  built projectedRelated =
    let 0 mapsSame : (state : EffectState name key value world) ->
          accumulatorEffectMap nameEq keyEq selected
            (modelHandle (builtModel built)) state =
          accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel)
            state
        mapsSame state = trans (builtMapRuntime built state)
          (reloadingModelMapRuntime nameEq keyEq selected component parent
            retiredFlag table remaining accumulator view sourceModel found state)
        0 sourceRuns : (accumulatorEffectMap nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before) =
          Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before)))
        sourceRuns = advanceAccumulatorResultRuns nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before)
        0 targetRuns : (accumulatorEffectMap nameEq keyEq selected
          (modelHandle (builtModel built))
          (projectEffectState @{nameEq} afterState) =
          Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built))
            (projectEffectState @{nameEq} afterState)))
        targetRuns = advanceAccumulatorResultRuns nameEq keyEq selected
          (modelHandle (builtModel built))
          (projectEffectState @{nameEq} afterState)
        0 respected : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel)
            (projectEffectState @{nameEq} before))
          (accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel)
            (projectEffectState @{nameEq} afterState))
        respected = accumulatorEffectMapRespects nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState) projectedRelated
        0 atOutputs : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before)))
          (Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built))
            (projectEffectState @{nameEq} afterState)))
        atOutputs = partialRelatedRewrite sourceRuns targetRuns
          (rewrite mapsSame (projectEffectState @{nameEq} afterState) in respected)
        0 related : EffectStateRelated keyEq
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before))
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built))
            (projectEffectState @{nameEq} afterState))
        related = case atOutputs of PartialDefined relation => relation
        0 sourceRetired : retired (modelFiber sourceModel) = retiredFlag
        sourceRetired = cong retired
          (justPairInjective (trans (sym (modelFound sourceModel)) found))
        0 targetToSource : retired (modelFiber (builtModel built)) =
          retired (modelFiber sourceModel)
        targetToSource = trans (builtRetired built) (sym sourceRetired)
    in MkSelectedAdvanceRecovery (builtModel built) targetToSource
      (advanceAccumulatorResult nameEq keyEq selected (modelHandle sourceModel)
        (projectEffectState @{nameEq} before))
      (advanceAccumulatorResult nameEq keyEq selected
        (modelHandle (builtModel built))
        (projectEffectState @{nameEq} afterState))
      sourceRuns targetRuns related

0 successfulAdvanceRecovery :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (whole : Transitions wholeFirst wholeLast) ->
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
  (found : lookupFiber @{nameEq} selected (registry before) =
    Just (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view))) ->
  (capability : DepValues key value
    (dependencies (componentDependencies component))) ->
  (localAfter : LocalState key value world (componentProvisions component)) ->
  (undo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  runStepEffect step capability
    (MkLocalState (worldState before)
      (restrictOwnedPreservingOrder (componentProvisions component)
        (ownedValues table))) = Right (localAfter, undo) ->
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq
    selected whole before) ->
  (built : BuiltAccumulatorModel name key world error value nameEq keyEq selected
    whole afterState (componentProvisions component) retiredFlag
    (pushLocalUndo (componentProvisions component) accumulator undo)) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} selected (ownedValues (localTable localAfter))
      (setEffectAmbient (localWorld localAfter)
        (projectEffectState @{nameEq} before)))
    (projectEffectState @{nameEq} afterState) ->
  SelectedAdvanceRecovery name key world error value nameEq keyEq selected before
    afterState whole (modelHandle sourceModel) (retired (modelFiber sourceModel))
successfulAdvanceRecovery nameEq keyEq selected before afterState whole component parent retiredFlag table step rest accumulator view found
  capability localAfter undo ran sourceModel built movedToTarget =
    let 0 sourceRuntimeToModel :
          (accumulatorRuntimeEffectMap nameEq keyEq selected accumulator
             (projectEffectState @{nameEq} before) =
           accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel)
             (projectEffectState @{nameEq} before))
        sourceRuntimeToModel = reloadingModelMapRuntime nameEq keyEq selected
          component parent retiredFlag table (step :: rest) accumulator view
          sourceModel found (projectEffectState @{nameEq} before)
        0 ranProjected : (runStepEffect step capability
          (MkLocalState (effectAmbient (projectEffectState @{nameEq} before))
            (restrictOwnedPreservingOrder (componentProvisions component)
              (effectTables (projectEffectState @{nameEq} before) selected))) =
          Right (localAfter, undo))
        ranProjected = rewrite projectedActorTable nameEq selected before
          (MkFiber component parent retiredFlag table
            (Reloading (step :: rest) accumulator view)) found in ran
        0 primitive : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (accumulatorRuntimeEffectMap nameEq keyEq selected
            (pushLocalUndo (componentProvisions component) accumulator undo)
            (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))))
          (accumulatorRuntimeEffectMap nameEq keyEq selected accumulator
            (projectEffectState @{nameEq} before))
        primitive = successfulPushEffectRecovery nameEq keyEq selected
          (componentProvisions component) accumulator step capability
          (projectEffectState @{nameEq} before) localAfter undo ranProjected
        0 primitiveAtModel : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (accumulatorEffectMap nameEq keyEq selected (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))))
          (accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel)
            (projectEffectState @{nameEq} before))
        primitiveAtModel = partialRelatedRewrite
          (sym (builtMapRuntime built (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))))) sourceRuntimeToModel primitive
        0 targetRespects : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (accumulatorEffectMap nameEq keyEq selected (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))))
          (accumulatorEffectMap nameEq keyEq selected (modelHandle (builtModel built))
            (projectEffectState @{nameEq} afterState))
        targetRespects = accumulatorEffectMapRespects nameEq keyEq selected
          (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))) (projectEffectState @{nameEq} afterState)
          movedToTarget
        0 sourceRuns : (accumulatorEffectMap nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before) =
          Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before)))
        sourceRuns = advanceAccumulatorResultRuns nameEq keyEq selected
          (modelHandle sourceModel) (projectEffectState @{nameEq} before)
        0 targetRuns : (accumulatorEffectMap nameEq keyEq selected
          (modelHandle (builtModel built)) (projectEffectState @{nameEq} afterState) =
          Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built)) (projectEffectState @{nameEq} afterState)))
        targetRuns = advanceAccumulatorResultRuns nameEq keyEq selected
          (modelHandle (builtModel built)) (projectEffectState @{nameEq} afterState)
        0 movedRuns : (accumulatorEffectMap nameEq keyEq selected
          (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))) =
          Just (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before)))))
        movedRuns = advanceAccumulatorResultRuns nameEq keyEq selected
          (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before)))
        0 primitiveOutputs : EffectStateRelated keyEq
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))))
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before))
        primitiveOutputs = case partialRelatedRewrite movedRuns sourceRuns
          primitiveAtModel of PartialDefined relation => relation
        0 targetOutputs : EffectStateRelated keyEq
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built)) (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter)
              (projectEffectState @{nameEq} before))))
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built)) (projectEffectState @{nameEq} afterState))
        targetOutputs = case partialRelatedRewrite movedRuns targetRuns
          targetRespects of PartialDefined relation => relation
        0 related : EffectStateRelated keyEq
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle sourceModel) (projectEffectState @{nameEq} before))
          (advanceAccumulatorResult nameEq keyEq selected
            (modelHandle (builtModel built)) (projectEffectState @{nameEq} afterState))
        related = transitive (EffectStateEquivalence keyEq)
          (symmetric (EffectStateEquivalence keyEq) primitiveOutputs)
          targetOutputs
        0 sourceRetired : retired (modelFiber sourceModel) = retiredFlag
        sourceRetired = cong retired
          (justPairInjective (trans (sym (modelFound sourceModel)) found))
        0 targetToSource : retired (modelFiber (builtModel built)) =
          retired (modelFiber sourceModel)
        targetToSource = trans (builtRetired built) (sym sourceRetired)
    in MkSelectedAdvanceRecovery (builtModel built) targetToSource
      (advanceAccumulatorResult nameEq keyEq selected (modelHandle sourceModel)
        (projectEffectState @{nameEq} before))
      (advanceAccumulatorResult nameEq keyEq selected (modelHandle (builtModel built))
        (projectEffectState @{nameEq} afterState))
      sourceRuns targetRuns related

0 advanceProjectedRelatedFromRun :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  (moved : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance selected) tag before
    (projectEffectState @{nameEq} before) = Just moved ->
  EffectStateRelated keyEq moved (projectEffectState @{nameEq} afterState)
advanceProjectedRelatedFromRun nameEq keyEq selected before afterState tag raw
  moved mapRuns = case advanceActualEffectFrame nameEq keyEq selected before
    afterState tag raw of
    MkActualEffectFrame framed => case partialRelatedRewrite mapRuns Refl framed of
      PartialDefined related => related

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
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAdvanceRecovery name key world error value nameEq keyEq selected before
    afterState whole (modelHandle model) (retired (modelFiber model))
selectedAdvanceFromRaw {name} {key} {world} {error} {value}
  nameEq keyEq selected (MkSystemState ambient fibers) afterState tag
  checked whole occurs
  (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
    modelTransformation modelFactorization modelConfinement)
  with (lookupFiber @{nameEq} selected fibers) proof found
  selectedAdvanceFromRaw nameEq keyEq selected
    (MkSystemState ambient fibers) afterState tag checked whole occurs
    (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
      modelTransformation modelFactorization modelConfinement) | Nothing =
        void (nothingIsNotJust modelFound)
  selectedAdvanceFromRaw nameEq keyEq selected
    (MkSystemState ambient fibers) afterState tag checked whole occurs
    (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
      modelTransformation modelFactorization modelConfinement) |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (lifecycle)
    selectedAdvanceFromRaw nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization modelConfinement) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust checked)
    selectedAdvanceFromRaw nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization modelConfinement) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust checked)
    selectedAdvanceFromRaw nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization modelConfinement) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome = void (nothingIsNotJust checked)
    selectedAdvanceFromRaw nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization modelConfinement) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading [] accumulator view)) fibers) view) proof matches
      selectedAdvanceFromRaw nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization modelConfinement) |
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
            0 tagShape : tag = LFinishTag
            tagShape = sym (cong fst (justPairInjective raw))
            0 rawConcrete : (applyAction @{nameEq} @{keyEq}
              (the (Action name key value world error) (LAdvance selected))
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)) = Just (tag, afterState))
            rawConcrete = rewrite found in rewrite matches in raw
            0 mapRuns : partialEffectMapFor nameEq keyEq
              (the (Action name key value world error) (LAdvance selected)) tag
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers))
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))) =
              Just (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
            mapRuns = rewrite tagShape in rewrite found in Refl
            0 projectedRelated : EffectStateRelated keyEq
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
              (projectEffectState @{nameEq} afterState)
            projectedRelated = advanceProjectedRelatedFromRun nameEq keyEq
              selected (MkSystemState ambient fibers) afterState tag rawConcrete
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))) mapRuns
        in controlAdvanceRecovery nameEq keyEq selected
          (MkSystemState ambient fibers) afterState whole component
          parent retiredFlag table [] accumulator view found
          (MkAccumulatorModel modelFiber (trans found modelFound) modelAccumulator
            modelInstalled modelTransformation modelFactorization
            modelConfinement)
          (controlAdvanceModel nameEq keyEq selected ambient fibers afterState
            whole component parent retiredFlag table [] accumulator view found
            ambient table (Active accumulator view) (AccumulatorActive view Refl)
            concrete concreteShape concreteIsAfter modelFiber
            (trans found modelFound) modelAccumulator modelInstalled
            modelTransformation modelFactorization modelConfinement)
          projectedRelated
      selectedAdvanceFromRaw nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization modelConfinement) |
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
            0 tagShape : tag = LDivertTag
            tagShape = sym (cong fst (justPairInjective raw))
            0 rawConcrete : (applyAction @{nameEq} @{keyEq}
              (the (Action name key value world error) (LAdvance selected))
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)) = Just (tag, afterState))
            rawConcrete = rewrite found in rewrite matches in raw
            0 mapRuns : partialEffectMapFor nameEq keyEq
              (the (Action name key value world error) (LAdvance selected)) tag
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers))
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))) =
              Just (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
            mapRuns = rewrite tagShape in rewrite found in Refl
            0 projectedRelated : EffectStateRelated keyEq
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)))
              (projectEffectState @{nameEq} afterState)
            projectedRelated = advanceProjectedRelatedFromRun nameEq keyEq
              selected (MkSystemState ambient fibers) afterState tag rawConcrete
              (projectEffectState @{nameEq}
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))) mapRuns
        in controlAdvanceRecovery nameEq keyEq selected
          (MkSystemState ambient fibers) afterState whole component
          parent retiredFlag table [] accumulator view found
          (MkAccumulatorModel modelFiber (trans found modelFound) modelAccumulator
            modelInstalled modelTransformation modelFactorization
            modelConfinement)
          (controlAdvanceModel nameEq keyEq selected ambient fibers afterState
            whole component parent retiredFlag table [] accumulator view found
            ambient table (Unloading accumulator view Nothing)
            (AccumulatorUnloading view Nothing Refl) concrete concreteShape
            concreteIsAfter modelFiber (trans found modelFound) modelAccumulator
            modelInstalled modelTransformation modelFactorization
            modelConfinement) projectedRelated
    selectedAdvanceFromRaw nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag checked whole occurs
      (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
        modelTransformation modelFactorization modelConfinement) |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view fibers) proof resolved
      selectedAdvanceFromRaw nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization modelConfinement) |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Nothing =
              void (nothingIsNotJust checked)
      selectedAdvanceFromRaw nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag checked whole occurs
        (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
          modelTransformation modelFactorization modelConfinement) |
          Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Just capability
        with (runStepEffect step capability
          (MkLocalState ambient
            (restrictOwnedPreservingOrder (componentProvisions component)
              (ownedValues table)))) proof ran
        selectedAdvanceFromRaw nameEq keyEq selected
          (MkSystemState ambient fibers) afterState tag checked whole occurs
          (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
            modelTransformation modelFactorization modelConfinement) |
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
              0 tagShape : tag = LRaiseTag
              tagShape = sym (cong fst (justPairInjective raw))
              0 rawConcrete : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LAdvance selected))
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers)) = Just (tag, afterState))
              rawConcrete = rewrite found in rewrite resolved in rewrite ran in raw
              0 mapRuns : partialEffectMapFor nameEq keyEq
                (the (Action name key value world error) (LAdvance selected)) tag
                (the (SystemState name key value world error)
                  (MkSystemState ambient fibers))
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))) =
                Just (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers)))
              mapRuns = rewrite tagShape in Refl
              0 projectedRelated : EffectStateRelated keyEq
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers)))
                (projectEffectState @{nameEq} afterState)
              projectedRelated = advanceProjectedRelatedFromRun nameEq keyEq
                selected (MkSystemState ambient fibers) afterState tag rawConcrete
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))) mapRuns
          in controlAdvanceRecovery nameEq keyEq selected
            (MkSystemState ambient fibers) afterState whole component
            parent retiredFlag table (step :: rest) accumulator view found
            (MkAccumulatorModel modelFiber (trans found modelFound) modelAccumulator
            modelInstalled modelTransformation modelFactorization
            modelConfinement)
            (controlAdvanceModel nameEq keyEq selected ambient fibers afterState
              whole component parent retiredFlag table (step :: rest) accumulator
              view found ambient table (Unloading accumulator view (Just err))
              (AccumulatorUnloading view (Just err) Refl) concrete concreteShape
              concreteIsAfter modelFiber (trans found modelFound)
              modelAccumulator modelInstalled modelTransformation
              modelFactorization modelConfinement) projectedRelated
        selectedAdvanceFromRaw nameEq keyEq selected
          (MkSystemState ambient fibers) afterState tag checked whole occurs
          (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
            modelTransformation modelFactorization modelConfinement) |
            Just (MkFiber component parent retiredFlag table lifecycle) |
              Reloading (step :: rest) accumulator view | Just capability |
                Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)) fibers) view) proof matches
          selectedAdvanceFromRaw nameEq keyEq selected
            (MkSystemState ambient fibers) afterState tag checked whole occurs
            (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
              modelTransformation modelFactorization modelConfinement) |
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
                0 tagShape : tag = LDivertTag
                tagShape = sym (cong fst (justPairInjective raw))
                0 rawConcrete : (applyAction @{nameEq} @{keyEq}
                  (the (Action name key value world error) (LAdvance selected))
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers)) = Just (tag, afterState))
                rawConcrete = rewrite found in rewrite resolved in rewrite ran in
                  rewrite matches in raw
                0 resolvedEffect : (resolveEffectValues @{keyEq}
                  (dependencies (componentDependencies component)) view
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) = Just capability)
                resolvedEffect = trans (resolveEffectValuesProjected nameEq keyEq
                  (dependencies (componentDependencies component)) view
                  (MkSystemState ambient fibers)) resolved
                0 mapRuns : (partialEffectMapFor nameEq keyEq
                  (the (Action name key value world error) (LAdvance selected))
                  tag (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) =
                  Just (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers))))))
                mapRuns = rewrite tagShape in
                  rewrite advanceDivertMapSameAsIter nameEq keyEq selected
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState ambient fibers))) in
                  partialEffectMapAdvanceIterRuns nameEq keyEq selected ambient
                    fibers component parent retiredFlag table step rest accumulator
                    view capability found resolvedEffect localAfter undo ran
                0 movedToTarget : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers)))))
                  (projectEffectState @{nameEq} afterState)
                movedToTarget = advanceProjectedRelatedFromRun nameEq keyEq
                  selected (MkSystemState ambient fibers) afterState tag
                  rawConcrete
                  (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers))))) mapRuns
                0 built : BuiltAccumulatorModel name key world error value
                  nameEq keyEq selected whole afterState
                  (componentProvisions component) retiredFlag
                  (pushLocalUndo (componentProvisions component) accumulator undo)
                built = successfulAdvanceModel nameEq keyEq selected
                  (MkSystemState ambient fibers) afterState tag whole anchor
                  component parent retiredFlag table step rest accumulator view
                  found capability resolved localAfter undo ran
                  (Unloading
                    (pushLocalUndo (componentProvisions component) accumulator undo)
                    view Nothing)
                  (AccumulatorUnloading view Nothing Refl) concrete concreteShape
                  concreteIsAfter modelFiber (trans found modelFound)
                  modelAccumulator modelInstalled modelTransformation
                  modelFactorization modelConfinement
            in successfulAdvanceRecovery nameEq keyEq selected
              (MkSystemState ambient fibers) afterState whole component parent
              retiredFlag table step rest accumulator view found capability
              localAfter undo ran
              (MkAccumulatorModel modelFiber (trans found modelFound)
                modelAccumulator modelInstalled modelTransformation
                modelFactorization modelConfinement)
              built movedToTarget
          selectedAdvanceFromRaw nameEq keyEq selected
            (MkSystemState ambient fibers) afterState tag checked whole occurs
            (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
              modelTransformation modelFactorization modelConfinement) |
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
                0 tagShape : tag = LFinishTag
                tagShape = sym (cong fst (justPairInjective raw))
                0 rawConcrete : (applyAction @{nameEq} @{keyEq}
                  (the (Action name key value world error) (LAdvance selected))
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers)) = Just (tag, afterState))
                rawConcrete = rewrite found in rewrite resolved in rewrite ran in
                  rewrite matches in raw
                0 resolvedEffect : (resolveEffectValues @{keyEq}
                  (dependencies (componentDependencies component)) view
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) = Just capability)
                resolvedEffect = trans (resolveEffectValuesProjected nameEq keyEq
                  (dependencies (componentDependencies component)) view
                  (MkSystemState ambient fibers)) resolved
                0 mapRuns : (partialEffectMapFor nameEq keyEq
                  (the (Action name key value world error) (LAdvance selected))
                  tag (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) =
                  Just (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers))))))
                mapRuns = rewrite tagShape in
                  partialEffectMapAdvanceFinishRuns nameEq keyEq selected ambient
                    fibers component parent retiredFlag table step [] accumulator
                    view capability found resolvedEffect localAfter undo ran
                0 movedToTarget : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers)))))
                  (projectEffectState @{nameEq} afterState)
                movedToTarget = advanceProjectedRelatedFromRun nameEq keyEq
                  selected (MkSystemState ambient fibers) afterState tag
                  rawConcrete
                  (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers))))) mapRuns
                0 built : BuiltAccumulatorModel name key world error value
                  nameEq keyEq selected whole afterState
                  (componentProvisions component) retiredFlag
                  (pushLocalUndo (componentProvisions component) accumulator undo)
                built = successfulAdvanceModel nameEq keyEq selected
                  (MkSystemState ambient fibers) afterState tag whole anchor
                  component parent retiredFlag table step [] accumulator view
                  found capability resolved localAfter undo ran
                  (Active
                    (pushLocalUndo (componentProvisions component) accumulator undo)
                    view)
                  (AccumulatorActive view Refl) concrete concreteShape
                  concreteIsAfter modelFiber (trans found modelFound)
                  modelAccumulator modelInstalled modelTransformation
                  modelFactorization modelConfinement
            in successfulAdvanceRecovery nameEq keyEq selected
              (MkSystemState ambient fibers) afterState whole component parent
              retiredFlag table step [] accumulator view found capability
              localAfter undo ran
              (MkAccumulatorModel modelFiber (trans found modelFound)
                modelAccumulator modelInstalled modelTransformation
                modelFactorization modelConfinement)
              built movedToTarget
          selectedAdvanceFromRaw nameEq keyEq selected
            (MkSystemState ambient fibers) afterState tag checked whole occurs
            (MkAccumulatorModel modelFiber modelFound modelAccumulator modelInstalled
              modelTransformation modelFactorization modelConfinement) |
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
                0 tagShape : tag = LIterTag
                tagShape = sym (cong fst (justPairInjective raw))
                0 rawConcrete : (applyAction @{nameEq} @{keyEq}
                  (the (Action name key value world error) (LAdvance selected))
                  (the (SystemState name key value world error)
                    (MkSystemState ambient fibers)) = Just (tag, afterState))
                rawConcrete = rewrite found in rewrite resolved in rewrite ran in
                  rewrite matches in raw
                0 resolvedEffect : (resolveEffectValues @{keyEq}
                  (dependencies (componentDependencies component)) view
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) = Just capability)
                resolvedEffect = trans (resolveEffectValuesProjected nameEq keyEq
                  (dependencies (componentDependencies component)) view
                  (MkSystemState ambient fibers)) resolved
                0 mapRuns : (partialEffectMapFor nameEq keyEq
                  (the (Action name key value world error) (LAdvance selected))
                  tag (the (SystemState name key value world error)
                    (MkSystemState ambient fibers))
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState ambient fibers))) =
                  Just (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers))))))
                mapRuns = rewrite tagShape in
                  partialEffectMapAdvanceIterRuns nameEq keyEq selected ambient
                    fibers component parent retiredFlag table step
                    (nextStep :: more) accumulator view capability found
                    resolvedEffect localAfter undo ran
                0 movedToTarget : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers)))))
                  (projectEffectState @{nameEq} afterState)
                movedToTarget = advanceProjectedRelatedFromRun nameEq keyEq
                  selected (MkSystemState ambient fibers) afterState tag
                  rawConcrete
                  (setEffectTable @{nameEq} selected
                    (ownedValues (localTable localAfter))
                    (setEffectAmbient (localWorld localAfter)
                      (projectEffectState @{nameEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient fibers))))) mapRuns
                0 built : BuiltAccumulatorModel name key world error value
                  nameEq keyEq selected whole afterState
                  (componentProvisions component) retiredFlag
                  (pushLocalUndo (componentProvisions component) accumulator undo)
                built = successfulAdvanceModel nameEq keyEq selected
                  (MkSystemState ambient fibers) afterState tag whole anchor
                  component parent retiredFlag table step (nextStep :: more)
                  accumulator view found capability resolved localAfter undo ran
                  (Reloading (nextStep :: more)
                    (pushLocalUndo (componentProvisions component) accumulator undo)
                    view)
                  (AccumulatorReloading (nextStep :: more) view Refl) concrete
                  concreteShape concreteIsAfter modelFiber (trans found modelFound)
                  modelAccumulator modelInstalled modelTransformation
                  modelFactorization modelConfinement
            in successfulAdvanceRecovery nameEq keyEq selected
              (MkSystemState ambient fibers) afterState whole component parent
              retiredFlag table step (nextStep :: more) accumulator view found
              capability localAfter undo ran
              (MkAccumulatorModel modelFiber (trans found modelFound)
                modelAccumulator modelInstalled modelTransformation
                modelFactorization modelConfinement)
              built movedToTarget

||| Public checked-step recovery specialization. Every control branch preserves
||| the old accumulator map; every successful iterator branch applies the
||| Finding-#11 conditional inverse at its canonical source.
public export
0 selectedAdvanceAccumulatorRecovery :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq
      (LAdvance selected) tag checked) whole) ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  SelectedAdvanceRecovery name key world error value nameEq keyEq selected before
    afterState whole (modelHandle model) (retired (modelFiber model))
selectedAdvanceAccumulatorRecovery nameEq keyEq selected before afterState tag
  checked whole occurs model =
    selectedAdvanceFromRaw nameEq keyEq selected before afterState tag checked
      {raw = advanceRaw checked} whole occurs
      {anchor = MkAdvanceOccurrence checked occurs} model

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
    targetModel (selectedAdvanceFromRaw nameEq keyEq selected before afterState
      tag checked {raw = advanceRaw checked} whole occurs
      {anchor = MkAdvanceOccurrence checked occurs} model)
