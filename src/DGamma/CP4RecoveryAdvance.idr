module DGamma.CP4RecoveryAdvance

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4DeletionFrameCore
import DGamma.Unified
import Decidable.Equality

%default total

||| The actual projected source evaluates a reachable current iterator stage
||| with exactly the capability/result/undo used by the checked L-Advance rule.
public export
0 actualIteratorStageYields :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  {whole : Transitions wholeFirst wholeLast} ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq (LAdvance selected) tag checked) whole) ->
  (fiber : Fiber name key value world error) ->
  (found : lookupFiber @{nameEq} selected (registry before) = Just fiber) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (life : fiberLifecycle fiber = Reloading (step :: rest) accumulator view) ->
  (capability : DepValues key value
    (dependencies (componentDependencies (fiberComponent fiber))) ) ->
  (resolved : resolveCommittedValues   {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies (fiberComponent fiber))) view
    (registry before) = Just capability) ->
  (localAfter : LocalState key value world
    (componentProvisions (fiberComponent fiber))) ->
  (undo : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (ran : runStepEffect step capability
    (MkLocalState (worldState before)
      (restrictOwnedPreservingOrder
        (componentProvisions (fiberComponent fiber))
        (ownedValues (fiberTable fiber)))) = Right (localAfter, undo)) ->
  let stage = StageFromAdvance nameEq keyEq selected tag checked occurs fiber
        found (step :: rest) accumulator view life step rest SuffixHere
      origin = projectEffectState @{nameEq} before
  in iteratorStageEffect stage origin = Just
    (setEffectTable @{nameEq} selected (ownedValues (localTable localAfter))
      (setEffectAmbient (localWorld localAfter) origin),
     yieldedInverseEffectMap nameEq keyEq selected
       (componentProvisions (fiberComponent fiber)) undo,
     MkIteratorContinuation rest)
actualIteratorStageYields {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState tag checked occurs fiber found step rest
  accumulator view life capability resolved localAfter undo ran =
    rewrite resolveEffectValuesProjected nameEq keyEq
      (dependencies (componentDependencies (fiberComponent fiber))) view before in
    rewrite resolved in rewrite projectedActorTable nameEq selected before fiber
      found in rewrite ran in Refl

0 yieldedGeneratorMapFromStageRun :
  (stage : IteratorStage name key world error value selected whole) ->
  (origin, after : EffectState name key value world) ->
  (undo : PartialEffectMap name key value world) ->
  (continuation : IteratorContinuation key value world error) ->
  iteratorStageEffect stage origin = Just (after, undo, continuation) ->
  (state : EffectState name key value world) ->
  traceGeneratorMap (IteratorYieldedGenerator stage origin) state = undo state
yieldedGeneratorMapFromStageRun stage origin after undo continuation stageRuns
  state = rewrite stageRuns in Refl

||| One successful actual L-Advance extends the selected accumulator's generated
||| transformation by the exact yielded inverse occurrence. This is the
||| temporal induction's only accumulator-changing branch.
public export
0 successfulAdvancePushesAccumulatorFactorization :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState)) ->
  {whole : Transitions wholeFirst wholeLast} ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq (LAdvance selected) tag checked) whole) ->
  (fiber : Fiber name key value world error) ->
  (found : lookupFiber @{nameEq} selected (registry before) = Just fiber) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (life : fiberLifecycle fiber = Reloading (step :: rest) accumulator view) ->
  (capability : DepValues key value
    (dependencies (componentDependencies (fiberComponent fiber))) ) ->
  (resolved : resolveCommittedValues   {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies (fiberComponent fiber))) view
    (registry before) = Just capability) ->
  (localAfter : LocalState key value world
    (componentProvisions (fiberComponent fiber))) ->
  (undo : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (ran : runStepEffect step capability
    (MkLocalState (worldState before)
      (restrictOwnedPreservingOrder
        (componentProvisions (fiberComponent fiber))
        (ownedValues (fiberTable fiber)))) = Right (localAfter, undo)) ->
  (old : TraceEffectTransformation name key world error value selected whole) ->
  AccumulatorFactorization nameEq keyEq selected
    (componentProvisions (fiberComponent fiber)) accumulator old ->
  let stage = StageFromAdvance nameEq keyEq selected tag checked occurs fiber
        found (step :: rest) accumulator view life step rest SuffixHere
      generator = IteratorYieldedGenerator stage
        (projectEffectState @{nameEq} before)
  in AccumulatorFactorization nameEq keyEq selected
    (componentProvisions (fiberComponent fiber))
    (pushLocalUndo (componentProvisions (fiberComponent fiber)) accumulator undo)
    (TraceCompose old (TraceGenerator generator))
successfulAdvancePushesAccumulatorFactorization nameEq keyEq selected before
  afterState tag checked occurs fiber found step rest accumulator view life
  capability resolved localAfter undo ran old oldFactor =
    let stage : IteratorStage name key world error value selected whole
        stage = StageFromAdvance nameEq keyEq selected tag checked occurs fiber
          found (step :: rest) accumulator view life step rest SuffixHere
        origin : EffectState name key value world
        origin = projectEffectState @{nameEq} before
        generator : TraceEffectGenerator name key world error value selected whole
        generator = IteratorYieldedGenerator stage origin
        0 stageRuns : iteratorStageEffect stage origin = Just
          (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter) origin),
           yieldedInverseEffectMap nameEq keyEq selected
             (componentProvisions (fiberComponent fiber)) undo,
           MkIteratorContinuation rest)
        stageRuns = actualIteratorStageYields nameEq keyEq selected before
          afterState tag checked occurs fiber found step rest accumulator view
          life capability resolved localAfter undo ran
        0 generatorMap : (state : EffectState name key value world) ->
          traceGeneratorMap generator state = yieldedInverseEffectMap nameEq
            keyEq selected (componentProvisions (fiberComponent fiber)) undo state
        generatorMap = yieldedGeneratorMapFromStageRun stage origin
          (setEffectTable @{nameEq} selected
            (ownedValues (localTable localAfter))
            (setEffectAmbient (localWorld localAfter) origin))
          (yieldedInverseEffectMap nameEq keyEq selected
            (componentProvisions (fiberComponent fiber)) undo)
          (MkIteratorContinuation rest) stageRuns
    in pushAccumulatorFactorization nameEq keyEq selected
      (componentProvisions (fiberComponent fiber)) accumulator undo old generator
      oldFactor generatorMap
