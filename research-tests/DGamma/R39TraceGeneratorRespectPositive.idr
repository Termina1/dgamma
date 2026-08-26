module DGamma.R39TraceGeneratorRespectPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R39RelationalMapAlgebraPositive
import DGamma.R39AdvanceYieldedMapProducerPositive
import Decidable.Equality

%default total

0 r39ReindexEffectRelated :
  EffectStateRelated leftKeyEq left right ->
  EffectStateRelated rightKeyEq left right
r39ReindexEffectRelated (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated ambient tables

0 r39ReindexPartialRelated :
  PartialRelated (EffectState name key value world)
    (EffectStateRelated leftKeyEq) left right ->
  PartialRelated (EffectState name key value world)
    (EffectStateRelated rightKeyEq) left right
r39ReindexPartialRelated PartialUndefined = PartialUndefined
r39ReindexPartialRelated (PartialDefined related) =
  PartialDefined (r39ReindexEffectRelated related)

0 r39LookupBindingFromEqualBindings :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  lookupBinding @{keyEq} wanted left = lookupBinding @{keyEq} wanted right
r39LookupBindingFromEqualBindings keyEq wanted
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    cong (lookupEntries @{keyEq} wanted) same

0 r39ResolveEffectValuesRelated :
  (keyEq : DecEq key) -> (deps : List key) -> (view : View name deps) ->
  {left, right : EffectState name key value world} ->
  EffectStateRelated keyEq left right ->
  resolveEffectValues @{keyEq} deps view left =
    resolveEffectValues @{keyEq} deps view right
r39ResolveEffectValuesRelated keyEq [] EmptyView related = Refl
r39ResolveEffectValuesRelated keyEq (wanted :: rest)
  (ProviderView provider later) related
  with (lookupBinding @{keyEq} wanted (effectTables left provider)) proof leftLookup
  r39ResolveEffectValuesRelated keyEq (wanted :: rest)
    (ProviderView provider later) related | Nothing =
      let lookupSame = r39LookupBindingFromEqualBindings keyEq wanted
            (effectTables left provider) (effectTables right provider)
            (tablesExact related provider)
          rightLookup = trans (sym lookupSame) leftLookup
      in rewrite rightLookup in Refl
  r39ResolveEffectValuesRelated keyEq (wanted :: rest)
    (ProviderView provider later) related | Just found =
      let lookupSame = r39LookupBindingFromEqualBindings keyEq wanted
            (effectTables left provider) (effectTables right provider)
            (tablesExact related provider)
          rightLookup = trans (sym lookupSame) leftLookup
      in rewrite rightLookup in cong (map (OneDepValue found))
        (r39ResolveEffectValuesRelated keyEq rest later related)

0 r39SetActorRuntimeRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (worldValue : world) -> (table : CoeffectContext key value) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor table
      (setEffectAmbient worldValue left))
    (setEffectTable @{nameEq} actor table
      (setEffectAmbient worldValue right))
r39SetActorRuntimeRelated nameEq keyEq actor worldValue table left right related =
  MkEffectStateRelated Refl tables
  where
  0 tables : (selected : name) ->
    bindings (effectTables
      (setEffectTable @{nameEq} actor table
        (setEffectAmbient worldValue left)) selected) =
    bindings (effectTables
      (setEffectTable @{nameEq} actor table
        (setEffectAmbient worldValue right)) selected)
  tables selected with (decEq @{nameEq} selected actor)
    tables selected | Yes same = case same of Refl => Refl
    tables selected | No distinct = tablesExact related selected

||| Strengthened probe version of `iteratorStageOutcomeRelated`.  The
||| successful branch retains the yielded forward-state relation required by
||| the iterator-forward generator; the yielded inverse remains related by the
||| existing same-input Equation-55 clause.
public export
0 r39IteratorStageRuntimeOutcomeRelated :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage right) (iteratorStageOutcome stage left)
r39IteratorStageRuntimeOutcomeRelated {name} {key} {world} {error} {value}
  keyEq (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
    remaining accumulator view lifecycle step rest suffix) left right related
  with (resolveEffectValues @{stageKeyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view left)
    proof leftResolved
  r39IteratorStageRuntimeOutcomeRelated keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix)
    left right related | Nothing =
      let 0 stageRelated : EffectStateRelated stageKeyEq left right
          stageRelated = r39ReindexEffectRelated related
          0 resolvedSame :
            resolveEffectValues @{stageKeyEq}
              (dependencies (componentDependencies (fiberComponent fiber))) view
              left =
            resolveEffectValues @{stageKeyEq}
              (dependencies (componentDependencies (fiberComponent fiber))) view
              right
          resolvedSame = r39ResolveEffectValuesRelated stageKeyEq
            (dependencies (componentDependencies (fiberComponent fiber))) view
            stageRelated
          0 rightResolved : resolveEffectValues @{stageKeyEq}
            (dependencies (componentDependencies (fiberComponent fiber))) view
            right = Nothing
          rightResolved = trans (sym resolvedSame) leftResolved
      in rewrite rightResolved in RuntimeOutcomesUndefined
  r39IteratorStageRuntimeOutcomeRelated keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix)
    left right related | Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient left)
        (restrictOwnedPreservingOrder @{stageKeyEq}
          (componentProvisions (fiberComponent fiber))
          (effectTables left actor)))) proof leftRan
    r39IteratorStageRuntimeOutcomeRelated keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix)
      left right related | Just capability | Left failure =
        let 0 stageRelated : EffectStateRelated stageKeyEq left right
            stageRelated = r39ReindexEffectRelated related
            0 resolvedSame :
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view left =
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view right
            resolvedSame = r39ResolveEffectValuesRelated stageKeyEq
              (dependencies (componentDependencies (fiberComponent fiber))) view
              stageRelated
            0 rightResolved : resolveEffectValues @{stageKeyEq}
              (dependencies (componentDependencies (fiberComponent fiber))) view
              right = Just capability
            rightResolved = trans (sym resolvedSame) leftResolved
            0 ownedSame :
              restrictOwnedPreservingOrder @{stageKeyEq}
                (componentProvisions (fiberComponent fiber))
                (effectTables left actor) =
              restrictOwnedPreservingOrder @{stageKeyEq}
                (componentProvisions (fiberComponent fiber))
                (effectTables right actor)
            ownedSame = canonicalNormalizationFromEqualBindings @{stageKeyEq}
              (componentProvisions (fiberComponent fiber))
              (effectTables left actor) (effectTables right actor)
              (tablesExact stageRelated actor)
            0 localSame :
              MkLocalState (effectAmbient left)
                (restrictOwnedPreservingOrder @{stageKeyEq}
                  (componentProvisions (fiberComponent fiber))
                  (effectTables left actor)) =
              MkLocalState (effectAmbient right)
                (restrictOwnedPreservingOrder @{stageKeyEq}
                  (componentProvisions (fiberComponent fiber))
                  (effectTables right actor))
            localSame = rewrite ambientExact stageRelated in
              rewrite ownedSame in Refl
            runSame = cong (runStepEffect step capability) localSame
            rightRan = trans (sym runSame) leftRan
        in rewrite rightResolved in rewrite rightRan in
          RuntimeFailuresAgree Refl
    r39IteratorStageRuntimeOutcomeRelated keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix)
      left right related | Just capability | Right (after, undo) =
        let 0 stageRelated : EffectStateRelated stageKeyEq left right
            stageRelated = r39ReindexEffectRelated related
            0 resolvedSame :
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view left =
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view right
            resolvedSame = r39ResolveEffectValuesRelated stageKeyEq
              (dependencies (componentDependencies (fiberComponent fiber))) view
              stageRelated
            0 rightResolved : resolveEffectValues @{stageKeyEq}
              (dependencies (componentDependencies (fiberComponent fiber))) view
              right = Just capability
            rightResolved = trans (sym resolvedSame) leftResolved
            0 ownedSame :
              restrictOwnedPreservingOrder @{stageKeyEq}
                (componentProvisions (fiberComponent fiber))
                (effectTables left actor) =
              restrictOwnedPreservingOrder @{stageKeyEq}
                (componentProvisions (fiberComponent fiber))
                (effectTables right actor)
            ownedSame = canonicalNormalizationFromEqualBindings @{stageKeyEq}
              (componentProvisions (fiberComponent fiber))
              (effectTables left actor) (effectTables right actor)
              (tablesExact stageRelated actor)
            0 localSame :
              MkLocalState (effectAmbient left)
                (restrictOwnedPreservingOrder @{stageKeyEq}
                  (componentProvisions (fiberComponent fiber))
                  (effectTables left actor)) =
              MkLocalState (effectAmbient right)
                (restrictOwnedPreservingOrder @{stageKeyEq}
                  (componentProvisions (fiberComponent fiber))
                  (effectTables right actor))
            localSame = rewrite ambientExact stageRelated in
              rewrite ownedSame in Refl
            runSame = cong (runStepEffect step capability) localSame
            rightRan = trans (sym runSame) leftRan
            0 outputRelatedAtStage : EffectStateRelated stageKeyEq
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) left))
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) right))
            outputRelatedAtStage = r39SetActorRuntimeRelated nameEq stageKeyEq
              actor (localWorld after) (ownedValues (localTable after)) left right
              stageRelated
            0 outputRelated : EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) left))
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) right))
            outputRelated = r39ReindexEffectRelated outputRelatedAtStage
            undoMap = yieldedInverseEffectMap nameEq stageKeyEq actor
              (componentProvisions (fiberComponent fiber)) undo
        in rewrite rightResolved in rewrite rightRan in
          RuntimeYieldsAgree outputRelated
            (effectPartialMapReflexive keyEq undoMap)

0 r39IteratorForwardProjectionExact :
  (stage : IteratorStage name key world error value actor trace) ->
  (state : EffectState name key value world) ->
  r39RuntimeForwardProjection (iteratorStageOutcome stage state) =
    traceGeneratorMap (IteratorForwardGenerator stage) state
r39IteratorForwardProjectionExact
  (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
    accumulator view lifecycle step rest suffix) state
  with (resolveEffectValues @{keyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view state)
  r39IteratorForwardProjectionExact
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
      accumulator view lifecycle step rest suffix) state | Nothing = Refl
  r39IteratorForwardProjectionExact
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
      accumulator view lifecycle step rest suffix) state | Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient state)
        (restrictOwnedPreservingOrder @{keyEq}
          (componentProvisions (fiberComponent fiber))
          (effectTables state actor))))
    r39IteratorForwardProjectionExact
      (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) state |
        Just capability | Left failure = Refl
    r39IteratorForwardProjectionExact
      (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) state |
        Just capability | Right (after, undo) = Refl

||| The forward generator is exactly the successful-forward projection of the
||| strengthened runtime outcome relation.
public export
0 r39IteratorForwardGeneratorMapRespects :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap (IteratorForwardGenerator stage))
    (traceGeneratorMap (IteratorForwardGenerator stage))
r39IteratorForwardGeneratorMapRespects keyEq stage {x} {y} inputs =
  r39PartialRewrite
    (r39IteratorForwardProjectionExact stage x)
    (r39IteratorForwardProjectionExact stage y)
    (r39RuntimeForwardAgreementProjection
      (r39IteratorStageRuntimeOutcomeRelated keyEq stage x y inputs))

||| Every yielded generator's inverse is producer-known to be a lifted local
||| undo.  Splitting the immutable stage invocation exposes that map and reuses
||| the accumulator-map respect theorem.
public export
0 r39IteratorYieldedGeneratorMapRespects :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  (origin : EffectState name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap (IteratorYieldedGenerator stage origin))
    (traceGeneratorMap (IteratorYieldedGenerator stage origin))
r39IteratorYieldedGeneratorMapRespects {name} {key} {world} {error} {value}
  keyEq (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
    remaining accumulator view lifecycle step rest suffix) origin {x} {y} inputs
  with (resolveEffectValues @{stageKeyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view origin)
    proof resolved
  r39IteratorYieldedGeneratorMapRespects keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix) origin inputs |
      Nothing = PartialUndefined
  r39IteratorYieldedGeneratorMapRespects keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix) origin inputs |
      Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient origin)
        (restrictOwnedPreservingOrder @{stageKeyEq}
          (componentProvisions (fiberComponent fiber))
          (effectTables origin actor)))) proof ran
    r39IteratorYieldedGeneratorMapRespects keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) origin inputs |
        Just capability | Left failure = PartialUndefined
    r39IteratorYieldedGeneratorMapRespects keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) origin inputs |
        Just capability | Right (after, undo) =
          r39ReindexPartialRelated
            (accumulatorRuntimeEffectMapRespects nameEq stageKeyEq actor
              (componentProvisions (fiberComponent fiber)) undo x y
              (r39ReindexEffectRelated inputs))

||| Identity-correspondence producer probe over all three Definition-54
||| generator constructors.  This is the anti-oscillation check needed by
||| finite-derivation and operational-permutation terminators.
public export
0 r39TraceGeneratorMapRespects :
  (keyEq : DecEq key) ->
  (generator : TraceEffectGenerator name key world error value actor trace) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap generator) (traceGeneratorMap generator)
r39TraceGeneratorMapRespects = replayTraceGeneratorMapRespects
