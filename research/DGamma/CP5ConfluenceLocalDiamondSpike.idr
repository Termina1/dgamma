module DGamma.CP5ConfluenceLocalDiamondSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Core
import DGamma.Unified
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionControlOrchestration
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionPlanSuccess
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionFrameRetire
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP4DeletionSelectedForeignLifecycleDivert
import DGamma.CP4DeletionSelectedForeignLifecycleLeave
import DGamma.CP4DeletionSelectedForeignLifecycleUnload
import DGamma.CP4DeletionSelectedForeignLifecycleFrame
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome
import DGamma.CP4Support
import Data.Nat
import Data.Maybe
import Data.List.Elem
import Decidable.Equality

%default total

||| Exactly the three paper-Lemma-71 activation rules.  The host collapses
||| L-Iter and L-Finish into the action LAdvance and distinguishes them by tag.
public export
data PaperActivationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  PaperBeginStep :
    transitionAction transition = LBegin actor ->
    transitionTag transition = LBeginTag ->
    PaperActivationStep transition
  PaperIterStep :
    transitionAction transition = LAdvance actor ->
    transitionTag transition = LIterTag ->
    PaperActivationStep transition
  PaperFinishStep :
    transitionAction transition = LAdvance actor ->
    transitionTag transition = LFinishTag ->
    PaperActivationStep transition

||| The three explicit host orchestration rules.
public export
data PaperOrchestrationStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  PaperInsertStep :
    transitionAction transition = OInsert actor parent component ->
    PaperOrchestrationStep transition
  PaperRetireStep :
    transitionAction transition = ORetire actor ->
    PaperOrchestrationStep transition
  PaperRemoveStep :
    transitionAction transition = ORemove actor ->
    PaperOrchestrationStep transition


||| Relational map algebra used by the revision-20 replay boundary.
0 replayEffectRelatedSymmetric :
  EffectStateRelated keyEq left right -> EffectStateRelated keyEq right left
replayEffectRelatedSymmetric (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\actor => sym (tables actor))

0 replayEffectRelatedTransitive :
  EffectStateRelated keyEq left middle ->
  EffectStateRelated keyEq middle right ->
  EffectStateRelated keyEq left right
replayEffectRelatedTransitive (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

0 replayPartialRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
replayPartialRewrite Refl Refl related = related

0 replayEffectPartialSymmetric :
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    right left
replayEffectPartialSymmetric PartialUndefined = PartialUndefined
replayEffectPartialSymmetric (PartialDefined related) =
  PartialDefined (replayEffectRelatedSymmetric related)

0 replayEffectPartialTransitive :
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    first middle ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    middle last ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    first last
replayEffectPartialTransitive PartialUndefined PartialUndefined = PartialUndefined
replayEffectPartialTransitive (PartialDefined first) (PartialDefined second) =
  PartialDefined (replayEffectRelatedTransitive first second)

||| Every currently retained exact producer supplies the relational candidate
||| because each transition map already respects `EffectStateRelated`.
0 replayExactMapsGivePartialMapsRelated :
  (source, target : PartialEffectMap name key value world) ->
  EffectPartialMapRespects keyEq target ->
  ((state : EffectState name key value world) -> source state = target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) source target
replayExactMapsGivePartialMapsRelated source target targetRespects exact
  {x} {y} inputs =
    replayPartialRewrite (sym (exact x)) Refl (targetRespects x y inputs)

||| Strong relational map preservation is closed under the exact executable
||| `partialCompose` used by Definition 60 transformations.
0 replayPartialMapsRelatedCompose :
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceAfter targetAfter ->
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceBefore targetBefore ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialCompose sourceAfter sourceBefore)
    (partialCompose targetAfter targetBefore)
replayPartialMapsRelatedCompose {sourceAfter} {targetAfter} {sourceBefore}
  {targetBefore} afterRelated beforeRelated {x} {y} inputs
  with (sourceBefore x) proof sourceRun
  replayPartialMapsRelatedCompose afterRelated beforeRelated inputs | Nothing
    with (targetBefore y) proof targetRun
    replayPartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Nothing | Nothing = PartialUndefined
    replayPartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Nothing | Just targetMiddle =
        case replayPartialRewrite sourceRun targetRun (beforeRelated inputs) of
          _ impossible
  replayPartialMapsRelatedCompose afterRelated beforeRelated inputs |
    Just sourceMiddle with (targetBefore y) proof targetRun
    replayPartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Just sourceMiddle | Nothing =
        case replayPartialRewrite sourceRun targetRun (beforeRelated inputs) of
          _ impossible
    replayPartialMapsRelatedCompose afterRelated beforeRelated inputs |
      Just sourceMiddle | Just targetMiddle =
        let 0 middleRelated : EffectStateRelated keyEq sourceMiddle targetMiddle
            middleRelated = case replayPartialRewrite sourceRun targetRun
              (beforeRelated inputs) of PartialDefined related => related
        in afterRelated middleRelated

0 replayPartialMapsRelatedTransitive :
  PartialMapsRelated (EffectStateEquivalence keyEq) first middle ->
  PartialMapsRelated (EffectStateEquivalence keyEq) middle last ->
  PartialMapsRelated (EffectStateEquivalence keyEq) first last
replayPartialMapsRelatedTransitive firstRelated secondRelated {x} {y} inputs =
  replayEffectPartialTransitive (firstRelated inputs)
    (secondRelated (effectStateReflexive keyEq y))

||| Consumer probe for `generatedMonoidsCommute`: a source commute square
||| transports through two relational map pairs without exact map equality.
0 replayPartialCommuteFromRelatedMaps :
  (leftSource, leftTarget, rightSource, rightTarget :
    PartialEffectMap name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) leftSource leftTarget ->
  PartialMapsRelated (EffectStateEquivalence keyEq) rightSource rightTarget ->
  PartialCommute (EffectStateEquivalence keyEq) leftSource rightSource ->
  PartialCommute (EffectStateEquivalence keyEq) leftTarget rightTarget
replayPartialCommuteFromRelatedMaps leftSource leftTarget rightSource rightTarget
  leftRelated rightRelated sourceCommute state =
    let 0 inputRelated = effectStateReflexive keyEq state
        0 sourceLeftRightToTarget =
          replayPartialMapsRelatedCompose leftRelated rightRelated inputRelated
        0 sourceRightLeftToTarget =
          replayPartialMapsRelatedCompose rightRelated leftRelated inputRelated
    in replayEffectPartialTransitive
      (replayEffectPartialSymmetric sourceLeftRightToTarget)
      (replayEffectPartialTransitive (sourceCommute state)
        sourceRightLeftToTarget)

||| Executable successful-forward projection used by an iterator generator.
replayRuntimeForwardProjection :
  Maybe (IteratorStageOutcome name key value world error) ->
  Maybe (EffectState name key value world)
replayRuntimeForwardProjection Nothing = Nothing
replayRuntimeForwardProjection (Just (IteratorRaised failure)) = Nothing
replayRuntimeForwardProjection (Just (IteratorYielded after undo continuation)) =
  Just after

||| Executable yielded-inverse projection. Undefined/failure outcomes generate
||| no inverse and are represented by the everywhere-undefined partial map.
replayRuntimeYieldedProjection :
  Maybe (IteratorStageOutcome name key value world error) ->
  PartialEffectMap name key value world
replayRuntimeYieldedProjection Nothing = \state => Nothing
replayRuntimeYieldedProjection (Just (IteratorRaised failure)) = \state => Nothing
replayRuntimeYieldedProjection
  (Just (IteratorYielded after undo continuation)) = undo

0 replayRuntimeForwardAgreementProjection :
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    targetOutcome sourceOutcome ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (replayRuntimeForwardProjection sourceOutcome)
    (replayRuntimeForwardProjection targetOutcome)
replayRuntimeForwardAgreementProjection RuntimeOutcomesUndefined = PartialUndefined
replayRuntimeForwardAgreementProjection (RuntimeFailuresAgree errorsSame) =
  PartialUndefined
replayRuntimeForwardAgreementProjection
  (RuntimeYieldsAgree afterRelated undoMaps) = PartialDefined afterRelated


0 replayReindexEffectRelated :
  EffectStateRelated leftKeyEq left right ->
  EffectStateRelated rightKeyEq left right
replayReindexEffectRelated (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated ambient tables

0 replayReindexPartialRelated :
  PartialRelated (EffectState name key value world)
    (EffectStateRelated leftKeyEq) left right ->
  PartialRelated (EffectState name key value world)
    (EffectStateRelated rightKeyEq) left right
replayReindexPartialRelated PartialUndefined = PartialUndefined
replayReindexPartialRelated (PartialDefined related) =
  PartialDefined (replayReindexEffectRelated related)

0 replayLookupBindingFromEqualBindings :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  lookupBinding @{keyEq} wanted left = lookupBinding @{keyEq} wanted right
replayLookupBindingFromEqualBindings keyEq wanted
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    cong (lookupEntries @{keyEq} wanted) same

0 replayResolveEffectValuesRelated :
  (keyEq : DecEq key) -> (deps : List key) -> (view : View name deps) ->
  {left, right : EffectState name key value world} ->
  EffectStateRelated keyEq left right ->
  resolveEffectValues @{keyEq} deps view left =
    resolveEffectValues @{keyEq} deps view right
replayResolveEffectValuesRelated keyEq [] EmptyView related = Refl
replayResolveEffectValuesRelated keyEq (wanted :: rest)
  (ProviderView provider later) related
  with (lookupBinding @{keyEq} wanted (effectTables left provider)) proof leftLookup
  replayResolveEffectValuesRelated keyEq (wanted :: rest)
    (ProviderView provider later) related | Nothing =
      let lookupSame = replayLookupBindingFromEqualBindings keyEq wanted
            (effectTables left provider) (effectTables right provider)
            (tablesExact related provider)
          rightLookup = trans (sym lookupSame) leftLookup
      in rewrite rightLookup in Refl
  replayResolveEffectValuesRelated keyEq (wanted :: rest)
    (ProviderView provider later) related | Just found =
      let lookupSame = replayLookupBindingFromEqualBindings keyEq wanted
            (effectTables left provider) (effectTables right provider)
            (tablesExact related provider)
          rightLookup = trans (sym lookupSame) leftLookup
      in rewrite rightLookup in cong (map (OneDepValue found))
        (replayResolveEffectValuesRelated keyEq rest later related)

0 replaySetActorRuntimeRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (worldValue : world) -> (table : CoeffectContext key value) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor table
      (setEffectAmbient worldValue left))
    (setEffectTable @{nameEq} actor table
      (setEffectAmbient worldValue right))
replaySetActorRuntimeRelated nameEq keyEq actor worldValue table left right related =
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
0 replayIteratorStageRuntimeOutcomeRelated :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  (left, right : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage right) (iteratorStageOutcome stage left)
replayIteratorStageRuntimeOutcomeRelated {name} {key} {world} {error} {value}
  keyEq (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
    remaining accumulator view lifecycle step rest suffix) left right related
  with (resolveEffectValues @{stageKeyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view left)
    proof leftResolved
  replayIteratorStageRuntimeOutcomeRelated keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix)
    left right related | Nothing =
      let 0 stageRelated : EffectStateRelated stageKeyEq left right
          stageRelated = replayReindexEffectRelated related
          0 resolvedSame :
            resolveEffectValues @{stageKeyEq}
              (dependencies (componentDependencies (fiberComponent fiber))) view
              left =
            resolveEffectValues @{stageKeyEq}
              (dependencies (componentDependencies (fiberComponent fiber))) view
              right
          resolvedSame = replayResolveEffectValuesRelated stageKeyEq
            (dependencies (componentDependencies (fiberComponent fiber))) view
            stageRelated
          0 rightResolved : resolveEffectValues @{stageKeyEq}
            (dependencies (componentDependencies (fiberComponent fiber))) view
            right = Nothing
          rightResolved = trans (sym resolvedSame) leftResolved
      in rewrite rightResolved in RuntimeOutcomesUndefined
  replayIteratorStageRuntimeOutcomeRelated keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix)
    left right related | Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient left)
        (restrictOwnedPreservingOrder @{stageKeyEq}
          (componentProvisions (fiberComponent fiber))
          (effectTables left actor)))) proof leftRan
    replayIteratorStageRuntimeOutcomeRelated keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix)
      left right related | Just capability | Left failure =
        let 0 stageRelated : EffectStateRelated stageKeyEq left right
            stageRelated = replayReindexEffectRelated related
            0 resolvedSame :
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view left =
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view right
            resolvedSame = replayResolveEffectValuesRelated stageKeyEq
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
    replayIteratorStageRuntimeOutcomeRelated keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix)
      left right related | Just capability | Right (after, undo) =
        let 0 stageRelated : EffectStateRelated stageKeyEq left right
            stageRelated = replayReindexEffectRelated related
            0 resolvedSame :
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view left =
              resolveEffectValues @{stageKeyEq}
                (dependencies (componentDependencies (fiberComponent fiber)))
                view right
            resolvedSame = replayResolveEffectValuesRelated stageKeyEq
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
            outputRelatedAtStage = replaySetActorRuntimeRelated nameEq stageKeyEq
              actor (localWorld after) (ownedValues (localTable after)) left right
              stageRelated
            0 outputRelated : EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) left))
              (setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) right))
            outputRelated = replayReindexEffectRelated outputRelatedAtStage
            undoMap = yieldedInverseEffectMap nameEq stageKeyEq actor
              (componentProvisions (fiberComponent fiber)) undo
        in rewrite rightResolved in rewrite rightRan in
          RuntimeYieldsAgree outputRelated
            (effectPartialMapReflexive keyEq undoMap)

0 replayIteratorForwardProjectionExact :
  (stage : IteratorStage name key world error value actor trace) ->
  (state : EffectState name key value world) ->
  replayRuntimeForwardProjection (iteratorStageOutcome stage state) =
    traceGeneratorMap (IteratorForwardGenerator stage) state
replayIteratorForwardProjectionExact
  (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
    accumulator view lifecycle step rest suffix) state
  with (resolveEffectValues @{keyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view state)
  replayIteratorForwardProjectionExact
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
      accumulator view lifecycle step rest suffix) state | Nothing = Refl
  replayIteratorForwardProjectionExact
    (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
      accumulator view lifecycle step rest suffix) state | Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient state)
        (restrictOwnedPreservingOrder @{keyEq}
          (componentProvisions (fiberComponent fiber))
          (effectTables state actor))))
    replayIteratorForwardProjectionExact
      (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) state |
        Just capability | Left failure = Refl
    replayIteratorForwardProjectionExact
      (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) state |
        Just capability | Right (after, undo) = Refl

||| The forward generator is exactly the successful-forward projection of the
||| strengthened runtime outcome relation.
0 replayIteratorForwardGeneratorMapRespects :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap (IteratorForwardGenerator stage))
    (traceGeneratorMap (IteratorForwardGenerator stage))
replayIteratorForwardGeneratorMapRespects keyEq stage {x} {y} inputs =
  replayPartialRewrite
    (replayIteratorForwardProjectionExact stage x)
    (replayIteratorForwardProjectionExact stage y)
    (replayRuntimeForwardAgreementProjection
      (replayIteratorStageRuntimeOutcomeRelated keyEq stage x y inputs))

||| Every yielded generator's inverse is producer-known to be a lifted local
||| undo.  Splitting the immutable stage invocation exposes that map and reuses
||| the accumulator-map respect theorem.
0 replayIteratorYieldedGeneratorMapRespects :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  (origin : EffectState name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap (IteratorYieldedGenerator stage origin))
    (traceGeneratorMap (IteratorYieldedGenerator stage origin))
replayIteratorYieldedGeneratorMapRespects {name} {key} {world} {error} {value}
  keyEq (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
    remaining accumulator view lifecycle step rest suffix) origin {x} {y} inputs
  with (resolveEffectValues @{stageKeyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view origin)
    proof resolved
  replayIteratorYieldedGeneratorMapRespects keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix) origin inputs |
      Nothing = PartialUndefined
  replayIteratorYieldedGeneratorMapRespects keyEq
    (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
      remaining accumulator view lifecycle step rest suffix) origin inputs |
      Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient origin)
        (restrictOwnedPreservingOrder @{stageKeyEq}
          (componentProvisions (fiberComponent fiber))
          (effectTables origin actor)))) proof ran
    replayIteratorYieldedGeneratorMapRespects keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) origin inputs |
        Just capability | Left failure = PartialUndefined
    replayIteratorYieldedGeneratorMapRespects keyEq
      (StageFromAdvance nameEq stageKeyEq actor tag equation occurs fiber found
        remaining accumulator view lifecycle step rest suffix) origin inputs |
        Just capability | Right (after, undo) =
          replayReindexPartialRelated
            (accumulatorRuntimeEffectMapRespects nameEq stageKeyEq actor
              (componentProvisions (fiberComponent fiber)) undo x y
              (replayReindexEffectRelated inputs))

||| Identity-correspondence producer probe over all three Definition-54
||| generator constructors.  This is the anti-oscillation check needed by
||| finite-derivation and operational-permutation terminators.
public export
0 replayTraceGeneratorMapRespects :
  (keyEq : DecEq key) ->
  (generator : TraceEffectGenerator name key world error value actor trace) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap generator) (traceGeneratorMap generator)
replayTraceGeneratorMapRespects keyEq
  (ActualForwardGenerator before afterState nameEq storedKeyEq action tag checked
    occurs actorMatches) = \inputs =>
      replayReindexPartialRelated
        (partialEffectMapForRespects nameEq storedKeyEq action tag before _ _
          (replayReindexEffectRelated inputs))
replayTraceGeneratorMapRespects keyEq (IteratorForwardGenerator stage) =
  replayIteratorForwardGeneratorMapRespects keyEq stage
replayTraceGeneratorMapRespects keyEq (IteratorYieldedGenerator stage origin) =
  replayIteratorYieldedGeneratorMapRespects keyEq stage origin

0 replayTransitionMapRespects :
  (keyEq : DecEq key) ->
  (transition : Transition before afterState) ->
  EffectPartialMapRespects keyEq (partialEffectMap transition)
replayTransitionMapRespects keyEq
  (Fired nameEq storedKeyEq action tag checked) left right inputs =
    replayReindexPartialRelated
      (partialEffectMapForRespects nameEq storedKeyEq action tag before left right
        (replayReindexEffectRelated inputs))

0 replayExactTransitionMapsRelated :
  (keyEq : DecEq key) ->
  (source : Transition sourceBefore sourceAfter) ->
  (target : Transition targetBefore targetAfter) ->
  ((state : EffectState name key value world) ->
    partialEffectMap source state = partialEffectMap target state) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap source) (partialEffectMap target)
replayExactTransitionMapsRelated keyEq source target exact =
  replayExactMapsGivePartialMapsRelated (partialEffectMap source)
    (partialEffectMap target) (replayTransitionMapRespects keyEq target) exact

||| A reusable RAR correspondence, not a deletion-only embedding.  Every actual
||| or yielded generator and every iterator stage of the replayed trace is tied
||| to one generator/stage in the source trace with relationally matching maps
||| and the same stage outcome.  This is the capital needed to transport both
||| fields of `TraceIndependent` after deletion, suffix replay, and adjacent
||| swaps without identifying proof-bearing coeffect contexts.
public export
record RelationalReplayCorrespondence
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal)
  (replayed : Transitions replayedFirst replayedFinal) where
  constructor MkRelationalReplayCorrespondence
  replayGeneratorOrigin : (actor : name) ->
    TraceEffectGenerator name key world error value actor replayed ->
    TraceEffectGenerator name key world error value actor source
  0 replayGeneratorMapsRelated : (keyEq : DecEq key) -> (actor : name) ->
    (generator : TraceEffectGenerator name key world error value actor replayed) ->
    PartialMapsRelated (EffectStateEquivalence keyEq)
      (traceGeneratorMap (replayGeneratorOrigin actor generator))
      (traceGeneratorMap generator)
  replayIteratorStageOrigin : (actor : name) ->
    IteratorStage name key world error value actor replayed ->
    IteratorStage name key world error value actor source
  0 replayIteratorOutcomePreserved : (actor : name) ->
    (stage : IteratorStage name key world error value actor replayed) ->
    (state : EffectState name key value world) ->
    iteratorStageOutcome stage state =
      iteratorStageOutcome (replayIteratorStageOrigin actor stage) state

0 replayTransformationOrigin :
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  RelationalReplayCorrespondence name key world error value source replayed ->
  TraceEffectTransformation name key world error value actor replayed ->
  TraceEffectTransformation name key world error value actor source
replayTransformationOrigin correspondence TraceIdentity = TraceIdentity
replayTransformationOrigin correspondence (TraceGenerator generator) =
  TraceGenerator (replayGeneratorOrigin correspondence actor generator)
replayTransformationOrigin correspondence (TraceCompose after before) =
  TraceCompose (replayTransformationOrigin correspondence after)
    (replayTransformationOrigin correspondence before)

0 replayTransformationMapsRelated :
  (keyEq : DecEq key) ->
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  (correspondence : RelationalReplayCorrespondence name key world error value
    source replayed) ->
  (transformation : TraceEffectTransformation name key world error value actor
    replayed) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (runTraceEffectTransformation
      (replayTransformationOrigin correspondence transformation))
    (runTraceEffectTransformation transformation)
replayTransformationMapsRelated keyEq correspondence TraceIdentity =
  \inputs => PartialDefined inputs
replayTransformationMapsRelated keyEq correspondence
  (TraceGenerator generator) =
    replayGeneratorMapsRelated correspondence keyEq actor generator
replayTransformationMapsRelated keyEq correspondence
  (TraceCompose after before) =
    replayPartialMapsRelatedCompose
      (replayTransformationMapsRelated keyEq correspondence after)
      (replayTransformationMapsRelated keyEq correspondence before)

0 replayPartialComposeCong :
  (leftSource, leftTarget, rightSource, rightTarget :
    PartialEffectMap name key value world) ->
  ((state : EffectState name key value world) ->
    leftSource state = leftTarget state) ->
  ((state : EffectState name key value world) ->
    rightSource state = rightTarget state) ->
  (state : EffectState name key value world) ->
  partialCompose leftSource rightSource state =
    partialCompose leftTarget rightTarget state
replayPartialComposeCong leftSource leftTarget rightSource rightTarget leftSame
  rightSame state with (rightSource state) proof sourceRun
  replayPartialComposeCong leftSource leftTarget rightSource rightTarget leftSame
    rightSame state | Nothing =
      rewrite sym (rightSame state) in rewrite sourceRun in Refl
  replayPartialComposeCong leftSource leftTarget rightSource rightTarget leftSame
    rightSame state | Just middle =
      rewrite sym (rightSame state) in rewrite sourceRun in leftSame middle

0 replayPartialCommuteTransport :
  (leftSource, leftTarget, rightSource, rightTarget :
    PartialEffectMap name key value world) ->
  ((state : EffectState name key value world) ->
    leftSource state = leftTarget state) ->
  ((state : EffectState name key value world) ->
    rightSource state = rightTarget state) ->
  PartialCommute (EffectStateEquivalence keyEq) leftSource rightSource ->
  PartialCommute (EffectStateEquivalence keyEq) leftTarget rightTarget
replayPartialCommuteTransport leftSource leftTarget rightSource rightTarget
  leftSame rightSame commute state =
    let leftThenRight = replayPartialComposeCong leftSource leftTarget rightSource
          rightTarget leftSame rightSame state
        rightThenLeft = replayPartialComposeCong rightSource rightTarget leftSource
          leftTarget rightSame leftSame state
        relatedSource = commute state
        relatedRight = replace
          {p = \observed => PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq)
            (partialCompose leftSource rightSource state) observed}
          rightThenLeft relatedSource
    in replace
      {p = \observed => PartialRelated (EffectState name key value world)
        (EffectStateRelated keyEq) observed
        (partialCompose rightTarget leftTarget state)}
      leftThenRight relatedRight

0 replayRelationalEquivalentMapsSymmetric :
  PartialMapsEquivalent (EffectStateEquivalence keyEq) left right ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq) right left
replayRelationalEquivalentMapsSymmetric maps input =
  replayEffectPartialSymmetric (maps input)

0 replayRelationalOutcomeAgreementSymmetric :
  IteratorOutcomeAgreement name key value world error keyEq left right ->
  IteratorOutcomeAgreement name key value world error keyEq right left
replayRelationalOutcomeAgreementSymmetric IteratorOutcomesUndefined =
  IteratorOutcomesUndefined
replayRelationalOutcomeAgreementSymmetric (IteratorFailuresAgree errorsSame) =
  IteratorFailuresAgree (sym errorsSame)
replayRelationalOutcomeAgreementSymmetric
  (IteratorSuccessfulYieldsAgree continuationSame undoMaps) =
    IteratorSuccessfulYieldsAgree (sym continuationSame)
      (replayRelationalEquivalentMapsSymmetric undoMaps)


0 replayRelationalStageOutcomesRelatedFromExact :
  (keyEq : DecEq key) ->
  (sourceStage : IteratorStage name key world error value actor source) ->
  (targetStage : IteratorStage name key world error value actor replayed) ->
  ((state : EffectState name key value world) ->
    iteratorStageOutcome targetStage state =
      iteratorStageOutcome sourceStage state) ->
  {sourceInput, targetInput : EffectState name key value world} ->
  EffectStateRelated keyEq sourceInput targetInput ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome sourceStage sourceInput)
    (iteratorStageOutcome targetStage targetInput)
replayRelationalStageOutcomesRelatedFromExact keyEq sourceStage targetStage exact inputs =
  replace
    {p = \observed => IteratorOutcomeAgreement name key value world error keyEq
      observed (iteratorStageOutcome targetStage targetInput)}
    (exact sourceInput)
    (iteratorStageOutcomeRelated keyEq targetStage sourceInput targetInput inputs)

0 replayRelationalSourceStableAtExactRun :
  (keyEq : DecEq key) ->
  (stage : IteratorStage name key world error value actor trace) ->
  (foreign : PartialEffectMap name key value world) ->
  (origin, moved : EffectState name key value world) ->
  foreign origin = Just moved ->
  IteratorOutcomeStableUnder keyEq stage foreign origin ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage moved) (iteratorStageOutcome stage origin)
replayRelationalSourceStableAtExactRun keyEq stage foreign origin moved defined stable
  with (foreign origin) proof observed
  replayRelationalSourceStableAtExactRun keyEq stage foreign origin moved defined stable |
    Nothing = void (nothingIsNotJust defined)
  replayRelationalSourceStableAtExactRun keyEq stage foreign origin moved defined stable |
    Just actual = replace
      {p = \candidate => IteratorOutcomeAgreement name key value world error
        keyEq (iteratorStageOutcome stage candidate)
        (iteratorStageOutcome stage origin)}
      (justInjective defined) stable

0 replayRelationalIteratorStableFromRelationalMaps :
  (keyEq : DecEq key) ->
  (sourceStage : IteratorStage name key world error value left source) ->
  (targetStage : IteratorStage name key world error value left replayed) ->
  (sourceForeign, targetForeign : PartialEffectMap name key value world) ->
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceForeign targetForeign ->
  ((origin : EffectState name key value world) ->
    IteratorOutcomeStableUnder keyEq sourceStage sourceForeign origin) ->
  ({sourceInput, targetInput : EffectState name key value world} ->
    EffectStateRelated keyEq sourceInput targetInput ->
    IteratorOutcomeAgreement name key value world error keyEq
      (iteratorStageOutcome sourceStage sourceInput)
      (iteratorStageOutcome targetStage targetInput)) ->
  (origin : EffectState name key value world) ->
  IteratorOutcomeStableUnder keyEq targetStage targetForeign origin
replayRelationalIteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
  targetForeign mapsRelated sourceStable stagesRelated origin
  with (targetForeign origin) proof targetRun
  replayRelationalIteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
    targetForeign mapsRelated sourceStable stagesRelated origin | Nothing = ()
  replayRelationalIteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
    targetForeign mapsRelated sourceStable stagesRelated origin | Just targetMoved
    with (sourceForeign origin) proof sourceRun
    replayRelationalIteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
      targetForeign mapsRelated sourceStable stagesRelated origin |
      Just targetMoved | Nothing =
        case replayPartialRewrite sourceRun targetRun
          (mapsRelated (effectStateReflexive keyEq origin)) of _ impossible
    replayRelationalIteratorStableFromRelationalMaps keyEq sourceStage targetStage sourceForeign
      targetForeign mapsRelated sourceStable stagesRelated origin |
      Just targetMoved | Just sourceMoved =
        let 0 movedInputs : EffectStateRelated keyEq sourceMoved targetMoved
            movedInputs = case replayPartialRewrite sourceRun targetRun
              (mapsRelated (effectStateReflexive keyEq origin)) of
                PartialDefined related => related
            0 targetMovedToSourceMoved : IteratorOutcomeAgreement name key value
              world error keyEq (iteratorStageOutcome targetStage targetMoved)
              (iteratorStageOutcome sourceStage sourceMoved)
            targetMovedToSourceMoved = replayRelationalOutcomeAgreementSymmetric
              (stagesRelated movedInputs)
            0 sourceMovedToSourceOrigin : IteratorOutcomeAgreement name key value
              world error keyEq (iteratorStageOutcome sourceStage sourceMoved)
              (iteratorStageOutcome sourceStage origin)
            sourceMovedToSourceOrigin = replayRelationalSourceStableAtExactRun keyEq
              sourceStage sourceForeign origin sourceMoved sourceRun
              (sourceStable origin)
            0 sourceOriginToTargetOrigin : IteratorOutcomeAgreement name key value
              world error keyEq (iteratorStageOutcome sourceStage origin)
              (iteratorStageOutcome targetStage origin)
            sourceOriginToTargetOrigin = stagesRelated
              (effectStateReflexive keyEq origin)
        in iteratorOutcomeAgreementTransitive targetMovedToSourceMoved
          (iteratorOutcomeAgreementTransitive sourceMovedToSourceOrigin
            sourceOriginToTargetOrigin)


0 replayOutcomeStableAtExactRun :
  (stage : IteratorStage name key world error value actor trace) ->
  (foreign : PartialEffectMap name key value world) ->
  (origin, moved : EffectState name key value world) ->
  foreign origin = Just moved ->
  IteratorOutcomeStableUnder keyEq stage foreign origin ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage moved) (iteratorStageOutcome stage origin)
replayOutcomeStableAtExactRun stage foreign origin moved defined stable
  with (foreign origin) proof observed
  replayOutcomeStableAtExactRun stage foreign origin moved defined stable |
    Nothing = void (nothingIsNotJust defined)
  replayOutcomeStableAtExactRun stage foreign origin moved defined stable |
    Just actual =
      replace
        {p = \candidate => IteratorOutcomeAgreement name key value world error
          keyEq (iteratorStageOutcome stage candidate)
          (iteratorStageOutcome stage origin)}
        (justInjective defined) stable

0 replayIteratorStable :
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  (correspondence : RelationalReplayCorrespondence name key world error value
    source replayed) ->
  TraceIndependent name key world error value keyEq source ->
  (left, right : name) -> Not (left = right) ->
  (stage : IteratorStage name key world error value left replayed) ->
  (foreign : TraceEffectTransformation name key world error value right
    replayed) ->
  (origin : EffectState name key value world) ->
  IteratorOutcomeStableUnder keyEq stage
    (runTraceEffectTransformation foreign) origin
replayIteratorStable {keyEq} correspondence independent left right distinct
  stage foreign origin =
    replayRelationalIteratorStableFromRelationalMaps keyEq
      (replayIteratorStageOrigin correspondence left stage) stage
      (runTraceEffectTransformation
        (replayTransformationOrigin correspondence foreign))
      (runTraceEffectTransformation foreign)
      (replayTransformationMapsRelated keyEq correspondence foreign)
      (\point => iteratorYieldsStable independent left right distinct
        (replayIteratorStageOrigin correspondence left stage)
        (replayTransformationOrigin correspondence foreign) point)
      (replayRelationalStageOutcomesRelatedFromExact keyEq
        (replayIteratorStageOrigin correspondence left stage) stage
        (replayIteratorOutcomePreserved correspondence left stage)) origin

||| Generic independence transport.  Deletion and sorting must construct the
||| correspondence above as part of their internal replay result; this theorem
||| deliberately does not claim that an arbitrary public `DeletionResult`
||| contains enough evidence by itself.
public export
0 traceIndependentAfterRelationalReplaySpike :
  (keyEq : DecEq key) ->
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  RelationalReplayCorrespondence name key world error value source replayed ->
  TraceIndependent name key world error value keyEq source ->
  TraceIndependent name key world error value keyEq replayed
traceIndependentAfterRelationalReplaySpike keyEq correspondence independent =
  MkTraceIndependent
    (\left, right, distinct, leftTransformation, rightTransformation =>
      replayPartialCommuteFromRelatedMaps
        (runTraceEffectTransformation
          (replayTransformationOrigin correspondence leftTransformation))
        (runTraceEffectTransformation leftTransformation)
        (runTraceEffectTransformation
          (replayTransformationOrigin correspondence rightTransformation))
        (runTraceEffectTransformation rightTransformation)
        (replayTransformationMapsRelated keyEq correspondence leftTransformation)
        (replayTransformationMapsRelated keyEq correspondence rightTransformation)
        (generatedMonoidsCommute independent left right distinct
          (replayTransformationOrigin correspondence leftTransformation)
          (replayTransformationOrigin correspondence rightTransformation)))
    (replayIteratorStable correspondence independent)

||| Replay correspondence composes structurally.  This checked helper is the
||| one-trace bridge from original→closing-free and closing-free→sorted replay;
||| it is kept transparent rather than assumed by an opaque schedule producer.
public export
composeRelationalReplayCorrespondence :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  RelationalReplayCorrespondence name key world error value source middle ->
  RelationalReplayCorrespondence name key world error value middle target ->
  RelationalReplayCorrespondence name key world error value source target
composeRelationalReplayCorrespondence left right =
  MkRelationalReplayCorrespondence
    (\actor, generator => replayGeneratorOrigin left actor
      (replayGeneratorOrigin right actor generator))
    (\keyEq, actor, generator => replayPartialMapsRelatedTransitive
      (replayGeneratorMapsRelated left keyEq actor
        (replayGeneratorOrigin right actor generator))
      (replayGeneratorMapsRelated right keyEq actor generator))
    (\actor, stage => replayIteratorStageOrigin left actor
      (replayIteratorStageOrigin right actor stage))
    (\actor, stage, state => trans
      (replayIteratorOutcomePreserved right actor stage state)
      (replayIteratorOutcomePreserved left actor
        (replayIteratorStageOrigin right actor stage) state))

||| Registration generations need their own permutation when transitions are
||| swapped: the raw O-Insert action is preserved, but its global birth ordinal
||| may move.  This composition is deliberately local to operational replay so
||| it cannot be confused with the accepted left-to-right generation bijection.
public export
composeReplayGenerationBijection : RegistrationGenerationBijection name ->
  RegistrationGenerationBijection name -> RegistrationGenerationBijection name
composeReplayGenerationBijection left right =
  MkRegistrationGenerationBijection
    (generationForward right . generationForward left)
    (generationBackward left . generationBackward right)
    (\generation => trans
      (cong (generationBackward left)
        (generationLeftInverse right (generationForward left generation)))
      (generationLeftInverse left generation))
    (\generation => trans
      (cong (generationForward right)
        (generationRightInverse left (generationBackward right generation)))
      (generationRightInverse right generation))

||| Convert the specialized generated-registration occurrence to the exact
||| all-action occurrence used by the general replay map.  Both views retain the
||| same dependent prefix, transition, suffix, action, and decomposition.
public export
0 generatedRegistrationActionOccurrence :
  LocatedGeneratedRegistration child parent component trace ->
  LocatedActionOccurrence (OInsert child (ChildOf parent) component) trace
generatedRegistrationActionOccurrence occurrence =
  MkLocatedActionOccurrence
    (registrationBefore occurrence)
    (registrationAfter occurrence)
    (beforeRegistration occurrence)
    (registrationTransition occurrence)
    (afterRegistration occurrence)
    (registrationAction occurrence)
    (registrationDecomposition occurrence)

||| Exact transition-occurrence capital retained by operational permutation.
||| Generated registrations are not an independently replaceable second map:
||| their specialized origin must convert to exactly the all-action origin of
||| the same replayed O-Insert occurrence.
public export
record ActionRegistrationReplayCorrespondence
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal)
  (replayed : Transitions replayedFirst replayedFinal) where
  constructor MkActionRegistrationReplayCorrespondence
  replayGenerationRenaming : RegistrationGenerationBijection name
  replayActionOrigin : {action : Action name key value world error} ->
    LocatedActionOccurrence action replayed -> LocatedActionOccurrence action source
  0 replayActionTagPreserved :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action replayed) ->
    transitionTag (locatedTransition (replayActionOrigin occurrence)) =
      transitionTag (locatedTransition occurrence)
  replayGeneratedRegistrationOrigin :
    {child, parent : name} ->
    {component : Component key value world error} ->
    LocatedGeneratedRegistration child parent component replayed ->
    LocatedGeneratedRegistration child parent component source
  0 replayGeneratedActionOriginCoherent :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component replayed) ->
    generatedRegistrationActionOccurrence
      (replayGeneratedRegistrationOrigin occurrence) =
    replayActionOrigin (generatedRegistrationActionOccurrence occurrence)
  0 replayGeneratedOrdinalPreserved :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component replayed) ->
    generationForward replayGenerationRenaming
      (registrationGeneration (replayGeneratedRegistrationOrigin occurrence)) =
        registrationGeneration occurrence

public export
identityActionRegistrationReplayCorrespondence :
  (trace : Transitions initial finalState) ->
  ActionRegistrationReplayCorrespondence name key world error value trace trace
identityActionRegistrationReplayCorrespondence trace =
  MkActionRegistrationReplayCorrespondence
    identityRegistrationGenerationBijection id (\occurrence => Refl) id
    (\occurrence => Refl) (\occurrence => Refl)

||| Occurrence capital composes in the same direction as trace replay.  The
||| ordinal equation explicitly uses the composed replay-generation bijection.
public export
composeActionRegistrationReplayCorrespondence :
  {source : Transitions sourceFirst sourceFinal} ->
  {middle : Transitions middleFirst middleFinal} ->
  {target : Transitions targetFirst targetFinal} ->
  ActionRegistrationReplayCorrespondence name key world error value source middle ->
  ActionRegistrationReplayCorrespondence name key world error value middle target ->
  ActionRegistrationReplayCorrespondence name key world error value source target
composeActionRegistrationReplayCorrespondence left right =
  MkActionRegistrationReplayCorrespondence
    (composeReplayGenerationBijection (replayGenerationRenaming left)
      (replayGenerationRenaming right))
    (\occurrence => replayActionOrigin left (replayActionOrigin right occurrence))
    (\occurrence => trans
      (replayActionTagPreserved left (replayActionOrigin right occurrence))
      (replayActionTagPreserved right occurrence))
    (\occurrence => replayGeneratedRegistrationOrigin left
      (replayGeneratedRegistrationOrigin right occurrence))
    (\occurrence => trans
      (replayGeneratedActionOriginCoherent left
        (replayGeneratedRegistrationOrigin right occurrence))
      (cong (replayActionOrigin left)
        (replayGeneratedActionOriginCoherent right occurrence)))
    (\occurrence => trans
      (cong (generationForward (replayGenerationRenaming right))
        (replayGeneratedOrdinalPreserved left
          (replayGeneratedRegistrationOrigin right occurrence)))
      (replayGeneratedOrdinalPreserved right occurrence))

||| Every premise consumed again by deletion selection, Lemmas 68/70, or the
||| next adjacent swap.  Using one shared record prevents the sorting and
||| deletion recursions from silently dropping capital at their boundaries.
public export
record ReplayInvariantBundle
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkReplayInvariantBundle
  0 replayAligned : AlignedTransitions name key world error value nameEq keyEq trace
  0 replayDiscipline : RegistrationDiscipline protocol nameEq trace
  0 replayInitialWellFormed :
    registryWellFormed @{nameEq} @{keyEq} initial = True
  0 replayInitialEmpty : bindings (registry initial) = []
  0 replayFinalWellFormed :
    registryWellFormed @{nameEq} @{keyEq} finalState = True
  0 replayQuiet : quiet @{nameEq} @{keyEq} finalState = True
  0 replayNoFailure : noFailedFibers finalState = True
  0 replayTotal : TraceComponentsTotal nameEq keyEq trace
  0 replayIndependent : TraceIndependent name key world error value keyEq trace
  0 replayProvenance : RegistrationProvenance protocol nameEq trace
  0 replayProtocolRanked : RegistryProtocolRanked protocol nameEq finalState
  0 replayParentRanksIncrease :
    RegistryParentRanksIncrease protocol nameEq finalState
  0 replayPrecedenceAcyclic : PrecedenceAcyclic nameEq finalState
  0 replaySupportWellFounded : SupportWellFounded nameEq finalState
  0 replaySupportMatchesActive : SupportMatchesActive nameEq keyEq finalState

||| The exact `ReachedFromEmpty` value consumed by Lemmas 68 and 70 is
||| definitionally reconstructed from each recursive bundle, rather than being
||| mentioned only in prose.
public export
0 replayReachedFromEmpty :
  {trace : Transitions initial finalState} ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ReachedFromEmpty name key world error value nameEq keyEq finalState
replayReachedFromEmpty premises =
  MkReachedFromEmpty initial trace (replayAligned premises)
    (replayInitialEmpty premises) (replayInitialWellFormed premises)

||| Endpoint quotient carried by every suffix replay.  It is strong enough to
||| compose effects and actor-name-indexed controls without demanding equality
||| of function-valued tables, registry order, or accumulators.
public export
record RelationalReplayEndpoint
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (sourceFinal, replayedFinal : SystemState name key value world error) where
  constructor MkRelationalReplayEndpoint
  0 replayedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} sourceFinal)
    (projectEffectState @{nameEq} replayedFinal)
  0 replayedControls : ControlEquivalent name key world error value nameEq
    sourceFinal replayedFinal
  0 replayedWellFormed :
    registryWellFormed @{nameEq} @{keyEq} replayedFinal = True

||| Quotient adequacy must compose through an arbitrary number of adjacent
||| swaps; endpoint relations are therefore explicit algebra rather than an
||| unstated appeal to equality.
public export
0 relationalReplayEndpointReflexiveSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq state state
relationalReplayEndpointReflexiveSpike nameEq keyEq state wellFormed =
  MkRelationalReplayEndpoint
    (effectStateReflexive keyEq (projectEffectState @{nameEq} state))
    (MkControlEquivalent
      (\actor => fiberControlMaybeReflexive
        (lookupFiber @{nameEq} actor (registry state))))
    wellFormed

public export
0 relationalReplayEndpointTransitiveSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, middle, right : SystemState name key value world error) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq left middle ->
  RelationalReplayEndpoint name key world error value nameEq keyEq middle right ->
  RelationalReplayEndpoint name key world error value nameEq keyEq left right
relationalReplayEndpointTransitiveSpike nameEq keyEq left middle right
  (MkRelationalReplayEndpoint firstEffects firstControls middleWellFormed)
  (MkRelationalReplayEndpoint secondEffects secondControls rightWellFormed) =
    MkRelationalReplayEndpoint
      (effectsTransitive firstEffects secondEffects)
      (controlEquivalentTransitive firstControls secondControls)
      rightWellFormed
  where
  0 effectsTransitive :
    EffectStateRelated keyEq leftEffect middleEffect ->
    EffectStateRelated keyEq middleEffect rightEffect ->
    EffectStateRelated keyEq leftEffect rightEffect
  effectsTransitive
    (MkEffectStateRelated firstAmbient firstTables)
    (MkEffectStateRelated secondAmbient secondTables) =
      MkEffectStateRelated (trans firstAmbient secondAmbient)
        (\actor => trans (firstTables actor) (secondTables actor))

||| Relational local diamond suitable for splicing by replay.  Action and tag
||| equalities are both explicit: L-Iter and L-Finish share LAdvance, so action
||| equality alone cannot recover a located paper activation step.
public export
record LocalRelationalDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkLocalRelationalDiamond
  swappedMiddle : SystemState name key value world error
  swappedFinal : SystemState name key value world error
  movedRight : Transition first swappedMiddle
  movedLeft : Transition swappedMiddle swappedFinal
  0 movedPairAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
  0 movedRightAction : transitionAction movedRight = transitionAction right
  0 movedRightTag : transitionTag movedRight = transitionTag right
  0 movedLeftAction : transitionAction movedLeft = transitionAction left
  0 movedLeftTag : transitionTag movedLeft = transitionTag left
  0 movedRightActivationBranch :
    PaperActivationStep right -> PaperActivationStep movedRight
  0 movedLeftActivationBranch :
    PaperActivationStep left -> PaperActivationStep movedLeft
  0 movedRightOrchestrationBranch :
    PaperOrchestrationStep right -> PaperOrchestrationStep movedRight
  0 movedLeftOrchestrationBranch :
    PaperOrchestrationStep left -> PaperOrchestrationStep movedLeft
  0 swappedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} swappedFinal)
  0 swappedControlEquivalent : ControlEquivalent name key world error value nameEq
    originalFinal swappedFinal
  0 swappedWellFormed : registryWellFormed @{nameEq} @{keyEq} swappedFinal = True

0 alignedMovedPairWithCheckedTail :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, movedMiddle, movedFinal : SystemState name key value world error} ->
  (movedRight : Transition first movedMiddle) ->
  (0 movedRightAligned : AlignedTransitions name key world error value nameEq
    keyEq (MoreTransitions movedRight NoTransitions)) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (0 leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction movedMiddle =
    Just (leftTag, movedFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions movedRight
      (MoreTransitions
        (Fired {before = movedMiddle} {afterState = movedFinal}
          nameEq keyEq leftAction leftTag leftChecked)
        NoTransitions))
alignedMovedPairWithCheckedTail nameEq keyEq movedRight movedRightAligned
  leftAction leftTag leftChecked = case movedRightAligned of
    AlignedStep rightAction rightTag rightChecked NoTransitions AlignedEnd =>
      AlignedStep rightAction rightTag rightChecked
        (MoreTransitions
          (Fired {before = movedMiddle} {afterState = movedFinal}
            nameEq keyEq leftAction leftTag leftChecked)
          NoTransitions)
        (AlignedStep leftAction leftTag leftChecked NoTransitions AlignedEnd)

record LocalAlignedHeadView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {before, afterState, finalState : SystemState name key value world error}
  (transition : Transition before afterState)
  (rest : Transitions afterState finalState) where
  constructor MkLocalAlignedHeadView
  alignedHeadAction : Action name key value world error
  alignedHeadTag : RuleTag
  0 alignedHeadChecked : checkedApplyAction @{nameEq} @{keyEq}
    alignedHeadAction before = Just (alignedHeadTag, afterState)
  0 alignedHeadActionProjection : transitionAction transition =
    alignedHeadAction
  0 alignedHeadTagProjection : transitionTag transition = alignedHeadTag

0 localAlignedHeadView :
  (aligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest)) ->
  LocalAlignedHeadView name key world error value nameEq keyEq transition rest
localAlignedHeadView (AlignedStep action tag checked rest alignedRest) =
  MkLocalAlignedHeadView action tag checked Refl Refl

0 localTransitionActorActionOwner :
  (transition : Transition before afterState) ->
  transitionActor transition = actionOwner (transitionAction transition)
localTransitionActorActionOwner
  (Fired nameEq keyEq (OInsert actor parent component) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (ORetire actor) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (ORemove actor) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (LBegin actor) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (LAdvance actor) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (LDivert actor) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (LLeave actor) tag checked) = Refl
localTransitionActorActionOwner
  (Fired nameEq keyEq (LUnload actor) tag checked) = Refl

0 localAlignedTail :
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  AlignedTransitions name key world error value nameEq keyEq rest
localAlignedTail (AlignedStep action tag checked rest alignedRest) = alignedRest

||| Source-sensitive evidence for swapping two orchestration rules.  The early
||| checked transition proves the moved rule's freshness/applicability at the
||| source.  Registration discipline plus the generation scan retain exact
||| birth ordinals/parent-local positions; the negative fields prevent two
||| yielded insertions from crossing their own licensing births.
public export
record OrchestrationSwapSafety
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkOrchestrationSwapSafety
  earlyRightFinal : SystemState name key value world error
  earlyRight : Transition first earlyRightFinal
  0 earlyRightAction : transitionAction earlyRight = transitionAction right
  0 earlyRightTag : transitionTag earlyRight = transitionTag right
  0 sourceRegistrationDiscipline : RegistrationDiscipline protocol nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
  sourceStartOrdinal : Nat
  sourceStartLive : GenerationEnvironment name
  sourceEndOrdinal : Nat
  sourceEndLive : GenerationEnvironment name
  0 sourceGenerationScan : GenerationTraceScan nameEq sourceStartOrdinal
    sourceStartLive (MoreTransitions left (MoreTransitions right NoTransitions))
    sourceEndOrdinal sourceEndLive
  0 insertedChildrenDistinct :
    (leftChild, rightChild : name) ->
    (leftParent, rightParent : Parent name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left = OInsert leftChild leftParent leftComponent ->
    transitionAction right = OInsert rightChild rightParent rightComponent ->
    Not (leftChild = rightChild)
  0 generatedLicensesDoNotCross :
    (leftChild, leftParent, rightChild, rightParent : name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent ->
    transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent ->
    (Not (leftChild = rightParent), Not (rightChild = leftParent))

||| Locate the first transition after an exact prefixTrace decomposition.  The
||| operational occurrence fold below uses this constructor for the moved-right
||| node rather than accepting a caller-selected occurrence.
public export
0 locatedFirstAfterPrefix :
  {initial, pairFirst, pairMiddle, finalState :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (first : Transition pairFirst pairMiddle) ->
  (rest : Transitions pairMiddle finalState) ->
  appendTransitions prefixTrace (MoreTransitions first rest) = global ->
  LocatedActionOccurrence (transitionAction first) global
locatedFirstAfterPrefix global prefixTrace first rest decomposition =
  MkLocatedActionOccurrence _ _ prefixTrace first rest Refl decomposition

||| Locate the second transition after an exact prefixTrace decomposition.
public export
0 locatedSecondAfterPrefix :
  {initial, pairFirst, pairMiddle, pairFinal, finalState :
    SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (first : Transition pairFirst pairMiddle) ->
  (second : Transition pairMiddle pairFinal) ->
  (rest : Transitions pairFinal finalState) ->
  appendTransitions prefixTrace
    (MoreTransitions first (MoreTransitions second rest)) = global ->
  LocatedActionOccurrence (transitionAction second) global
locatedSecondAfterPrefix global prefixTrace first second rest decomposition =
  MkLocatedActionOccurrence _ _
    (appendTransitions prefixTrace (MoreTransitions first NoTransitions)) second rest
    Refl
    (trans (appendTransitionsAssociative prefixTrace
      (MoreTransitions first NoTransitions) (MoreTransitions second rest))
      decomposition)

||| Exhaustive ordinal semantics of one adjacent transposition.  Prefix and
||| suffix occurrences retain their absolute ordinal; moved-right and moved-left
||| exchange the two adjacent source ordinals.
public export
data AdjacentSwapOrdinalRelation :
  (prefixCount, targetOrdinal, sourceOrdinal : Nat) -> Type where
  AdjacentPrefixOrdinal : LT targetOrdinal prefixCount ->
    AdjacentSwapOrdinalRelation prefixCount targetOrdinal targetOrdinal
  AdjacentMovedRightOrdinal :
    AdjacentSwapOrdinalRelation prefixCount prefixCount (S prefixCount)
  AdjacentMovedLeftOrdinal :
    AdjacentSwapOrdinalRelation prefixCount (S prefixCount) prefixCount
  AdjacentSuffixOrdinal : LTE (S (S prefixCount)) targetOrdinal ->
    AdjacentSwapOrdinalRelation prefixCount targetOrdinal targetOrdinal

||| The four regions cover every target ordinal.  This executable classifier is
||| independent of occurrence actions/tags, so repeated identical Iter nodes do
||| not create an unclassified case.
public export
adjacentSwapOrdinalExhaustive : (prefixCount, targetOrdinal : Nat) ->
  (sourceOrdinal : Nat **
    AdjacentSwapOrdinalRelation prefixCount targetOrdinal sourceOrdinal)
adjacentSwapOrdinalExhaustive Z Z =
  (S Z ** AdjacentMovedRightOrdinal)
adjacentSwapOrdinalExhaustive Z (S Z) =
  (Z ** AdjacentMovedLeftOrdinal)
adjacentSwapOrdinalExhaustive Z (S (S later)) =
  (S (S later) ** AdjacentSuffixOrdinal (LTESucc (LTESucc LTEZero)))
adjacentSwapOrdinalExhaustive (S prefixCount) Z =
  (Z ** AdjacentPrefixOrdinal (LTESucc LTEZero))
adjacentSwapOrdinalExhaustive (S prefixCount) (S targetOrdinal) =
  case adjacentSwapOrdinalExhaustive prefixCount targetOrdinal of
    (_ ** AdjacentPrefixOrdinal before) =>
      (S targetOrdinal ** AdjacentPrefixOrdinal (LTESucc before))
    (_ ** AdjacentMovedRightOrdinal) =>
      (S (S prefixCount) ** AdjacentMovedRightOrdinal)
    (_ ** AdjacentMovedLeftOrdinal) =>
      (S prefixCount ** AdjacentMovedLeftOrdinal)
    (_ ** AdjacentSuffixOrdinal after) =>
      (S targetOrdinal ** AdjacentSuffixOrdinal (LTESucc after))

public export
0 adjacentTwoSuccNotLTE : LTE (S (S n)) n -> Void
adjacentTwoSuccNotLTE {n = Z} LTEZero impossible
adjacentTwoSuccNotLTE {n = S later} (LTESucc before) =
  adjacentTwoSuccNotLTE before

public export
0 adjacentSeparatedBoundsImpossible :
  LTE (S (S upper)) lower -> LTE (S lower) upper -> Void
adjacentSeparatedBoundsImpossible {upper = Z} after LTEZero impossible
adjacentSeparatedBoundsImpossible {upper = S upper} {lower = Z}
  LTEZero before impossible
adjacentSeparatedBoundsImpossible {upper = S upper} {lower = S lower}
  (LTESucc after) (LTESucc before) =
    adjacentSeparatedBoundsImpossible after before

||| Pairwise arithmetic disjointness of the four regions.
public export
0 adjacentPrefixNotMovedRight : LT prefixCount prefixCount -> Void
adjacentPrefixNotMovedRight = succNotLTEpred

public export
0 adjacentPrefixNotMovedLeft : LT (S prefixCount) prefixCount -> Void
adjacentPrefixNotMovedLeft = adjacentTwoSuccNotLTE

public export
0 adjacentPrefixNotSuffix :
  LT targetOrdinal prefixCount ->
  LTE (S (S prefixCount)) targetOrdinal -> Void
adjacentPrefixNotSuffix before after =
  adjacentSeparatedBoundsImpossible after before

public export
0 adjacentMovedRightNotSuffix : LTE (S (S prefixCount)) prefixCount -> Void
adjacentMovedRightNotSuffix = adjacentTwoSuccNotLTE

public export
0 adjacentMovedLeftNotSuffix : LTE (S (S prefixCount)) (S prefixCount) -> Void
adjacentMovedLeftNotSuffix = succNotLTEpred

||| First-source authenticity for one adjacent swap.  The occurrence map is
||| produced by one globally fixed suffix-replay fold, and every target
||| occurrence—prefix, moved pair, or suffix—must satisfy the exhaustive ordinal
||| relation above.
public export
record AdjacentSwapOperationalOccurrenceFold
  (name, key, world, error : Type) (value : key -> Type)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal, swappedMiddle,
    swappedFinal, replayedFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (prefixTrace : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle)
  (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal)
  (movedRight : Transition pairFirst swappedMiddle)
  (movedLeft : Transition swappedMiddle swappedFinal)
  (replayedSuffix : Transitions swappedFinal replayedFinal)
  (swappedTrace : Transitions initial replayedFinal) where
  constructor MkAdjacentSwapOperationalOccurrenceFold
  operationalOriginalDecomposition : appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = original
  operationalSwappedDecomposition : appendTransitions prefixTrace
    (MoreTransitions movedRight (MoreTransitions movedLeft replayedSuffix)) =
      swappedTrace
  operationalOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence
    name key world error value original swappedTrace
  0 operationalOrdinalRelation :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action swappedTrace) ->
    AdjacentSwapOrdinalRelation (transitionCount prefixTrace)
      (locatedActionOrdinal occurrence)
      (locatedActionOrdinal
        (replayActionOrigin operationalOccurrenceCorrespondence occurrence))

||| Producer-sealed recursive suffix replay.  Every node owns its exact checked
||| source and target heads and their relational/occurrence capital.  It carries
||| no `ReplayInvariantBundle`: only the outer whole trace starts at the
||| authenticated empty registry.  Constructors are deliberately hidden from
||| importers; only the O6 producer in this module may assemble the spine.
export
data SealedSuffixReplaySpine :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal :
    SystemState name key value world error} ->
  Transitions sourceFirst sourceFinal ->
  Transitions replayedFirst replayedFinal -> Type where
  SealedSuffixReplayEnd :
    SealedSuffixReplaySpine name key world error value nameEq keyEq
      NoTransitions NoTransitions
  SealedSuffixReplayStep :
    (sourceStep : Transition sourceFirst sourceMiddle) ->
    (replayedStep : Transition replayedFirst replayedMiddle) ->
    (sourceTail : Transitions sourceMiddle sourceFinal) ->
    (replayedTail : Transitions replayedMiddle replayedFinal) ->
    (0 sameAction : transitionAction replayedStep =
      transitionAction sourceStep) ->
    (0 sameTag : transitionTag replayedStep = transitionTag sourceStep) ->
    (0 headRAR : RelationalReplayCorrespondence name key world error value
      (MoreTransitions sourceStep NoTransitions)
      (MoreTransitions replayedStep NoTransitions)) ->
    (0 headMapsRelated : PartialMapsRelated
      (EffectStateEquivalence keyEq)
      (partialEffectMap sourceStep) (partialEffectMap replayedStep)) ->
    (0 headEndpoint : RelationalReplayEndpoint name key world error value nameEq
      keyEq sourceMiddle replayedMiddle) ->
    (0 headOccurrences : ActionRegistrationReplayCorrespondence name key world
      error value (MoreTransitions sourceStep NoTransitions)
      (MoreTransitions replayedStep NoTransitions)) ->
    (0 headRelativeOrdinal :
      {action : Action name key value world error} ->
      (occurrence : LocatedActionOccurrence action
        (MoreTransitions replayedStep NoTransitions)) ->
      locatedActionOrdinal occurrence = locatedActionOrdinal
        (replayActionOrigin headOccurrences occurrence)) ->
    SealedSuffixReplaySpine name key world error value nameEq keyEq sourceTail
      replayedTail ->
    SealedSuffixReplaySpine name key world error value nameEq keyEq
      (MoreTransitions sourceStep sourceTail)
      (MoreTransitions replayedStep replayedTail)

||| Producer-local result of replaying one exact checked suffix head from a
||| pointwise-related state.  This is deliberately not exported: it is the
||| recursive implementation unit for `adjacentSwapSuffixSpike`, not a new
||| caller-supplied boundary.  Every field is indexed by the source transition
||| and the checked replay transition constructed at this point.
record PointwiseRelationalHeadReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceBefore, sourceAfter : SystemState name key value world error}
  (sourceStep : Transition sourceBefore sourceAfter)
  (replayedBefore : SystemState name key value world error) where
  constructor MkPointwiseRelationalHeadReplay
  headReplayedAfter : SystemState name key value world error
  headReplayedStep : Transition replayedBefore headReplayedAfter
  0 headSameAction : transitionAction headReplayedStep =
    transitionAction sourceStep
  0 headSameTag : transitionTag headReplayedStep = transitionTag sourceStep
  0 headAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions headReplayedStep NoTransitions)
  0 headReplayRAR : RelationalReplayCorrespondence name key world error value
    (MoreTransitions sourceStep NoTransitions)
    (MoreTransitions headReplayedStep NoTransitions)
  0 headReplayMapsRelated : PartialMapsRelated
    (EffectStateEquivalence keyEq)
    (partialEffectMap sourceStep) (partialEffectMap headReplayedStep)
  0 headReplayEndpoint : RelationalReplayEndpoint name key world error value
    nameEq keyEq sourceAfter headReplayedAfter
  0 headReplayOccurrences : ActionRegistrationReplayCorrespondence name key
    world error value (MoreTransitions sourceStep NoTransitions)
    (MoreTransitions headReplayedStep NoTransitions)
  0 headReplayRelativeOrdinal :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action
      (MoreTransitions headReplayedStep NoTransitions)) ->
    locatedActionOrdinal occurrence = locatedActionOrdinal
      (replayActionOrigin headReplayOccurrences occurrence)

||| Once the exact head producer and recursive tail have been constructed, the
||| frozen spine node is definition-only.  In particular, no map, endpoint, or
||| occurrence proof can enter here independently of its owning head result.
0 sealPointwiseRelationalHead :
  {sourceStep : Transition sourceFirst sourceMiddle} ->
  {sourceTail : Transitions sourceMiddle sourceFinal} ->
  (head : PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    sourceStep replayedFirst) ->
  {replayedTail : Transitions
    (headReplayedAfter head) replayedFinal} ->
  SealedSuffixReplaySpine name key world error value nameEq keyEq sourceTail
    replayedTail ->
  SealedSuffixReplaySpine name key world error value nameEq keyEq
    (MoreTransitions sourceStep sourceTail)
    (MoreTransitions (headReplayedStep head) replayedTail)
sealPointwiseRelationalHead head tail =
  SealedSuffixReplayStep _ _ _ _
    (headSameAction head) (headSameTag head) (headReplayRAR head)
    (headReplayMapsRelated head) (headReplayEndpoint head)
    (headReplayOccurrences head) (headReplayRelativeOrdinal head) tail

0 checkedTargetWellFormed :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
checkedTargetWellFormed nameEq keyEq action before afterState tag checked
  with (applyAction @{nameEq} @{keyEq} action before) proof raw
  checkedTargetWellFormed nameEq keyEq action before afterState tag checked |
    Nothing = case checked of Refl impossible
  checkedTargetWellFormed nameEq keyEq action before afterState tag checked |
    Just (actualTag, actualAfter)
    with (registryWellFormed @{nameEq} @{keyEq} actualAfter) proof wellFormed
    checkedTargetWellFormed nameEq keyEq action before afterState tag checked |
      Just (actualTag, actualAfter) | False = case checked of Refl impossible
    checkedTargetWellFormed nameEq keyEq action before afterState tag checked |
      Just (actualTag, actualAfter) | True =
        case justInjective checked of
          Refl => wellFormed

0 singletonPrefixTooLong :
  {first, point, beforeLocated, afterLocated, finalState :
    SystemState name key value world error} ->
  (prefixStep : Transition first point) ->
  (prefixRest : Transitions point beforeLocated) ->
  (located : Transition beforeLocated afterLocated) ->
  (suffix : Transitions afterLocated finalState) ->
  (only : Transition first finalState) ->
  appendTransitions (MoreTransitions prefixStep prefixRest)
    (MoreTransitions located suffix) = MoreTransitions only NoTransitions -> Void
singletonPrefixTooLong prefixStep NoTransitions located suffix only
  decomposition = case cong transitionCount decomposition of Refl impossible
singletonPrefixTooLong prefixStep (MoreTransitions head tail) located suffix only
  decomposition = case cong transitionCount decomposition of Refl impossible

0 singletonActionOrigin :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  transitionAction replayed = transitionAction source ->
  LocatedActionOccurrence action (MoreTransitions replayed NoTransitions) ->
  LocatedActionOccurrence action (MoreTransitions source NoTransitions)
singletonActionOrigin source replayed sameAction
  (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions located Refl) =
    MkLocatedActionOccurrence _ _ NoTransitions source NoTransitions
      (trans (sym sameAction) located) Refl
singletonActionOrigin source replayed sameAction
  (MkLocatedActionOccurrence _ _ (MoreTransitions head tail) located suffix
    actionSame decomposition) =
      void (singletonPrefixTooLong head tail located suffix replayed decomposition)

0 singletonTagPreserved :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sameAction : transitionAction replayed = transitionAction source) ->
  transitionTag replayed = transitionTag source ->
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions replayed NoTransitions)) ->
  transitionTag (locatedTransition
    (singletonActionOrigin source replayed sameAction occurrence)) =
  transitionTag (locatedTransition occurrence)
singletonTagPreserved source replayed sameAction sameTag
  (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions located Refl) =
    sym sameTag
singletonTagPreserved source replayed sameAction sameTag
  (MkLocatedActionOccurrence _ _ (MoreTransitions head tail) located suffix
    actionSame decomposition) =
      void (singletonPrefixTooLong head tail located suffix replayed decomposition)

0 singletonGeneratedOrigin :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  transitionAction replayed = transitionAction source ->
  LocatedGeneratedRegistration child parent component
    (MoreTransitions replayed NoTransitions) ->
  LocatedGeneratedRegistration child parent component
    (MoreTransitions source NoTransitions)
singletonGeneratedOrigin source replayed sameAction
  (MkLocatedGeneratedRegistration _ _ NoTransitions _ NoTransitions located
    Refl) =
      MkLocatedGeneratedRegistration _ _ NoTransitions source NoTransitions
        (trans (sym sameAction) located) Refl
singletonGeneratedOrigin source replayed sameAction
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head tail) located suffix
    actionSame decomposition) =
      void (singletonPrefixTooLong head tail located suffix replayed decomposition)

0 singletonGeneratedOriginCoherent :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sameAction : transitionAction replayed = transitionAction source) ->
  (occurrence : LocatedGeneratedRegistration child parent component
    (MoreTransitions replayed NoTransitions)) ->
  generatedRegistrationActionOccurrence
    (singletonGeneratedOrigin source replayed sameAction occurrence) =
  singletonActionOrigin source replayed sameAction
    (generatedRegistrationActionOccurrence occurrence)
singletonGeneratedOriginCoherent source replayed sameAction
  (MkLocatedGeneratedRegistration _ _ NoTransitions _ NoTransitions located
    Refl) = Refl
singletonGeneratedOriginCoherent source replayed sameAction
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head tail) located suffix
    actionSame decomposition) =
      void (singletonPrefixTooLong head tail located suffix replayed decomposition)

0 singletonGeneratedGenerationSame :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sameAction : transitionAction replayed = transitionAction source) ->
  (occurrence : LocatedGeneratedRegistration child parent component
    (MoreTransitions replayed NoTransitions)) ->
  registrationGeneration
    (singletonGeneratedOrigin source replayed sameAction occurrence) =
  registrationGeneration occurrence
singletonGeneratedGenerationSame source replayed sameAction
  (MkLocatedGeneratedRegistration _ _ NoTransitions _ NoTransitions located
    Refl) = Refl
singletonGeneratedGenerationSame source replayed sameAction
  (MkLocatedGeneratedRegistration _ _ (MoreTransitions head tail) located suffix
    actionSame decomposition) =
      void (singletonPrefixTooLong head tail located suffix replayed decomposition)

%inline
0 singletonActionRegistrationReplay :
  (source : Transition sourceBefore sourceAfter) ->
  (replayed : Transition replayedBefore replayedAfter) ->
  (sameAction : transitionAction replayed = transitionAction source) ->
  (sameTag : transitionTag replayed = transitionTag source) ->
  ActionRegistrationReplayCorrespondence name key world error value
    (MoreTransitions source NoTransitions)
    (MoreTransitions replayed NoTransitions)
singletonActionRegistrationReplay source replayed sameAction sameTag =
  MkActionRegistrationReplayCorrespondence
    (MkRegistrationGenerationBijection id id
      (\generation => Refl) (\generation => Refl))
    (singletonActionOrigin source replayed sameAction)
    (singletonTagPreserved source replayed sameAction sameTag)
    (singletonGeneratedOrigin source replayed sameAction)
    (singletonGeneratedOriginCoherent source replayed sameAction)
    (singletonGeneratedGenerationSame source replayed sameAction)

0 singletonOccursSelected :
  {selected : Transition selectedBefore selectedAfter} ->
  {only : Transition first finalState} ->
  OccursIn selected (MoreTransitions only NoTransitions) -> selected = only
singletonOccursSelected OccursHere = Refl
singletonOccursSelected (OccursLater later) = void (noOccurrenceInEmpty later)

0 noIteratorStageInSingletonNonAdvance :
  (transition : Transition before afterState) ->
  (action : Action name key value world error) ->
  transitionAction transition = action ->
  ((actor : name) -> Not (action = LAdvance actor)) ->
  IteratorStage name key world error value selected
    (MoreTransitions transition NoTransitions) -> Void
noIteratorStageInSingletonNonAdvance transition action actionExact notAdvance
  (StageFromAdvance nameEq keyEq selected tag equation occurs fiber found
    remaining accumulator view lifecycle step rest suffix) =
      case singletonOccursSelected occurs of
        Refl => notAdvance selected (sym actionExact)

0 singletonNonAdvanceGeneratorOrigin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action sourceBefore =
    Just (tag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{nameEq} @{keyEq} action replayedBefore =
    Just (tag, replayedAfter)) ->
  ((actor : name) -> Not (action = LAdvance actor)) ->
  (selected : name) ->
  TraceEffectGenerator name key world error value selected
    (MoreTransitions
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag replayedChecked) NoTransitions) ->
  TraceEffectGenerator name key world error value selected
    (MoreTransitions
      (Fired {before = sourceBefore} {afterState = sourceAfter}
        nameEq keyEq action tag sourceChecked) NoTransitions)
singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag sourceBefore
  sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
  notAdvance selected
  (ActualForwardGenerator _ _ _ _ _ _ _ occurs actorMatches) =
    case singletonOccursSelected occurs of
      Refl => ActualForwardGenerator sourceBefore sourceAfter nameEq keyEq action
        tag sourceChecked OccursHere actorMatches
singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag sourceBefore
  sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
  notAdvance selected (IteratorForwardGenerator stage) =
    void (noIteratorStageInSingletonNonAdvance
      (Fired nameEq keyEq action tag replayedChecked) action Refl notAdvance stage)
singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag sourceBefore
  sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
  notAdvance selected (IteratorYieldedGenerator stage origin) =
    void (noIteratorStageInSingletonNonAdvance
      (Fired nameEq keyEq action tag replayedChecked) action Refl notAdvance stage)

0 singletonNonAdvanceGeneratorUsesTransitionMap :
  (transition : Transition before afterState) ->
  (action : Action name key value world error) ->
  (actionExact : transitionAction transition = action) ->
  ((actor : name) -> Not (action = LAdvance actor)) ->
  (generator : TraceEffectGenerator name key world error value selected
    (MoreTransitions transition NoTransitions)) ->
  (state : EffectState name key value world) ->
  traceGeneratorMap generator state = partialEffectMap transition state
singletonNonAdvanceGeneratorUsesTransitionMap transition action actionExact
  notAdvance
  (ActualForwardGenerator _ _ _ _ _ _ _ occurs actorMatches) state =
    case singletonOccursSelected occurs of Refl => Refl
singletonNonAdvanceGeneratorUsesTransitionMap transition action actionExact
  notAdvance (IteratorForwardGenerator stage) state =
    void (noIteratorStageInSingletonNonAdvance transition action actionExact
      notAdvance stage)
singletonNonAdvanceGeneratorUsesTransitionMap transition action actionExact
  notAdvance (IteratorYieldedGenerator stage origin) state =
    void (noIteratorStageInSingletonNonAdvance transition action actionExact
      notAdvance stage)

0 singletonNonAdvanceGeneratorMapsRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action sourceBefore =
    Just (tag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{nameEq} @{keyEq} action replayedBefore =
    Just (tag, replayedAfter)) ->
  (notAdvance : (actor : name) -> Not (action = LAdvance actor)) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap
      (Fired {before = sourceBefore} {afterState = sourceAfter}
        nameEq keyEq action tag sourceChecked))
    (partialEffectMap
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag replayedChecked)) ->
  (observedKeyEq : DecEq key) ->
  (selected : name) ->
  (generator : TraceEffectGenerator name key world error value selected
    (MoreTransitions
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag replayedChecked) NoTransitions)) ->
  PartialMapsRelated (EffectStateEquivalence observedKeyEq)
    (traceGeneratorMap
      (singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag sourceBefore
        sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
        notAdvance selected generator))
    (traceGeneratorMap generator)
singletonNonAdvanceGeneratorMapsRelated nameEq keyEq action tag sourceBefore
  sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
  notAdvance mapsRelated observedKeyEq selected generator {x} {y} inputs =
    let 0 storedInputs : EffectStateRelated keyEq x y
        storedInputs = replayReindexEffectRelated inputs
        0 storedOutputs : PartialRelated
          (EffectState name key value world) (EffectStateRelated keyEq)
          (partialEffectMap
            (Fired {before = sourceBefore} {afterState = sourceAfter}
              nameEq keyEq action tag sourceChecked) x)
          (partialEffectMap
            (Fired {before = replayedBefore} {afterState = replayedAfter}
              nameEq keyEq action tag replayedChecked) y)
        storedOutputs = mapsRelated storedInputs
        0 observedOutputs : PartialRelated
          (EffectState name key value world) (EffectStateRelated observedKeyEq)
          (partialEffectMap
            (Fired {before = sourceBefore} {afterState = sourceAfter}
              nameEq keyEq action tag sourceChecked) x)
          (partialEffectMap
            (Fired {before = replayedBefore} {afterState = replayedAfter}
              nameEq keyEq action tag replayedChecked) y)
        observedOutputs = replayReindexPartialRelated storedOutputs
        0 sourceUses : traceGeneratorMap
          (singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag
            sourceBefore sourceAfter replayedBefore replayedAfter sourceChecked
            replayedChecked notAdvance selected generator) x =
          partialEffectMap
            (Fired {before = sourceBefore} {afterState = sourceAfter}
              nameEq keyEq action tag sourceChecked) x
        sourceUses = singletonNonAdvanceGeneratorUsesTransitionMap
          (Fired {before = sourceBefore} {afterState = sourceAfter}
            nameEq keyEq action tag sourceChecked)
          action Refl notAdvance
          (singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag
            sourceBefore sourceAfter replayedBefore replayedAfter sourceChecked
            replayedChecked notAdvance selected generator) x
        0 targetUses : traceGeneratorMap generator y =
          partialEffectMap
            (Fired {before = replayedBefore} {afterState = replayedAfter}
              nameEq keyEq action tag replayedChecked) y
        targetUses = singletonNonAdvanceGeneratorUsesTransitionMap
          (Fired {before = replayedBefore} {afterState = replayedAfter}
            nameEq keyEq action tag replayedChecked)
          action Refl notAdvance generator y
    in replayPartialRewrite (sym sourceUses) (sym targetUses) observedOutputs

0 singletonNonAdvanceRAR :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (sourceBefore, sourceAfter, replayedBefore, replayedAfter :
    SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action sourceBefore =
    Just (tag, sourceAfter)) ->
  (replayedChecked : checkedApplyAction @{nameEq} @{keyEq} action replayedBefore =
    Just (tag, replayedAfter)) ->
  (notAdvance : (actor : name) -> Not (action = LAdvance actor)) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap
      (Fired {before = sourceBefore} {afterState = sourceAfter}
        nameEq keyEq action tag sourceChecked))
    (partialEffectMap
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag replayedChecked)) ->
  RelationalReplayCorrespondence name key world error value
    (MoreTransitions
      (Fired {before = sourceBefore} {afterState = sourceAfter}
        nameEq keyEq action tag sourceChecked) NoTransitions)
    (MoreTransitions
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag replayedChecked) NoTransitions)
singletonNonAdvanceRAR nameEq keyEq action tag sourceBefore sourceAfter
  replayedBefore replayedAfter sourceChecked replayedChecked notAdvance
  mapPreserved =
    MkRelationalReplayCorrespondence
      (singletonNonAdvanceGeneratorOrigin nameEq keyEq action tag sourceBefore
        sourceAfter replayedBefore replayedAfter sourceChecked replayedChecked
        notAdvance)
      (singletonNonAdvanceGeneratorMapsRelated nameEq keyEq action tag
        sourceBefore sourceAfter replayedBefore replayedAfter sourceChecked
        replayedChecked notAdvance mapPreserved)
      (\selected, stage => void (noIteratorStageInSingletonNonAdvance
        (Fired nameEq keyEq action tag replayedChecked) action Refl notAdvance
        stage))
      (\selected, stage, state => void
        (noIteratorStageInSingletonNonAdvance
          (Fired nameEq keyEq action tag replayedChecked) action Refl notAdvance
          stage))

0 pointwiseSomeNoControlImpossible :
  FiberControlMaybeRelated (Just fiber) Nothing -> Void
pointwiseSomeNoControlImpossible relation impossible

0 pointwiseNoSomeControlImpossible :
  FiberControlMaybeRelated Nothing (Just fiber) -> Void
pointwiseNoSomeControlImpossible relation impossible

0 fiberControlNothingRight :
  FiberControlMaybeRelated Nothing right -> right = Nothing
fiberControlNothingRight NoControlFibers = Refl

0 pointwiseControlLookupAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry left) = Nothing ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry right) = Nothing
pointwiseControlLookupAbsent nameEq actor left right controls leftAbsent =
  let 0 relatedRight : FiberControlMaybeRelated
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
          {world = world} {error = error} actor (registry left))
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
          {world = world} {error = error} actor (registry right))
      relatedRight = controlPointwise controls actor
      0 absentRelated : FiberControlMaybeRelated Nothing
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
          {world = world} {error = error} actor (registry right))
      absentRelated = replace
        {p = \observed => FiberControlMaybeRelated observed
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor (registry right))}
        leftAbsent relatedRight
  in fiberControlNothingRight absentRelated

0 pointwiseControlLookupFound :
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  (leftFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry left) = Just leftFiber ->
  (rightFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor (registry right) = Just rightFiber,
     FiberControlRelated leftFiber rightFiber))
pointwiseControlLookupFound nameEq actor left right controls leftFiber leftFound
  with (lookupFiber @{nameEq} actor (registry right)) proof rightFound
  pointwiseControlLookupFound nameEq actor left right controls leftFiber
    leftFound | Nothing =
      let 0 relatedRight : FiberControlMaybeRelated (Just leftFiber)
            (lookupFiber @{nameEq} actor (registry right))
          relatedRight = replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry right))}
            leftFound (controlPointwise controls actor)
          0 impossibleRelation : FiberControlMaybeRelated (Just leftFiber) Nothing
          impossibleRelation = replace
            {p = \observed => FiberControlMaybeRelated (Just leftFiber) observed}
            rightFound relatedRight
      in void (pointwiseSomeNoControlImpossible impossibleRelation)
  pointwiseControlLookupFound nameEq actor left right controls leftFiber
    leftFound | Just rightFiber =
      let 0 relatedRight : FiberControlMaybeRelated (Just leftFiber)
            (lookupFiber @{nameEq} actor (registry right))
          relatedRight = replace
            {p = \observed => FiberControlMaybeRelated observed
              (lookupFiber @{nameEq} actor (registry right))}
            leftFound (controlPointwise controls actor)
          0 exactRelation : FiberControlMaybeRelated (Just leftFiber)
            (Just rightFiber)
          exactRelation = replace
            {p = \observed => FiberControlMaybeRelated (Just leftFiber) observed}
            rightFound relatedRight
      in case exactRelation of
        SomeControlFibers fibersRelated =>
          (rightFiber ** (Refl, fibersRelated))

0 pointwiseControlLookupPresenceSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  isJust (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry left)) =
  isJust (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry right))
pointwiseControlLookupPresenceSame nameEq actor left right controls
  with (lookupFiber @{nameEq} actor (registry left)) proof leftFound
  pointwiseControlLookupPresenceSame nameEq actor left right controls |
    Nothing = rewrite pointwiseControlLookupAbsent nameEq actor left right
      controls leftFound in Refl
  pointwiseControlLookupPresenceSame nameEq actor left right controls |
    Just leftFiber =
      case pointwiseControlLookupFound nameEq actor left right controls leftFiber
        leftFound of
        (rightFiber ** (rightFound, related)) => rewrite rightFound in Refl

0 pointwiseParentPresentSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent (registry left) =
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent (registry right)
pointwiseParentPresentSame nameEq Root left right controls = Refl
pointwiseParentPresentSame nameEq (ChildOf actor) left right controls =
  pointwiseControlLookupPresenceSame nameEq actor left right controls

0 boolAndLeftPointwise :
  (left, right : Bool) -> left && right = True -> left = True
boolAndLeftPointwise False right valid = case valid of Refl impossible
boolAndLeftPointwise True right valid = Refl

0 boolAndRightPointwise :
  (left, right : Bool) -> left && right = True -> right = True
boolAndRightPointwise False right valid = case valid of Refl impossible
boolAndRightPointwise True False valid = case valid of Refl impossible
boolAndRightPointwise True True valid = Refl

0 boolAndBothPointwise :
  (left, right : Bool) -> left = True -> right = True -> left && right = True
boolAndBothPointwise True True Refl Refl = Refl

0 bindingKeyElemPointwise :
  (entry : Binding key value) -> (entries : List (Binding key value)) ->
  Elem entry entries -> Elem (bindingKey entry) (bindingKeys entries)
bindingKeyElemPointwise entry (entry :: rest) Here = Here
bindingKeyElemPointwise entry (other :: rest) (There later) =
  There (bindingKeyElemPointwise entry rest later)

0 entryLookupFromElemPointwise :
  (nameEq : DecEq name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind selected fiber) entries ->
  lookupEntries @{nameEq} selected entries = Just fiber
entryLookupFromElemPointwise nameEq [] UniqueNil selected fiber present impossible
entryLookupFromElemPointwise nameEq (Bind current observed :: rest)
  (UniqueCons headFresh tailUnique) selected fiber present
  with (decEq @{nameEq} selected current)
  entryLookupFromElemPointwise nameEq (Bind selected observed :: rest)
    (UniqueCons headFresh tailUnique) selected fiber present | Yes Refl =
      let 0 sameFiber : (observed = fiber)
          sameFiber = case present of
            Here => Refl
            There later => void (headFresh
              (bindingKeyElemPointwise (Bind selected fiber) rest later))
      in case sameFiber of Refl => Refl
  entryLookupFromElemPointwise nameEq (Bind current observed :: rest)
    (UniqueCons headFresh tailUnique) selected fiber present | No distinct =
      case present of
        Here => void (distinct Refl)
        There later => entryLookupFromElemPointwise nameEq rest tailUnique
          selected fiber later

0 provisionsDisjointFromElemPointwise :
  (keyEq : DecEq key) -> (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind selected fiber) entries ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision entries = True ->
  not (provisionOverlap @{keyEq} provision
    (componentProvisions (fiberComponent fiber))) = True
provisionsDisjointFromElemPointwise keyEq provision
  (Bind selected fiber :: rest) selected fiber Here valid =
    boolAndLeftPointwise _ _ valid
provisionsDisjointFromElemPointwise keyEq provision
  (Bind current observed :: rest) selected fiber (There later) valid =
    provisionsDisjointFromElemPointwise keyEq provision rest selected fiber later
      (boolAndRightPointwise _ _ valid)

0 provisionsDisjointFromAllEntriesPointwise :
  (keyEq : DecEq key) -> (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    Elem (Bind selected fiber) entries ->
    not (provisionOverlap @{keyEq} provision
      (componentProvisions (fiberComponent fiber))) = True) ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision entries = True
provisionsDisjointFromAllEntriesPointwise keyEq provision [] each = Refl
provisionsDisjointFromAllEntriesPointwise keyEq provision
  (Bind selected fiber :: rest) each =
    boolAndBothPointwise _ _ (each selected fiber Here)
      (provisionsDisjointFromAllEntriesPointwise keyEq provision rest
        (\later, observed, present => each later observed (There present)))

0 entryElemFromLookupPointwise :
  (nameEq : DecEq name) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys entries) ->
  lookupEntries @{nameEq} selected entries = Just fiber ->
  Elem (Bind selected fiber) entries
entryElemFromLookupPointwise nameEq selected fiber [] UniqueNil found impossible
entryElemFromLookupPointwise nameEq selected fiber
  (Bind current observed :: rest) (UniqueCons headFresh tailUnique) found
  with (decEq @{nameEq} selected current)
  entryElemFromLookupPointwise nameEq current fiber
    (Bind current observed :: rest) (UniqueCons headFresh tailUnique) found |
    Yes Refl = case justInjective found of Refl => Here
  entryElemFromLookupPointwise nameEq selected fiber
    (Bind current observed :: rest) (UniqueCons headFresh tailUnique) found |
    No distinct = There (entryElemFromLookupPointwise nameEq selected fiber
      rest tailUnique found)

0 pointwiseProvisionsDisjointFromTrue :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision (bindings (registry left)) = True ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision (bindings (registry right)) = True
pointwiseProvisionsDisjointFromTrue nameEq keyEq provision
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  controls sourceDisjoint =
    provisionsDisjointFromAllEntriesPointwise keyEq provision rightEntries
      targetEntry
  where
  0 targetEntry : (selected : name) ->
    (targetFiber : Fiber name key value world error) ->
    Elem (Bind selected targetFiber) rightEntries ->
    not (provisionOverlap @{keyEq} provision
      (componentProvisions (fiberComponent targetFiber))) = True
  targetEntry selected targetFiber present =
    let 0 targetFoundEntries : (lookupEntries @{nameEq} selected rightEntries =
          Just targetFiber)
        targetFoundEntries = entryLookupFromElemPointwise nameEq rightEntries
          rightUnique selected targetFiber present
        0 targetFound : (lookupFiber @{nameEq} selected
          (MkCoeffectContext rightEntries rightUnique) = Just targetFiber)
        targetFound = targetFoundEntries
    in case pointwiseControlLookupFound nameEq selected
      (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
      (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
      (controlEquivalentSymmetric controls) targetFiber targetFound of
      (sourceFiber ** (sourceFound, related)) =>
        let 0 sourceFoundEntries : (lookupEntries @{nameEq} selected leftEntries =
              Just sourceFiber)
            sourceFoundEntries = lookupFiberEntries nameEq selected sourceFiber
              (MkCoeffectContext leftEntries leftUnique) sourceFound
            0 sourceEntryPresent : Elem (Bind selected sourceFiber) leftEntries
            sourceEntryPresent = entryElemFromLookupPointwise nameEq selected
              sourceFiber leftEntries leftUnique sourceFoundEntries
            0 sourceHead : not (provisionOverlap @{keyEq} provision
              (componentProvisions (fiberComponent sourceFiber))) = True
            sourceHead = provisionsDisjointFromElemPointwise keyEq provision
              leftEntries selected sourceFiber sourceEntryPresent sourceDisjoint
        in case related of
          FibersControlRelated _ _ _ _ _ _ _ _ _ _ _ => sourceHead

0 boolOrBothFalsePointwise :
  (left, right : Bool) -> left = False -> right = False -> left || right = False
boolOrBothFalsePointwise False False Refl Refl = Refl

0 parentDistinctMakesNotChildPointwise :
  (nameEq : DecEq name) -> (parent, child : name) ->
  (fiber : Fiber name key value world error) ->
  Not (fiberParent fiber = ChildOf parent) ->
  isChildOf @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent (Bind child fiber) = False
parentDistinctMakesNotChildPointwise nameEq parent child
  (MkFiber component Root retired table lifecycle) distinct = Refl
parentDistinctMakesNotChildPointwise nameEq parent child
  (MkFiber component (ChildOf candidate) retired table lifecycle) distinct
  with (decEq @{nameEq} parent candidate)
  parentDistinctMakesNotChildPointwise nameEq candidate child
    (MkFiber component (ChildOf candidate) retired table lifecycle) distinct |
    Yes Refl = void (distinct Refl)
  parentDistinctMakesNotChildPointwise nameEq parent child
    (MkFiber component (ChildOf candidate) retired table lifecycle) distinct |
    No different = Refl

0 hasChildInFromEntryParentsPointwise :
  (nameEq : DecEq name) -> (parent : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  ((child : name) -> (fiber : Fiber name key value world error) ->
    Elem (Bind child fiber) entries ->
    Not (fiberParent fiber = ChildOf parent)) ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent entries = False
hasChildInFromEntryParentsPointwise nameEq parent [] each = Refl
hasChildInFromEntryParentsPointwise nameEq parent
  (Bind child fiber :: rest) each =
    boolOrBothFalsePointwise _ _
      (parentDistinctMakesNotChildPointwise nameEq parent child fiber
        (each child fiber Here))
      (hasChildInFromEntryParentsPointwise nameEq parent rest
        (\later, observed, present => each later observed (There present)))

0 pointwiseNoChildPreserved :
  (nameEq : DecEq name) -> (parent : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent (registry left) = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent (registry right) = False
pointwiseNoChildPreserved nameEq parent
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  controls sourceNoChild =
    hasChildInFromEntryParentsPointwise nameEq parent rightEntries targetParent
  where
  0 targetParent : (child : name) ->
    (targetFiber : Fiber name key value world error) ->
    Elem (Bind child targetFiber) rightEntries ->
    Not (fiberParent targetFiber = ChildOf parent)
  targetParent child targetFiber present =
    let 0 targetFoundEntries : (lookupEntries @{nameEq} child rightEntries =
          Just targetFiber)
        targetFoundEntries = entryLookupFromElemPointwise nameEq rightEntries
          rightUnique child targetFiber present
        0 targetFound : (lookupFiber @{nameEq} child
          (MkCoeffectContext rightEntries rightUnique) = Just targetFiber)
        targetFound = targetFoundEntries
    in case pointwiseControlLookupFound nameEq child
      (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
      (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
      (controlEquivalentSymmetric controls) targetFiber targetFound of
      (sourceFiber ** (sourceFound, related)) =>
        let 0 sourceDistinct : Not
              (fiberParent sourceFiber = ChildOf parent)
            sourceDistinct = noChildLookupParentDistinct nameEq parent child
              sourceFiber (MkCoeffectContext leftEntries leftUnique)
              sourceNoChild sourceFound
        in case related of
          FibersControlRelated _ _ _ _ _ _ _ _ parentSame _ _ =>
            \targetSame => sourceDistinct (trans (sym parentSame) targetSame)

0 boolOrFalseRightPointwise :
  (left, right : Bool) -> left || right = False -> right = False
boolOrFalseRightPointwise False right valid = valid
boolOrFalseRightPointwise True right valid = case valid of Refl impossible

0 reliedOnByFalseAtEntryPointwise :
  (nameEq : DecEq name) -> (provider, self, current : name) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  Elem (Bind current fiber) entries ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self entries = False ->
  reliedHead @{nameEq} provider self (Bind current fiber) = False
reliedOnByFalseAtEntryPointwise nameEq provider self current fiber
  (Bind current fiber :: rest) Here allFalse with
    (reliedHead @{nameEq} provider self (Bind current fiber))
  reliedOnByFalseAtEntryPointwise nameEq provider self current fiber
    (Bind current fiber :: rest) Here allFalse | False = Refl
  reliedOnByFalseAtEntryPointwise nameEq provider self current fiber
    (Bind current fiber :: rest) Here allFalse | True =
      case allFalse of Refl impossible
reliedOnByFalseAtEntryPointwise nameEq provider self current fiber
  (other :: rest) (There later) allFalse =
    reliedOnByFalseAtEntryPointwise nameEq provider self current fiber rest later
      (boolOrFalseRightPointwise _ _ allFalse)

0 reliedOnByFromAllHeadsFalsePointwise :
  (nameEq : DecEq name) -> (provider, self : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  ((current : name) -> (fiber : Fiber name key value world error) ->
    Elem (Bind current fiber) entries ->
    reliedHead @{nameEq} provider self (Bind current fiber) = False) ->
  reliedOnBy @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider self entries = False
reliedOnByFromAllHeadsFalsePointwise nameEq provider self [] each = Refl
reliedOnByFromAllHeadsFalsePointwise nameEq provider self
  (Bind current fiber :: rest) each =
    boolOrBothFalsePointwise _ _ (each current fiber Here)
      (reliedOnByFromAllHeadsFalsePointwise nameEq provider self rest
        (\later, observed, present => each later observed (There present)))

||| Pointwise control equivalence transports the L-Unload reliance guard without
||| requiring a common registry order. Each target consumer is located by name,
||| related to the source consumer, and compared through the lifecycle
||| observation theorem rather than direct dependent `fiberLifecycle` reduction.
0 pointwiseReliedFalse :
  (nameEq : DecEq name) -> (provider : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  relied @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider (registry left) = False ->
  relied @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provider (registry right) = False
pointwiseReliedFalse nameEq provider
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  controls sourceUnrelied =
    reliedOnByFromAllHeadsFalsePointwise nameEq provider provider rightEntries
      targetHead
  where
  0 targetHead : (current : name) ->
    (targetFiber : Fiber name key value world error) ->
    Elem (Bind current targetFiber) rightEntries ->
    reliedHead @{nameEq} provider provider (Bind current targetFiber) = False
  targetHead current targetFiber present =
    let 0 targetFoundEntries : (lookupEntries @{nameEq} current rightEntries =
          Just targetFiber)
        targetFoundEntries = entryLookupFromElemPointwise nameEq rightEntries
          rightUnique current targetFiber present
        0 targetFound : lookupFiber @{nameEq} current
          (MkCoeffectContext rightEntries rightUnique) = Just targetFiber
        targetFound = targetFoundEntries
    in case pointwiseControlLookupFound nameEq current
      (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
      (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
      (controlEquivalentSymmetric controls) targetFiber targetFound of
      (sourceFiber ** (sourceFound, related)) =>
        let 0 sourceFoundEntries : (lookupEntries @{nameEq} current leftEntries =
              Just sourceFiber)
            sourceFoundEntries = lookupFiberEntries nameEq current sourceFiber
              (MkCoeffectContext leftEntries leftUnique) sourceFound
            0 sourcePresent : Elem (Bind current sourceFiber) leftEntries
            sourcePresent = entryElemFromLookupPointwise nameEq current
              sourceFiber leftEntries leftUnique sourceFoundEntries
            0 sourceHead : reliedHead @{nameEq} provider provider
              (Bind current sourceFiber) = False
            sourceHead = reliedOnByFalseAtEntryPointwise nameEq provider provider
              current sourceFiber leftEntries sourcePresent sourceUnrelied
            0 headsSame : reliedHead @{nameEq} provider provider
              (Bind current targetFiber) =
              reliedHead @{nameEq} provider provider (Bind current sourceFiber)
            headsSame = lifecycleControlReliedHeadSame nameEq provider provider
              current related
        in trans headsSame sourceHead

0 pointwiseLifecycleActiveSame : LifecycleControlRelated left right ->
  isActive left = isActive right
pointwiseLifecycleActiveSame (InactiveControls outcome) = Refl
pointwiseLifecycleActiveSame (ReloadingControls remaining accumulator view) = Refl
pointwiseLifecycleActiveSame (ActiveControls accumulator view) = Refl
pointwiseLifecycleActiveSame (UnloadingControls accumulator view outcome) = Refl

0 pointwiseFiberRetiredSame : FiberControlRelated left right ->
  retired left = retired right
pointwiseFiberRetiredSame
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) =
      retiredSame

0 pointwiseFiberInactiveSame : FiberControlRelated left right ->
  isInactive (fiberLifecycle left) = isInactive (fiberLifecycle right)
pointwiseFiberInactiveSame
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) =
      case lifecycleSame of
        InactiveControls outcome => Refl
        ReloadingControls remaining accumulator view => Refl
        ActiveControls accumulator view => Refl
        UnloadingControls accumulator view outcome => Refl

||| The O-Remove guard transports without reopening its operational view:
||| owner retirement/mode are pointwise control projections and childlessness
||| is the exact producer-owned observation transported over the registry.
0 pointwiseRemovalGuardRelated :
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  FiberControlRelated leftFiber rightFiber ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry left) = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor (registry right) = False ->
  (retired leftFiber && isInactive (fiberLifecycle leftFiber) &&
    not (hasChild @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor (registry left)) = True) ->
  (retired rightFiber && isInactive (fiberLifecycle rightFiber) &&
    not (hasChild @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor (registry right)) = True)
pointwiseRemovalGuardRelated nameEq actor left right leftFiber rightFiber related
  leftNoChild rightNoChild leftGuard =
    let 0 sourceRetired : (retired leftFiber = True)
        sourceRetired = boolAndLeftPointwise (retired leftFiber)
          (isInactive (fiberLifecycle leftFiber) &&
            not (hasChild @{nameEq} actor (registry left))) leftGuard
        0 sourceInactive : (isInactive (fiberLifecycle leftFiber) = True)
        sourceInactive = boolAndLeftPointwise
          (isInactive (fiberLifecycle leftFiber))
          (not (hasChild @{nameEq} actor (registry left)))
          (boolAndRightPointwise (retired leftFiber)
            (isInactive (fiberLifecycle leftFiber) &&
              not (hasChild @{nameEq} actor (registry left))) leftGuard)
        0 targetRetired : (retired rightFiber = True)
        targetRetired = trans (sym (pointwiseFiberRetiredSame related))
          sourceRetired
        0 targetInactive : (isInactive (fiberLifecycle rightFiber) = True)
        targetInactive = trans (sym (pointwiseFiberInactiveSame related))
          sourceInactive
        0 targetNotChild : (not (hasChild @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor
          (registry right)) = True)
        targetNotChild = rewrite rightNoChild in Refl
        0 targetRest : (isInactive (fiberLifecycle rightFiber) &&
          not (hasChild @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor (registry right)) = True)
        targetRest = boolAndBothPointwise _ _ targetInactive targetNotChild
    in boolAndBothPointwise _ _ targetRetired targetRest

0 pointwiseMemberKeyFromBindings :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectContext key value) ->
  bindings left = bindings right ->
  memberKey @{keyEq} wanted left = memberKey @{keyEq} wanted right
pointwiseMemberKeyFromBindings keyEq wanted
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same = case same of Refl => Refl

||| Runtime-provider candidacy is name-local: pointwise control fixes activity
||| while the relational effect boundary fixes that actor's owned table.
0 pointwiseProviderCandidateSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry left) = Just leftFiber ->
  lookupFiber @{nameEq} actor (registry right) = Just rightFiber ->
  FiberControlRelated leftFiber rightFiber ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  (isActive (fiberLifecycle leftFiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable leftFiber))) =
  (isActive (fiberLifecycle rightFiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable rightFiber)))
pointwiseProviderCandidateSame nameEq keyEq wanted actor left right
  leftFiber rightFiber leftFound rightFound fibersRelated effects =
    case fibersRelated of
      FibersControlRelated leftParent rightParent leftRetired rightRetired
        leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
        lifecycleSame =>
          let 0 activeSame : (isActive leftLifecycle = isActive rightLifecycle)
              activeSame = pointwiseLifecycleActiveSame lifecycleSame
              0 tablesSame : bindings (ownedValues leftTable) =
                bindings (ownedValues rightTable)
              tablesSame = relatedLocatedFiberTablesSame nameEq actor left right
                leftFiber rightFiber leftFound rightFound effects
              0 memberSame : memberKey @{keyEq} wanted (ownedValues leftTable) =
                memberKey @{keyEq} wanted (ownedValues rightTable)
              memberSame = pointwiseMemberKeyFromBindings keyEq wanted
                (ownedValues leftTable) (ownedValues rightTable) tablesSame
          in rewrite activeSame in cong (isActive rightLifecycle &&) memberSame

||| A named source candidate has one pointwise-related target candidate with the
||| same executable provider predicate.
0 pointwiseProviderCandidateAtName :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  (leftFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry left) = Just leftFiber ->
  (rightFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor (registry right) = Just rightFiber,
     FiberControlRelated leftFiber rightFiber,
     (isActive (fiberLifecycle leftFiber) &&
       memberKey @{keyEq} wanted (ownedValues (fiberTable leftFiber))) =
     (isActive (fiberLifecycle rightFiber) &&
       memberKey @{keyEq} wanted (ownedValues (fiberTable rightFiber)))))
pointwiseProviderCandidateAtName nameEq keyEq wanted actor left right controls
  effects leftFiber leftFound =
    case pointwiseControlLookupFound nameEq actor left right controls leftFiber
      leftFound of
      (rightFiber ** (rightFound, related)) =>
        (rightFiber ** (rightFound, related,
          pointwiseProviderCandidateSame nameEq keyEq wanted actor left right
            leftFiber rightFiber leftFound rightFound related effects))

0 providerInFromLocatedCandidate :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (actor : name) -> (fiber : Fiber name key value world error) ->
  Elem (Bind actor fiber) entries ->
  (isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable fiber))) = True ->
  (provider : name ** providerIn @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted entries =
    Just provider)
providerInFromLocatedCandidate nameEq keyEq wanted
  (Bind actor fiber :: rest) actor fiber Here candidate =
    rewrite candidate in (actor ** Refl)
providerInFromLocatedCandidate nameEq keyEq wanted
  (Bind current observed :: rest) actor fiber (There later) candidate
  with (isActive (fiberLifecycle observed) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable observed))) proof current
  providerInFromLocatedCandidate nameEq keyEq wanted
    (Bind current observed :: rest) actor fiber (There later) candidate | True =
      (current ** Refl)
  providerInFromLocatedCandidate nameEq keyEq wanted
    (Bind current observed :: rest) actor fiber (There later) candidate | False =
      case providerInFromLocatedCandidate nameEq keyEq wanted rest actor fiber
        later candidate of
        (provider ** found) => (provider ** found)

0 providerOfSoundCandidateTrue :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (provider : name) -> (fibers : Registry name key value world error) ->
  (sound : ProviderOfSound name key world error value nameEq keyEq wanted
    provider fibers) ->
  (isActive (fiberLifecycle (providerOfFiber sound)) &&
    memberKey @{keyEq} wanted
      (ownedValues (fiberTable (providerOfFiber sound)))) = True
providerOfSoundCandidateTrue nameEq keyEq wanted provider fibers sound =
  let 0 lookupSame :
        (valueFromProvider @{nameEq} @{keyEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} provider wanted fibers =
         lookupBinding @{keyEq} {key = key} {value = value} wanted
          (ownedValues (fiberTable (providerOfFiber sound))))
      lookupSame = rewrite providerOfLookup sound in Refl
      0 member : (memberKey @{keyEq} wanted
        (ownedValues (fiberTable (providerOfFiber sound))) = True)
      member = trans (sym (cong isJust lookupSame)) (providerOfValue sound)
  in boolAndBothPointwise _ _ (providerOfActive sound) member

record LocatedProviderCandidate
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (wanted : key) (actor : name)
  (fibers : Registry name key value world error) where
  constructor MkLocatedProviderCandidate
  providerCandidateFiber : Fiber name key value world error
  0 providerCandidateFound : lookupFiber @{nameEq} actor fibers =
    Just providerCandidateFiber
  0 providerCandidateEntry : Elem (Bind actor providerCandidateFiber)
    (bindings fibers)
  0 providerCandidateTrue :
    (isActive (fiberLifecycle providerCandidateFiber) &&
      memberKey @{keyEq} wanted
        (ownedValues (fiberTable providerCandidateFiber))) = True
  0 providerCandidateDeclares : Elem wanted (dependencies
    (componentProvisions (fiberComponent providerCandidateFiber)))

0 selectedProviderCandidate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (provider : name) -> (fibers : Registry name key value world error) ->
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted fibers = Just provider ->
  LocatedProviderCandidate name key world error value nameEq keyEq wanted
    provider fibers
selectedProviderCandidate nameEq keyEq wanted provider
  fibers@(MkCoeffectContext entries unique) selected =
    let sound = providerOfSound nameEq keyEq wanted provider fibers selected
        candidate = providerOfSoundCandidateTrue nameEq keyEq wanted provider
          fibers sound
        member = memberKeyTrueElemOpenAnchor keyEq wanted
          (ownedValues (fiberTable (providerOfFiber sound)))
          (boolAndRightPointwise _ _ candidate)
        entry = entryElemFromLookupPointwise nameEq provider
          (providerOfFiber sound) entries unique (providerOfLookup sound)
    in MkLocatedProviderCandidate (providerOfFiber sound)
      (providerOfLookup sound) entry candidate
      (ownedSound (fiberTable (providerOfFiber sound)) wanted member)

0 pointwiseTransportProviderCandidate :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor : name) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  LocatedProviderCandidate name key world error value nameEq keyEq wanted actor
    (registry left) ->
  LocatedProviderCandidate name key world error value nameEq keyEq wanted actor
    (registry right)
pointwiseTransportProviderCandidate nameEq keyEq wanted actor left
  right@(MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  controls effects candidate =
    case pointwiseProviderCandidateAtName nameEq keyEq wanted actor left right
      controls effects (providerCandidateFiber candidate)
      (providerCandidateFound candidate) of
      (rightFiber ** (rightFound, related, same)) =>
        let 0 targetTrue :
              ((isActive (fiberLifecycle rightFiber) &&
                memberKey @{keyEq} wanted
                  (ownedValues (fiberTable rightFiber))) = True)
            targetTrue = trans (sym same) (providerCandidateTrue candidate)
            0 targetEntry : Elem (Bind actor rightFiber) rightEntries
            targetEntry = entryElemFromLookupPointwise nameEq actor rightFiber
              rightEntries rightUnique rightFound
            0 member : Elem wanted
              (bindingKeys (bindings (ownedValues (fiberTable rightFiber))))
            member = memberKeyTrueElemOpenAnchor keyEq wanted
              (ownedValues (fiberTable rightFiber))
              (boolAndRightPointwise _ _ targetTrue)
        in MkLocatedProviderCandidate rightFiber rightFound targetEntry targetTrue
          (ownedSound (fiberTable rightFiber) wanted member)

0 boolNotAndTruePointwise :
  (observed : Bool) -> not observed = True -> observed = True -> Void
boolNotAndTruePointwise False notTrue observedTrue = case observedTrue of
  Refl impossible
boolNotAndTruePointwise True notTrue observedTrue = case notTrue of
  Refl impossible

0 elemDecFromElemPointwise : DecEq a =>
  (wanted : a) -> (values : List a) -> Elem wanted values ->
  elemDec wanted values = True
elemDecFromElemPointwise wanted (wanted :: rest) Here
  with (decEq wanted wanted)
  elemDecFromElemPointwise wanted (wanted :: rest) Here | Yes Refl = Refl
  elemDecFromElemPointwise wanted (wanted :: rest) Here | No contra =
    void (contra Refl)
elemDecFromElemPointwise wanted (current :: rest) (There later)
  with (decEq wanted current)
  elemDecFromElemPointwise current (current :: rest) (There later) |
    Yes Refl = Refl
  elemDecFromElemPointwise wanted (current :: rest) (There later) |
    No distinct = elemDecFromElemPointwise wanted rest later

0 foldlOrTruePointwise :
  (predicate : a -> Bool) -> (values : List a) ->
  foldl (\accepted, value => accepted || predicate value) True values = True
foldlOrTruePointwise predicate [] = Refl
foldlOrTruePointwise predicate (value :: rest) =
  foldlOrTruePointwise predicate rest

0 sharedAnyPointwise : DecEq key =>
  (wanted : key) -> (left, right : List key) ->
  Elem wanted left -> Elem wanted right ->
  any (\candidate => elemDec candidate right) left = True
sharedAnyPointwise wanted (wanted :: leftRest) right Here rightMember =
  rewrite elemDecFromElemPointwise wanted right rightMember in
    foldlOrTruePointwise (\candidate => elemDec candidate right) leftRest
sharedAnyPointwise wanted (current :: leftRest) right (There later) rightMember
  with (elemDec current right)
  sharedAnyPointwise wanted (current :: leftRest) right (There later)
    rightMember | True =
      foldlOrTruePointwise (\candidate => elemDec candidate right) leftRest
  sharedAnyPointwise wanted (current :: leftRest) right (There later)
    rightMember | False = sharedAnyPointwise wanted leftRest right later
      rightMember

0 sharedProvisionOverlapsPointwise :
  (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : CoeffectSpec key) ->
  Elem wanted (dependencies left) -> Elem wanted (dependencies right) ->
  provisionOverlap @{keyEq} left right = True
sharedProvisionOverlapsPointwise keyEq wanted
  (MkCoeffectSpec left leftUnique) (MkCoeffectSpec right rightUnique)
  leftMember rightMember = sharedAnyPointwise wanted left right leftMember
    rightMember

0 sharedProvisionRejectsDisjointPointwise :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) ->
  (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision entries = True ->
  Elem wanted (dependencies provision) ->
  (providerName : name) ->
  (providerFiber : Fiber name key value world error) ->
  Elem (Bind providerName providerFiber) entries ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent providerFiber))) -> Void
sharedProvisionRejectsDisjointPointwise keyEq wanted provision
  (Bind providerName providerFiber :: rest) disjoint provisionMember
  providerName providerFiber Here providerMember =
    let 0 headNotOverlap : (not (provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent providerFiber))) = True)
        headNotOverlap = boolAndLeftPointwise _ _ disjoint
        0 overlaps : (provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent providerFiber)) = True)
        overlaps = sharedProvisionOverlapsPointwise keyEq wanted provision
          (componentProvisions (fiberComponent providerFiber)) provisionMember
          providerMember
    in boolNotAndTruePointwise _ headNotOverlap overlaps
sharedProvisionRejectsDisjointPointwise keyEq wanted provision
  (Bind current currentFiber :: rest) disjoint provisionMember
  providerName providerFiber (There later) providerMember =
    sharedProvisionRejectsDisjointPointwise keyEq wanted provision rest
      (boolAndRightPointwise _ _ disjoint) provisionMember providerName
      providerFiber later providerMember

0 pairwiseSharedProvisionSameNamePointwise :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  pairwiseProvisionInvariant @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} entries = True ->
  (leftName, rightName : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  Elem (Bind leftName leftFiber) entries ->
  Elem (Bind rightName rightFiber) entries ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent leftFiber))) ->
  Elem wanted (dependencies
    (componentProvisions (fiberComponent rightFiber))) ->
  leftName = rightName
pairwiseSharedProvisionSameNamePointwise keyEq
  (Bind leftName leftFiber :: rest) pairwise leftName leftName leftFiber leftFiber
  Here Here wanted leftDeclares rightDeclares = Refl
pairwiseSharedProvisionSameNamePointwise keyEq
  (Bind leftName leftFiber :: rest) pairwise leftName rightName leftFiber rightFiber
  Here (There rightLater) wanted leftDeclares rightDeclares =
    void (sharedProvisionRejectsDisjointPointwise keyEq wanted
      (componentProvisions (fiberComponent leftFiber)) rest
      (boolAndLeftPointwise _ _ pairwise) leftDeclares rightName rightFiber
      rightLater rightDeclares)
pairwiseSharedProvisionSameNamePointwise keyEq
  (Bind rightName rightFiber :: rest) pairwise leftName rightName leftFiber
  rightFiber (There leftLater) Here wanted leftDeclares rightDeclares =
    void (sharedProvisionRejectsDisjointPointwise keyEq wanted
      (componentProvisions (fiberComponent rightFiber)) rest
      (boolAndLeftPointwise _ _ pairwise) rightDeclares leftName leftFiber
      leftLater leftDeclares)
pairwiseSharedProvisionSameNamePointwise keyEq
  (Bind current currentFiber :: rest) pairwise leftName rightName leftFiber
  rightFiber (There leftLater) (There rightLater) wanted leftDeclares
  rightDeclares = pairwiseSharedProvisionSameNamePointwise keyEq rest
    (boolAndRightPointwise _ _ pairwise) leftName rightName leftFiber rightFiber
    leftLater rightLater wanted leftDeclares rightDeclares

0 locatedProviderCandidateSelectsSome :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (actor : name) ->
  (fibers : Registry name key value world error) ->
  LocatedProviderCandidate name key world error value nameEq keyEq wanted actor
    fibers ->
  (provider : name ** providerOf @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted fibers = Just provider)
locatedProviderCandidateSelectsSome nameEq keyEq wanted actor
  (MkCoeffectContext entries unique) candidate =
    providerInFromLocatedCandidate nameEq keyEq wanted entries actor
      (providerCandidateFiber candidate) (providerCandidateEntry candidate)
      (providerCandidateTrue candidate)

0 locatedProviderCandidatesSameName :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (leftName, rightName : name) ->
  (fibers : Registry name key value world error) ->
  pairwiseProvisionInvariant @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (bindings fibers) = True ->
  LocatedProviderCandidate name key world error value nameEq keyEq wanted
    leftName fibers ->
  LocatedProviderCandidate name key world error value nameEq keyEq wanted
    rightName fibers ->
  leftName = rightName
locatedProviderCandidatesSameName nameEq keyEq wanted leftName rightName fibers pairwise
  leftCandidate rightCandidate = pairwiseSharedProvisionSameNamePointwise
    {name = name} {key = key} {world = world} {error = error} {value = value}
    keyEq (bindings fibers) pairwise leftName rightName
    (providerCandidateFiber leftCandidate)
    (providerCandidateFiber rightCandidate)
    (providerCandidateEntry leftCandidate)
    (providerCandidateEntry rightCandidate) wanted
    (providerCandidateDeclares leftCandidate)
    (providerCandidateDeclares rightCandidate)

0 pointwiseRegistryPairwise :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  pairwiseProvisionInvariant @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (bindings (registry state)) = True
pointwiseRegistryPairwise nameEq keyEq
  (MkSystemState ambient (MkCoeffectContext entries unique)) valid =
    boolAndLeftPointwise _ _
      (boolAndRightPointwise _ _
        (boolAndRightPointwise _ _ valid))

||| Runtime provider selection is invariant under pointwise control/effect
||| equivalence.  Candidate transport supplies existence in the independently
||| ordered registry; pairwise provision well-formedness fixes the selected name.
0 pointwiseProviderOfSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  registryWellFormed @{nameEq} @{keyEq} right = True ->
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted (registry left) =
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted (registry right)
pointwiseProviderOfSame nameEq keyEq wanted left right controls effects rightValid
  with (providerOf @{nameEq} @{keyEq} wanted (registry left)) proof leftSelected
  pointwiseProviderOfSame nameEq keyEq wanted left right controls effects
    rightValid | Nothing
    with (providerOf @{nameEq} @{keyEq} wanted (registry right)) proof rightSelected
    pointwiseProviderOfSame nameEq keyEq wanted left right controls effects
      rightValid | Nothing | Nothing = Refl
    pointwiseProviderOfSame nameEq keyEq wanted left right controls effects
      rightValid | Nothing | Just rightName =
        let rightCandidate = selectedProviderCandidate nameEq keyEq wanted
              rightName (registry right) rightSelected
            leftCandidate = pointwiseTransportProviderCandidate nameEq keyEq
              wanted rightName right left (controlEquivalentSymmetric controls)
              (effectStateRelatedSymmetric effects) rightCandidate
        in case locatedProviderCandidateSelectsSome nameEq keyEq wanted
          rightName (registry left) leftCandidate of
          (leftName ** leftSome) =>
            case trans (sym leftSelected) leftSome of Refl impossible
  pointwiseProviderOfSame nameEq keyEq wanted left right controls effects
    rightValid | Just leftName
    with (providerOf @{nameEq} @{keyEq} wanted (registry right)) proof rightSelected
    pointwiseProviderOfSame nameEq keyEq wanted left right controls effects
      rightValid | Just leftName | Nothing =
        let leftCandidate = selectedProviderCandidate nameEq keyEq wanted
              leftName (registry left) leftSelected
            rightCandidate = pointwiseTransportProviderCandidate nameEq keyEq
              wanted leftName left right controls effects leftCandidate
        in case locatedProviderCandidateSelectsSome nameEq keyEq wanted
          leftName (registry right) rightCandidate of
          (rightName ** rightSome) =>
            case trans (sym rightSelected) rightSome of Refl impossible
    pointwiseProviderOfSame nameEq keyEq wanted left right controls effects
      rightValid | Just leftName | Just rightName =
        let leftCandidate = selectedProviderCandidate nameEq keyEq wanted
              leftName (registry left) leftSelected
            transportedLeft = pointwiseTransportProviderCandidate nameEq keyEq
              wanted leftName left right controls effects leftCandidate
            selectedRight = selectedProviderCandidate nameEq keyEq wanted
              rightName (registry right) rightSelected
            sameName = locatedProviderCandidatesSameName nameEq keyEq wanted
              leftName rightName (registry right)
              (pointwiseRegistryPairwise nameEq keyEq right rightValid)
              transportedLeft selectedRight
        in cong Just sameName

||| Provider-name equality lifts structurally to exact dependency resolution.
||| This remains executable against independently ordered registries because
||| each selected provider is fixed by the provision invariant above.
0 pointwiseResolveViewSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (requested : List key) ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  registryWellFormed @{nameEq} @{keyEq} right = True ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} requested (registry left) =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} requested (registry right)
pointwiseResolveViewSame nameEq keyEq [] left right controls effects rightValid =
  Refl
pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls effects
  rightValid with (providerOf @{nameEq} @{keyEq} wanted (registry left))
    proof leftSelected
  pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls
    effects rightValid | Nothing
    with (providerOf @{nameEq} @{keyEq} wanted (registry right)) proof rightSelected
    pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls
      effects rightValid | Nothing | Nothing = Refl
    pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls
      effects rightValid | Nothing | Just rightName =
        let sameHead = pointwiseProviderOfSame nameEq keyEq wanted left right
              controls effects rightValid
        in case trans (sym leftSelected) (trans sameHead rightSelected) of
          Refl impossible
  pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls
    effects rightValid | Just leftName
    with (providerOf @{nameEq} @{keyEq} wanted (registry right)) proof rightSelected
    pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls
      effects rightValid | Just leftName | Nothing =
        let sameHead = pointwiseProviderOfSame nameEq keyEq wanted left right
              controls effects rightValid
        in case trans (sym leftSelected) (trans sameHead rightSelected) of
          Refl impossible
    pointwiseResolveViewSame nameEq keyEq (wanted :: rest) left right controls
      effects rightValid | Just leftName | Just rightName =
        let sameHead = pointwiseProviderOfSame nameEq keyEq wanted left right
              controls effects rightValid
            sameSelected = trans (sym leftSelected)
              (trans sameHead rightSelected)
        in case justInjective sameSelected of
          Refl => cong (map (ProviderView leftName))
            (pointwiseResolveViewSame nameEq keyEq rest left right controls
              effects rightValid)

||| Related owners share one component. Their retired flags are eliminated
||| before the target query is normalized: retired owners both yield `Nothing`,
||| and only unretired owners consult pointwise dependency resolution.
0 pointwiseConcreteTargetFiberSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (leftLifecycle, rightLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  leftRetired = rightRetired ->
  (left, right : SystemState name key value world error) ->
  ControlEquivalent name key world error value nameEq left right ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  registryWellFormed @{nameEq} @{keyEq} right = True ->
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (MkFiber component leftParent leftRetired leftTable leftLifecycle)
    (registry left) =
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (MkFiber component rightParent rightRetired rightTable rightLifecycle)
    (registry right)
pointwiseConcreteTargetFiberSame nameEq keyEq component leftParent rightParent
  True True leftTable rightTable leftLifecycle rightLifecycle Refl left right
  controls effects rightValid =
    let 0 leftExplicit = targetFiberExplicit {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq keyEq component
          leftParent True leftTable leftLifecycle (registry left)
        0 rightExplicit = targetFiberExplicit {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq keyEq component
          rightParent True rightTable rightLifecycle (registry right)
    in trans leftExplicit (sym rightExplicit)
pointwiseConcreteTargetFiberSame nameEq keyEq component leftParent rightParent
  False False leftTable rightTable leftLifecycle rightLifecycle Refl left right
  controls effects rightValid =
    let 0 leftExplicit = targetFiberExplicit {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq keyEq component
          leftParent False leftTable leftLifecycle (registry left)
        0 rightExplicit = targetFiberExplicit {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq keyEq component
          rightParent False rightTable rightLifecycle (registry right)
        0 resolveSame = pointwiseResolveViewSame nameEq keyEq
          (dependencies (componentDependencies component)) left right controls
          effects rightValid
    in trans leftExplicit (trans resolveSame (sym rightExplicit))
pointwiseConcreteTargetFiberSame nameEq keyEq component leftParent rightParent
  True False leftTable rightTable leftLifecycle rightLifecycle retiredSame left
  right controls effects rightValid = case retiredSame of Refl impossible
pointwiseConcreteTargetFiberSame nameEq keyEq component leftParent rightParent
  False True leftTable rightTable leftLifecycle rightLifecycle retiredSame left
  right controls effects rightValid = case retiredSame of Refl impossible

0 pointwiseControlAfterInsert :
  (nameEq : DecEq name) -> (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : lookupFiber @{nameEq} actor leftRegistry = Nothing) ->
  (rightAbsent : lookupFiber @{nameEq} actor rightRegistry = Nothing) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld
      (insertBinding @{nameEq} actor (freshFiber component parent) leftRegistry
        leftAbsent))
    (MkSystemState rightWorld
      (insertBinding @{nameEq} actor (freshFiber component parent) rightRegistry
        rightAbsent))
pointwiseControlAfterInsert nameEq actor parent component leftWorld rightWorld
  leftRegistry rightRegistry leftAbsent rightAbsent controls =
    MkControlEquivalent pointwise
  where
  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected
      (insertBinding @{nameEq} actor (freshFiber component parent) leftRegistry
        leftAbsent))
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected
      (insertBinding @{nameEq} actor (freshFiber component parent) rightRegistry
        rightAbsent))
  pointwise selected with (decEq @{nameEq} selected actor)
    pointwise selected | Yes same = case same of
      Refl =>
        rewrite lookupInserted actor (freshFiber component parent) leftRegistry
          leftAbsent in
        rewrite lookupInserted actor (freshFiber component parent) rightRegistry
          rightAbsent in
          SomeControlFibers (fiberControlReflexive (freshFiber component parent))
    pointwise selected | No distinct =
      rewrite lookupInsertOther selected actor distinct
        (freshFiber component parent) leftRegistry leftAbsent in
      rewrite lookupInsertOther selected actor distinct
        (freshFiber component parent) rightRegistry rightAbsent in
        controlPointwise controls selected

||| Replacing the same named owner with newly related control states preserves
||| pointwise control even when the two registries use different list orders.
0 pointwiseControlAfterReplace :
  (nameEq : DecEq name) -> (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  (leftFound : lookupFiber @{nameEq} actor leftRegistry = Just leftOld) ->
  (rightFound : lookupFiber @{nameEq} actor rightRegistry = Just rightOld) ->
  FiberControlRelated leftNext rightNext ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld
      (replaceBinding @{nameEq} actor leftNext leftRegistry))
    (MkSystemState rightWorld
      (replaceBinding @{nameEq} actor rightNext rightRegistry))
pointwiseControlAfterReplace nameEq actor leftWorld rightWorld leftRegistry
  rightRegistry leftOld rightOld leftNext rightNext leftFound rightFound
  nextRelated controls = MkControlEquivalent pointwise
  where
  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (lookupFiber @{nameEq} selected
      (replaceBinding @{nameEq} actor leftNext leftRegistry))
    (lookupFiber @{nameEq} selected
      (replaceBinding @{nameEq} actor rightNext rightRegistry))
  pointwise selected with (decEq @{nameEq} selected actor)
    pointwise selected | Yes same = case same of
      Refl => rewrite lookupReplacedFiber actor leftOld leftNext leftRegistry
        leftFound in
        rewrite lookupReplacedFiber actor rightOld rightNext rightRegistry
          rightFound in SomeControlFibers nextRelated
    pointwise selected | No distinct =
      rewrite lookupReplaceOther selected actor distinct leftNext leftRegistry in
      rewrite lookupReplaceOther selected actor distinct rightNext rightRegistry in
        controlPointwise controls selected

0 retireFiberControlRelated :
  FiberControlRelated left right ->
  FiberControlRelated (retireFiber left) (retireFiber right)
retireFiberControlRelated
  (FibersControlRelated {component} leftParent rightParent leftRetired
    rightRetired leftTable rightTable leftLifecycle rightLifecycle parentSame
    retiredSame lifecycleSame) =
      FibersControlRelated {component = component} leftParent rightParent True True
        leftTable rightTable leftLifecycle rightLifecycle parentSame Refl
        lifecycleSame

0 pointwiseControlAfterRetire :
  (nameEq : DecEq name) -> (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (leftFound : lookupFiber @{nameEq} actor leftRegistry = Just leftFiber) ->
  (rightFound : lookupFiber @{nameEq} actor rightRegistry = Just rightFiber) ->
  FiberControlRelated leftFiber rightFiber ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld
      (replaceBinding @{nameEq} actor (retireFiber leftFiber) leftRegistry))
    (MkSystemState rightWorld
      (replaceBinding @{nameEq} actor (retireFiber rightFiber) rightRegistry))
pointwiseControlAfterRetire nameEq actor leftWorld rightWorld leftRegistry
  rightRegistry leftFiber rightFiber leftFound rightFound fibersRelated controls =
    MkControlEquivalent pointwise
  where
  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (lookupFiber @{nameEq} selected
      (replaceBinding @{nameEq} actor (retireFiber leftFiber) leftRegistry))
    (lookupFiber @{nameEq} selected
      (replaceBinding @{nameEq} actor (retireFiber rightFiber) rightRegistry))
  pointwise selected with (decEq @{nameEq} selected actor)
    pointwise selected | Yes same = case same of
      Refl => rewrite lookupReplacedFiber actor leftFiber (retireFiber leftFiber)
        leftRegistry leftFound in
        rewrite lookupReplacedFiber actor rightFiber (retireFiber rightFiber)
          rightRegistry rightFound in
            SomeControlFibers (retireFiberControlRelated fibersRelated)
    pointwise selected | No distinct =
      rewrite lookupReplaceOther selected actor distinct (retireFiber leftFiber)
        leftRegistry in
      rewrite lookupReplaceOther selected actor distinct (retireFiber rightFiber)
        rightRegistry in controlPointwise controls selected

0 retireSourceIngredients :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor)
    (MkSystemState ambient source) = Just (ORetireTag, afterState) ->
  (oldFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor source = Just oldFiber,
     MkSystemState ambient
       (replaceBinding @{nameEq} actor (retireFiber oldFiber) source) =
       afterState))
retireSourceIngredients nameEq keyEq actor ambient source afterState raw =
  case retireSuccessView nameEq keyEq actor ambient source ORetireTag afterState
    raw of
    MkRetireSuccessView oldFiber found => (oldFiber ** (found, Refl))

0 retireEffectFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (ORetireTag, afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState)
retireEffectFrameRelated nameEq keyEq actor before afterState raw =
  case retireActualEffectFrame nameEq keyEq actor before afterState ORetireTag raw of
    MkActualEffectFrame (PartialDefined related) => related

||| Package an already-derived checked target head into the exact frozen
||| producer envelope.  Occurrence and relative-ordinal evidence is rebuilt here
||| from the owned source/target transitions, rather than accepted independently.
0 packagePointwiseRelationalHeadReplay :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceStep : Transition sourceBefore sourceAfter) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions sourceStep NoTransitions) ->
  (replayedAfter : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (0 targetChecked : checkedApplyAction @{nameEq} @{keyEq} action
    replayedBefore = Just (tag, replayedAfter)) ->
  transitionAction sourceStep = action ->
  transitionTag sourceStep = tag ->
  RelationalReplayCorrespondence name key world error value
    (MoreTransitions sourceStep NoTransitions)
    (MoreTransitions
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag targetChecked)
      NoTransitions) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (partialEffectMap sourceStep)
    (partialEffectMap
      (Fired {before = replayedBefore} {afterState = replayedAfter}
        nameEq keyEq action tag targetChecked)) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceAfter
    replayedAfter ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq sourceStep
    replayedBefore
packagePointwiseRelationalHeadReplay nameEq keyEq sourceStep sourceAligned
  replayedAfter action tag targetChecked sourceAction sourceTag rar mapPreserved
  endpoint =
    let replayedStep : Transition replayedBefore replayedAfter
        replayedStep = Fired nameEq keyEq action tag targetChecked
        0 sameAction : transitionAction replayedStep = transitionAction sourceStep
        sameAction = sym sourceAction
        0 sameTag : transitionTag replayedStep = transitionTag sourceStep
        sameTag = sym sourceTag
        0 replayedAligned : AlignedTransitions name key world error value nameEq
          keyEq (MoreTransitions replayedStep NoTransitions)
        replayedAligned = AlignedStep action tag targetChecked NoTransitions
          AlignedEnd
        0 occurrences : ActionRegistrationReplayCorrespondence name key world
          error value (MoreTransitions sourceStep NoTransitions)
          (MoreTransitions replayedStep NoTransitions)
        occurrences = singletonActionRegistrationReplay sourceStep replayedStep
          sameAction sameTag
        0 relativeOrdinal :
          {observed : Action name key value world error} ->
          (occurrence : LocatedActionOccurrence observed
            (MoreTransitions replayedStep NoTransitions)) ->
          locatedActionOrdinal occurrence = locatedActionOrdinal
            (replayActionOrigin occurrences occurrence)
        relativeOrdinal
          (MkLocatedActionOccurrence _ _ NoTransitions _ NoTransitions located
            Refl) = Refl
        relativeOrdinal
          (MkLocatedActionOccurrence _ _ (MoreTransitions head tail) located
            suffix actionSame decomposition) =
              void (singletonPrefixTooLong head tail located suffix replayedStep
                decomposition)
    in MkPointwiseRelationalHeadReplay replayedAfter replayedStep sameAction
      sameTag replayedAligned rar mapPreserved endpoint occurrences
      relativeOrdinal

||| The O-Insert actual frame specializes the generic checked transition frame
||| to the installed empty effect table. This is retained beside the pointwise
||| applicability lemmas for the next bounded O-Insert attempt.
0 insertEffectFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (OInsert actor parent component) before =
    Just (OInsertTag, afterState) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq} before))
    (projectEffectState @{nameEq} afterState)
insertEffectFrameRelated nameEq keyEq actor parent component before afterState
  checked = case actualTransitionEffectFrame nameEq keyEq
    (OInsert actor parent component) OInsertTag before afterState checked of
      MkActualEffectFrame (PartialDefined related) => related

0 nothingNotJustInsertPointwise : Nothing = Just value -> Void
nothingNotJustInsertPointwise Refl impossible

||| Unindexed source evidence for a successful checked O-Insert. Unlike the
||| imported indexed view, this result keeps the caller's `afterState` abstract
||| and carries the concrete endpoint equation as producer-owned evidence.
0 insertSourceIngredientsPointwise :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (OInsert actor parent component)
    (MkSystemState ambient source) = Just (OInsertTag, afterState) ->
  (absent : lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor source = Nothing **
    (parentPresent @{nameEq} {name = name} {key = key} {value = value}
       {world = world} {error = error} parent source &&
       provisionsDisjointFrom @{keyEq} {name = name} {key = key}
         {value = value} {world = world} {error = error}
         (componentProvisions component) (bindings source) = True,
     MkSystemState ambient
       (insertBinding @{nameEq} actor (freshFiber component parent) source
         absent) = afterState))
insertSourceIngredientsPointwise nameEq keyEq actor parent component ambient source
  afterState raw with (parentPresent @{nameEq} parent source &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (bindings source)) proof guards
  insertSourceIngredientsPointwise nameEq keyEq actor parent component ambient
    source afterState raw | False = void (nothingNotJustInsertPointwise raw)
  insertSourceIngredientsPointwise nameEq keyEq actor parent component ambient
    source afterState raw | True
    with (setFresh @{nameEq} actor (freshFiber component parent) source)
      proof inserted
    insertSourceIngredientsPointwise nameEq keyEq actor parent component ambient
      source afterState raw | True | Nothing =
        void (nothingNotJustInsertPointwise raw)
    insertSourceIngredientsPointwise nameEq keyEq actor parent component ambient
      source afterState raw | True | Just applied =
        case justInjective raw of
          Refl => rewrite setFreshAfter nameEq actor
            (freshFiber component parent) source applied inserted in
              (setFreshAbsent nameEq actor (freshFiber component parent) source
                applied inserted ** (Refl, Refl))

||| O-Remove installs the empty effect table at its actor. The checked actual
||| frame is independent of the still-open source guard normalizer.
0 removeEffectFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORemove actor) before =
    Just (ORemoveTag, afterState) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq} before))
    (projectEffectState @{nameEq} afterState)
removeEffectFrameRelated nameEq keyEq actor before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq (ORemove actor) ORemoveTag
    before afterState checked of
      MkActualEffectFrame (PartialDefined related) => related

||| Source-owned L-Begin decomposition.  Owner lookup is obtained before the
||| public plan view, so no local `with` refines the caller's raw endpoint.
0 beginSourceIngredientsPointwise :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState ambient source) = Just (LBeginTag, afterState) ->
  (oldFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor source = Just oldFiber,
     ForeignBeginPlanView name key world error value nameEq keyEq actor ambient
       source oldFiber LBeginTag afterState))
beginSourceIngredientsPointwise nameEq keyEq actor ambient source afterState raw =
  case lifecycleOwnerPresent nameEq keyEq (LBegin actor) Refl
    (MkSystemState ambient source) afterState LBeginTag raw of
    (oldFiber ** found) => (oldFiber ** (found,
      foreignBeginPlanView nameEq keyEq actor ambient source oldFiber found
        LBeginTag afterState raw))

||| L-Begin, L-Divert, and L-Leave are control-only replacements. Their checked
||| actual frames therefore relate the pre-state effect projection directly to
||| the exact operational endpoint.
0 beginEffectFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (LBeginTag, afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState)
beginEffectFrameRelated nameEq keyEq actor before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq (LBegin actor) LBeginTag before
    afterState checked of
      MkActualEffectFrame (PartialDefined related) => related

0 divertEffectFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (LDivert actor) before =
    Just (LDivertTag, afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState)
divertEffectFrameRelated nameEq keyEq actor before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq (LDivert actor) LDivertTag before
    afterState checked of
      MkActualEffectFrame (PartialDefined related) => related

0 leaveEffectFrameRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (LLeave actor) before =
    Just (LLeaveTag, afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState)
leaveEffectFrameRelated nameEq keyEq actor before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq (LLeave actor) LLeaveTag before
    afterState checked of
      MkActualEffectFrame (PartialDefined related) => related

||| Complete pointwise L-Begin head. The source plan view fixes the exact clean
||| owner; provider resolution is rebuilt against the independently ordered
||| target registry before both owners enter the same reloading program/view.
0 replayPointwiseBeginHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor)
    sourceBefore = Just (LBeginTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceBefore
    replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq (LBegin actor) LBeginTag sourceChecked)
    replayedBefore
replayPointwiseBeginHead nameEq keyEq actor
  {sourceBefore = MkSystemState sourceWorld sourceRegistry}
  {sourceAfter} {replayedBefore = MkSystemState replayedWorld replayedRegistry}
  sourceChecked sourceWellFormed beforeEndpoint =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (LBegin actor)
          sourceState = Just (LBeginTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (LBegin actor) sourceState
          sourceAfter LBeginTag sourceChecked
    in case beginSourceIngredientsPointwise nameEq keyEq actor sourceWorld
      sourceRegistry sourceAfter sourceRaw of
      (sourceFiber ** (sourceFound, sourceView)) => case sourceView of
        MkForeignBeginPlanView {component} {parent = sourceParent}
          {table = sourceTable} view ownerShape sourceTarget tagShape afterShape =>
            case ownerShape of
              Refl => case pointwiseControlLookupFound nameEq actor sourceState
                replayedState (replayedControls beforeEndpoint)
                (MkFiber component sourceParent False sourceTable
                  (Inactive Nothing)) sourceFound of
                (replayedFiber ** (replayedFound, fibersRelated)) =>
                  let 0 outerRightShape =
                        fiberControlRelatedRightIsRight fibersRelated
                  in case fibersRelated of
                    FibersControlRelated sourceParent replayedParent False
                      replayedRetired sourceTable replayedTable
                      (Inactive Nothing) replayedLifecycle parentSame retiredSame
                      lifecycleSame => case retiredSame of
                        Refl => case lifecycleSame of
                          InactiveControls outcomeSame => case outcomeSame of
                            Refl =>
                              let sourceOwner : Fiber name key value world error
                                  sourceOwner = MkFiber component sourceParent False
                                    sourceTable (Inactive Nothing)
                                  replayedOwner : Fiber name key value world error
                                  replayedOwner = MkFiber component replayedParent
                                    False replayedTable (Inactive Nothing)
                                  0 exactReplayedFound : lookupFiber @{nameEq}
                                    actor replayedRegistry = Just replayedOwner
                                  exactReplayedFound = trans replayedFound
                                    (cong Just (sym outerRightShape))
                                  0 sourceExplicit : targetFiber @{nameEq} @{keyEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error}
                                    sourceOwner sourceRegistry =
                                    resolveView @{nameEq} @{keyEq} {name = name}
                                      {key = key} {value = value} {world = world}
                                      {error = error} (dependencies
                                        (componentDependencies component))
                                      sourceRegistry
                                  sourceExplicit = targetFiberExplicit
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} nameEq keyEq
                                    component sourceParent False sourceTable
                                    (Inactive Nothing) sourceRegistry
                                  0 sourceResolve : resolveView @{nameEq} @{keyEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} (dependencies
                                      (componentDependencies component))
                                    sourceRegistry = Just view
                                  sourceResolve = trans (sym sourceExplicit)
                                    sourceTarget
                                  0 resolveSame : resolveView @{nameEq} @{keyEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} (dependencies
                                      (componentDependencies component))
                                    sourceRegistry = resolveView @{nameEq} @{keyEq}
                                      {name = name} {key = key} {value = value}
                                      {world = world} {error = error} (dependencies
                                        (componentDependencies component))
                                      replayedRegistry
                                  resolveSame = pointwiseResolveViewSame nameEq
                                    keyEq (dependencies
                                      (componentDependencies component))
                                    sourceState replayedState
                                    (replayedControls beforeEndpoint)
                                    (replayedEffects beforeEndpoint)
                                    (replayedWellFormed beforeEndpoint)
                                  0 replayedResolve : resolveView @{nameEq} @{keyEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} (dependencies
                                      (componentDependencies component))
                                    replayedRegistry = Just view
                                  replayedResolve = trans (sym resolveSame)
                                    sourceResolve
                                  0 replayedExplicit : targetFiber @{nameEq}
                                    @{keyEq} {name = name} {key = key}
                                    {value = value} {world = world} {error = error}
                                    replayedOwner replayedRegistry =
                                    resolveView @{nameEq} @{keyEq} {name = name}
                                      {key = key} {value = value} {world = world}
                                      {error = error} (dependencies
                                        (componentDependencies component))
                                      replayedRegistry
                                  replayedExplicit = targetFiberExplicit
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} nameEq keyEq
                                    component replayedParent False replayedTable
                                    (Inactive Nothing) replayedRegistry
                                  0 replayedTarget : targetFiber @{nameEq} @{keyEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error}
                                    replayedOwner replayedRegistry = Just view
                                  replayedTarget = trans replayedExplicit
                                    replayedResolve
                                  sourceNext : Fiber name key value world error
                                  sourceNext = MkFiber component sourceParent False
                                    sourceTable
                                    (Reloading (componentProgram component)
                                      (\local => local) view)
                                  replayedNext : Fiber name key value world error
                                  replayedNext = MkFiber component replayedParent
                                    False replayedTable
                                    (Reloading (componentProgram component)
                                      (\local => local) view)
                                  0 nextOwnerRelated : FiberControlRelated
                                    sourceNext replayedNext
                                  nextOwnerRelated = FibersControlRelated
                                    sourceParent replayedParent False False
                                    sourceTable replayedTable
                                    (Reloading (componentProgram component)
                                      (\local => local) view)
                                    (Reloading (componentProgram component)
                                      (\local => local) view)
                                    parentSame Refl
                                    (beginLifecycleControlRelated
                                      (componentProgram component) view)
                                  targetState : SystemState name key value world
                                    error
                                  targetState = MkSystemState replayedWorld
                                    (replaceBinding @{nameEq} actor replayedNext
                                      replayedRegistry)
                                  0 targetRaw : applyAction @{nameEq} @{keyEq}
                                    (LBegin actor) replayedState =
                                    Just (LBeginTag, targetState)
                                  targetRaw = rewrite exactReplayedFound in
                                    rewrite replayedTarget in Refl
                                  0 targetWellFormed : registryWellFormed
                                    @{nameEq} @{keyEq} targetState = True
                                  targetWellFormed = preservationTheoremProof
                                    nameEq keyEq (LBegin actor) replayedState
                                    targetState LBeginTag
                                    (replayedWellFormed beforeEndpoint) targetRaw
                                  0 targetChecked : checkedApplyAction @{nameEq}
                                    @{keyEq} (LBegin actor) replayedState =
                                    Just (LBeginTag, targetState)
                                  targetChecked = rewrite targetRaw in
                                    rewrite targetWellFormed in Refl
                                  0 sourceFrame : EffectStateRelated keyEq
                                    (projectEffectState @{nameEq} sourceState)
                                    (projectEffectState @{nameEq} sourceAfter)
                                  sourceFrame = beginEffectFrameRelated nameEq
                                    keyEq actor sourceState sourceAfter
                                    sourceChecked
                                  0 targetFrame : EffectStateRelated keyEq
                                    (projectEffectState @{nameEq} replayedState)
                                    (projectEffectState @{nameEq} targetState)
                                  targetFrame = beginEffectFrameRelated nameEq
                                    keyEq actor replayedState targetState
                                    targetChecked
                                  0 nextEffects : EffectStateRelated keyEq
                                    (projectEffectState @{nameEq} sourceAfter)
                                    (projectEffectState @{nameEq} targetState)
                                  nextEffects = effectStateRelatedTransitive
                                    (effectStateRelatedSymmetric sourceFrame)
                                    (effectStateRelatedTransitive
                                      (replayedEffects beforeEndpoint) targetFrame)
                                  0 nextControlsConcrete : ControlEquivalent name
                                    key world error value nameEq
                                    (MkSystemState sourceWorld
                                      (replaceBinding @{nameEq} actor sourceNext
                                        sourceRegistry)) targetState
                                  nextControlsConcrete =
                                    pointwiseControlAfterReplace nameEq actor
                                      sourceWorld replayedWorld sourceRegistry
                                      replayedRegistry sourceOwner replayedOwner
                                      sourceNext replayedNext sourceFound
                                      exactReplayedFound nextOwnerRelated
                                      (replayedControls beforeEndpoint)
                                  0 nextControls : ControlEquivalent name key
                                    world error value nameEq sourceAfter
                                    targetState
                                  nextControls = replace
                                    {p = \observed => ControlEquivalent name key
                                      world error value nameEq observed targetState}
                                    afterShape nextControlsConcrete
                                  sourceStep : Transition sourceState sourceAfter
                                  sourceStep = Fired nameEq keyEq (LBegin actor)
                                    LBeginTag sourceChecked
                                  replayedStep : Transition replayedState
                                    targetState
                                  replayedStep = Fired nameEq keyEq (LBegin actor)
                                    LBeginTag targetChecked
                                  0 mapPreserved :
                                    (state : EffectState name key value world) ->
                                    partialEffectMap sourceStep state =
                                      partialEffectMap replayedStep state
                                  mapPreserved state = Refl
                                  0 mapsRelated : PartialMapsRelated
                                    (EffectStateEquivalence keyEq) (partialEffectMap sourceStep)
                                    (partialEffectMap replayedStep)
                                  mapsRelated = replayExactTransitionMapsRelated keyEq sourceStep
                                    replayedStep mapPreserved
                                  0 notAdvance : (selected : name) -> Not
                                    (the (Action name key value world error)
                                      (LBegin actor) = LAdvance selected)
                                  notAdvance selected Refl impossible
                                  0 rar : RelationalReplayCorrespondence name key
                                    world error value
                                    (MoreTransitions sourceStep NoTransitions)
                                    (MoreTransitions replayedStep NoTransitions)
                                  rar = singletonNonAdvanceRAR nameEq keyEq
                                    (LBegin actor) LBeginTag sourceState
                                    sourceAfter replayedState targetState
                                    sourceChecked targetChecked notAdvance
                                    mapsRelated
                                  0 nextEndpoint : RelationalReplayEndpoint name
                                    key world error value nameEq keyEq sourceAfter
                                    targetState
                                  nextEndpoint = MkRelationalReplayEndpoint
                                    nextEffects nextControls targetWellFormed
                                  sourceAligned : AlignedTransitions name key
                                    world error value nameEq keyEq
                                    (MoreTransitions sourceStep NoTransitions)
                                  sourceAligned = AlignedStep (LBegin actor)
                                    LBeginTag sourceChecked NoTransitions AlignedEnd
                              in packagePointwiseRelationalHeadReplay nameEq keyEq
                                sourceStep sourceAligned targetState
                                (LBegin actor) LBeginTag targetChecked Refl Refl
                                rar mapsRelated nextEndpoint

||| Complete pointwise L-Divert head. The target owner keeps its native
||| remaining program, accumulator, and view indices; only the comparison view
||| is transported after the target query itself has been related.
0 replayPointwiseDivertHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (LDivert actor)
    sourceBefore = Just (LDivertTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceBefore
    replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq (LDivert actor) LDivertTag sourceChecked)
    replayedBefore
replayPointwiseDivertHead nameEq keyEq actor
  {sourceBefore = MkSystemState sourceWorld sourceRegistry}
  {sourceAfter} {replayedBefore = MkSystemState replayedWorld replayedRegistry}
  sourceChecked sourceWellFormed beforeEndpoint =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (LDivert actor)
          sourceState = Just (LDivertTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (LDivert actor) sourceState
          sourceAfter LDivertTag sourceChecked
    in case foreignDivertPlanView nameEq keyEq actor sourceWorld sourceRegistry
      LDivertTag sourceAfter sourceRaw of
      MkLocatedForeignDivertPlanView observedOwner sourceFound planView =>
        case foreignDivertReplayData planView of
          MkForeignDivertReplayData component sourceParent sourceRetired
            sourceTable remaining sourceAccumulator sourceView ownerShape
            sourceMismatch observedTag observedAfter => case ownerShape of
              Refl =>
                case pointwiseControlLookupFound nameEq actor sourceState replayedState
                  (replayedControls beforeEndpoint) observedOwner sourceFound of
                  (replayedOwner ** (replayedFound, fibersRelated)) =>
                    let 0 outerRightShape =
                          fiberControlRelatedRightIsRight fibersRelated
                    in case fibersRelated of
                      FibersControlRelated sourceParent replayedParent sourceRetired
                        replayedRetired sourceTable replayedTable
                        (Reloading remaining sourceAccumulator sourceView)
                        replayedLifecycle parentSame retiredSame lifecycleSame =>
                          case reloadingRightControls lifecycleSame of
                            MkReloadingRightControls replayedRemaining
                              replayedAccumulator replayedView replayedLifecycleShape
                              remainingSame accumulatorsSame viewsSame =>
                                case replayedLifecycleShape of
                                  Refl =>
                                    let sourceOwner : Fiber name key value world error
                                        sourceOwner = MkFiber component sourceParent
                                          sourceRetired sourceTable
                                          (Reloading remaining sourceAccumulator
                                            sourceView)
                                        replayedOwner : Fiber name key value world error
                                        replayedOwner = MkFiber component replayedParent
                                          replayedRetired replayedTable
                                          (Reloading replayedRemaining
                                            replayedAccumulator replayedView)
                                        0 exactReplayedFound : lookupFiber @{nameEq}
                                          actor replayedRegistry = Just replayedOwner
                                        exactReplayedFound = trans replayedFound
                                          (cong Just (sym outerRightShape))
                                        0 targetsSame : targetFiber @{nameEq} @{keyEq}
                                          {name = name} {key = key} {value = value}
                                          {world = world} {error = error}
                                          sourceOwner sourceRegistry =
                                          targetFiber @{nameEq} @{keyEq}
                                            {name = name} {key = key} {value = value}
                                            {world = world} {error = error}
                                            replayedOwner replayedRegistry
                                        targetsSame = pointwiseConcreteTargetFiberSame
                                          nameEq keyEq component sourceParent
                                          replayedParent sourceRetired replayedRetired
                                          sourceTable replayedTable
                                          (Reloading remaining sourceAccumulator
                                            sourceView)
                                          (Reloading replayedRemaining
                                            replayedAccumulator replayedView)
                                          retiredSame sourceState replayedState
                                          (replayedControls beforeEndpoint)
                                          (replayedEffects beforeEndpoint)
                                          (replayedWellFormed beforeEndpoint)
                                        0 replayedMismatchSourceView : targetMatches
                                          @{nameEq} (targetFiber @{nameEq} @{keyEq}
                                            replayedOwner replayedRegistry)
                                          sourceView = False
                                        replayedMismatchSourceView = trans
                                          (cong (\target => targetMatches @{nameEq}
                                            target sourceView) (sym targetsSame))
                                          sourceMismatch
                                        0 replayedMismatch : targetMatches @{nameEq}
                                          (targetFiber @{nameEq} @{keyEq}
                                            replayedOwner replayedRegistry)
                                          replayedView = False
                                        replayedMismatch = trans
                                          (sym (cong (targetMatches @{nameEq}
                                            (targetFiber @{nameEq} @{keyEq}
                                              replayedOwner replayedRegistry))
                                            viewsSame)) replayedMismatchSourceView
                                        sourceNext : Fiber name key value world error
                                        sourceNext = MkFiber component sourceParent
                                          sourceRetired sourceTable
                                          (Unloading sourceAccumulator sourceView
                                            Nothing)
                                        replayedNext : Fiber name key value world error
                                        replayedNext = MkFiber component replayedParent
                                          replayedRetired replayedTable
                                          (Unloading replayedAccumulator replayedView
                                            Nothing)
                                        0 nextLifecycleRelated :
                                          LifecycleControlRelated
                                            (Unloading sourceAccumulator sourceView
                                              Nothing)
                                            (Unloading replayedAccumulator replayedView
                                              Nothing)
                                        nextLifecycleRelated =
                                          divertLifecycleControlRelated lifecycleSame
                                        0 nextOwnerRelated : FiberControlRelated
                                          sourceNext replayedNext
                                        nextOwnerRelated = FibersControlRelated
                                          sourceParent replayedParent sourceRetired
                                          replayedRetired sourceTable replayedTable
                                          (Unloading sourceAccumulator sourceView
                                            Nothing)
                                          (Unloading replayedAccumulator replayedView
                                            Nothing)
                                          parentSame retiredSame nextLifecycleRelated
                                        targetState : SystemState name key value world
                                          error
                                        targetState = MkSystemState replayedWorld
                                          (replaceBinding @{nameEq} actor replayedNext
                                            replayedRegistry)
                                        0 targetRaw : applyAction @{nameEq} @{keyEq}
                                          (LDivert actor) replayedState =
                                          Just (LDivertTag, targetState)
                                        targetRaw = rewrite exactReplayedFound in
                                          rewrite replayedMismatch in Refl
                                        0 targetWellFormed : registryWellFormed
                                          @{nameEq} @{keyEq} targetState = True
                                        targetWellFormed = preservationTheoremProof
                                          nameEq keyEq (LDivert actor) replayedState
                                          targetState LDivertTag
                                          (replayedWellFormed beforeEndpoint) targetRaw
                                        0 targetChecked : checkedApplyAction @{nameEq}
                                          @{keyEq} (LDivert actor) replayedState =
                                          Just (LDivertTag, targetState)
                                        targetChecked = rewrite targetRaw in
                                          rewrite targetWellFormed in Refl
                                        0 sourceFrame : EffectStateRelated keyEq
                                          (projectEffectState @{nameEq} sourceState)
                                          (projectEffectState @{nameEq} sourceAfter)
                                        sourceFrame = divertEffectFrameRelated nameEq
                                          keyEq actor sourceState sourceAfter
                                          sourceChecked
                                        0 targetFrame : EffectStateRelated keyEq
                                          (projectEffectState @{nameEq} replayedState)
                                          (projectEffectState @{nameEq} targetState)
                                        targetFrame = divertEffectFrameRelated nameEq
                                          keyEq actor replayedState targetState
                                          targetChecked
                                        0 nextEffects : EffectStateRelated keyEq
                                          (projectEffectState @{nameEq} sourceAfter)
                                          (projectEffectState @{nameEq} targetState)
                                        nextEffects = effectStateRelatedTransitive
                                          (effectStateRelatedSymmetric sourceFrame)
                                          (effectStateRelatedTransitive
                                            (replayedEffects beforeEndpoint) targetFrame)
                                        0 sourceAfterShape : MkSystemState sourceWorld
                                          (replaceBinding @{nameEq} actor sourceNext
                                            sourceRegistry) = sourceAfter
                                        sourceAfterShape = observedAfter
                                        0 nextControlsConcrete : ControlEquivalent name
                                          key world error value nameEq
                                          (MkSystemState sourceWorld
                                            (replaceBinding @{nameEq} actor sourceNext
                                              sourceRegistry)) targetState
                                        nextControlsConcrete =
                                          pointwiseControlAfterReplace nameEq actor
                                            sourceWorld replayedWorld sourceRegistry
                                            replayedRegistry sourceOwner replayedOwner
                                            sourceNext replayedNext sourceFound
                                            exactReplayedFound nextOwnerRelated
                                            (replayedControls beforeEndpoint)
                                        0 nextControls : ControlEquivalent name key
                                          world error value nameEq sourceAfter
                                          targetState
                                        nextControls = replace
                                          {p = \observed => ControlEquivalent name key
                                            world error value nameEq observed targetState}
                                          sourceAfterShape nextControlsConcrete
                                        sourceStep : Transition sourceState sourceAfter
                                        sourceStep = Fired nameEq keyEq (LDivert actor)
                                          LDivertTag sourceChecked
                                        replayedStep : Transition replayedState
                                          targetState
                                        replayedStep = Fired nameEq keyEq (LDivert actor)
                                          LDivertTag targetChecked
                                        0 mapPreserved :
                                          (state : EffectState name key value world) ->
                                          partialEffectMap sourceStep state =
                                            partialEffectMap replayedStep state
                                        mapPreserved state = Refl
                                        0 mapsRelated : PartialMapsRelated
                                          (EffectStateEquivalence keyEq) (partialEffectMap sourceStep)
                                          (partialEffectMap replayedStep)
                                        mapsRelated = replayExactTransitionMapsRelated keyEq sourceStep
                                          replayedStep mapPreserved
                                        0 notAdvance : (selected : name) -> Not
                                          (the (Action name key value world error)
                                            (LDivert actor) = LAdvance selected)
                                        notAdvance selected Refl impossible
                                        0 rar : RelationalReplayCorrespondence name key
                                          world error value
                                          (MoreTransitions sourceStep NoTransitions)
                                          (MoreTransitions replayedStep NoTransitions)
                                        rar = singletonNonAdvanceRAR nameEq keyEq
                                          (LDivert actor) LDivertTag sourceState
                                          sourceAfter replayedState targetState
                                          sourceChecked targetChecked notAdvance
                                          mapsRelated
                                        0 nextEndpoint : RelationalReplayEndpoint name
                                          key world error value nameEq keyEq sourceAfter
                                          targetState
                                        nextEndpoint = MkRelationalReplayEndpoint
                                          nextEffects nextControls targetWellFormed
                                        sourceAligned : AlignedTransitions name key
                                          world error value nameEq keyEq
                                          (MoreTransitions sourceStep NoTransitions)
                                        sourceAligned = AlignedStep (LDivert actor)
                                          LDivertTag sourceChecked NoTransitions
                                          AlignedEnd
                                    in packagePointwiseRelationalHeadReplay nameEq keyEq
                                      sourceStep sourceAligned targetState
                                      (LDivert actor) LDivertTag targetChecked Refl Refl
                                      rar mapsRelated nextEndpoint

||| Complete pointwise L-Leave head. The related target keeps its native
||| accumulator and view indices; only the mismatch comparison view is
||| transported after the target query itself has been related.
0 replayPointwiseLeaveHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (LLeave actor)
    sourceBefore = Just (LLeaveTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceBefore
    replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq (LLeave actor) LLeaveTag sourceChecked)
    replayedBefore
replayPointwiseLeaveHead nameEq keyEq actor
  {sourceBefore = MkSystemState sourceWorld sourceRegistry}
  {sourceAfter} {replayedBefore = MkSystemState replayedWorld replayedRegistry}
  sourceChecked sourceWellFormed beforeEndpoint =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (LLeave actor)
          sourceState = Just (LLeaveTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (LLeave actor) sourceState
          sourceAfter LLeaveTag sourceChecked
    in case foreignLeavePlanView nameEq keyEq actor sourceWorld sourceRegistry
      LLeaveTag sourceAfter sourceRaw of
      MkLocatedForeignLeavePlanView observedOwner sourceFound planView =>
        case foreignLeaveReplayData planView of
          MkForeignLeaveReplayData component sourceParent sourceRetired
            sourceTable sourceAccumulator sourceView ownerShape
            sourceMismatch observedTag observedAfter => case ownerShape of
              Refl =>
                case pointwiseControlLookupFound nameEq actor sourceState replayedState
                  (replayedControls beforeEndpoint) observedOwner sourceFound of
                  (replayedOwner ** (replayedFound, fibersRelated)) =>
                    let 0 outerRightShape =
                          fiberControlRelatedRightIsRight fibersRelated
                    in case fibersRelated of
                      FibersControlRelated sourceParent replayedParent sourceRetired
                        replayedRetired sourceTable replayedTable
                        (Active sourceAccumulator sourceView)
                        replayedLifecycle parentSame retiredSame lifecycleSame =>
                          case activeRightControls lifecycleSame of
                            MkActiveRightControls replayedAccumulator replayedView
                              replayedLifecycleShape accumulatorsSame viewsSame =>
                                case replayedLifecycleShape of
                                  Refl =>
                                    let sourceOwner : Fiber name key value world error
                                        sourceOwner = MkFiber component sourceParent
                                          sourceRetired sourceTable
                                          (Active sourceAccumulator sourceView)
                                        replayedOwner : Fiber name key value world error
                                        replayedOwner = MkFiber component replayedParent
                                          replayedRetired replayedTable
                                          (Active replayedAccumulator replayedView)
                                        0 exactReplayedFound : lookupFiber @{nameEq}
                                          actor replayedRegistry = Just replayedOwner
                                        exactReplayedFound = trans replayedFound
                                          (cong Just (sym outerRightShape))
                                        0 targetsSame : targetFiber @{nameEq} @{keyEq}
                                          {name = name} {key = key} {value = value}
                                          {world = world} {error = error}
                                          sourceOwner sourceRegistry =
                                          targetFiber @{nameEq} @{keyEq}
                                            {name = name} {key = key} {value = value}
                                            {world = world} {error = error}
                                            replayedOwner replayedRegistry
                                        targetsSame = pointwiseConcreteTargetFiberSame
                                          nameEq keyEq component sourceParent
                                          replayedParent sourceRetired replayedRetired
                                          sourceTable replayedTable
                                          (Active sourceAccumulator sourceView)
                                          (Active replayedAccumulator replayedView)
                                          retiredSame sourceState replayedState
                                          (replayedControls beforeEndpoint)
                                          (replayedEffects beforeEndpoint)
                                          (replayedWellFormed beforeEndpoint)
                                        0 replayedMismatchSourceView : targetMatches
                                          @{nameEq} (targetFiber @{nameEq} @{keyEq}
                                            replayedOwner replayedRegistry)
                                          sourceView = False
                                        replayedMismatchSourceView = trans
                                          (cong (\target => targetMatches @{nameEq}
                                            target sourceView) (sym targetsSame))
                                          sourceMismatch
                                        0 replayedMismatch : targetMatches @{nameEq}
                                          (targetFiber @{nameEq} @{keyEq}
                                            replayedOwner replayedRegistry)
                                          replayedView = False
                                        replayedMismatch = trans
                                          (sym (cong (targetMatches @{nameEq}
                                            (targetFiber @{nameEq} @{keyEq}
                                              replayedOwner replayedRegistry))
                                            viewsSame)) replayedMismatchSourceView
                                        sourceNext : Fiber name key value world error
                                        sourceNext = MkFiber component sourceParent
                                          sourceRetired sourceTable
                                          (Unloading sourceAccumulator sourceView
                                            Nothing)
                                        replayedNext : Fiber name key value world error
                                        replayedNext = MkFiber component replayedParent
                                          replayedRetired replayedTable
                                          (Unloading replayedAccumulator replayedView
                                            Nothing)
                                        0 nextLifecycleRelated :
                                          LifecycleControlRelated
                                            (Unloading sourceAccumulator sourceView
                                              Nothing)
                                            (Unloading replayedAccumulator replayedView
                                              Nothing)
                                        nextLifecycleRelated =
                                          leaveLifecycleControlRelated lifecycleSame
                                        0 nextOwnerRelated : FiberControlRelated
                                          sourceNext replayedNext
                                        nextOwnerRelated = FibersControlRelated
                                          sourceParent replayedParent sourceRetired
                                          replayedRetired sourceTable replayedTable
                                          (Unloading sourceAccumulator sourceView
                                            Nothing)
                                          (Unloading replayedAccumulator replayedView
                                            Nothing)
                                          parentSame retiredSame nextLifecycleRelated
                                        targetState : SystemState name key value world
                                          error
                                        targetState = MkSystemState replayedWorld
                                          (replaceBinding @{nameEq} actor replayedNext
                                            replayedRegistry)
                                        0 targetRaw : applyAction @{nameEq} @{keyEq}
                                          (LLeave actor) replayedState =
                                          Just (LLeaveTag, targetState)
                                        targetRaw = rewrite exactReplayedFound in
                                          rewrite replayedMismatch in Refl
                                        0 targetWellFormed : registryWellFormed
                                          @{nameEq} @{keyEq} targetState = True
                                        targetWellFormed = preservationTheoremProof
                                          nameEq keyEq (LLeave actor) replayedState
                                          targetState LLeaveTag
                                          (replayedWellFormed beforeEndpoint) targetRaw
                                        0 targetChecked : checkedApplyAction @{nameEq}
                                          @{keyEq} (LLeave actor) replayedState =
                                          Just (LLeaveTag, targetState)
                                        targetChecked = rewrite targetRaw in
                                          rewrite targetWellFormed in Refl
                                        0 sourceFrame : EffectStateRelated keyEq
                                          (projectEffectState @{nameEq} sourceState)
                                          (projectEffectState @{nameEq} sourceAfter)
                                        sourceFrame = leaveEffectFrameRelated nameEq
                                          keyEq actor sourceState sourceAfter
                                          sourceChecked
                                        0 targetFrame : EffectStateRelated keyEq
                                          (projectEffectState @{nameEq} replayedState)
                                          (projectEffectState @{nameEq} targetState)
                                        targetFrame = leaveEffectFrameRelated nameEq
                                          keyEq actor replayedState targetState
                                          targetChecked
                                        0 nextEffects : EffectStateRelated keyEq
                                          (projectEffectState @{nameEq} sourceAfter)
                                          (projectEffectState @{nameEq} targetState)
                                        nextEffects = effectStateRelatedTransitive
                                          (effectStateRelatedSymmetric sourceFrame)
                                          (effectStateRelatedTransitive
                                            (replayedEffects beforeEndpoint) targetFrame)
                                        0 sourceAfterShape : MkSystemState sourceWorld
                                          (replaceBinding @{nameEq} actor sourceNext
                                            sourceRegistry) = sourceAfter
                                        sourceAfterShape = observedAfter
                                        0 nextControlsConcrete : ControlEquivalent name
                                          key world error value nameEq
                                          (MkSystemState sourceWorld
                                            (replaceBinding @{nameEq} actor sourceNext
                                              sourceRegistry)) targetState
                                        nextControlsConcrete =
                                          pointwiseControlAfterReplace nameEq actor
                                            sourceWorld replayedWorld sourceRegistry
                                            replayedRegistry sourceOwner replayedOwner
                                            sourceNext replayedNext sourceFound
                                            exactReplayedFound nextOwnerRelated
                                            (replayedControls beforeEndpoint)
                                        0 nextControls : ControlEquivalent name key
                                          world error value nameEq sourceAfter
                                          targetState
                                        nextControls = replace
                                          {p = \observed => ControlEquivalent name key
                                            world error value nameEq observed targetState}
                                          sourceAfterShape nextControlsConcrete
                                        sourceStep : Transition sourceState sourceAfter
                                        sourceStep = Fired nameEq keyEq (LLeave actor)
                                          LLeaveTag sourceChecked
                                        replayedStep : Transition replayedState
                                          targetState
                                        replayedStep = Fired nameEq keyEq (LLeave actor)
                                          LLeaveTag targetChecked
                                        0 mapPreserved :
                                          (state : EffectState name key value world) ->
                                          partialEffectMap sourceStep state =
                                            partialEffectMap replayedStep state
                                        mapPreserved state = Refl
                                        0 mapsRelated : PartialMapsRelated
                                          (EffectStateEquivalence keyEq) (partialEffectMap sourceStep)
                                          (partialEffectMap replayedStep)
                                        mapsRelated = replayExactTransitionMapsRelated keyEq sourceStep
                                          replayedStep mapPreserved
                                        0 notAdvance : (selected : name) -> Not
                                          (the (Action name key value world error)
                                            (LLeave actor) = LAdvance selected)
                                        notAdvance selected Refl impossible
                                        0 rar : RelationalReplayCorrespondence name key
                                          world error value
                                          (MoreTransitions sourceStep NoTransitions)
                                          (MoreTransitions replayedStep NoTransitions)
                                        rar = singletonNonAdvanceRAR nameEq keyEq
                                          (LLeave actor) LLeaveTag sourceState
                                          sourceAfter replayedState targetState
                                          sourceChecked targetChecked notAdvance
                                          mapsRelated
                                        0 nextEndpoint : RelationalReplayEndpoint name
                                          key world error value nameEq keyEq sourceAfter
                                          targetState
                                        nextEndpoint = MkRelationalReplayEndpoint
                                          nextEffects nextControls targetWellFormed
                                        sourceAligned : AlignedTransitions name key
                                          world error value nameEq keyEq
                                          (MoreTransitions sourceStep NoTransitions)
                                        sourceAligned = AlignedStep (LLeave actor)
                                          LLeaveTag sourceChecked NoTransitions
                                          AlignedEnd
                                    in packagePointwiseRelationalHeadReplay nameEq keyEq
                                      sourceStep sourceAligned targetState
                                      (LLeave actor) LLeaveTag targetChecked Refl Refl
                                      rar mapsRelated nextEndpoint

||| Complete pointwise O-Insert head. Applicability, checked target, endpoint,
||| map, RAR, occurrence, and ordinal evidence are all constructed together.
0 replayPointwiseInsertHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert actor parent component) sourceBefore =
    Just (OInsertTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceBefore
    replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq (OInsert actor parent component) OInsertTag sourceChecked)
    replayedBefore
replayPointwiseInsertHead nameEq keyEq actor parent component
  {sourceBefore = MkSystemState sourceWorld sourceRegistry}
  {sourceAfter} {replayedBefore = MkSystemState replayedWorld replayedRegistry}
  sourceChecked sourceWellFormed beforeEndpoint =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq}
          (OInsert actor parent component) sourceState =
          Just (OInsertTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq
          (OInsert actor parent component) sourceState sourceAfter OInsertTag
          sourceChecked
    in case insertSourceIngredientsPointwise nameEq keyEq actor parent component
      sourceWorld sourceRegistry sourceAfter sourceRaw of
      (sourceAbsent ** (sourceGuards, sourceAfterExact)) =>
        let 0 targetAbsent : (lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} actor
              replayedRegistry = Nothing)
            targetAbsent = pointwiseControlLookupAbsent nameEq actor sourceState
              replayedState (replayedControls beforeEndpoint) sourceAbsent
            0 parentSame : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              sourceRegistry = parentPresent @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} parent
                replayedRegistry)
            parentSame = pointwiseParentPresentSame nameEq parent sourceState
              replayedState (replayedControls beforeEndpoint)
            0 sourceParent : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              sourceRegistry = True)
            sourceParent = boolAndLeftPointwise _ _ sourceGuards
            0 targetParent : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              replayedRegistry = True)
            targetParent = trans (sym parentSame) sourceParent
            0 sourceDisjoint : (provisionsDisjointFrom @{keyEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              (componentProvisions component) (bindings sourceRegistry) = True)
            sourceDisjoint = boolAndRightPointwise _ _ sourceGuards
            0 targetDisjoint : (provisionsDisjointFrom @{keyEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              (componentProvisions component) (bindings replayedRegistry) = True)
            targetDisjoint = pointwiseProvisionsDisjointFromTrue nameEq keyEq
              (componentProvisions component) sourceState replayedState
              (replayedControls beforeEndpoint) sourceDisjoint
            0 targetGuards : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              replayedRegistry && provisionsDisjointFrom @{keyEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                (componentProvisions component) (bindings replayedRegistry) = True)
            targetGuards = boolAndBothPointwise _ _ targetParent targetDisjoint
        in case setFreshFromAbsent nameEq actor (freshFiber component parent)
          replayedRegistry targetAbsent of
          (applied ** inserted) =>
            let targetState : SystemState name key value world error
                targetState = MkSystemState replayedWorld (coeffectAfter applied)
                0 targetRaw : applyAction @{nameEq} @{keyEq}
                  (OInsert actor parent component) replayedState =
                  Just (OInsertTag, targetState)
                targetRaw = rewrite targetGuards in rewrite inserted in Refl
                0 targetWellFormed : registryWellFormed @{nameEq} @{keyEq}
                  targetState = True
                targetWellFormed = preservationTheoremProof nameEq keyEq
                  (OInsert actor parent component) replayedState targetState
                  OInsertTag (replayedWellFormed beforeEndpoint) targetRaw
                0 targetChecked : checkedApplyAction @{nameEq} @{keyEq}
                  (OInsert actor parent component) replayedState =
                  Just (OInsertTag, targetState)
                targetChecked = rewrite targetRaw in
                  rewrite targetWellFormed in Refl
                0 setRelated : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq} sourceState))
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq} replayedState))
                setRelated = setRelatedEffectTables nameEq keyEq actor
                  (emptyContext {key = key} {value = value})
                  (emptyContext {key = key} {value = value}) Refl
                  (replayedEffects beforeEndpoint)
                0 sourceFrame : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq} sourceState))
                  (projectEffectState @{nameEq} sourceAfter)
                sourceFrame = insertEffectFrameRelated nameEq keyEq actor parent
                  component sourceState sourceAfter sourceChecked
                0 targetFrame : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq} replayedState))
                  (projectEffectState @{nameEq} targetState)
                targetFrame = insertEffectFrameRelated nameEq keyEq actor parent
                  component replayedState targetState targetChecked
                0 nextEffects : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} sourceAfter)
                  (projectEffectState @{nameEq} targetState)
                nextEffects = effectStateRelatedTransitive
                  (effectStateRelatedSymmetric sourceFrame)
                  (effectStateRelatedTransitive setRelated targetFrame)
                0 targetShape : (coeffectAfter applied =
                  insertBinding @{nameEq} actor (freshFiber component parent)
                    replayedRegistry
                    (setFreshAbsent nameEq actor (freshFiber component parent)
                      replayedRegistry applied inserted))
                targetShape = setFreshAfter nameEq actor
                  (freshFiber component parent) replayedRegistry applied inserted
                0 nextControlsConcrete : ControlEquivalent name key world error
                  value nameEq
                  (MkSystemState sourceWorld
                    (insertBinding @{nameEq} actor
                      (freshFiber component parent) sourceRegistry sourceAbsent))
                  (MkSystemState replayedWorld
                    (insertBinding @{nameEq} actor
                      (freshFiber component parent) replayedRegistry
                      (setFreshAbsent nameEq actor (freshFiber component parent)
                        replayedRegistry applied inserted)))
                nextControlsConcrete = pointwiseControlAfterInsert nameEq actor
                  parent component sourceWorld replayedWorld sourceRegistry
                  replayedRegistry sourceAbsent
                  (setFreshAbsent nameEq actor (freshFiber component parent)
                    replayedRegistry applied inserted)
                  (replayedControls beforeEndpoint)
                0 nextControlsInserted : ControlEquivalent name key world error
                  value nameEq sourceAfter
                  (MkSystemState replayedWorld
                    (insertBinding @{nameEq} actor
                      (freshFiber component parent) replayedRegistry
                      (setFreshAbsent nameEq actor (freshFiber component parent)
                        replayedRegistry applied inserted)))
                nextControlsInserted = replace
                  {p = \observed => ControlEquivalent name key world error value
                    nameEq observed
                    (MkSystemState replayedWorld
                      (insertBinding @{nameEq} actor
                        (freshFiber component parent) replayedRegistry
                        (setFreshAbsent nameEq actor
                          (freshFiber component parent) replayedRegistry applied
                          inserted)))}
                  sourceAfterExact nextControlsConcrete
                0 nextControls : ControlEquivalent name key world error value
                  nameEq sourceAfter targetState
                nextControls = rewrite targetShape in nextControlsInserted
                sourceStep : Transition sourceState sourceAfter
                sourceStep = Fired nameEq keyEq
                  (OInsert actor parent component) OInsertTag sourceChecked
                replayedStep : Transition replayedState targetState
                replayedStep = Fired nameEq keyEq
                  (OInsert actor parent component) OInsertTag targetChecked
                0 mapPreserved :
                  (state : EffectState name key value world) ->
                  partialEffectMap sourceStep state =
                    partialEffectMap replayedStep state
                mapPreserved state = Refl
                0 mapsRelated : PartialMapsRelated
                  (EffectStateEquivalence keyEq) (partialEffectMap sourceStep)
                  (partialEffectMap replayedStep)
                mapsRelated = replayExactTransitionMapsRelated keyEq sourceStep
                  replayedStep mapPreserved
                0 notAdvance : (selected : name) -> Not
                  (the (Action name key value world error)
                    (OInsert actor parent component) = LAdvance selected)
                notAdvance selected Refl impossible
                0 rar : RelationalReplayCorrespondence name key world error value
                  (MoreTransitions sourceStep NoTransitions)
                  (MoreTransitions replayedStep NoTransitions)
                rar = singletonNonAdvanceRAR nameEq keyEq
                  (OInsert actor parent component) OInsertTag sourceState
                  sourceAfter replayedState targetState sourceChecked targetChecked
                  notAdvance mapsRelated
                0 nextEndpoint : RelationalReplayEndpoint name key world error
                  value nameEq keyEq sourceAfter targetState
                nextEndpoint = MkRelationalReplayEndpoint nextEffects nextControls
                  targetWellFormed
                sourceAligned : AlignedTransitions name key world error value
                  nameEq keyEq (MoreTransitions sourceStep NoTransitions)
                sourceAligned = AlignedStep (OInsert actor parent component)
                  OInsertTag sourceChecked NoTransitions AlignedEnd
            in packagePointwiseRelationalHeadReplay nameEq keyEq sourceStep
              sourceAligned targetState (OInsert actor parent component)
              OInsertTag targetChecked Refl Refl rar mapsRelated nextEndpoint

||| First concrete branch of the private pointwise head replayer.  O-Retire is
||| control-only, so its map is definitionally identity; applicability and the
||| next quotient are reconstructed from the exact source transition plus the
||| incoming pointwise endpoint.
0 replayPointwiseRetireHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
    sourceBefore = Just (ORetireTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceBefore
    replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq (ORetire actor) ORetireTag sourceChecked)
    replayedBefore
replayPointwiseRetireHead nameEq keyEq actor
  {sourceBefore = MkSystemState sourceWorld sourceRegistry}
  {sourceAfter} {replayedBefore = MkSystemState replayedWorld replayedRegistry}
  sourceChecked sourceWellFormed beforeEndpoint =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
          sourceState = Just (ORetireTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (ORetire actor)
          sourceState sourceAfter ORetireTag sourceChecked
    in case retireSourceIngredients nameEq keyEq actor sourceWorld sourceRegistry
      sourceAfter sourceRaw of
      (sourceFiber ** (sourceFound, sourceAfterExact)) =>
        case pointwiseControlLookupFound nameEq actor sourceState replayedState
          (replayedControls beforeEndpoint) sourceFiber sourceFound of
          (replayedFiber ** (replayedFound, fibersRelated)) =>
            let targetState : SystemState name key value world error
                targetState = MkSystemState replayedWorld
                  (replaceBinding @{nameEq} actor (retireFiber replayedFiber)
                    replayedRegistry)
                0 targetRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
                  replayedState = Just (ORetireTag, targetState)
                targetRaw = rewrite replayedFound in Refl
                0 targetWellFormed : registryWellFormed @{nameEq} @{keyEq}
                  targetState = True
                targetWellFormed = preservationTheoremProof nameEq keyEq
                  (ORetire actor) replayedState targetState ORetireTag
                  (replayedWellFormed beforeEndpoint) targetRaw
                0 targetChecked : checkedApplyAction @{nameEq} @{keyEq}
                  (ORetire actor) replayedState =
                  Just (ORetireTag, targetState)
                targetChecked = rewrite targetRaw in
                  rewrite targetWellFormed in Refl
                0 sourceFrame : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} sourceState)
                  (projectEffectState @{nameEq} sourceAfter)
                sourceFrame = retireEffectFrameRelated nameEq keyEq actor
                  sourceState sourceAfter sourceRaw
                0 targetFrame : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} replayedState)
                  (projectEffectState @{nameEq} targetState)
                targetFrame = retireEffectFrameRelated nameEq keyEq actor
                  replayedState targetState targetRaw
                0 nextEffects : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} sourceAfter)
                  (projectEffectState @{nameEq} targetState)
                nextEffects = effectStateRelatedTransitive
                  (effectStateRelatedSymmetric sourceFrame)
                  (effectStateRelatedTransitive (replayedEffects beforeEndpoint)
                    targetFrame)
                0 nextControlsConcrete : ControlEquivalent name key world error
                  value nameEq
                  (MkSystemState sourceWorld
                    (replaceBinding @{nameEq} actor (retireFiber sourceFiber)
                      sourceRegistry)) targetState
                nextControlsConcrete = pointwiseControlAfterRetire nameEq actor
                  sourceWorld replayedWorld sourceRegistry replayedRegistry
                  sourceFiber replayedFiber sourceFound replayedFound
                  fibersRelated (replayedControls beforeEndpoint)
                0 nextControls : ControlEquivalent name key world error value
                  nameEq sourceAfter targetState
                nextControls = replace
                  {p = \observed => ControlEquivalent name key world error value
                    nameEq observed targetState}
                  sourceAfterExact nextControlsConcrete
                sourceStep : Transition sourceState sourceAfter
                sourceStep = Fired nameEq keyEq (ORetire actor) ORetireTag
                  sourceChecked
                replayedStep : Transition replayedState targetState
                replayedStep = Fired nameEq keyEq (ORetire actor) ORetireTag
                  targetChecked
                0 mapPreserved :
                  (state : EffectState name key value world) ->
                  partialEffectMap sourceStep state =
                    partialEffectMap replayedStep state
                mapPreserved state = Refl
                0 mapsRelated : PartialMapsRelated
                  (EffectStateEquivalence keyEq) (partialEffectMap sourceStep)
                  (partialEffectMap replayedStep)
                mapsRelated = replayExactTransitionMapsRelated keyEq sourceStep
                  replayedStep mapPreserved
                0 notAdvance : (selected : name) -> Not
                  (the (Action name key value world error) (ORetire actor) =
                    LAdvance selected)
                notAdvance selected Refl impossible
                0 rar : RelationalReplayCorrespondence name key world error value
                  (MoreTransitions sourceStep NoTransitions)
                  (MoreTransitions replayedStep NoTransitions)
                rar = singletonNonAdvanceRAR nameEq keyEq (ORetire actor)
                  ORetireTag sourceState sourceAfter replayedState targetState
                  sourceChecked targetChecked notAdvance mapsRelated
                0 nextEndpoint : RelationalReplayEndpoint name key world error
                  value nameEq keyEq sourceAfter targetState
                nextEndpoint = MkRelationalReplayEndpoint nextEffects nextControls
                  targetWellFormed
                sourceAligned : AlignedTransitions name key world error value
                  nameEq keyEq (MoreTransitions sourceStep NoTransitions)
                sourceAligned = AlignedStep (ORetire actor) ORetireTag
                  sourceChecked NoTransitions AlignedEnd
            in packagePointwiseRelationalHeadReplay nameEq keyEq sourceStep
              sourceAligned targetState (ORetire actor) ORetireTag targetChecked
              Refl Refl rar mapsRelated nextEndpoint

||| Internal one-step evaluator used by the structural suffix recursion.  Its
||| endpoint input is exactly the result of the preceding checked replay (or the
||| local diamond for the first head); it is never exposed as a premise of the
||| public adjacent-swap theorem.
PointwiseRelationalHeadReplayer :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> Type
PointwiseRelationalHeadReplayer name key world error value nameEq keyEq =
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceStep : Transition sourceBefore sourceAfter) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions sourceStep NoTransitions) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq
    sourceBefore replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq sourceStep
    replayedBefore

||| Exact existential returned by the first genuine generic spine recursion.
||| It exposes no caller-selected evidence: target trace, endpoint, and seal are
||| all produced together under the source suffix and replay start indices.
record PointwiseSuffixSpineReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceFirst, sourceFinal : SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal)
  (replayedFirst : SystemState name key value world error) where
  constructor MkPointwiseSuffixSpineReplay
  spineReplayedFinal : SystemState name key value world error
  spineReplayedTrace : Transitions replayedFirst spineReplayedFinal
  0 spineReplayEndpoint : RelationalReplayEndpoint name key world error value
    nameEq keyEq sourceFinal spineReplayedFinal
  0 spineReplaySeal : SealedSuffixReplaySpine name key world error value nameEq
    keyEq source spineReplayedTrace

||| Structural recursion over the exact aligned suffix.  The only semantic
||| subproblem is the private per-action head replayer.  Once a head is produced,
||| its checked endpoint is threaded into the recursive call and all frozen
||| spine capital is sealed definitionally.
0 replayPointwiseSuffixSpineWith :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  PointwiseRelationalHeadReplayer name key world error value nameEq keyEq ->
  {sourceFirst, sourceFinal, replayedFirst :
    SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceFinal) ->
  AlignedTransitions name key world error value nameEq keyEq source ->
  registryWellFormed @{nameEq} @{keyEq} sourceFirst = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq
    sourceFirst replayedFirst ->
  PointwiseSuffixSpineReplay name key world error value nameEq keyEq source
    replayedFirst
replayPointwiseSuffixSpineWith nameEq keyEq replayHead NoTransitions AlignedEnd
  sourceWellFormed endpoint =
    MkPointwiseSuffixSpineReplay _ NoTransitions endpoint SealedSuffixReplayEnd
replayPointwiseSuffixSpineWith nameEq keyEq replayHead
  (MoreTransitions {middle = sourceMiddle}
    (Fired {before = sourceFirst} {afterState = sourceMiddle}
      nameEq keyEq action tag checked) sourceTail)
  (AlignedStep action tag checked sourceTail alignedTail) sourceWellFormed
  endpoint =
    let head = replayHead
          (Fired {before = sourceFirst} {afterState = sourceMiddle}
            nameEq keyEq action tag checked)
          (AlignedStep action tag checked NoTransitions AlignedEnd)
          sourceWellFormed endpoint
        0 sourceMiddleWellFormed = checkedTargetWellFormed nameEq keyEq action
          _ _ tag checked
        tail = replayPointwiseSuffixSpineWith nameEq keyEq replayHead sourceTail
          alignedTail sourceMiddleWellFormed (headReplayEndpoint head)
    in MkPointwiseSuffixSpineReplay (spineReplayedFinal tail)
      (MoreTransitions (headReplayedStep head) (spineReplayedTrace tail))
      (spineReplayEndpoint tail)
      (sealPointwiseRelationalHead head (spineReplaySeal tail))

||| A complete adjacent transposition: the local pair is swapped, the untouched
||| suffix is replayed, and the next recursion receives the same full premise
||| bundle.  It also exposes exact same-external-input and generator/stage
||| correspondence rather than expecting endpoint relations to imply them.
export
record AdjacentSwapResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (tracePrefix : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle)
  (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal)
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) where
  constructor MkAdjacentSwapResult
  adjacentReplayedFinal : SystemState name key value world error
  adjacentReplayedSuffix :
    Transitions (swappedFinal diamond) adjacentReplayedFinal
  adjacentSwappedTrace : Transitions initial adjacentReplayedFinal
  0 adjacentOriginalDecomposition : appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original
  0 adjacentSwappedDecomposition : adjacentSwappedTrace =
    appendTransitions tracePrefix
      (MoreTransitions (movedRight diamond)
        (MoreTransitions (movedLeft diamond) adjacentReplayedSuffix))
  adjacentSameExternalInputs :
    SameExternalOrchestration nameEq original adjacentSwappedTrace
  adjacentReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original adjacentSwappedTrace
  adjacentEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq originalFinal adjacentReplayedFinal
  adjacentPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq adjacentSwappedTrace
  0 adjacentSealedSuffixReplay : SealedSuffixReplaySpine name key world error
    value nameEq keyEq suffix adjacentReplayedSuffix
  0 adjacentSealedOccurrenceFold : AdjacentSwapOperationalOccurrenceFold name key
    world error value original tracePrefix left right suffix (movedRight diamond)
    (movedLeft diamond) adjacentReplayedSuffix adjacentSwappedTrace

namespace AdjacentSwapResult
  public export
  replayedFinal :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    AdjacentSwapResult name key world error value protocol nameEq keyEq original
      tracePrefix left right suffix diamond ->
    SystemState name key value world error
  replayedFinal = adjacentReplayedFinal

  public export
  replayedSuffix :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    Transitions (swappedFinal diamond) (replayedFinal result)
  replayedSuffix = adjacentReplayedSuffix

  public export
  swappedTrace :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    Transitions initial (replayedFinal result)
  swappedTrace result = adjacentSwappedTrace result

  public export
  0 originalDecomposition :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    appendTransitions tracePrefix
      (MoreTransitions left (MoreTransitions right suffix)) = original
  originalDecomposition = adjacentOriginalDecomposition

  public export
  0 swappedDecomposition :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    swappedTrace result = appendTransitions tracePrefix
      (MoreTransitions (movedRight diamond)
        (MoreTransitions (movedLeft diamond) (replayedSuffix result)))
  swappedDecomposition result = adjacentSwappedDecomposition result

  public export
  swappedSameExternalInputs :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    SameExternalOrchestration nameEq original (swappedTrace result)
  swappedSameExternalInputs result = adjacentSameExternalInputs result

  public export
  swappedReplayCorrespondence :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    RelationalReplayCorrespondence name key world error value original
      (swappedTrace result)
  swappedReplayCorrespondence result = adjacentReplayCorrespondence result

  public export
  swappedEndpoint :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    RelationalReplayEndpoint name key world error value nameEq keyEq originalFinal
      (replayedFinal result)
  swappedEndpoint result = adjacentEndpoint result

  public export
  swappedPremises :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    ReplayInvariantBundle name key world error value protocol nameEq keyEq
      (swappedTrace result)
  swappedPremises result = adjacentPremises result

  public export
  0 sealedSuffixReplay :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    SealedSuffixReplaySpine name key world error value nameEq keyEq suffix
      (replayedSuffix result)
  sealedSuffixReplay = adjacentSealedSuffixReplay

  public export
  0 sealedOccurrenceFold :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
      SystemState name key value world error} ->
    {original : Transitions initial originalFinal} ->
    {tracePrefix : Transitions initial pairFirst} ->
    {left : Transition pairFirst pairMiddle} ->
    {right : Transition pairMiddle pairFinal} ->
    {suffix : Transitions pairFinal originalFinal} ->
    {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right} ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original tracePrefix left right suffix diamond) ->
    AdjacentSwapOperationalOccurrenceFold name key world error value original
      tracePrefix left right suffix (movedRight diamond) (movedLeft diamond)
      (replayedSuffix result) (swappedTrace result)
  sealedOccurrenceFold result = adjacentSealedOccurrenceFold result

||| The first operational occurrence certificate is the exact producer-owned
||| fold sealed inside this opaque adjacent result.
public export
0 swappedOccurrenceFold :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond) ->
  AdjacentSwapOperationalOccurrenceFold name key world error value original tracePrefix
    left right suffix (movedRight diamond) (movedLeft diamond)
    (replayedSuffix result) (swappedTrace result)
swappedOccurrenceFold result = sealedOccurrenceFold result

public export
0 swappedOccurrenceCorrespondence :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original tracePrefix left right suffix diamond) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (swappedTrace result)
swappedOccurrenceCorrespondence result =
  operationalOccurrenceCorrespondence (swappedOccurrenceFold result)

||| The finite derivation records which one of the four source-sensitive local
||| diamonds justified every adjacent transition transposition.  Thus a block
||| producer cannot hide an unclassified pair behind endpoint assertions.
public export
data AdjacentSwapOrientationEvidence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, middle, afterState : SystemState name key value world error} ->
  Transition before middle -> Transition middle afterState -> Type where
  AdjacentActivationActivation :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperActivationStep left -> PaperActivationStep right ->
    AdjacentSwapOrientationEvidence left right
  AdjacentActivationOrchestration :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperActivationStep left -> PaperOrchestrationStep right ->
    AdjacentSwapOrientationEvidence left right
  AdjacentOrchestrationActivation :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperOrchestrationStep left -> PaperActivationStep right ->
    AdjacentSwapOrientationEvidence left right
  AdjacentOrchestrationOrchestration :
    (left : Transition before middle) ->
    (right : Transition middle afterState) ->
    PaperOrchestrationStep left -> PaperOrchestrationStep right ->
    AdjacentSwapOrientationEvidence left right

||| A finite whole-block replay is not an assertion about its endpoint.  It is
||| an explicit list of source-sensitive adjacent transpositions, each carrying
||| the concrete A/A, A/O, O/A, or O/O `LocalRelationalDiamond` and the complete
||| `AdjacentSwapResult` returned by suffix replay.
public export
data FiniteAdjacentSwapDerivation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  Transitions initial sourceFinal -> Transitions initial targetFinal -> Type where
  FiniteAdjacentSwapDone :
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
      trace trace
  FiniteAdjacentSwapStep :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
      SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (prefixTrace : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq (swappedTrace result) target) ->
    FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
      original target

||| A nontrivial actor-block transposition cannot use the zero-node terminator.
||| This family exposes its first concrete orientation/diamond/result and leaves
||| `FiniteAdjacentSwapDone` available only for the tail after all crossings.
public export
data NonEmptyFiniteAdjacentSwapDerivation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  Transitions initial sourceFinal -> Transitions initial targetFinal -> Type where
  NonEmptyAdjacentSwap :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
      SystemState name key value world error} ->
    (original : Transitions initial originalFinal) ->
    (prefixTrace : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq (swappedTrace result) target) ->
    NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq original target

public export
nonEmptyToFiniteAdjacentSwapDerivation :
  NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq
    keyEq source target ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    source target
nonEmptyToFiniteAdjacentSwapDerivation
  (NonEmptyAdjacentSwap original prefixTrace left right suffix orientation diamond
    result target rest) =
      FiniteAdjacentSwapStep original prefixTrace left right suffix orientation
        diamond result target rest

public export
finiteAdjacentSwapNodeCount :
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    source target -> Nat
finiteAdjacentSwapNodeCount FiniteAdjacentSwapDone = Z
finiteAdjacentSwapNodeCount
  (FiniteAdjacentSwapStep _ _ _ _ _ _ _ _ _ rest) =
    S (finiteAdjacentSwapNodeCount rest)

public export
nonEmptyAdjacentSwapNodeCount :
  NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq
    keyEq source target -> Nat
nonEmptyAdjacentSwapNodeCount
  (NonEmptyAdjacentSwap _ _ _ _ _ _ _ _ _ rest) =
    S (finiteAdjacentSwapNodeCount rest)

public export
0 finiteDerivationReplayCorrespondence :
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol
    nameEq keyEq source target) ->
  RelationalReplayCorrespondence name key world error value source target
finiteDerivationReplayCorrespondence FiniteAdjacentSwapDone =
  MkRelationalReplayCorrespondence (\actor, generator => generator)
    (\observedKeyEq, actor, generator =>
      replayTraceGeneratorMapRespects observedKeyEq generator)
    (\actor, stage => stage)
    (\actor, stage, state => Refl)
finiteDerivationReplayCorrespondence
  (FiniteAdjacentSwapStep _ _ _ _ _ _ _ result _ rest) =
    composeRelationalReplayCorrespondence (swappedReplayCorrespondence result)
      (finiteDerivationReplayCorrespondence rest)

public export
0 finiteDerivationOccurrenceCorrespondence :
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol
    nameEq keyEq source target) ->
  ActionRegistrationReplayCorrespondence name key world error value source target
finiteDerivationOccurrenceCorrespondence {source}
  FiniteAdjacentSwapDone = identityActionRegistrationReplayCorrespondence source
finiteDerivationOccurrenceCorrespondence
  (FiniteAdjacentSwapStep _ _ _ _ _ _ _ result _ rest) =
    composeActionRegistrationReplayCorrespondence
      (swappedOccurrenceCorrespondence result)
      (finiteDerivationOccurrenceCorrespondence rest)

0 localPartialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
localPartialRelatedRewrite Refl Refl related = related

0 localPartialDefinedRelation :
  PartialRelated state rel (Just left) (Just right) -> rel left right
localPartialDefinedRelation (PartialDefined related) = related

0 localEffectStateSymmetric : EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq right left
localEffectStateSymmetric (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\actor => sym (tables actor))

0 localEffectStateTransitive : EffectStateRelated keyEq left middle ->
  EffectStateRelated keyEq middle right -> EffectStateRelated keyEq left right
localEffectStateTransitive
  (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

record FramedEffectOutput
  (keyEq : DecEq key) (effectMap : PartialEffectMap name key value world)
  (input, target : EffectState name key value world) where
  constructor MkFramedEffectOutput
  0 framedOutput : EffectState name key value world
  0 framedMapRuns : effectMap input = Just framedOutput
  0 framedOutputRelated : EffectStateRelated keyEq framedOutput target

0 framedEffectOutput :
  (keyEq : DecEq key) ->
  (effectMap : PartialEffectMap name key value world) ->
  (input, target : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (effectMap input) (Just target) ->
  FramedEffectOutput keyEq effectMap input target
framedEffectOutput keyEq effectMap input target frame
  with (effectMap input) proof runs
  framedEffectOutput keyEq effectMap input target frame | Nothing =
    case frame of _ impossible
  framedEffectOutput keyEq effectMap input target frame | Just output =
    MkFramedEffectOutput output runs (localPartialDefinedRelation frame)

record RelatedEffectMapOutput
  (keyEq : DecEq key) (effectMap : PartialEffectMap name key value world)
  (left, right, leftOutput : EffectState name key value world) where
  constructor MkRelatedEffectMapOutput
  0 relatedMapOutput : EffectState name key value world
  0 relatedMapRuns : effectMap right = Just relatedMapOutput
  0 relatedMapOutputs : EffectStateRelated keyEq leftOutput relatedMapOutput

0 effectMapOutputOnRelatedRight :
  (keyEq : DecEq key) ->
  (effectMap : PartialEffectMap name key value world) ->
  EffectPartialMapRespects keyEq effectMap ->
  (left, right, leftOutput : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  effectMap left = Just leftOutput ->
  RelatedEffectMapOutput keyEq effectMap left right leftOutput
effectMapOutputOnRelatedRight keyEq effectMap respects left right leftOutput
  related leftRuns with (effectMap right) proof rightRuns
  effectMapOutputOnRelatedRight keyEq effectMap respects left right leftOutput
    related leftRuns | Nothing =
      let contradiction = localPartialRelatedRewrite leftRuns rightRuns
            (respects left right related)
      in case contradiction of _ impossible
  effectMapOutputOnRelatedRight keyEq effectMap respects left right leftOutput
    related leftRuns | Just rightOutput =
      let 0 outputs : EffectStateRelated keyEq leftOutput rightOutput
          outputs = localPartialDefinedRelation
            (localPartialRelatedRewrite leftRuns rightRuns
              (respects left right related))
      in MkRelatedEffectMapOutput rightOutput rightRuns outputs

0 replaceEntriesDistinctCommute :
  (keyEq : DecEq key) -> (left, right : key) -> Not (left = right) ->
  (leftNext : value left) -> (rightNext : value right) ->
  (entries : List (Binding key value)) ->
  replaceEntries @{keyEq} left leftNext
    (replaceEntries @{keyEq} right rightNext entries) =
  replaceEntries @{keyEq} right rightNext
    (replaceEntries @{keyEq} left leftNext entries)
replaceEntriesDistinctCommute keyEq left right distinct leftNext rightNext [] =
  Refl
replaceEntriesDistinctCommute keyEq left right distinct leftNext rightNext
  (Bind current old :: rest)
  with (decEq @{keyEq} right current) proof rightCurrent
  replaceEntriesDistinctCommute keyEq left current distinct leftNext rightNext
    (Bind current old :: rest) | Yes Refl
    with (decEq @{keyEq} left current) proof leftCurrent
    replaceEntriesDistinctCommute keyEq current current distinct leftNext
      rightNext (Bind current old :: rest) | Yes Refl | Yes Refl =
        void (distinct Refl)
    replaceEntriesDistinctCommute keyEq left current distinct leftNext rightNext
      (Bind current old :: rest) | Yes Refl | No notLeft
      with (decEq @{keyEq} current current)
      replaceEntriesDistinctCommute keyEq left current distinct leftNext
        rightNext (Bind current old :: rest) | Yes Refl | No notLeft |
        Yes Refl
        with (decEq @{keyEq} left current)
        replaceEntriesDistinctCommute keyEq current current distinct leftNext
          rightNext (Bind current old :: rest) | Yes Refl | No notLeft |
          Yes Refl | Yes Refl = void (notLeft Refl)
        replaceEntriesDistinctCommute keyEq left current distinct leftNext
          rightNext (Bind current old :: rest) | Yes Refl | No notLeft |
          Yes Refl | No stillNotLeft = Refl
      replaceEntriesDistinctCommute keyEq left current distinct leftNext
        rightNext (Bind current old :: rest) | Yes Refl | No notLeft |
        No absurd = void (absurd Refl)
  replaceEntriesDistinctCommute keyEq left right distinct leftNext rightNext
    (Bind current old :: rest) | No notRight
    with (decEq @{keyEq} left current) proof leftCurrent
    replaceEntriesDistinctCommute keyEq current right distinct leftNext rightNext
      (Bind current old :: rest) | No notRight | Yes Refl
      with (decEq @{keyEq} right current)
      replaceEntriesDistinctCommute keyEq current current distinct leftNext
        rightNext (Bind current old :: rest) | No notRight | Yes Refl |
        Yes Refl = void (notRight Refl)
      replaceEntriesDistinctCommute keyEq current right distinct leftNext
        rightNext (Bind current old :: rest) | No notRight | Yes Refl |
        No stillNotRight
        with (decEq @{keyEq} current current)
        replaceEntriesDistinctCommute keyEq current right distinct leftNext
          rightNext (Bind current old :: rest) | No notRight | Yes Refl |
          No stillNotRight | Yes Refl = Refl
        replaceEntriesDistinctCommute keyEq current right distinct leftNext
          rightNext (Bind current old :: rest) | No notRight | Yes Refl |
          No stillNotRight | No absurd = void (absurd Refl)
    replaceEntriesDistinctCommute keyEq left right distinct leftNext rightNext
      (Bind current old :: rest) | No notRight | No notLeft
      with (decEq @{keyEq} left current)
      replaceEntriesDistinctCommute keyEq current right distinct leftNext
        rightNext (Bind current old :: rest) | No notRight | No notLeft |
        Yes Refl = void (notLeft Refl)
      replaceEntriesDistinctCommute keyEq left right distinct leftNext rightNext
        (Bind current old :: rest) | No notRight | No notLeft | No stillNotLeft
        with (decEq @{keyEq} right current)
        replaceEntriesDistinctCommute keyEq left current distinct leftNext
          rightNext (Bind current old :: rest) | No notRight | No notLeft |
          No stillNotLeft | Yes Refl = void (notRight Refl)
        replaceEntriesDistinctCommute keyEq left right distinct leftNext
          rightNext (Bind current old :: rest) | No notRight | No notLeft |
          No stillNotLeft | No stillNotRight =
            cong (Bind current old ::)
              (replaceEntriesDistinctCommute keyEq left right distinct leftNext
                rightNext rest)

0 orderedControlsSymmetric :
  OrderedRegistryControlsRelated name key world error value left right ->
  OrderedRegistryControlsRelated name key world error value right left
orderedControlsSymmetric OrderedControlsNil = OrderedControlsNil
orderedControlsSymmetric
  (OrderedControlsCons actor related rest) =
    OrderedControlsCons actor (fiberControlSymmetric related)
      (orderedControlsSymmetric rest)

0 orderedControlsAfterDistinctReplacements :
  (nameEq : DecEq name) -> (leftActor, rightActor : name) ->
  Not (leftActor = rightActor) ->
  (source, original, swapped :
    List (Binding name (FiberAt name key value world error))) ->
  (leftOriginal, leftMoved, rightOriginal, rightEarly :
    Fiber name key value world error) ->
  FiberControlRelated leftOriginal leftMoved ->
  FiberControlRelated rightOriginal rightEarly ->
  original = replaceEntries @{nameEq} rightActor rightOriginal
    (replaceEntries @{nameEq} leftActor leftOriginal source) ->
  swapped = replaceEntries @{nameEq} leftActor leftMoved
    (replaceEntries @{nameEq} rightActor rightEarly source) ->
  OrderedRegistryControlsRelated name key world error value original swapped
orderedControlsAfterDistinctReplacements nameEq leftActor rightActor distinct
  source original swapped leftOriginal leftMoved rightOriginal rightEarly
  leftRelated rightRelated originalShape swappedShape =
    let 0 sourceRelated = orderedControlsReflexive source
        0 leftReplaced = orderedControlsReplace nameEq leftActor leftOriginal
          leftMoved leftRelated source source sourceRelated
        0 bothReplaced = orderedControlsReplace nameEq rightActor rightOriginal
          rightEarly rightRelated
          (replaceEntries @{nameEq} leftActor leftOriginal source)
          (replaceEntries @{nameEq} leftActor leftMoved source) leftReplaced
        0 swappedToCanonical = trans swappedShape
          (replaceEntriesDistinctCommute nameEq leftActor rightActor distinct
            leftMoved rightEarly source)
        0 atOriginal = replace
          {p = \entries => OrderedRegistryControlsRelated name key world error
            value entries
            (replaceEntries @{nameEq} rightActor rightEarly
              (replaceEntries @{nameEq} leftActor leftMoved source))}
          (sym originalShape) bothReplaced
    in replace
      {p = \entries => OrderedRegistryControlsRelated name key world error value
        original entries}
      (sym swappedToCanonical) atOriginal

0 localPartialEffectRelatedTransitive :
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    first middle ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    middle finalState ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    first finalState
localPartialEffectRelatedTransitive PartialUndefined PartialUndefined =
  PartialUndefined
localPartialEffectRelatedTransitive (PartialDefined first)
  (PartialDefined second) =
    PartialDefined (localEffectStateTransitive first second)

0 localIteratorOutcomeAgreementTransitive :
  IteratorOutcomeAgreement name key value world error keyEq first middle ->
  IteratorOutcomeAgreement name key value world error keyEq middle finalOutcome ->
  IteratorOutcomeAgreement name key value world error keyEq first finalOutcome
localIteratorOutcomeAgreementTransitive IteratorOutcomesUndefined
  IteratorOutcomesUndefined = IteratorOutcomesUndefined
localIteratorOutcomeAgreementTransitive
  (IteratorFailuresAgree firstError) (IteratorFailuresAgree secondError) =
    IteratorFailuresAgree (trans firstError secondError)
localIteratorOutcomeAgreementTransitive
  (IteratorSuccessfulYieldsAgree firstContinuation firstUndo)
  (IteratorSuccessfulYieldsAgree secondContinuation secondUndo) =
    IteratorSuccessfulYieldsAgree
      (trans firstContinuation secondContinuation)
      (\input => localPartialEffectRelatedTransitive
        (firstUndo input) (secondUndo input))

0 localPartialRelatedSymmetric :
  (eq : Equivalence state) ->
  PartialRelated state (relation eq) left right ->
  PartialRelated state (relation eq) right left
localPartialRelatedSymmetric eq PartialUndefined = PartialUndefined
localPartialRelatedSymmetric eq (PartialDefined related) =
  PartialDefined (DGamma.Core.Equivalence.symmetric eq related)

0 localIteratorOutcomeAgreementSymmetric :
  IteratorOutcomeAgreement name key value world error keyEq left right ->
  IteratorOutcomeAgreement name key value world error keyEq right left
localIteratorOutcomeAgreementSymmetric IteratorOutcomesUndefined =
  IteratorOutcomesUndefined
localIteratorOutcomeAgreementSymmetric (IteratorFailuresAgree errorsSame) =
  IteratorFailuresAgree (sym errorsSame)
localIteratorOutcomeAgreementSymmetric
  (IteratorSuccessfulYieldsAgree continuationSame undoMaps) =
    IteratorSuccessfulYieldsAgree (sym continuationSame)
      (\input => localPartialRelatedSymmetric (EffectStateEquivalence keyEq)
        (undoMaps input))

0 iteratorOutcomeAfterFramedForeign :
  (keyEq : DecEq key) ->
  {trace : Transitions traceFirst traceLast} ->
  TraceIndependent name key world error value keyEq trace ->
  (selected, foreignActor : name) -> Not (selected = foreignActor) ->
  (stage : IteratorStage name key world error value selected trace) ->
  (foreign : TraceEffectTransformation name key world error value foreignActor
    trace) ->
  (origin, target : EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (runTraceEffectTransformation foreign origin) (Just target) ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage target) (iteratorStageOutcome stage origin)
iteratorOutcomeAfterFramedForeign keyEq independent selected foreignActor
  distinct stage foreign origin target frame =
    let 0 framed = framedEffectOutput keyEq
          (runTraceEffectTransformation foreign) origin target frame
        0 targetToGenerated = iteratorStageOutcomeRelated keyEq stage target
          (framedOutput framed)
          (localEffectStateSymmetric (framedOutputRelated framed))
        0 generatedToOrigin = replayOutcomeStableAtExactRun stage
          (runTraceEffectTransformation foreign) origin (framedOutput framed)
          (framedMapRuns framed)
          (iteratorYieldsStable independent selected foreignActor distinct stage
            foreign origin)
    in localIteratorOutcomeAgreementTransitive targetToGenerated
      generatedToOrigin

0 localPartialComposeDefined :
  (after, before : PartialMap state) -> (origin, middle, final : state) ->
  before origin = Just middle -> after middle = Just final ->
  partialCompose after before origin = Just final
localPartialComposeDefined after before origin middle final beforeRuns afterRuns
  with (before origin)
  localPartialComposeDefined after before origin middle final beforeRuns afterRuns |
    Nothing = void (nothingIsNotJust beforeRuns)
  localPartialComposeDefined after before origin middle final beforeRuns afterRuns |
    Just actual = case justInjective beforeRuns of
      Refl => rewrite afterRuns in Refl

0 localPartialComposeAfterRun :
  (after, before : PartialMap state) -> (origin, middle, final : state) ->
  before origin = Just middle ->
  partialCompose after before origin = Just final ->
  after middle = Just final
localPartialComposeAfterRun after before origin middle final beforeRuns composed
  with (before origin)
  localPartialComposeAfterRun after before origin middle final beforeRuns composed |
    Nothing = void (nothingIsNotJust beforeRuns)
  localPartialComposeAfterRun after before origin middle final beforeRuns composed |
    Just actual = case justInjective beforeRuns of
      Refl => composed

record CommutedEffectOutput
  (keyEq : DecEq key)
  (leftMap, rightMap : PartialEffectMap name key value world)
  (source, middle, originalFinal, earlyMiddle :
    EffectState name key value world) where
  constructor MkCommutedEffectOutput
  0 commutedOutput : EffectState name key value world
  0 commutedLeftRuns : leftMap earlyMiddle = Just commutedOutput
  0 originalFinalToCommuted :
    EffectStateRelated keyEq originalFinal commutedOutput

0 commuteEffectFrames :
  (keyEq : DecEq key) ->
  (leftMap, rightMap : PartialEffectMap name key value world) ->
  EffectPartialMapRespects keyEq leftMap ->
  EffectPartialMapRespects keyEq rightMap ->
  PartialCommute (EffectStateEquivalence keyEq) leftMap rightMap ->
  (source, middle, originalFinal, earlyMiddle :
    EffectState name key value world) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (leftMap source) (Just middle) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (rightMap middle) (Just originalFinal) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (rightMap source) (Just earlyMiddle) ->
  CommutedEffectOutput keyEq leftMap rightMap source middle originalFinal
    earlyMiddle
commuteEffectFrames keyEq leftMap rightMap leftRespects rightRespects commute
  source middle originalFinal earlyMiddle leftFrame rightFrame earlyRightFrame =
    let leftSource = framedEffectOutput keyEq leftMap source middle leftFrame
        rightMiddle = framedEffectOutput keyEq rightMap middle originalFinal
          rightFrame
        rightSource = framedEffectOutput keyEq rightMap source earlyMiddle
          earlyRightFrame
        rightAfterLeft = effectMapOutputOnRelatedRight keyEq rightMap
          rightRespects middle (framedOutput leftSource)
          (framedOutput rightMiddle)
          (localEffectStateSymmetric (framedOutputRelated leftSource))
          (framedMapRuns rightMiddle)
        originalCompositionRuns = localPartialComposeDefined rightMap leftMap
          source (framedOutput leftSource) (relatedMapOutput rightAfterLeft)
          (framedMapRuns leftSource) (relatedMapRuns rightAfterLeft)
        commutedAtSource = localPartialRelatedRewrite Refl
          originalCompositionRuns (commute source)
        swappedComposition = framedEffectOutput keyEq
          (partialCompose leftMap rightMap) source
          (relatedMapOutput rightAfterLeft) commutedAtSource
        leftAfterRightRuns = localPartialComposeAfterRun leftMap rightMap source
          (framedOutput rightSource) (framedOutput swappedComposition)
          (framedMapRuns rightSource) (framedMapRuns swappedComposition)
        leftAtEarlyMiddle = effectMapOutputOnRelatedRight keyEq leftMap
          leftRespects (framedOutput rightSource) earlyMiddle
          (framedOutput swappedComposition) (framedOutputRelated rightSource)
          leftAfterRightRuns
        originalToRightMiddle = localEffectStateSymmetric
          (framedOutputRelated rightMiddle)
        rightMiddleToOriginalComposition = relatedMapOutputs rightAfterLeft
        originalCompositionToSwapped = localEffectStateSymmetric
          (framedOutputRelated swappedComposition)
        swappedToMoved = relatedMapOutputs leftAtEarlyMiddle
        0 originalToMoved : EffectStateRelated keyEq originalFinal
          (relatedMapOutput leftAtEarlyMiddle)
        originalToMoved = localEffectStateTransitive originalToRightMiddle
          (localEffectStateTransitive rightMiddleToOriginalComposition
            (localEffectStateTransitive originalCompositionToSwapped
              swappedToMoved))
    in MkCommutedEffectOutput (relatedMapOutput leftAtEarlyMiddle)
      (relatedMapRuns leftAtEarlyMiddle) originalToMoved

0 checkedEffectFrameRelation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (partialEffectMapFor nameEq keyEq action tag before
      (projectEffectState @{nameEq} before))
    (Just (projectEffectState @{nameEq} afterState))
checkedEffectFrameRelation nameEq keyEq action tag before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq action tag before afterState
    checked of
      MkActualEffectFrame related => related

0 advanceRuntimeEffectMapOriginLookupCong :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry left) =
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry right) ->
  (state : EffectState name key value world) ->
  advanceRuntimeEffectMap nameEq keyEq actor left state =
    advanceRuntimeEffectMap nameEq keyEq actor right state
advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) same state
  with (lookupFiber @{nameEq} actor leftRegistry)
  advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) same state | Nothing
    with (lookupFiber @{nameEq} actor rightRegistry)
    advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry) same state | Nothing | Nothing =
        Refl
    advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry) same state | Nothing |
      Just rightFiber = case same of Refl impossible
  advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) same state | Just leftFiber
    with (lookupFiber @{nameEq} actor rightRegistry)
    advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry) same state | Just leftFiber |
      Nothing = case same of Refl impossible
    advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor
      (MkSystemState leftWorld leftRegistry)
      (MkSystemState rightWorld rightRegistry) same state | Just leftFiber |
      Just rightFiber = case justInjective same of
        Refl => Refl

0 transitionForeignLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  Not (selected = actionOwner action) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (registry afterState) =
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (registry before)
transitionForeignLookup nameEq keyEq selected {before} {afterState} action tag
  checked distinct =
    let raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        update = applyActionLocalUpdate nameEq keyEq action before afterState tag
          raw
    in systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
      before afterState update

0 retireProviderCandidateSame :
  (keyEq : DecEq key) -> (wanted : key) ->
  (fiber : Fiber name key value world error) ->
  (isActive (fiberLifecycle (retireFiber fiber)) &&
    memberKey @{keyEq} wanted
      (ownedValues (fiberTable (retireFiber fiber)))) =
  (isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable fiber)))
retireProviderCandidateSame keyEq wanted
  (MkFiber component parent retiredFlag table lifecycle) = Refl

0 providerInRetireHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor : name) -> (fiber : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted
    (Bind actor (retireFiber fiber) :: rest) =
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted (Bind actor fiber :: rest)
providerInRetireHead nameEq keyEq wanted actor fiber rest
  with (isActive (fiberLifecycle fiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable fiber))) proof sourceRun
  providerInRetireHead nameEq keyEq wanted actor fiber rest | False =
    let targetRun = trans (retireProviderCandidateSame keyEq wanted fiber)
          sourceRun
    in rewrite targetRun in Refl
  providerInRetireHead nameEq keyEq wanted actor fiber rest | True =
    let targetRun = trans (retireProviderCandidateSame keyEq wanted fiber)
          sourceRun
    in rewrite targetRun in Refl

0 providerInRetireEntries :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor : name) -> (oldFiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} actor entries = Just oldFiber ->
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted
    (replaceEntries @{nameEq} actor (retireFiber oldFiber) entries) =
  providerIn @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted entries
providerInRetireEntries nameEq keyEq wanted actor oldFiber [] found =
  case found of Refl impossible
providerInRetireEntries nameEq keyEq wanted actor oldFiber
  (Bind current fiber :: rest) found with (decEq @{nameEq} actor current)
  providerInRetireEntries nameEq keyEq wanted current oldFiber
    (Bind current fiber :: rest) found | Yes Refl =
      case justInjective found of
        Refl => providerInRetireHead nameEq keyEq wanted current fiber rest
  providerInRetireEntries nameEq keyEq wanted actor oldFiber
    (Bind current fiber :: rest) found | No distinct
    with (isActive (fiberLifecycle fiber) &&
      memberKey @{keyEq} wanted (ownedValues (fiberTable fiber)))
    providerInRetireEntries nameEq keyEq wanted actor oldFiber
      (Bind current fiber :: rest) found | No distinct | True = Refl
    providerInRetireEntries nameEq keyEq wanted actor oldFiber
      (Bind current fiber :: rest) found | No distinct | False =
        providerInRetireEntries nameEq keyEq wanted actor oldFiber rest found

0 providerOfRetireRegistry :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor : name) -> (oldFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just oldFiber ->
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted
    (replaceBinding @{nameEq} actor (retireFiber oldFiber) fibers) =
  providerOf @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted fibers
providerOfRetireRegistry nameEq keyEq wanted actor oldFiber
  (MkCoeffectContext entries unique) found =
    providerInRetireEntries nameEq keyEq wanted actor oldFiber entries found

0 resolveViewRetireRegistry :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) ->
  (actor : name) -> (oldFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just oldFiber ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} deps
    (replaceBinding @{nameEq} actor (retireFiber oldFiber) fibers) =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} deps fibers
resolveViewRetireRegistry nameEq keyEq [] actor oldFiber fibers found = Refl
resolveViewRetireRegistry {name} {key} {world} {error} {value}
  nameEq keyEq (wanted :: rest) actor oldFiber fibers found
  with (providerOf @{nameEq} @{keyEq} wanted fibers) proof sourceProvider
  resolveViewRetireRegistry {name} {key} {world} {error} {value}
    nameEq keyEq (wanted :: rest) actor oldFiber fibers found | Nothing =
      let targetProvider = trans
            (providerOfRetireRegistry nameEq keyEq wanted actor oldFiber fibers
              found)
            sourceProvider
      in rewrite targetProvider in Refl
  resolveViewRetireRegistry {name} {key} {world} {error} {value}
    nameEq keyEq (wanted :: rest) actor oldFiber fibers found |
    Just provider =
      let targetProvider = trans
            (providerOfRetireRegistry nameEq keyEq wanted actor oldFiber fibers
              found)
            sourceProvider
      in rewrite targetProvider in cong (map (ProviderView provider))
        (resolveViewRetireRegistry nameEq keyEq rest actor oldFiber fibers found)

0 targetFiberRetireRegistry :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observed : Fiber name key value world error) ->
  (actor : name) -> (oldFiber : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just oldFiber ->
  targetFiber @{nameEq} @{keyEq} observed
    (replaceBinding @{nameEq} actor (retireFiber oldFiber) fibers) =
  targetFiber @{nameEq} @{keyEq} observed fibers
targetFiberRetireRegistry nameEq keyEq
  (MkFiber component parent False table lifecycle) actor oldFiber fibers found =
    resolveViewRetireRegistry nameEq keyEq
      (dependencies (componentDependencies component)) actor oldFiber fibers
      found
targetFiberRetireRegistry nameEq keyEq
  (MkFiber component parent True table lifecycle) actor oldFiber fibers found =
    Refl

0 inactiveLifecycleFromRemovalGuard :
  (retiredFlag : Bool) ->
  (lifecycle : Lifecycle key value world error name deps provision) ->
  (childPresent : Bool) ->
  retiredFlag && isInactive lifecycle && not childPresent = True ->
  (outcome : Maybe error ** lifecycle = Inactive outcome)
inactiveLifecycleFromRemovalGuard retiredFlag (Inactive outcome) childPresent
  valid = (outcome ** Refl)
inactiveLifecycleFromRemovalGuard False (Reloading remaining accumulator view)
  childPresent valid = case valid of Refl impossible
inactiveLifecycleFromRemovalGuard True (Reloading remaining accumulator view)
  childPresent valid = case valid of Refl impossible
inactiveLifecycleFromRemovalGuard False (Active accumulator view) childPresent
  valid = case valid of Refl impossible
inactiveLifecycleFromRemovalGuard True (Active accumulator view) childPresent
  valid = case valid of Refl impossible
inactiveLifecycleFromRemovalGuard False (Unloading accumulator view outcome)
  childPresent valid = case valid of Refl impossible
inactiveLifecycleFromRemovalGuard True (Unloading accumulator view outcome)
  childPresent valid = case valid of Refl impossible

0 targetFiberStableAfterPaperOrchestration :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  PaperOrchestrationStep
    (Fired {before} {afterState} nameEq keyEq action tag checked) ->
  (observed : Fiber name key value world error) ->
  targetFiber @{nameEq} @{keyEq} observed (registry afterState) =
    targetFiber @{nameEq} @{keyEq} observed (registry before)
targetFiberStableAfterPaperOrchestration {name} {key} {world} {error} {value}
  nameEq keyEq action tag {before = MkSystemState ambient source} {afterState}
  checked (PaperInsertStep {actor} {parent} {component} actionSame) observed =
    case actionSame of
      Refl =>
        let raw = checkedActionProjects nameEq keyEq
              (OInsert actor parent component) (MkSystemState ambient source)
              afterState tag checked
        in case foreignInsertPlanView nameEq keyEq actor parent component ambient
          source tag afterState raw of
          MkForeignInsertPlanView absent guards => case observed of
            MkFiber observedComponent observedParent False observedTable
              observedLifecycle =>
                resolveViewInactiveInsert nameEq keyEq
                  (dependencies
                    (componentDependencies observedComponent)) actor component
                  parent source absent
            MkFiber observedComponent observedParent True observedTable
              observedLifecycle => Refl
targetFiberStableAfterPaperOrchestration {name} {key} {world} {error} {value}
  nameEq keyEq action tag {before = MkSystemState ambient source} {afterState}
  checked (PaperRetireStep {actor} actionSame) observed = case actionSame of
    Refl =>
      let raw = checkedActionProjects nameEq keyEq (ORetire actor)
            (MkSystemState ambient source) afterState tag checked
      in case retireSuccessView nameEq keyEq actor ambient source tag afterState
        raw of
        MkRetireSuccessView oldFiber oldFound =>
          targetFiberRetireRegistry nameEq keyEq observed actor oldFiber source
            oldFound
targetFiberStableAfterPaperOrchestration {name} {key} {world} {error} {value}
  nameEq keyEq action tag {before = MkSystemState ambient source} {afterState}
  checked (PaperRemoveStep {actor} actionSame) observed = case actionSame of
    Refl =>
      let raw = checkedActionProjects nameEq keyEq (ORemove actor)
            (MkSystemState ambient source) afterState tag checked
      in case removeSuccessView nameEq keyEq actor ambient source tag afterState
        raw of
        MkRemoveSuccessView
          (MkFiber component parent retiredFlag table lifecycle)
          oldFound removable noChild =>
            case inactiveLifecycleFromRemovalGuard retiredFlag lifecycle
              (hasChild @{nameEq} actor source) removable of
              (outcome ** Refl) => targetFiberInactiveDelete nameEq keyEq observed
                actor component parent retiredFlag table outcome source oldFound

0 parentPresentStaticReplacement :
  (nameEq : DecEq name) -> (parent : Parent name) -> (changed : name) ->
  (next, old : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} changed source = Just old ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent
    (replaceBinding @{nameEq} changed next source) =
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent source
parentPresentStaticReplacement nameEq Root changed next old source found = Refl
parentPresentStaticReplacement nameEq (ChildOf parent) changed next old source
  found with (decEq @{nameEq} parent changed)
  parentPresentStaticReplacement nameEq (ChildOf changed) changed next old source
    found | Yes Refl =
      rewrite lookupReplacedFiber changed old next source found in
      rewrite found in Refl
  parentPresentStaticReplacement nameEq (ChildOf parent) changed next old source
    found | No distinct = rewrite lookupReplaceOther parent changed distinct next
      source in Refl

0 provisionsDisjointStaticReplacementEntries :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (changed : name) -> (next, old : Fiber name key value world error) ->
  lookupEntries @{nameEq} changed entries = Just old ->
  fiberComponent next = fiberComponent old ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision
    (replaceEntries @{nameEq} changed next entries) =
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision entries
provisionsDisjointStaticReplacementEntries nameEq keyEq provision [] changed
  next old found staticComponent = case found of Refl impossible
provisionsDisjointStaticReplacementEntries nameEq keyEq provision
  (Bind current observed :: rest) changed next old found staticComponent
  with (decEq @{nameEq} changed current)
  provisionsDisjointStaticReplacementEntries nameEq keyEq provision
    (Bind current observed :: rest) current next old found staticComponent |
    Yes Refl = case justInjective found of
      Refl => rewrite staticComponent in Refl
  provisionsDisjointStaticReplacementEntries nameEq keyEq provision
    (Bind current observed :: rest) changed next old found staticComponent |
    No distinct = cong
      (not (provisionOverlap @{keyEq} provision
        (componentProvisions (fiberComponent observed))) &&)
      (provisionsDisjointStaticReplacementEntries nameEq keyEq provision rest
        changed next old found staticComponent)

0 provisionsDisjointStaticReplacement :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (changed : name) -> (next, old : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} changed source = Just old ->
  fiberComponent next = fiberComponent old ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision
    (bindings (replaceBinding @{nameEq} changed next source)) =
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision (bindings source)
provisionsDisjointStaticReplacement nameEq keyEq provision changed next old
  (MkCoeffectContext entries unique) found staticComponent =
    provisionsDisjointStaticReplacementEntries nameEq keyEq provision entries
      changed next old found staticComponent

0 localAndBothTrue : (left, right : Bool) -> left = True -> right = True ->
  left && right = True
localAndBothTrue True True Refl Refl = Refl

0 providerInCandidateExists :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} provider entries = Just fiber ->
  providerCandidate @{keyEq} {value = value} {world = world} {error = error}
    wanted fiber = True ->
  (chosen : name ** providerIn @{nameEq} @{keyEq} {value = value}
    {world = world} {error = error} wanted entries = Just chosen)
providerInCandidateExists nameEq keyEq wanted provider fiber [] found candidate =
  case found of Refl impossible
providerInCandidateExists nameEq keyEq wanted provider fiber
  (Bind current observed :: rest) found candidate
  with (decEq @{nameEq} provider current)
  providerInCandidateExists nameEq keyEq wanted current fiber
    (Bind current observed :: rest) found candidate | Yes Refl =
      case justInjective found of
        Refl => rewrite candidate in (current ** Refl)
  providerInCandidateExists nameEq keyEq wanted provider fiber
    (Bind current observed :: rest) found candidate | No distinct
    with (providerCandidate @{keyEq} {value = value} {world = world}
      {error = error} wanted observed) proof currentCandidate
    providerInCandidateExists nameEq keyEq wanted provider fiber
      (Bind current observed :: rest) found candidate | No distinct | True =
        (current ** Refl)
    providerInCandidateExists nameEq keyEq wanted provider fiber
      (Bind current observed :: rest) found candidate | No distinct | False =
        providerInCandidateExists nameEq keyEq wanted provider fiber rest found
          candidate

0 beginSourceOwnerNotActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor (registry before) = Just fiber,
      isActive (fiberLifecycle fiber) = False))
beginSourceOwnerNotActive nameEq keyEq actor
  {before = MkSystemState ambient fibers} {afterState} tag checked
  with (lookupFiber @{nameEq} actor fibers) proof found
  beginSourceOwnerNotActive nameEq keyEq actor
    {before = MkSystemState ambient fibers} {afterState} tag checked | Nothing =
      void (nothingIsNotJust checked)
  beginSourceOwnerNotActive nameEq keyEq actor
    {before = MkSystemState ambient fibers} {afterState} tag checked | Just fiber
    with (fiberLifecycle fiber) proof life
    beginSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Inactive Nothing =
        let 0 inactiveProof : (isActive (fiberLifecycle fiber) = False)
            inactiveProof = rewrite life in Refl
        in (fiber ** (Refl, inactiveProof))
    beginSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Inactive (Just failure) = void (nothingIsNotJust checked)
    beginSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust checked)
    beginSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Active accumulator view = void (nothingIsNotJust checked)
    beginSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust checked)

0 advanceSourceOwnerNotActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    (lookupFiber @{nameEq} actor (registry before) = Just fiber,
      isActive (fiberLifecycle fiber) = False))
advanceSourceOwnerNotActive nameEq keyEq actor
  {before = MkSystemState ambient fibers} {afterState} tag checked
  with (lookupFiber @{nameEq} actor fibers) proof found
  advanceSourceOwnerNotActive nameEq keyEq actor
    {before = MkSystemState ambient fibers} {afterState} tag checked | Nothing =
      void (nothingIsNotJust checked)
  advanceSourceOwnerNotActive nameEq keyEq actor
    {before = MkSystemState ambient fibers} {afterState} tag checked | Just fiber
    with (fiberLifecycle fiber) proof life
    advanceSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Inactive outcome = void (nothingIsNotJust checked)
    advanceSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Reloading remaining accumulator view =
        let 0 inactiveProof : (isActive (fiberLifecycle fiber) = False)
            inactiveProof = rewrite life in Refl
        in (fiber ** (Refl, inactiveProof))
    advanceSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Active accumulator view = void (nothingIsNotJust checked)
    advanceSourceOwnerNotActive nameEq keyEq actor
      {before = MkSystemState ambient fibers} {afterState} tag checked |
      Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust checked)

0 activationSourceOwnerNotActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  PaperActivationStep
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) ->
  (fiber : Fiber name key value world error **
    (lookupFiber @{nameEq} (actionOwner action) (registry before) = Just fiber,
      isActive (fiberLifecycle fiber) = False))
activationSourceOwnerNotActive nameEq keyEq action tag checked
  (PaperBeginStep actionSame tagSame) =
    case actionSame of
      Refl => beginSourceOwnerNotActive nameEq keyEq _ tag checked
activationSourceOwnerNotActive nameEq keyEq action tag checked
  (PaperIterStep actionSame tagSame) =
    case actionSame of
      Refl => advanceSourceOwnerNotActive nameEq keyEq _ tag checked
activationSourceOwnerNotActive nameEq keyEq action tag checked
  (PaperFinishStep actionSame tagSame) =
    case actionSame of
      Refl => advanceSourceOwnerNotActive nameEq keyEq _ tag checked

0 valueFromProviderLookupMember :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (wanted : key) ->
  (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} provider fibers = Just fiber ->
  isJust (valueFromProvider @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} provider wanted fibers) = True ->
  memberKey @{keyEq} {value = value} wanted
    (ownedValues (fiberTable fiber)) = True
valueFromProviderLookupMember nameEq keyEq provider wanted
  (MkCoeffectContext entries unique) fiber found present
  with (lookupEntries @{nameEq} provider entries) proof observed
  valueFromProviderLookupMember nameEq keyEq provider wanted
    (MkCoeffectContext entries unique) fiber found present | Nothing =
      case found of Refl impossible
  valueFromProviderLookupMember nameEq keyEq provider wanted
    (MkCoeffectContext entries unique) fiber found present | Just observedFiber =
      case justInjective found of
        Refl => present

0 providerOfStableAfterForeignActivation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (activation : PaperActivationStep
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked)) ->
  providerOf @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} wanted (registry before) = Just provider ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True ->
  providerOf @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} wanted (registry afterState) = Just provider
providerOfStableAfterForeignActivation {name} {key} {world} {error} {value}
  nameEq keyEq wanted provider {before} {afterState} action tag checked
  activation sourceProvider afterWellFormed =
    case activationSourceOwnerNotActive nameEq keyEq action tag checked
      activation of
      (ownerFiber ** (ownerFound, ownerInactive)) =>
        let sourceSound = providerOfSound {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq keyEq wanted
              provider (registry before) sourceProvider
            0 providerFiber : Fiber name key value world error
            providerFiber = providerOfFiber sourceSound
            0 providerFound : (lookupFiber @{nameEq} provider (registry before) =
              Just providerFiber)
            providerFound = providerOfLookup sourceSound
            0 providerActive : (isActive (fiberLifecycle providerFiber) = True)
            providerActive = providerOfActive sourceSound
            0 providerMember : (memberKey @{keyEq} wanted
              (ownedValues (fiberTable providerFiber)) = True)
            providerMember = valueFromProviderLookupMember nameEq keyEq
              provider wanted (registry before) providerFiber providerFound
              (providerOfValue sourceSound)
            0 providerCandidateSource : (providerCandidate @{keyEq}
              {value = value} {world = world} {error = error} wanted providerFiber =
              True)
            providerCandidateSource = rewrite providerActive in
              rewrite providerMember in Refl
            0 providerDistinct : Not (provider = actionOwner action)
            providerDistinct same =
              let 0 ownerFoundAtProvider : (lookupFiber @{nameEq} provider
                    (registry before) = Just ownerFiber)
                  ownerFoundAtProvider = replace
                    {p = \candidate => lookupFiber @{nameEq} candidate
                      (registry before) = Just ownerFiber}
                    (sym same) ownerFound
                  fiberSame : providerFiber = ownerFiber
                  fiberSame = justInjective
                    (trans (sym providerFound) ownerFoundAtProvider)
                  0 providerInactive : (isActive (fiberLifecycle providerFiber) =
                    False)
                  providerInactive = replace
                    {p = \fiber => isActive (fiberLifecycle fiber) = False}
                    (sym fiberSame) ownerInactive
              in case trans (sym providerActive) providerInactive of Refl impossible
            0 raw : (applyAction @{nameEq} @{keyEq} action before =
              Just (tag, afterState))
            raw = checkedActionProjects nameEq keyEq action before afterState
              tag checked
            0 update : SystemLocalUpdate name key world error value nameEq
              (actionOwner action) before afterState
            update = applyActionLocalUpdate nameEq keyEq action before
              afterState tag raw
            0 targetProviderFound : (lookupFiber @{nameEq} provider
              (registry afterState) = Just providerFiber)
            targetProviderFound = trans
              (systemLocalUpdateForeign nameEq provider (actionOwner action)
                providerDistinct before afterState update)
              providerFound
            0 pairwise : (pairwiseProvisionInvariant @{keyEq} {value = value}
              {world = world} {error = error}
              (bindings (registry afterState)) = True)
            pairwise = registryWellFormedPairwiseOpenAnchor nameEq keyEq
              afterState afterWellFormed
            0 providerEntry : (Elem (Bind provider providerFiber)
              (bindings (registry afterState)))
            providerEntry = lookupEntryElemOpenAnchor nameEq provider
              (bindings (registry afterState)) providerFiber
              (lookupFiberEntries nameEq provider providerFiber
                (registry afterState) targetProviderFound)
            0 providerDeclares : (Elem wanted (dependencies
              (componentProvisions (fiberComponent providerFiber))))
            providerDeclares = ownedSound (fiberTable providerFiber) wanted
              (memberKeyTrueElemOpenAnchor keyEq wanted
                (ownedValues (fiberTable providerFiber)) providerMember)
        in case providerInCandidateExists nameEq keyEq wanted provider providerFiber
          (bindings (registry afterState))
          (lookupFiberEntries nameEq provider providerFiber
            (registry afterState) targetProviderFound)
          providerCandidateSource of
          (chosen ** chosenFound) =>
            let chosenSound = providerOfSound {name = name} {key = key}
                  {world = world} {error = error} {value = value} nameEq keyEq wanted
                  chosen (registry afterState) chosenFound
                0 chosenFiber : Fiber name key value world error
                chosenFiber = providerOfFiber chosenSound
                0 chosenFoundInRegistry : (lookupFiber @{nameEq} chosen
                  (registry afterState) = Just chosenFiber)
                chosenFoundInRegistry = providerOfLookup chosenSound
                0 chosenEntry : (Elem (Bind chosen chosenFiber)
                  (bindings (registry afterState)))
                chosenEntry = lookupEntryElemOpenAnchor nameEq chosen
                  (bindings (registry afterState)) chosenFiber
                  (lookupFiberEntries nameEq chosen chosenFiber
                    (registry afterState) chosenFoundInRegistry)
                0 chosenMember : (memberKey @{keyEq} wanted
                  (ownedValues (fiberTable chosenFiber)) = True)
                chosenMember = valueFromProviderLookupMember nameEq keyEq
                  chosen wanted (registry afterState) chosenFiber
                  chosenFoundInRegistry (providerOfValue chosenSound)
                0 chosenDeclares : (Elem wanted (dependencies
                  (componentProvisions (fiberComponent chosenFiber))))
                chosenDeclares = ownedSound (fiberTable chosenFiber) wanted
                  (memberKeyTrueElemOpenAnchor keyEq wanted
                    (ownedValues (fiberTable chosenFiber)) chosenMember)
                0 chosenSame : (chosen = provider)
                chosenSame = pairwiseSharedProvisionSameName keyEq
                  (bindings (registry afterState)) pairwise chosen provider
                  chosenFiber providerFiber chosenEntry providerEntry wanted
                  chosenDeclares providerDeclares
            in trans chosenFound (cong Just chosenSame)

0 resolveViewStableAfterForeignActivation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (activation : PaperActivationStep
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked)) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True ->
  resolveView @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps (registry before) = Just view ->
  resolveView @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} deps (registry afterState) = Just view
resolveViewStableAfterForeignActivation nameEq keyEq [] EmptyView action tag
  checked activation afterWellFormed sourceResolved = Refl
resolveViewStableAfterForeignActivation {name} {key} {world} {error} {value}
  nameEq keyEq (wanted :: restDeps) view {before} {afterState} action tag
  checked activation afterWellFormed sourceResolved
  with (providerOf @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} wanted (registry before)) proof sourceProvider
  resolveViewStableAfterForeignActivation {name} {key} {world} {error} {value}
    nameEq keyEq (wanted :: restDeps) view {before} {afterState} action tag
    checked activation afterWellFormed sourceResolved | Nothing =
      case sourceResolved of Refl impossible
  resolveViewStableAfterForeignActivation {name} {key} {world} {error} {value}
    nameEq keyEq (wanted :: restDeps) view {before} {afterState} action tag
    checked activation afterWellFormed sourceResolved | Just provider
    with (resolveView @{nameEq} @{keyEq} {value = value} {world = world}
      {error = error} restDeps (registry before)) proof sourceRest
    resolveViewStableAfterForeignActivation {name} {key} {world} {error} {value}
      nameEq keyEq (wanted :: restDeps) view {before} {afterState} action tag
      checked activation afterWellFormed sourceResolved | Just provider |
      Nothing = case sourceResolved of Refl impossible
    resolveViewStableAfterForeignActivation {name} {key} {world} {error} {value}
      nameEq keyEq (wanted :: restDeps) view {before} {afterState} action tag
      checked activation afterWellFormed sourceResolved | Just provider |
      Just restView =
        case justInjective sourceResolved of
          Refl =>
            let 0 targetProvider = providerOfStableAfterForeignActivation
                  nameEq keyEq wanted provider action tag checked activation
                  sourceProvider afterWellFormed
                0 targetRest = resolveViewStableAfterForeignActivation
                  nameEq keyEq restDeps restView action tag checked activation
                  afterWellFormed sourceRest
            in rewrite targetProvider in rewrite targetRest in Refl

0 targetFiberStableAfterForeignActivation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (activation : PaperActivationStep
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked)) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True ->
  targetFiber @{nameEq} @{keyEq} fiber (registry before) = Just view ->
  targetFiber @{nameEq} @{keyEq} fiber (registry afterState) = Just view
targetFiberStableAfterForeignActivation {name} {key} {world} {error} {value}
  nameEq keyEq fiber view {before} {afterState} action tag checked activation
  afterWellFormed sourceTarget with (retired fiber)
  targetFiberStableAfterForeignActivation {name} {key} {world} {error} {value}
    nameEq keyEq fiber view {before} {afterState} action tag checked activation
    afterWellFormed sourceTarget | True =
      case sourceTarget of Refl impossible
  targetFiberStableAfterForeignActivation {name} {key} {world} {error} {value}
    nameEq keyEq fiber view {before} {afterState} action tag checked activation
    afterWellFormed sourceTarget | False =
      resolveViewStableAfterForeignActivation nameEq keyEq
        (dependencies (componentDependencies (fiberComponent fiber))) view
        action tag checked activation afterWellFormed sourceTarget

0 localViewEqRefl : (nameEq : DecEq name) -> (view : View name deps) ->
  viewEq @{nameEq} view view = True
localViewEqRefl nameEq EmptyView = Refl
localViewEqRefl nameEq (ProviderView provider rest)
  with (decEq @{nameEq} provider provider)
  localViewEqRefl nameEq (ProviderView provider rest) | Yes Refl =
    localViewEqRefl nameEq rest
  localViewEqRefl nameEq (ProviderView provider rest) | No contra =
    void (contra Refl)

0 localViewEqTrueEqual : (nameEq : DecEq name) ->
  (left, right : View name deps) -> viewEq @{nameEq} left right = True ->
  left = right
localViewEqTrueEqual nameEq EmptyView EmptyView valid = Refl
localViewEqTrueEqual nameEq (ProviderView left leftRest)
  (ProviderView right rightRest) valid with (decEq @{nameEq} left right)
  localViewEqTrueEqual nameEq (ProviderView right leftRest)
    (ProviderView right rightRest) valid | Yes Refl =
      cong (ProviderView right)
        (localViewEqTrueEqual nameEq leftRest rightRest valid)
  localViewEqTrueEqual nameEq (ProviderView left leftRest)
    (ProviderView right rightRest) valid | No distinct =
      case valid of Refl impossible

0 targetMatchesExact : (nameEq : DecEq name) ->
  (candidate : Maybe (View name deps)) -> (view : View name deps) ->
  targetMatches @{nameEq} candidate view = True -> candidate = Just view
targetMatchesExact nameEq Nothing view matches = case matches of Refl impossible
targetMatchesExact nameEq (Just target) view matches =
  cong Just (localViewEqTrueEqual nameEq target view matches)

record RawActivationMove
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error) (tag : RuleTag)
  (before : SystemState name key value world error) where
  constructor MkRawActivationMove
  rawActivationAfter : SystemState name key value world error
  0 rawActivationRuns : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, rawActivationAfter)

0 localIsSelectedParent : DecEq name -> name -> Parent name -> Bool
localIsSelectedParent nameEq selected Root = False
localIsSelectedParent nameEq selected (ChildOf candidate) =
  case decEq @{nameEq} selected candidate of
    Yes Refl => True
    No different => False

0 localIsChildOfParentEquation :
  (nameEq : DecEq name) -> (selected, observed : name) ->
  (fiber : Fiber name key value world error) ->
  isChildOf @{nameEq} selected (Bind observed fiber) =
    localIsSelectedParent nameEq selected (fiberParent fiber)
localIsChildOfParentEquation nameEq selected observed
  (MkFiber component Root retiredFlag table lifecycle) = Refl
localIsChildOfParentEquation nameEq selected observed
  (MkFiber component (ChildOf candidate) retiredFlag table lifecycle)
  with (decEq @{nameEq} selected candidate)
  localIsChildOfParentEquation nameEq candidate observed
    (MkFiber component (ChildOf candidate) retiredFlag table lifecycle) |
    Yes Refl = Refl
  localIsChildOfParentEquation nameEq selected observed
    (MkFiber component (ChildOf candidate) retiredFlag table lifecycle) |
    No different = Refl

0 localIsChildOfSameParent :
  (nameEq : DecEq name) -> (selected, observed : name) ->
  (next, old : Fiber name key value world error) ->
  fiberParent next = fiberParent old ->
  isChildOf @{nameEq} selected (Bind observed next) =
    isChildOf @{nameEq} selected (Bind observed old)
localIsChildOfSameParent nameEq selected observed next old sameParent =
  trans (localIsChildOfParentEquation nameEq selected observed next)
    (trans (cong (localIsSelectedParent nameEq selected) sameParent)
      (sym (localIsChildOfParentEquation nameEq selected observed old)))

0 hasChildInStaticReplacement :
  (nameEq : DecEq name) -> (selected, changed : name) ->
  (next, old : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} changed entries = Just old ->
  fiberParent next = fiberParent old ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected
    (replaceEntries @{nameEq} changed next entries) =
  hasChildIn @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected entries
hasChildInStaticReplacement nameEq selected changed next old [] found sameParent =
  case found of Refl impossible
hasChildInStaticReplacement nameEq selected changed next old
  (Bind current observed :: rest) found sameParent
  with (decEq @{nameEq} changed current) proof changedCurrent
  hasChildInStaticReplacement nameEq selected current next old
    (Bind current observed :: rest) found sameParent | Yes Refl =
      rewrite localIsChildOfSameParent nameEq selected current next observed
        (trans sameParent (cong fiberParent (sym (justInjective found)))) in Refl
  hasChildInStaticReplacement nameEq selected changed next old
    (Bind current observed :: rest) found sameParent | No different =
      cong (isChildOf @{nameEq} selected (Bind current observed) ||)
        (hasChildInStaticReplacement nameEq selected changed next old rest found
          sameParent)

0 hasChildStaticReplacement :
  (nameEq : DecEq name) -> (selected, changed : name) ->
  (next, old : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} changed source = Just old ->
  fiberParent next = fiberParent old ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected
    (replaceBinding @{nameEq} changed next source) =
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected source
hasChildStaticReplacement nameEq selected changed next old
  (MkCoeffectContext entries unique) found sameParent =
    hasChildInStaticReplacement nameEq selected changed next old entries found
      sameParent

0 lookupBeforeForeignReplacement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (wanted, changed : name) ->
  Not (wanted = changed) ->
  (next : Fiber name key value world error) ->
  (source, after : Registry name key value world error) ->
  after = replaceBinding @{nameEq} changed next source ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted source =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} wanted after
lookupBeforeForeignReplacement {name} {key} {world} {error} {value}
  nameEq wanted changed distinct next source after afterShape =
    trans (sym (lookupReplaceOther @{nameEq} {key = name}
      {value = FiberAt name key value world error} wanted changed distinct next
      source))
      (sym (cong (lookupFiber @{nameEq} {name = name} {key = key}
        {value = value} {world = world} {error = error} wanted) afterShape))

0 orchestrationRawAfterForeignReplacement :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceAfter : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (sourceAmbient, movedAmbient : world) ->
  (source : Registry name key value world error) ->
  (changed : name) -> (next, old : Fiber name key value world error) ->
  (oldFound : lookupFiber @{nameEq} changed source = Just old) ->
  (staticComponent : fiberComponent next = fiberComponent old) ->
  (staticParent : fiberParent next = fiberParent old) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action
    (MkSystemState sourceAmbient source) = Just (tag, sourceAfter)) ->
  (paper : PaperOrchestrationStep
    (Fired {before = MkSystemState sourceAmbient source}
      {afterState = sourceAfter} nameEq keyEq action tag sourceChecked)) ->
  Not (actionOwner action = changed) ->
  RawActivationMove nameEq keyEq action tag
    (MkSystemState movedAmbient
      (replaceBinding @{nameEq} changed next source))
orchestrationRawAfterForeignReplacement {name} {key} {world} {error} {value}
  nameEq keyEq action tag sourceAmbient movedAmbient source changed next old
  oldFound staticComponent staticParent sourceChecked
  (PaperInsertStep {actor} {parent} {component} actionSame) distinct =
    case actionSame of
      Refl =>
        let sourceRaw = checkedActionProjects nameEq keyEq
              (OInsert actor parent component) (MkSystemState sourceAmbient source)
              sourceAfter tag sourceChecked
        in case foreignInsertPlanView nameEq keyEq actor parent component
          sourceAmbient source tag sourceAfter sourceRaw of
          MkForeignInsertPlanView absent guards =>
            let movedRegistry : Registry name key value world error
                movedRegistry = replaceBinding @{nameEq} changed next source
                0 movedAbsent : lookupFiber @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor
                  movedRegistry = Nothing
                movedAbsent = trans
                  (lookupReplaceOther actor changed distinct next source) absent
                0 parentSame : parentPresent @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} parent
                  movedRegistry = parentPresent @{nameEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  parent source
                parentSame = parentPresentStaticReplacement nameEq parent changed
                  next old source oldFound
                0 provisionsSame : provisionsDisjointFrom @{keyEq}
                    {name = name} {key = key} {value = value} {world = world}
                    {error = error} (componentProvisions component)
                    (bindings movedRegistry) = provisionsDisjointFrom @{keyEq}
                    {name = name} {key = key} {value = value} {world = world}
                    {error = error} (componentProvisions component)
                    (bindings source)
                provisionsSame = provisionsDisjointStaticReplacement nameEq keyEq
                  (componentProvisions component) changed next old source oldFound
                  staticComponent
                0 movedGuards : (parentPresent @{nameEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  parent movedRegistry && provisionsDisjointFrom @{keyEq}
                    {name = name} {key = key} {value = value} {world = world}
                    {error = error} (componentProvisions component)
                    (bindings movedRegistry) = True)
                movedGuards = rewrite parentSame in rewrite provisionsSame in guards
            in case setFreshFromAbsent nameEq actor (freshFiber component parent)
              movedRegistry movedAbsent of
              (applied ** inserted) =>
                let movedAfter : SystemState name key value world error
                    movedAfter = MkSystemState movedAmbient (coeffectAfter applied)
                    0 movedRaw : applyAction @{nameEq} @{keyEq}
                      (OInsert actor parent component)
                      (MkSystemState movedAmbient movedRegistry) =
                      Just (OInsertTag, movedAfter)
                    movedRaw = rewrite movedGuards in rewrite inserted in Refl
                in MkRawActivationMove movedAfter movedRaw
orchestrationRawAfterForeignReplacement {name} {key} {world} {error} {value}
  nameEq keyEq action tag sourceAmbient movedAmbient source changed next old
  oldFound staticComponent staticParent sourceChecked
  (PaperRetireStep {actor} actionSame) distinct = case actionSame of
    Refl =>
      let sourceRaw = checkedActionProjects nameEq keyEq (ORetire actor)
            (MkSystemState sourceAmbient source) sourceAfter tag sourceChecked
      in case retireSuccessView nameEq keyEq actor sourceAmbient source tag
        sourceAfter sourceRaw of
        MkRetireSuccessView actorFiber actorFound =>
          let movedRegistry : Registry name key value world error
              movedRegistry = replaceBinding @{nameEq} changed next source
              0 movedFound : lookupFiber @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} actor
                movedRegistry = Just actorFiber
              movedFound = trans
                (lookupReplaceOther actor changed distinct next source) actorFound
              movedAfter : SystemState name key value world error
              movedAfter = MkSystemState movedAmbient
                (replaceBinding @{nameEq} actor (retireFiber actorFiber)
                  movedRegistry)
              0 movedRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
                (MkSystemState movedAmbient movedRegistry) =
                Just (ORetireTag, movedAfter)
              movedRaw = rewrite movedFound in Refl
          in MkRawActivationMove movedAfter movedRaw
orchestrationRawAfterForeignReplacement {name} {key} {world} {error} {value}
  nameEq keyEq action tag sourceAmbient movedAmbient source changed next old
  oldFound staticComponent staticParent sourceChecked
  (PaperRemoveStep {actor} actionSame) distinct = case actionSame of
    Refl =>
      let sourceRaw = checkedActionProjects nameEq keyEq (ORemove actor)
            (MkSystemState sourceAmbient source) sourceAfter tag sourceChecked
      in case removeSuccessView nameEq keyEq actor sourceAmbient source tag
        sourceAfter sourceRaw of
        MkRemoveSuccessView actorFiber actorFound removable noChild =>
          let movedRegistry : Registry name key value world error
              movedRegistry = replaceBinding @{nameEq} changed next source
              0 movedFound : lookupFiber @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} actor
                movedRegistry = Just actorFiber
              movedFound = trans
                (lookupReplaceOther actor changed distinct next source) actorFound
              0 movedNoChild : hasChild @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} actor
                movedRegistry = False
              movedNoChild = hasChildReplaceFalse nameEq actor changed next old
                source oldFound staticParent noChild
              0 normalizedGuard : (retired actorFiber &&
                isInactive (fiberLifecycle actorFiber) && not False = True)
              normalizedGuard = replace
                {p = \child => retired actorFiber &&
                  isInactive (fiberLifecycle actorFiber) && not child = True}
                noChild removable
              0 movedGuard : (retired actorFiber &&
                isInactive (fiberLifecycle actorFiber) &&
                not (hasChild @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor
                  movedRegistry) = True)
              movedGuard = rewrite movedNoChild in normalizedGuard
              movedAfter : SystemState name key value world error
              movedAfter = MkSystemState movedAmbient
                (deleteBinding @{nameEq} actor movedRegistry)
              0 movedRaw : applyAction @{nameEq} @{keyEq} (ORemove actor)
                (MkSystemState movedAmbient movedRegistry) =
                Just (ORemoveTag, movedAfter)
              movedRaw = rewrite movedFound in rewrite movedGuard in Refl
          in MkRawActivationMove movedAfter movedRaw


0 paperOrchestrationNonLifecycle :
  {transition : Transition before afterState} ->
  PaperOrchestrationStep transition ->
  isLifecycleAction (transitionAction transition) = False
paperOrchestrationNonLifecycle
  {transition = Fired nameEq keyEq action tag checked}
  (PaperInsertStep actionSame) = case actionSame of Refl => Refl
paperOrchestrationNonLifecycle
  {transition = Fired nameEq keyEq action tag checked}
  (PaperRetireStep actionSame) = case actionSame of Refl => Refl
paperOrchestrationNonLifecycle
  {transition = Fired nameEq keyEq action tag checked}
  (PaperRemoveStep actionSame) = case actionSame of Refl => Refl

0 localForeignInsertViewTag : (tag : RuleTag) ->
  ForeignInsertPlanView name key world error value nameEq keyEq actor parent
    component ambient source tag afterState -> tag = OInsertTag
localForeignInsertViewTag OInsertTag
  (MkForeignInsertPlanView absent guards) = Refl

0 localRetireViewTag : (tag : RuleTag) ->
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState -> tag = ORetireTag
localRetireViewTag ORetireTag (MkRetireSuccessView fiber found) = Refl

0 localRemoveViewTag : (tag : RuleTag) ->
  RemoveSuccessView name key world error value nameEq actor ambient source tag
    afterState -> tag = ORemoveTag
localRemoveViewTag ORemoveTag
  (MkRemoveSuccessView fiber found guard noChild) = Refl

0 localOrchestrationSuccessfulTagsSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftBefore, leftAfter : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (leftTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} action leftBefore =
    Just (leftTag, leftAfter)) ->
  (rightBefore, rightAfter : SystemState name key value world error) ->
  (rightTag : RuleTag) ->
  (rightRaw : applyAction @{nameEq} @{keyEq} action rightBefore =
    Just (rightTag, rightAfter)) ->
  leftTag = rightTag
localOrchestrationSuccessfulTagsSame nameEq keyEq
  (OInsert actor parent component) orchestration leftTag leftChecked
  (MkSystemState rightWorld rightRegistry) rightAfter rightTag rightRaw =
    let leftRaw = checkedActionProjects nameEq keyEq
          (OInsert actor parent component) leftBefore leftAfter leftTag
          leftChecked
    in case leftBefore of
      MkSystemState leftWorld leftRegistry =>
        case foreignInsertPlanView nameEq keyEq actor parent component
          leftWorld leftRegistry leftTag leftAfter leftRaw of
          MkForeignInsertPlanView leftAbsent leftGuards =>
            case foreignInsertPlanView nameEq keyEq actor parent component
              rightWorld rightRegistry rightTag rightAfter rightRaw of
              MkForeignInsertPlanView rightAbsent rightGuards => Refl
localOrchestrationSuccessfulTagsSame nameEq keyEq (ORetire actor)
  orchestration leftTag leftChecked (MkSystemState rightWorld rightRegistry)
  rightAfter rightTag rightRaw =
    let leftRaw = checkedActionProjects nameEq keyEq (ORetire actor)
          leftBefore leftAfter leftTag leftChecked
    in case leftBefore of
      MkSystemState leftWorld leftRegistry =>
        case retireSuccessView nameEq keyEq actor leftWorld leftRegistry
          leftTag leftAfter leftRaw of
          MkRetireSuccessView leftFiber leftFound =>
            case retireSuccessView nameEq keyEq actor rightWorld rightRegistry
              rightTag rightAfter rightRaw of
              MkRetireSuccessView rightFiber rightFound => Refl
localOrchestrationSuccessfulTagsSame nameEq keyEq (ORemove actor)
  orchestration leftTag leftChecked (MkSystemState rightWorld rightRegistry)
  rightAfter rightTag rightRaw =
    let leftRaw = checkedActionProjects nameEq keyEq (ORemove actor)
          leftBefore leftAfter leftTag leftChecked
    in case leftBefore of
      MkSystemState leftWorld leftRegistry =>
        case removeSuccessView nameEq keyEq actor leftWorld leftRegistry
          leftTag leftAfter leftRaw of
          MkRemoveSuccessView leftFiber leftFound leftGuard leftNoChild =>
            case removeSuccessView nameEq keyEq actor rightWorld rightRegistry
              rightTag rightAfter rightRaw of
              MkRemoveSuccessView rightFiber rightFound rightGuard
                rightNoChild => Refl
localOrchestrationSuccessfulTagsSame nameEq keyEq (LBegin actor) Refl leftTag
  leftChecked rightBefore rightAfter rightTag rightRaw impossible
localOrchestrationSuccessfulTagsSame nameEq keyEq (LAdvance actor) Refl leftTag
  leftChecked rightBefore rightAfter rightTag rightRaw impossible
localOrchestrationSuccessfulTagsSame nameEq keyEq (LDivert actor) Refl leftTag
  leftChecked rightBefore rightAfter rightTag rightRaw impossible
localOrchestrationSuccessfulTagsSame nameEq keyEq (LLeave actor) Refl leftTag
  leftChecked rightBefore rightAfter rightTag rightRaw impossible
localOrchestrationSuccessfulTagsSame nameEq keyEq (LUnload actor) Refl leftTag
  leftChecked rightBefore rightAfter rightTag rightRaw impossible

0 insertionParentOutsideFromLaterRemove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (removed : name) -> (rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (ORemove removed)
    middle = Just (rightTag, originalFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  InsertionParentOutside leftAction removed
insertionParentOutsideFromLaterRemove {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  leftAction leftTag removed rightTag leftChecked rightChecked
  (PaperInsertStep {actor} {parent = Root} {component} actionSame) =
    case actionSame of Refl => ()
insertionParentOutsideFromLaterRemove {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  leftAction leftTag removed rightTag leftChecked rightChecked
  (PaperInsertStep {actor} {parent = ChildOf parent} {component} actionSame) =
    case actionSame of
      Refl =>
        let 0 leftRaw = checkedActionProjects nameEq keyEq
              (OInsert actor (ChildOf parent) component)
              (MkSystemState ambient source) middle leftTag leftChecked
        in case foreignInsertPlanView nameEq keyEq actor (ChildOf parent)
          component ambient source leftTag middle leftRaw of
          leftView@(MkForeignInsertPlanView leftAbsent leftGuards) =>
            let middleRegistry : Registry name key value world error
                middleRegistry = insertBinding @{nameEq} actor
                  (freshFiber component (ChildOf parent)) source leftAbsent
                0 rightRaw : applyAction @{nameEq} @{keyEq} (ORemove removed)
                  (MkSystemState ambient middleRegistry) =
                  Just (rightTag, originalFinal)
                rightRaw = checkedActionProjects nameEq keyEq
                  (ORemove removed) middle originalFinal rightTag rightChecked
            in case removeSuccessView nameEq keyEq removed ambient
              middleRegistry rightTag originalFinal rightRaw of
              MkRemoveSuccessView removedFiber removedFound removable
                removedNoChild =>
                  \same => noChildLookupParentDistinct nameEq removed actor
                    (freshFiber component (ChildOf parent)) middleRegistry
                    removedNoChild (foreignInsertTargetFound leftView)
                    (cong ChildOf same)
insertionParentOutsideFromLaterRemove nameEq keyEq leftAction leftTag removed
  rightTag leftChecked rightChecked (PaperRetireStep actionSame) =
    case actionSame of Refl => ()
insertionParentOutsideFromLaterRemove nameEq keyEq leftAction leftTag removed
  rightTag leftChecked rightChecked (PaperRemoveStep actionSame) =
    case actionSame of Refl => ()

0 localAndLeftTrueO5 : (left, right : Bool) ->
  left && right = True -> left = True
localAndLeftTrueO5 False right both = case both of Refl impossible
localAndLeftTrueO5 True right both = Refl

0 localAndRightTrueO5 : (left, right : Bool) ->
  left && right = True -> right = True
localAndRightTrueO5 False right both = case both of Refl impossible
localAndRightTrueO5 True False both = case both of Refl impossible
localAndRightTrueO5 True True both = Refl

0 localElemDecTrueElemO5 : DecEq a => (wanted : a) -> (values : List a) ->
  elemDec wanted values = True -> Elem wanted values
localElemDecTrueElemO5 wanted [] present = case present of Refl impossible
localElemDecTrueElemO5 wanted (current :: rest) present
  with (decEq wanted current)
  localElemDecTrueElemO5 current (current :: rest) present | Yes Refl = Here
  localElemDecTrueElemO5 wanted (current :: rest) present | No distinct =
    There (localElemDecTrueElemO5 wanted rest present)

0 localElemDecFromElemO5 : (eq : DecEq a) -> (candidate : a) ->
  (values : List a) -> Elem candidate values ->
  elemDec @{eq} candidate values = True
localElemDecFromElemO5 eq candidate (candidate :: later) Here
  with (decEq @{eq} candidate candidate)
  localElemDecFromElemO5 eq candidate (candidate :: later) Here | Yes Refl = Refl
  localElemDecFromElemO5 eq candidate (candidate :: later) Here | No contra =
    void (contra Refl)
localElemDecFromElemO5 eq candidate (current :: later) (There member)
  with (decEq @{eq} candidate current)
  localElemDecFromElemO5 eq current (current :: later) (There member) |
    Yes Refl = Refl
  localElemDecFromElemO5 eq candidate (current :: later) (There member) |
    No distinct = localElemDecFromElemO5 eq candidate later member

0 localFoldlOrTrueO5 : (predicate : a -> Bool) -> (values : List a) ->
  foldl (\accepted, value => accepted || predicate value) True values = True
localFoldlOrTrueO5 predicate [] = Refl
localFoldlOrTrueO5 predicate (value :: rest) =
  localFoldlOrTrueO5 predicate rest

0 localSharedAnyO5 : (eq : DecEq a) -> (wanted : a) ->
  (left, right : List a) -> Elem wanted left -> Elem wanted right ->
  any (\candidate => elemDec @{eq} candidate right) left = True
localSharedAnyO5 eq wanted (wanted :: rest) right Here rightMember =
  rewrite localElemDecFromElemO5 eq wanted right rightMember in
    localFoldlOrTrueO5 (\candidate => elemDec @{eq} candidate right) rest
localSharedAnyO5 eq wanted (current :: rest) right (There leftMember)
  rightMember with (elemDec @{eq} current right)
  localSharedAnyO5 eq wanted (current :: rest) right (There leftMember)
    rightMember | True =
      localFoldlOrTrueO5 (\candidate => elemDec @{eq} candidate right) rest
  localSharedAnyO5 eq wanted (current :: rest) right (There leftMember)
    rightMember | False = localSharedAnyO5 eq wanted rest right leftMember
      rightMember

0 localOverlapWitnessO5 : DecEq a => (left, right : List a) ->
  any (\candidate => elemDec candidate right) left = True ->
  (wanted : a ** (Elem wanted left, Elem wanted right))
localOverlapWitnessO5 [] right overlap = case overlap of Refl impossible
localOverlapWitnessO5 (current :: rest) right overlap
  with (elemDec current right) proof currentMember
  localOverlapWitnessO5 (current :: rest) right overlap | True =
    (current ** (Here, localElemDecTrueElemO5 current right currentMember))
  localOverlapWitnessO5 (current :: rest) right overlap | False =
    case localOverlapWitnessO5 rest right overlap of
      (wanted ** (leftMember, rightMember)) =>
        (wanted ** (There leftMember, rightMember))

0 localProvisionOverlapFalseSymmetricO5 :
  (keyEq : DecEq key) -> (left, right : CoeffectSpec key) ->
  provisionOverlap @{keyEq} right left = False ->
  provisionOverlap @{keyEq} left right = False
localProvisionOverlapFalseSymmetricO5 keyEq
  (MkCoeffectSpec left leftUnique) (MkCoeffectSpec right rightUnique)
  reverseFalse with (any (\candidate => elemDec candidate right) left)
    proof forward
  localProvisionOverlapFalseSymmetricO5 keyEq
    (MkCoeffectSpec left leftUnique) (MkCoeffectSpec right rightUnique)
    reverseFalse | False = Refl
  localProvisionOverlapFalseSymmetricO5 keyEq
    (MkCoeffectSpec left leftUnique) (MkCoeffectSpec right rightUnique)
    reverseFalse | True =
      case localOverlapWitnessO5 left right forward of
        (wanted ** (leftMember, rightMember)) =>
          let 0 reverseTrue : Equal
                (any (\candidate => elemDec @{keyEq} candidate left) right) True
              reverseTrue = localSharedAnyO5 keyEq wanted right left rightMember
                leftMember
          in case trans (sym reverseTrue) reverseFalse of Refl impossible

0 localLookupNotElemNothingO5 : (eq : DecEq a) -> (wanted : a) ->
  (entries : List (Binding a value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries @{eq} wanted entries = Nothing
localLookupNotElemNothingO5 eq wanted [] absent = Refl
localLookupNotElemNothingO5 eq wanted (Bind current observed :: rest) absent
  with (decEq @{eq} wanted current)
  localLookupNotElemNothingO5 eq current (Bind current observed :: rest) absent |
    Yes Refl = void (absent Here)
  localLookupNotElemNothingO5 eq wanted (Bind current observed :: rest) absent |
    No distinct = localLookupNotElemNothingO5 eq wanted rest
      (\later => absent (There later))

0 localLookupDeleteEntriesSelfO5 : (eq : DecEq a) -> (removed : a) ->
  (entries : List (Binding a value)) ->
  UniqueKeys (bindingKeys entries) ->
  lookupEntries @{eq} removed (deleteEntries @{eq} removed entries) = Nothing
localLookupDeleteEntriesSelfO5 eq removed [] UniqueNil = Refl
localLookupDeleteEntriesSelfO5 eq removed (Bind current observed :: rest)
  (UniqueCons currentAbsent restUnique)
  with (decEq @{eq} removed current) proof compared
  localLookupDeleteEntriesSelfO5 eq current
    (Bind current observed :: rest) (UniqueCons currentAbsent restUnique) |
    Yes Refl = localLookupNotElemNothingO5 eq current rest currentAbsent
  localLookupDeleteEntriesSelfO5 eq removed
    (Bind current observed :: rest) (UniqueCons currentAbsent restUnique) |
    No distinct = rewrite compared in
      localLookupDeleteEntriesSelfO5 eq removed rest restUnique

0 localLookupDeleteSelfO5 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed : name) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed
    (deleteBinding @{nameEq} removed source) = Nothing
localLookupDeleteSelfO5 nameEq removed
  (MkCoeffectContext entries unique) =
    localLookupDeleteEntriesSelfO5 nameEq removed entries unique

||| Deleting the same owner from independently ordered pointwise registries
||| preserves control. The self branch deliberately exposes both entry lists
||| and uniqueness proofs so the producer's exact `nameEq` remains visible to
||| `localLookupDeleteEntriesSelfO5`.
0 pointwiseControlAfterDelete :
  (nameEq : DecEq name) -> (actor : name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld leftRegistry)
    (MkSystemState rightWorld rightRegistry) ->
  ControlEquivalent name key world error value nameEq
    (MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))
    (MkSystemState rightWorld (deleteBinding @{nameEq} actor rightRegistry))
pointwiseControlAfterDelete nameEq actor leftWorld rightWorld
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) controls =
    MkControlEquivalent pointwise
  where
  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (lookupFiber @{nameEq} selected
      (deleteBinding @{nameEq} actor
        (MkCoeffectContext leftEntries leftUnique)))
    (lookupFiber @{nameEq} selected
      (deleteBinding @{nameEq} actor
        (MkCoeffectContext rightEntries rightUnique)))
  pointwise selected with (decEq @{nameEq} selected actor)
    pointwise selected | Yes same = case same of
      Refl =>
        rewrite localLookupDeleteEntriesSelfO5 nameEq actor leftEntries leftUnique in
        rewrite localLookupDeleteEntriesSelfO5 nameEq actor rightEntries rightUnique in
          NoControlFibers
    pointwise selected | No distinct =
      rewrite lookupDeleteOther selected actor distinct
        (MkCoeffectContext leftEntries leftUnique) in
      rewrite lookupDeleteOther selected actor distinct
        (MkCoeffectContext rightEntries rightUnique) in
        controlPointwise controls selected

0 localLookupReplaceSelfO5 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (old, next : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} actor source = Just old ->
  lookupFiber @{nameEq} actor
    (replaceBinding @{nameEq} actor next source) = Just next
localLookupReplaceSelfO5 nameEq actor old next
  (MkCoeffectContext entries unique) found =
    DGamma.Coeffects.lookupReplaceEntries @{nameEq}
      {value = FiberAt name key value world error} actor old next entries found

0 localParentPresentTransportO5 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (selected : name) ->
  (source : Registry name key value world error) ->
  parent = ChildOf selected ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent source = True ->
  isJust (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected source) = True
localParentPresentTransportO5 nameEq (ChildOf selected) selected source Refl
  present = present

0 localIsJustNothingImpossibleO5 : {observed : Maybe a} ->
  observed = Nothing -> isJust observed = True -> Void
localIsJustNothingImpossibleO5 Refl present = case present of Refl impossible

0 localDeletedParentNotPresentO5 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed : name) ->
  (source : Registry name key value world error) ->
  isJust (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed
    (deleteBinding @{nameEq} removed source)) = True -> Void
localDeletedParentNotPresentO5 nameEq removed source present =
  localIsJustNothingImpossibleO5
    (localLookupDeleteSelfO5 nameEq removed source) present

0 localParentPresentAfterInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (inserted : name) ->
  (insertParent : Parent name) ->
  (component : Component key value world error) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} inserted source = Nothing) ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent source = True ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent
    (insertBinding @{nameEq} inserted (freshFiber component insertParent)
      source absent) = True
localParentPresentAfterInsert nameEq Root inserted insertParent component source
  absent present = Refl
localParentPresentAfterInsert nameEq (ChildOf parent) inserted insertParent
  component source absent present with (decEq @{nameEq} parent inserted)
  localParentPresentAfterInsert nameEq (ChildOf inserted) inserted insertParent
    component source absent present | Yes Refl =
      rewrite lookupInserted inserted (freshFiber component insertParent)
        source absent in Refl
  localParentPresentAfterInsert nameEq (ChildOf parent) inserted insertParent
    component source absent present | No distinct =
      rewrite lookupInsertOther parent inserted distinct
        (freshFiber component insertParent) source absent in present

0 localProvisionsDisjointAfterInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) -> (inserted : name) ->
  (insertParent : Parent name) ->
  (component : Component key value world error) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} inserted source = Nothing) ->
  provisionOverlap @{keyEq} provision (componentProvisions component) = False ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision (bindings source) = True ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision
    (bindings (insertBinding @{nameEq} inserted
      (freshFiber component insertParent) source absent)) = True
localProvisionsDisjointAfterInsert nameEq keyEq provision inserted insertParent
  component source absent pairDisjoint sourceDisjoint =
    rewrite insertBindingRuntimeBindings nameEq inserted
      (freshFiber component insertParent) source absent in
    rewrite pairDisjoint in sourceDisjoint

0 localNotTrueFalseO5 : (observed : Bool) -> not observed = True ->
  observed = False
localNotTrueFalseO5 False equation = Refl
localNotTrueFalseO5 True equation = case equation of Refl impossible

0 localParentPresentAfterDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (removed : name) ->
  ParentOutside parent removed ->
  (source : Registry name key value world error) ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent source = True ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent
    (deleteBinding @{nameEq} removed source) = True
localParentPresentAfterDelete nameEq Root removed outside source present = Refl
localParentPresentAfterDelete nameEq (ChildOf parent) removed distinct source
  present = rewrite lookupDeleteOther parent removed distinct source in present

0 orchestrationRawAfterDelete :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceAfter : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (removed : name) -> Not (actionOwner action = removed) ->
  InsertionParentOutside action removed ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action
    (MkSystemState ambient source) = Just (tag, sourceAfter)) ->
  (paper : PaperOrchestrationStep
    (Fired {before = MkSystemState ambient source} {afterState = sourceAfter}
      nameEq keyEq action tag sourceChecked)) ->
  RawActivationMove nameEq keyEq action tag
    (MkSystemState ambient (deleteBinding @{nameEq} removed source))
orchestrationRawAfterDelete {name} {key} {world} {error} {value}
  nameEq keyEq action tag ambient source removed distinct parentOutside
  sourceChecked (PaperInsertStep {actor} {parent} {component} actionSame) =
    case actionSame of
      Refl =>
        let 0 sourceRaw = checkedActionProjects nameEq keyEq
              (OInsert actor parent component) (MkSystemState ambient source)
              sourceAfter tag sourceChecked
            sourceView = foreignInsertPlanView nameEq keyEq actor parent
              component ambient source tag sourceAfter sourceRaw
            0 tagSame : Equal tag OInsertTag
            tagSame = localForeignInsertViewTag tag sourceView
        in case sourceView of
          MkForeignInsertPlanView sourceAbsent sourceGuards =>
            let target : Registry name key value world error
                target = deleteBinding @{nameEq} removed source
                0 sourceParent : parentPresent @{nameEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  parent source = True
                sourceParent = localAndLeftTrueO5 _ _ sourceGuards
                0 sourceDisjoint : provisionsDisjointFrom @{keyEq}
                  {name = name} {key = key} {value = value} {world = world}
                  {error = error} (componentProvisions component)
                  (bindings source) = True
                sourceDisjoint = localAndRightTrueO5 _ _ sourceGuards
                0 targetParent : parentPresent @{nameEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  parent target = True
                targetParent = localParentPresentAfterDelete nameEq parent
                  removed parentOutside source sourceParent
                0 deletedDisjoint : provisionsDisjointFrom @{keyEq}
                  {name = name} {key = key} {value = value} {world = world}
                  {error = error} (componentProvisions component)
                  (deleteEntries @{nameEq} removed (bindings source)) = True
                deletedDisjoint = provisionsDisjointDelete nameEq keyEq
                  (componentProvisions component) (bindings source) removed
                  sourceDisjoint
                0 targetBindings : bindings target =
                  deleteEntries @{nameEq} removed (bindings source)
                targetBindings = deleteBindingRuntimeBindings nameEq removed
                  source
                0 targetDisjoint : provisionsDisjointFrom @{keyEq}
                  {name = name} {key = key} {value = value} {world = world}
                  {error = error} (componentProvisions component)
                  (bindings target) = True
                targetDisjoint = replace
                  {p = \entries => provisionsDisjointFrom @{keyEq}
                    (componentProvisions component) entries = True}
                  (sym targetBindings) deletedDisjoint
                0 targetAbsent : lookupFiber @{nameEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  actor target = Nothing
                targetAbsent = trans
                  (lookupDeleteOther actor removed distinct source) sourceAbsent
            in case setFreshFromAbsent nameEq actor
              (freshFiber component parent) target targetAbsent of
              (applied ** inserted) =>
                let movedAfter : SystemState name key value world error
                    movedAfter = MkSystemState ambient (coeffectAfter applied)
                    0 movedRaw : applyAction @{nameEq} @{keyEq}
                      (OInsert actor parent component)
                      (MkSystemState ambient target) =
                      Just (OInsertTag, movedAfter)
                    movedRaw = rewrite targetParent in rewrite targetDisjoint in
                      rewrite inserted in Refl
                in case tagSame of
                  Refl => MkRawActivationMove movedAfter movedRaw
orchestrationRawAfterDelete {name} {key} {world} {error} {value}
  nameEq keyEq action tag ambient source removed distinct parentOutside
  sourceChecked (PaperRetireStep {actor} actionSame) = case actionSame of
    Refl =>
      let 0 sourceRaw = checkedActionProjects nameEq keyEq (ORetire actor)
            (MkSystemState ambient source) sourceAfter tag sourceChecked
          sourceView = retireSuccessView nameEq keyEq actor ambient source tag
            sourceAfter sourceRaw
          0 tagSame : Equal tag ORetireTag
          tagSame = localRetireViewTag tag sourceView
      in case sourceView of
        MkRetireSuccessView actorFiber actorFound =>
          let target : Registry name key value world error
              target = deleteBinding @{nameEq} removed source
              0 targetFound : lookupFiber @{nameEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                actor target = Just actorFiber
              targetFound = trans
                (lookupDeleteOther actor removed distinct source) actorFound
              movedAfter : SystemState name key value world error
              movedAfter = MkSystemState ambient
                (replaceBinding @{nameEq} actor (retireFiber actorFiber) target)
              0 movedRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
                (MkSystemState ambient target) = Just (ORetireTag, movedAfter)
              movedRaw = rewrite targetFound in Refl
          in case tagSame of
            Refl => MkRawActivationMove movedAfter movedRaw
orchestrationRawAfterDelete {name} {key} {world} {error} {value}
  nameEq keyEq action tag ambient source removed distinct parentOutside
  sourceChecked (PaperRemoveStep {actor} actionSame) = case actionSame of
    Refl =>
      let 0 sourceRaw = checkedActionProjects nameEq keyEq (ORemove actor)
            (MkSystemState ambient source) sourceAfter tag sourceChecked
          sourceView = removeSuccessView nameEq keyEq actor ambient source tag
            sourceAfter sourceRaw
          0 tagSame : Equal tag ORemoveTag
          tagSame = localRemoveViewTag tag sourceView
      in case sourceView of
        MkRemoveSuccessView actorFiber actorFound removable sourceNoChild =>
          let target : Registry name key value world error
              target = deleteBinding @{nameEq} removed source
              0 targetFound : lookupFiber @{nameEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                actor target = Just actorFiber
              targetFound = trans
                (lookupDeleteOther actor removed distinct source) actorFound
              0 targetNoChild : hasChild @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} actor target =
                False
              targetNoChild = hasChildDeleteFalse nameEq actor removed source
                sourceNoChild
              0 normalizedGuard : (retired actorFiber &&
                isInactive (fiberLifecycle actorFiber) && not False = True)
              normalizedGuard = replace
                {p = \child => retired actorFiber &&
                  isInactive (fiberLifecycle actorFiber) && not child = True}
                sourceNoChild removable
              0 targetGuard : (retired actorFiber &&
                isInactive (fiberLifecycle actorFiber) &&
                not (hasChild @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor target) =
                True)
              targetGuard = rewrite targetNoChild in normalizedGuard
              movedAfter : SystemState name key value world error
              movedAfter = MkSystemState ambient
                (deleteBinding @{nameEq} actor target)
              0 movedRaw : applyAction @{nameEq} @{keyEq} (ORemove actor)
                (MkSystemState ambient target) = Just (ORemoveTag, movedAfter)
              movedRaw = rewrite targetFound in rewrite targetGuard in Refl
          in case tagSame of
            Refl => MkRawActivationMove movedAfter movedRaw

0 orchestrationRawAfterCheckedRemove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (removed : name) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (ORemove removed)
    middle = Just (ORemoveTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (ORemove removed) first = Just (ORemoveTag, earlyRightFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  Not (actionOwner leftAction = removed) ->
  RawActivationMove nameEq keyEq leftAction leftTag earlyRightFinal
orchestrationRawAfterCheckedRemove {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  {earlyRightFinal} leftAction leftTag removed leftChecked rightChecked
  earlyRightChecked leftPaper distinct =
    let 0 earlyRaw = checkedActionProjects nameEq keyEq (ORemove removed)
          (MkSystemState ambient source) earlyRightFinal ORemoveTag
          earlyRightChecked
    in case removeSuccessView nameEq keyEq removed ambient source ORemoveTag
      earlyRightFinal earlyRaw of
      MkRemoveSuccessView removedFiber removedFound removable removedNoChild =>
        let canonicalEarly : SystemState name key value world error
            canonicalEarly = MkSystemState ambient
              (deleteBinding @{nameEq} removed source)
            0 earlyShape : canonicalEarly = earlyRightFinal
            earlyShape = Refl
            0 leftRaw : applyAction @{nameEq} @{keyEq} leftAction
              (MkSystemState ambient source) = Just (leftTag, middle)
            leftRaw = checkedActionProjects nameEq keyEq leftAction
              (MkSystemState ambient source) middle leftTag leftChecked
            0 parentOutside : InsertionParentOutside leftAction removed
            parentOutside = insertionParentOutsideFromLaterRemove nameEq keyEq
              leftAction leftTag removed ORemoveTag leftChecked rightChecked
              leftPaper
            0 canonicalMove : RawActivationMove nameEq keyEq leftAction leftTag
              canonicalEarly
            canonicalMove = orchestrationRawAfterDelete nameEq keyEq leftAction
              leftTag ambient source removed distinct parentOutside leftChecked
              leftPaper
        in replace
          {p = \before => RawActivationMove nameEq keyEq leftAction leftTag
            before}
          earlyShape canonicalMove

0 orchestrationRawAfterCheckedRetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, earlyRightFinal : SystemState name key value world error} ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (rightActor : name) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (ORetire rightActor) first = Just (ORetireTag, earlyRightFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  Not (actionOwner leftAction = rightActor) ->
  RawActivationMove nameEq keyEq leftAction leftTag earlyRightFinal
orchestrationRawAfterCheckedRetire {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle}
  {earlyRightFinal} leftAction leftTag rightActor leftChecked
  earlyRightChecked leftPaper distinct =
    let 0 earlyRaw = checkedActionProjects nameEq keyEq (ORetire rightActor)
          (MkSystemState ambient source) earlyRightFinal ORetireTag
          earlyRightChecked
    in case retireSuccessView nameEq keyEq rightActor ambient source ORetireTag
      earlyRightFinal earlyRaw of
      MkRetireSuccessView oldFiber oldFound =>
        orchestrationRawAfterForeignReplacement nameEq keyEq leftAction leftTag
          ambient ambient source rightActor (retireFiber oldFiber) oldFiber
          oldFound (fiberComponentRetire oldFiber)
          (fiberParentRetireHint oldFiber)
          leftChecked leftPaper distinct


0 orchestrationRawAfterCheckedInsert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (rightActor : name) -> (rightParent : Parent name) ->
  (rightComponent : Component key value world error) ->
  (rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) first =
    Just (rightTag, earlyRightFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  Not (actionOwner leftAction = rightActor) ->
  RawActivationMove nameEq keyEq leftAction leftTag earlyRightFinal
orchestrationRawAfterCheckedInsert {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  {earlyRightFinal} leftAction leftTag rightActor rightParent rightComponent
  rightTag leftChecked rightChecked earlyRightChecked leftPaper distinct =
    let 0 earlyRaw : Equal
          (applyAction @{nameEq} @{keyEq}
            (OInsert rightActor rightParent rightComponent)
            (MkSystemState ambient source))
          (Just (rightTag, earlyRightFinal))
        earlyRaw = checkedActionProjects nameEq keyEq
          (OInsert rightActor rightParent rightComponent)
          (MkSystemState ambient source) earlyRightFinal rightTag
          earlyRightChecked
        0 earlyView : ForeignInsertPlanView name key world error value nameEq
          keyEq rightActor rightParent rightComponent ambient source rightTag
          earlyRightFinal
        earlyView = foreignInsertPlanView nameEq keyEq rightActor rightParent
          rightComponent ambient source rightTag earlyRightFinal earlyRaw
        0 rightTagSame : Equal rightTag OInsertTag
        rightTagSame = localForeignInsertViewTag rightTag earlyView
        0 exactRightChecked : Equal
          (checkedApplyAction @{nameEq} @{keyEq}
            (OInsert rightActor rightParent rightComponent) middle)
          (Just (OInsertTag, originalFinal))
        exactRightChecked = replace
          {p = \observedTag => Equal
            (checkedApplyAction @{nameEq} @{keyEq}
              (OInsert rightActor rightParent rightComponent) middle)
            (Just (observedTag, originalFinal))}
          rightTagSame rightChecked
    in case earlyView of
      MkForeignInsertPlanView rightAbsent rightGuards =>
        let canonicalEarly : SystemState name key value world error
            canonicalEarly = MkSystemState ambient
              (insertBinding @{nameEq} rightActor
                (freshFiber rightComponent rightParent) source rightAbsent)
            0 earlyShape : Equal canonicalEarly earlyRightFinal
            earlyShape = Refl
            0 leftRaw : Equal
              (applyAction @{nameEq} @{keyEq} leftAction
                (MkSystemState ambient source)) (Just (leftTag, middle))
            leftRaw = checkedActionProjects nameEq keyEq leftAction
              (MkSystemState ambient source) middle leftTag leftChecked
            0 canonicalMove : RawActivationMove nameEq keyEq leftAction leftTag
              canonicalEarly
            canonicalMove = case leftPaper of
              PaperInsertStep {actor = leftActor} {parent = leftParent}
                {component = leftComponent} actionSame => case actionSame of
                Refl =>
                  let 0 sourceView : ForeignInsertPlanView name key world error
                        value nameEq keyEq leftActor leftParent leftComponent
                        ambient source leftTag middle
                      sourceView = foreignInsertPlanView nameEq keyEq leftActor
                        leftParent leftComponent ambient source leftTag middle
                        leftRaw
                      0 tagSame : Equal leftTag OInsertTag
                      tagSame = localForeignInsertViewTag leftTag sourceView
                  in case sourceView of
                    MkForeignInsertPlanView leftAbsent leftGuards =>
                      let canonicalMiddle : SystemState name key value world error
                          canonicalMiddle = MkSystemState ambient
                            (insertBinding @{nameEq} leftActor
                              (freshFiber leftComponent leftParent) source
                              leftAbsent)
                          0 middleShape : Equal canonicalMiddle middle
                          middleShape = Refl
                          0 laterRightRaw : Equal
                            (applyAction @{nameEq} @{keyEq}
                              (OInsert rightActor rightParent rightComponent)
                              middle) (Just (OInsertTag, originalFinal))
                          laterRightRaw = checkedActionProjects nameEq keyEq
                            (OInsert rightActor rightParent rightComponent)
                            middle originalFinal OInsertTag exactRightChecked
                          0 laterRightView : ForeignInsertPlanView name key
                            world error value nameEq keyEq rightActor rightParent
                            rightComponent ambient (registry middle) OInsertTag
                            originalFinal
                          laterRightView = foreignInsertPlanView nameEq keyEq
                            rightActor rightParent rightComponent ambient
                            (registry middle) OInsertTag originalFinal laterRightRaw
                      in case laterRightView of
                        MkForeignInsertPlanView laterRightAbsent
                          laterRightGuards =>
                            let target : Registry name key value world error
                                target = insertBinding @{nameEq} rightActor
                                  (freshFiber rightComponent rightParent) source
                                  rightAbsent
                                0 targetAbsent : lookupFiber @{nameEq}
                                  {name = name} {key = key} {value = value}
                                  {world = world} {error = error} leftActor
                                  target = Nothing
                                targetAbsent = trans
                                  (lookupInsertOther leftActor rightActor distinct
                                    (freshFiber rightComponent rightParent)
                                    source rightAbsent) leftAbsent
                                0 leftParentPresent : parentPresent @{nameEq}
                                  {name = name} {key = key} {value = value}
                                  {world = world} {error = error} leftParent
                                  source = True
                                leftParentPresent = localAndLeftTrueO5 _ _
                                  leftGuards
                                0 targetParentPresent : parentPresent @{nameEq}
                                  {name = name} {key = key} {value = value}
                                  {world = world} {error = error} leftParent
                                  target = True
                                targetParentPresent = localParentPresentAfterInsert
                                  nameEq leftParent rightActor rightParent
                                  rightComponent source rightAbsent
                                  leftParentPresent
                                0 leftSourceDisjoint : provisionsDisjointFrom
                                  @{keyEq} {name = name} {key = key}
                                  {value = value} {world = world} {error = error}
                                  (componentProvisions leftComponent)
                                  (bindings source) = True
                                leftSourceDisjoint = localAndRightTrueO5 _ _
                                  leftGuards
                                0 canonicalRightDisjoint :
                                  provisionsDisjointFrom @{keyEq} {name = name}
                                    {key = key} {value = value} {world = world}
                                    {error = error}
                                    (componentProvisions rightComponent)
                                    (bindings (registry canonicalMiddle)) = True
                                canonicalRightDisjoint = localAndRightTrueO5 _ _
                                  laterRightGuards
                                0 canonicalBindings : bindings
                                  (registry canonicalMiddle) =
                                  Bind leftActor
                                    (freshFiber leftComponent leftParent) ::
                                    bindings source
                                canonicalBindings = insertBindingRuntimeBindings
                                  nameEq leftActor
                                  (freshFiber leftComponent leftParent) source
                                  leftAbsent
                                0 explicitRightDisjoint :
                                  provisionsDisjointFrom @{keyEq} {name = name}
                                    {key = key} {value = value} {world = world}
                                    {error = error}
                                    (componentProvisions rightComponent)
                                    (Bind leftActor
                                      (freshFiber leftComponent leftParent) ::
                                      bindings source) = True
                                explicitRightDisjoint = replace
                                  {p = \entries => provisionsDisjointFrom @{keyEq}
                                    (componentProvisions rightComponent) entries =
                                    True}
                                  canonicalBindings canonicalRightDisjoint
                                0 laterRightDisjoint : provisionsDisjointFrom
                                  @{keyEq} {name = name} {key = key}
                                  {value = value} {world = world} {error = error}
                                  (componentProvisions rightComponent)
                                  (bindings (registry middle)) = True
                                laterRightDisjoint = replace
                                  {p = \state => provisionsDisjointFrom @{keyEq}
                                    (componentProvisions rightComponent)
                                    (bindings (registry state)) = True}
                                  middleShape canonicalRightDisjoint
                                0 reverseNotOverlap : not
                                  (provisionOverlap @{keyEq}
                                    (componentProvisions rightComponent)
                                    (componentProvisions leftComponent)) = True
                                reverseNotOverlap = localAndLeftTrueO5 _ _
                                  explicitRightDisjoint
                                0 reverseNoOverlap : provisionOverlap @{keyEq}
                                  (componentProvisions rightComponent)
                                  (componentProvisions leftComponent) = False
                                reverseNoOverlap = localNotTrueFalseO5 _
                                  reverseNotOverlap
                                0 forwardNoOverlap : provisionOverlap @{keyEq}
                                  (componentProvisions leftComponent)
                                  (componentProvisions rightComponent) = False
                                forwardNoOverlap =
                                  localProvisionOverlapFalseSymmetricO5 keyEq
                                    (componentProvisions leftComponent)
                                    (componentProvisions rightComponent)
                                    reverseNoOverlap
                                0 targetDisjoint : provisionsDisjointFrom
                                  @{keyEq} {name = name} {key = key}
                                  {value = value} {world = world} {error = error}
                                  (componentProvisions leftComponent)
                                  (bindings target) = True
                                targetDisjoint = localProvisionsDisjointAfterInsert
                                  nameEq keyEq
                                  (componentProvisions leftComponent) rightActor
                                  rightParent rightComponent source rightAbsent
                                  forwardNoOverlap leftSourceDisjoint
                            in case setFreshFromAbsent nameEq leftActor
                              (freshFiber leftComponent leftParent) target
                              targetAbsent of
                              (applied ** inserted) =>
                                let movedAfter : SystemState name key value
                                      world error
                                    movedAfter = MkSystemState ambient
                                      (coeffectAfter applied)
                                    0 movedRaw : applyAction @{nameEq} @{keyEq}
                                      (OInsert leftActor leftParent leftComponent)
                                      (MkSystemState ambient target) =
                                      Just (OInsertTag, movedAfter)
                                    movedRaw = rewrite targetParentPresent in
                                      rewrite targetDisjoint in
                                      rewrite inserted in Refl
                                in case tagSame of
                                  Refl => MkRawActivationMove movedAfter movedRaw
              PaperRetireStep {actor = leftActor} actionSame => case actionSame of
                Refl =>
                  case retireSuccessView nameEq keyEq leftActor ambient source
                    leftTag middle leftRaw of
                    sourceView@(MkRetireSuccessView leftFiber leftFound) =>
                      let target : Registry name key value world error
                          target = insertBinding @{nameEq} rightActor
                            (freshFiber rightComponent rightParent) source
                            rightAbsent
                          0 targetFound : lookupFiber @{nameEq} {name = name}
                            {key = key} {value = value} {world = world}
                            {error = error} leftActor target = Just leftFiber
                          targetFound = trans
                            (lookupInsertOther leftActor rightActor distinct
                              (freshFiber rightComponent rightParent) source
                              rightAbsent) leftFound
                          movedAfter : SystemState name key value world error
                          movedAfter = MkSystemState ambient
                            (replaceBinding @{nameEq} leftActor
                              (retireFiber leftFiber) target)
                          0 movedRaw : applyAction @{nameEq} @{keyEq}
                            (ORetire leftActor) (MkSystemState ambient target) =
                            Just (ORetireTag, movedAfter)
                          movedRaw = rewrite targetFound in Refl
                          0 tagSame : leftTag = ORetireTag
                          tagSame = localRetireViewTag leftTag sourceView
                      in case tagSame of
                        Refl => MkRawActivationMove movedAfter movedRaw
              PaperRemoveStep {actor = leftActor} actionSame => case actionSame of
                Refl =>
                  let 0 sourceView : RemoveSuccessView name key world error value
                        nameEq leftActor ambient source leftTag middle
                      sourceView = removeSuccessView nameEq keyEq leftActor
                        ambient source leftTag middle leftRaw
                      0 tagSame : Equal leftTag ORemoveTag
                      tagSame = localRemoveViewTag leftTag sourceView
                  in case sourceView of
                    MkRemoveSuccessView leftFiber leftFound removable
                      leftNoChild =>
                        let canonicalMiddle : SystemState name key value
                              world error
                            canonicalMiddle = MkSystemState ambient
                              (deleteBinding @{nameEq} leftActor source)
                            0 middleShape : Equal canonicalMiddle middle
                            middleShape = Refl
                            0 laterRightRaw : Equal
                              (applyAction @{nameEq} @{keyEq}
                                (OInsert rightActor rightParent rightComponent)
                                middle) (Just (OInsertTag, originalFinal))
                            laterRightRaw = checkedActionProjects nameEq keyEq
                              (OInsert rightActor rightParent rightComponent)
                              middle originalFinal OInsertTag exactRightChecked
                            0 laterRightView : ForeignInsertPlanView name key
                              world error value nameEq keyEq rightActor
                              rightParent rightComponent ambient
                              (registry middle) OInsertTag originalFinal
                            laterRightView = foreignInsertPlanView nameEq keyEq
                              rightActor rightParent rightComponent ambient
                              (registry middle) OInsertTag originalFinal
                              laterRightRaw
                        in case laterRightView of
                          MkForeignInsertPlanView laterRightAbsent
                            laterRightGuards =>
                              let 0 laterParentPresent : Equal
                                    (parentPresent @{nameEq} {name = name}
                                      {key = key} {value = value} {world = world}
                                      {error = error} rightParent
                                      (deleteBinding @{nameEq} leftActor source))
                                    True
                                  laterParentPresent = localAndLeftTrueO5 _ _
                                    laterRightGuards
                                  0 parentDifferent : Not
                                    (rightParent = ChildOf leftActor)
                                  parentDifferent = case rightParent of
                                    Root => \same => case same of Refl impossible
                                    ChildOf candidate => \same =>
                                      localDeletedParentNotPresentO5 nameEq
                                        leftActor source
                                        (localParentPresentTransportO5 nameEq
                                          (ChildOf candidate) leftActor
                                          (deleteBinding @{nameEq} leftActor
                                            source) same laterParentPresent)
                                  target : Registry name key value world error
                                  target = insertBinding @{nameEq} rightActor
                                    (freshFiber rightComponent rightParent)
                                    source rightAbsent
                                  0 targetFound : lookupFiber @{nameEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} leftActor
                                    target = Just leftFiber
                                  targetFound = trans
                                    (lookupInsertOther leftActor rightActor
                                      distinct
                                      (freshFiber rightComponent rightParent)
                                      source rightAbsent) leftFound
                                  0 targetNoChild : hasChild @{nameEq}
                                    {name = name} {key = key} {value = value}
                                    {world = world} {error = error} leftActor
                                    target = False
                                  targetNoChild = hasChildInsertFalse nameEq
                                    leftActor rightActor rightComponent
                                    rightParent source rightAbsent
                                    parentDifferent leftNoChild
                                  0 normalizedGuard : retired leftFiber &&
                                    isInactive (fiberLifecycle leftFiber) &&
                                    not False = True
                                  normalizedGuard = replace
                                    {p = \child => retired leftFiber &&
                                      isInactive (fiberLifecycle leftFiber) &&
                                      not child = True}
                                    leftNoChild removable
                                  0 targetGuard : retired leftFiber &&
                                    isInactive (fiberLifecycle leftFiber) &&
                                    not (hasChild @{nameEq} {name = name}
                                      {key = key} {value = value}
                                      {world = world} {error = error} leftActor
                                      target) = True
                                  targetGuard = rewrite targetNoChild in
                                    normalizedGuard
                                  movedAfter : SystemState name key value
                                    world error
                                  movedAfter = MkSystemState ambient
                                    (deleteBinding @{nameEq} leftActor target)
                                  0 movedRaw : applyAction @{nameEq} @{keyEq}
                                    (ORemove leftActor)
                                    (MkSystemState ambient target) =
                                    Just (ORemoveTag, movedAfter)
                                  movedRaw = rewrite targetFound in
                                    rewrite targetGuard in Refl
                              in case tagSame of
                                Refl => MkRawActivationMove movedAfter movedRaw
        in replace
          {p = \before => RawActivationMove nameEq keyEq leftAction leftTag
            before}
          earlyShape canonicalMove


0 orchestrationOwnerOutputsRelated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {firstBefore, firstAfter, secondBefore, secondAfter :
    SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (firstChecked : checkedApplyAction @{nameEq} @{keyEq} action firstBefore =
    Just (tag, firstAfter)) ->
  (secondChecked : checkedApplyAction @{nameEq} @{keyEq} action secondBefore =
    Just (tag, secondAfter)) ->
  PaperOrchestrationStep
    (Fired {before = firstBefore} {afterState = firstAfter}
      nameEq keyEq action tag firstChecked) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (actionOwner action)
      (registry firstBefore) =
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner action)
        (registry secondBefore) ->
  FiberControlMaybeRelated
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner action)
        (registry firstAfter))
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner action)
        (registry secondAfter))
orchestrationOwnerOutputsRelated nameEq keyEq {firstBefore} {firstAfter}
  {secondBefore} {secondAfter} action tag firstChecked secondChecked
  (PaperInsertStep {actor} {parent} {component} actionSame) sourceSame =
    case actionSame of
      Refl => case firstBefore of
        MkSystemState firstWorld firstRegistry =>
          let 0 firstRaw = checkedActionProjects nameEq keyEq
                (OInsert actor parent component)
                (MkSystemState firstWorld firstRegistry) firstAfter tag
                firstChecked
              firstView = foreignInsertPlanView nameEq keyEq actor parent component
                firstWorld firstRegistry tag firstAfter firstRaw
              0 tagSame : Equal tag OInsertTag
              tagSame = localForeignInsertViewTag tag firstView
          in case tagSame of
            Refl => case firstView of
              MkForeignInsertPlanView firstAbsent firstGuards =>
                case secondBefore of
                  MkSystemState secondWorld secondRegistry =>
                    let 0 secondRaw = checkedActionProjects nameEq keyEq
                          (OInsert actor parent component)
                          (MkSystemState secondWorld secondRegistry) secondAfter
                          OInsertTag secondChecked
                    in case foreignInsertPlanView nameEq keyEq actor parent
                      component secondWorld secondRegistry OInsertTag secondAfter
                      secondRaw of
                      MkForeignInsertPlanView secondAbsent secondGuards =>
                        rewrite lookupInserted actor (freshFiber component parent)
                          firstRegistry firstAbsent in
                        rewrite lookupInserted actor (freshFiber component parent)
                          secondRegistry secondAbsent in
                        SomeControlFibers
                          (fiberControlReflexive (freshFiber component parent))
orchestrationOwnerOutputsRelated nameEq keyEq {firstBefore} {firstAfter}
  {secondBefore} {secondAfter} action tag firstChecked secondChecked
  (PaperRetireStep {actor} actionSame) sourceSame = case actionSame of
    Refl => case firstBefore of
      MkSystemState firstWorld firstRegistry =>
        let 0 firstRaw = checkedActionProjects nameEq keyEq (ORetire actor)
              (MkSystemState firstWorld firstRegistry) firstAfter tag firstChecked
            firstView = retireSuccessView nameEq keyEq actor firstWorld
              firstRegistry tag firstAfter firstRaw
            0 tagSame : Equal tag ORetireTag
            tagSame = localRetireViewTag tag firstView
        in case tagSame of
          Refl => case firstView of
            MkRetireSuccessView firstFiber firstFound => case secondBefore of
              MkSystemState secondWorld secondRegistry =>
                let 0 secondRaw = checkedActionProjects nameEq keyEq
                      (ORetire actor) (MkSystemState secondWorld secondRegistry)
                      secondAfter ORetireTag secondChecked
                in case retireSuccessView nameEq keyEq actor secondWorld
                  secondRegistry ORetireTag secondAfter secondRaw of
                  MkRetireSuccessView secondFiber secondFound =>
                    case justInjective
                      (trans (sym firstFound) (trans sourceSame secondFound)) of
                      Refl =>
                        rewrite localLookupReplaceSelfO5 nameEq actor firstFiber
                          (retireFiber firstFiber) firstRegistry firstFound in
                        rewrite localLookupReplaceSelfO5 nameEq actor firstFiber
                          (retireFiber firstFiber) secondRegistry secondFound in
                        SomeControlFibers
                          (fiberControlReflexive (retireFiber firstFiber))
orchestrationOwnerOutputsRelated nameEq keyEq {firstBefore} {firstAfter}
  {secondBefore} {secondAfter} action tag firstChecked secondChecked
  (PaperRemoveStep {actor} actionSame) sourceSame = case actionSame of
    Refl => case firstBefore of
      MkSystemState firstWorld firstRegistry =>
        let 0 firstRaw = checkedActionProjects nameEq keyEq (ORemove actor)
              (MkSystemState firstWorld firstRegistry) firstAfter tag firstChecked
            firstView = removeSuccessView nameEq keyEq actor firstWorld
              firstRegistry tag firstAfter firstRaw
            0 tagSame : Equal tag ORemoveTag
            tagSame = localRemoveViewTag tag firstView
        in case tagSame of
          Refl => case firstView of
            MkRemoveSuccessView firstFiber firstFound firstGuard firstNoChild =>
              case secondBefore of
                MkSystemState secondWorld secondRegistry =>
                  let 0 secondRaw = checkedActionProjects nameEq keyEq
                        (ORemove actor)
                        (MkSystemState secondWorld secondRegistry) secondAfter
                        ORemoveTag secondChecked
                  in case removeSuccessView nameEq keyEq actor secondWorld
                    secondRegistry ORemoveTag secondAfter secondRaw of
                    MkRemoveSuccessView secondFiber secondFound secondGuard
                      secondNoChild =>
                        rewrite localLookupDeleteSelfO5 {key = key}
                          {value = value} {world = world} {error = error}
                          nameEq actor firstRegistry in
                        rewrite localLookupDeleteSelfO5 {key = key}
                          {value = value} {world = world} {error = error}
                          nameEq actor secondRegistry in
                        NoControlFibers

0 orchestrationRawAfterCheckedOrchestration :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  (rightPaper : PaperOrchestrationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked)) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  RawActivationMove nameEq keyEq leftAction leftTag earlyRightFinal
orchestrationRawAfterCheckedOrchestration {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  {earlyRightFinal} leftAction rightAction leftTag rightTag leftChecked
  rightChecked earlyRightChecked leftPaper
  (PaperInsertStep {actor = rightActor} {parent = rightParent}
    {component = rightComponent} actionSame) distinct =
      case actionSame of
        Refl => orchestrationRawAfterCheckedInsert nameEq keyEq leftAction
          leftTag rightActor rightParent rightComponent rightTag leftChecked
          rightChecked earlyRightChecked leftPaper distinct
orchestrationRawAfterCheckedOrchestration {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  {earlyRightFinal} leftAction rightAction leftTag rightTag leftChecked
  rightChecked earlyRightChecked leftPaper
  (PaperRetireStep {actor = rightActor} actionSame) distinct =
    case actionSame of
      Refl =>
        let 0 earlyRaw : Equal
              (applyAction @{nameEq} @{keyEq} (ORetire rightActor)
                (the (SystemState name key value world error)
                  (MkSystemState ambient source)))
              (Just (rightTag, earlyRightFinal))
            earlyRaw = checkedActionProjects nameEq keyEq (ORetire rightActor)
              (the (SystemState name key value world error)
                  (MkSystemState ambient source)) earlyRightFinal rightTag
              earlyRightChecked
            0 earlyView : RetireSuccessView name key world error value nameEq
              rightActor ambient source rightTag earlyRightFinal
            earlyView = retireSuccessView nameEq keyEq rightActor ambient source
              rightTag earlyRightFinal earlyRaw
            0 tagSame : Equal rightTag ORetireTag
            tagSame = localRetireViewTag rightTag earlyView
            0 exactEarly : Equal
              (checkedApplyAction @{nameEq} @{keyEq} (ORetire rightActor)
                (the (SystemState name key value world error)
                  (MkSystemState ambient source)))
              (Just (ORetireTag, earlyRightFinal))
            exactEarly = replace
              {p = \observedTag => Equal
                (checkedApplyAction @{nameEq} @{keyEq} (ORetire rightActor)
                  (the (SystemState name key value world error)
                  (MkSystemState ambient source)))
                (Just (observedTag, earlyRightFinal))}
              tagSame earlyRightChecked
        in orchestrationRawAfterCheckedRetire nameEq keyEq leftAction leftTag
          rightActor leftChecked exactEarly leftPaper distinct
orchestrationRawAfterCheckedOrchestration {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState ambient source} {middle} {originalFinal}
  {earlyRightFinal} leftAction rightAction leftTag rightTag leftChecked
  rightChecked earlyRightChecked leftPaper
  (PaperRemoveStep {actor = rightActor} actionSame) distinct =
    case actionSame of
      Refl =>
        let 0 earlyRaw : Equal
              (applyAction @{nameEq} @{keyEq} (ORemove rightActor)
                (the (SystemState name key value world error)
                  (MkSystemState ambient source)))
              (Just (rightTag, earlyRightFinal))
            earlyRaw = checkedActionProjects nameEq keyEq (ORemove rightActor)
              (the (SystemState name key value world error)
                  (MkSystemState ambient source)) earlyRightFinal rightTag
              earlyRightChecked
            0 earlyView : RemoveSuccessView name key world error value nameEq
              rightActor ambient source rightTag earlyRightFinal
            earlyView = removeSuccessView nameEq keyEq rightActor ambient source
              rightTag earlyRightFinal earlyRaw
            0 tagSame : Equal rightTag ORemoveTag
            tagSame = localRemoveViewTag rightTag earlyView
            0 exactRight : Equal
              (checkedApplyAction @{nameEq} @{keyEq} (ORemove rightActor) middle)
              (Just (ORemoveTag, originalFinal))
            exactRight = replace
              {p = \observedTag => Equal
                (checkedApplyAction @{nameEq} @{keyEq} (ORemove rightActor)
                  middle) (Just (observedTag, originalFinal))}
              tagSame rightChecked
            0 exactEarly : Equal
              (checkedApplyAction @{nameEq} @{keyEq} (ORemove rightActor)
                (the (SystemState name key value world error)
                  (MkSystemState ambient source)))
              (Just (ORemoveTag, earlyRightFinal))
            exactEarly = replace
              {p = \observedTag => Equal
                (checkedApplyAction @{nameEq} @{keyEq} (ORemove rightActor)
                  (the (SystemState name key value world error)
                  (MkSystemState ambient source)))
                (Just (observedTag, earlyRightFinal))}
              tagSame earlyRightChecked
        in orchestrationRawAfterCheckedRemove nameEq keyEq leftAction leftTag
          rightActor leftChecked exactRight exactEarly leftPaper distinct

0 beginRawAfterForeignState :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftActor : name) ->
  {first, middle, movedBefore : SystemState name key value world error} ->
  (foreignAction : Action name key value world error) ->
  (foreignTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin leftActor)
    first = Just (LBeginTag, middle)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, movedBefore)) ->
  Not (leftActor = actionOwner foreignAction) ->
  ((fiber : Fiber name key value world error) ->
    (view : View name (dependencies
      (componentDependencies (fiberComponent fiber)))) ->
    targetFiber @{nameEq} @{keyEq} fiber (registry first) = Just view ->
    targetFiber @{nameEq} @{keyEq} fiber (registry movedBefore) = Just view) ->
  RawActivationMove nameEq keyEq (LBegin leftActor) LBeginTag movedBefore
beginRawAfterForeignState {name} {key} {world} {error} {value}
  nameEq keyEq leftActor
  {first = MkSystemState firstWorld firstRegistry} {middle} {movedBefore}
  foreignAction foreignTag leftChecked foreignChecked distinct targets =
    let 0 leftRaw : (applyAction @{nameEq} @{keyEq} (LBegin leftActor)
          (MkSystemState firstWorld firstRegistry) = Just (LBeginTag, middle))
        leftRaw = checkedActionProjects nameEq keyEq (LBegin leftActor)
          (MkSystemState firstWorld firstRegistry) middle LBeginTag leftChecked
    in case beginSourceOwnerNotActive nameEq keyEq leftActor
      {before = MkSystemState firstWorld firstRegistry} {afterState = middle}
      LBeginTag leftChecked of
      (sourceFiber ** (sourceFound, sourceInactive)) =>
        case foreignBeginPlanView nameEq keyEq leftActor firstWorld firstRegistry
          sourceFiber sourceFound LBeginTag middle leftRaw of
          MkForeignBeginPlanView {component} {parent} {table} view ownerShape
            sourceTarget tagShape afterShape => case ownerShape of
              Refl =>
                let exactFiber : Fiber name key value world error
                    exactFiber = MkFiber component parent False table
                      (Inactive Nothing)
                    0 targetAtMoved : (targetFiber @{nameEq} @{keyEq}
                      exactFiber (registry movedBefore) = Just view)
                    targetAtMoved = targets exactFiber view sourceTarget
                    0 foundAtMoved : (lookupFiber @{nameEq} leftActor
                      (registry movedBefore) = Just exactFiber)
                    foundAtMoved = trans
                      (transitionForeignLookup nameEq keyEq leftActor
                        foreignAction foreignTag foreignChecked distinct)
                      sourceFound
                    movedAfter : SystemState name key value world error
                    movedAfter = MkSystemState (worldState movedBefore)
                      (replaceBinding @{nameEq} leftActor
                        (setFiberLifecycle exactFiber
                          (Reloading (componentProgram component) id view))
                        (registry movedBefore))
                    0 movedRaw : (applyAction @{nameEq} @{keyEq}
                      (LBegin leftActor) movedBefore =
                      Just (LBeginTag, movedAfter))
                    movedRaw = rewrite foundAtMoved in
                      rewrite targetAtMoved in Refl
                in MkRawActivationMove movedAfter movedRaw

0 beginRawAfterForeignActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftActor : name) ->
  {first, middle, earlyRightFinal : SystemState name key value world error} ->
  (foreignAction : Action name key value world error) ->
  (foreignTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin leftActor)
    first = Just (LBeginTag, middle)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, earlyRightFinal)) ->
  (foreignActivation : PaperActivationStep
    (Fired {before = first} {afterState = earlyRightFinal}
      nameEq keyEq foreignAction foreignTag foreignChecked)) ->
  Not (leftActor = actionOwner foreignAction) ->
  registryWellFormed @{nameEq} @{keyEq} earlyRightFinal = True ->
  RawActivationMove nameEq keyEq (LBegin leftActor) LBeginTag earlyRightFinal
beginRawAfterForeignActivation {name} {key} {world} {error} {value}
  nameEq keyEq leftActor
  {first = MkSystemState firstWorld firstRegistry} {middle} {earlyRightFinal}
  foreignAction foreignTag leftChecked foreignChecked foreignActivation distinct
  earlyWellFormed =
    let 0 leftRaw : (applyAction @{nameEq} @{keyEq} (LBegin leftActor)
          (MkSystemState firstWorld firstRegistry) = Just (LBeginTag, middle))
        leftRaw = checkedActionProjects nameEq keyEq (LBegin leftActor)
          (MkSystemState firstWorld firstRegistry) middle LBeginTag leftChecked
    in case beginSourceOwnerNotActive nameEq keyEq leftActor
      {before = MkSystemState firstWorld firstRegistry} {afterState = middle}
      LBeginTag leftChecked of
      (sourceFiber ** (sourceFound, sourceInactive)) =>
        case foreignBeginPlanView nameEq keyEq leftActor firstWorld firstRegistry
          sourceFiber sourceFound LBeginTag middle leftRaw of
          MkForeignBeginPlanView {component} {parent} {table} view ownerShape
            sourceTarget tagShape afterShape =>
              case ownerShape of
                Refl =>
                  let exactFiber : Fiber name key value world error
                      exactFiber = MkFiber component parent False table
                        (Inactive Nothing)
                      0 targetAtEarly : (targetFiber @{nameEq} @{keyEq}
                        exactFiber (registry earlyRightFinal) = Just view)
                      targetAtEarly = targetFiberStableAfterForeignActivation
                        nameEq keyEq exactFiber view foreignAction foreignTag
                        foreignChecked foreignActivation earlyWellFormed sourceTarget
                      0 foundAtEarly : (lookupFiber @{nameEq} leftActor
                        (registry earlyRightFinal) = Just exactFiber)
                      foundAtEarly = trans
                        (transitionForeignLookup nameEq keyEq leftActor
                          foreignAction foreignTag foreignChecked distinct)
                        sourceFound
                      movedAfter : SystemState name key value world error
                      movedAfter = MkSystemState (worldState earlyRightFinal)
                        (replaceBinding @{nameEq} leftActor
                          (setFiberLifecycle exactFiber
                            (Reloading (componentProgram component) id view))
                          (registry earlyRightFinal))
                      0 movedRaw : (applyAction @{nameEq} @{keyEq}
                        (LBegin leftActor) earlyRightFinal =
                        Just (LBeginTag, movedAfter))
                      movedRaw = rewrite foundAtEarly in
                        rewrite targetAtEarly in Refl
                  in MkRawActivationMove movedAfter movedRaw

data PaperAdvanceSource :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (tag : RuleTag) ->
  SystemState name key value world error -> Type where
  AdvanceSourceIter :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
    {ambient : world} -> {fibers : Registry name key value world error} ->
    {before : SystemState name key value world error} ->
    {component : Component key value world error} -> {parent : Parent name} ->
    {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    {step, next : StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component)} ->
    {more : List (StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component))} ->
    {accumulator : LocalState key value world
        (componentProvisions component) ->
      LocalState key value world (componentProvisions component)} ->
    {view : View name
      (dependencies (componentDependencies component))} ->
    MkSystemState ambient fibers = before ->
    lookupFiber @{nameEq} actor fibers =
      Just (MkFiber component parent retiredFlag table
        (Reloading (step :: next :: more) accumulator view)) ->
    targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table
        (Reloading (step :: next :: more) accumulator view)) fibers = Just view ->
    PaperAdvanceSource name key world error value nameEq keyEq actor LIterTag
      before
  AdvanceSourceFinishEmpty :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
    {ambient : world} -> {fibers : Registry name key value world error} ->
    {before : SystemState name key value world error} ->
    {component : Component key value world error} -> {parent : Parent name} ->
    {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    {accumulator : LocalState key value world
        (componentProvisions component) ->
      LocalState key value world (componentProvisions component)} ->
    {view : View name
      (dependencies (componentDependencies component))} ->
    MkSystemState ambient fibers = before ->
    lookupFiber @{nameEq} actor fibers =
      Just (MkFiber component parent retiredFlag table
        (Reloading [] accumulator view)) ->
    targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table
        (Reloading [] accumulator view)) fibers = Just view ->
    PaperAdvanceSource name key world error value nameEq keyEq actor LFinishTag
      before
  AdvanceSourceFinishOne :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} ->
    {ambient : world} -> {fibers : Registry name key value world error} ->
    {before : SystemState name key value world error} ->
    {component : Component key value world error} -> {parent : Parent name} ->
    {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    {step : StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component)} ->
    {accumulator : LocalState key value world
        (componentProvisions component) ->
      LocalState key value world (componentProvisions component)} ->
    {view : View name
      (dependencies (componentDependencies component))} ->
    MkSystemState ambient fibers = before ->
    lookupFiber @{nameEq} actor fibers =
      Just (MkFiber component parent retiredFlag table
        (Reloading [step] accumulator view)) ->
    targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table
        (Reloading [step] accumulator view)) fibers = Just view ->
    PaperAdvanceSource name key world error value nameEq keyEq actor LFinishTag
      before

0 paperAdvanceSource :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState) ->
  Either (tag = LIterTag) (tag = LFinishTag) ->
  PaperAdvanceSource name key world error value nameEq keyEq actor tag before
paperAdvanceSource {name} {key} {world} {error} {value}
  nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
  raw paperTag with (lookupFiber @{nameEq} actor fibers) proof found
  paperAdvanceSource {name} {key} {world} {error} {value}
    nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
    raw paperTag | Nothing = void (nothingIsNotJust raw)
  paperAdvanceSource {name} {key} {world} {error} {value}
    nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
    raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle)
    with (lifecycle) proof life
    paperAdvanceSource {name} {key} {world} {error} {value}
      nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
      raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
      Inactive outcome = void (nothingIsNotJust raw)
    paperAdvanceSource {name} {key} {world} {error} {value}
      nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
      raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
      Active accumulator view = void (nothingIsNotJust raw)
    paperAdvanceSource {name} {key} {world} {error} {value}
      nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
      raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
      Unloading accumulator view outcome = void (nothingIsNotJust raw)
    paperAdvanceSource {name} {key} {world} {error} {value}
      nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
      raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
      Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq}
          (MkFiber component parent retiredFlag table
            (Reloading [] accumulator view)) fibers) view) proof matches
      paperAdvanceSource {name} {key} {world} {error} {value}
        nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
        raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading [] accumulator view | False =
          case justInjective raw of
            Refl => case paperTag of
              Left Refl impossible
              Right Refl impossible
      paperAdvanceSource {name} {key} {world} {error} {value}
        nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
        raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading [] accumulator view | True =
          case justInjective raw of
            Refl => AdvanceSourceFinishEmpty Refl found
              (targetMatchesExact nameEq _ view matches)
    paperAdvanceSource {name} {key} {world} {error} {value}
      nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
      raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
      Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies component)) view fibers)
      paperAdvanceSource {name} {key} {world} {error} {value}
        nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
        raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading (step :: rest) accumulator view | Nothing =
          void (nothingIsNotJust raw)
      paperAdvanceSource {name} {key} {world} {error} {value}
        nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState} tag
        raw paperTag | Just (MkFiber component parent retiredFlag table lifecycle) |
        Reloading (step :: rest) accumulator view | Just capability
        with (runStepEffect step capability
          (MkLocalState ambient
            (restrictOwnedPreservingOrder (componentProvisions component)
              (ownedValues table))))
        paperAdvanceSource {name} {key} {world} {error} {value}
          nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState}
          tag raw paperTag |
          Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading (step :: rest) accumulator view | Just capability |
          Left failure = case justInjective raw of
            Refl => case paperTag of
              Left Refl impossible
              Right Refl impossible
        paperAdvanceSource {name} {key} {world} {error} {value}
          nameEq keyEq actor {before = MkSystemState ambient fibers} {afterState}
          tag raw paperTag |
          Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading (step :: rest) accumulator view | Just capability |
          Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq}
              (MkFiber component parent retiredFlag table
                (Reloading (step :: rest) accumulator view)) fibers) view)
            proof matches
          paperAdvanceSource {name} {key} {world} {error} {value}
            nameEq keyEq actor {before = MkSystemState ambient fibers}
            {afterState} tag raw paperTag |
            Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: rest) accumulator view | Just capability |
            Right (localAfter, undo) | False = case justInjective raw of
              Refl => case paperTag of
                Left Refl impossible
                Right Refl impossible
          paperAdvanceSource {name} {key} {world} {error} {value}
            nameEq keyEq actor {before = MkSystemState ambient fibers}
            {afterState} tag raw paperTag |
            Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: []) accumulator view | Just capability |
            Right (localAfter, undo) | True = case justInjective raw of
              Refl => AdvanceSourceFinishOne Refl found
                (targetMatchesExact nameEq _ view matches)
          paperAdvanceSource {name} {key} {world} {error} {value}
            nameEq keyEq actor {before = MkSystemState ambient fibers}
            {afterState} tag raw paperTag |
            Just (MkFiber component parent retiredFlag table lifecycle) |
            Reloading (step :: next :: more) accumulator view | Just capability |
            Right (localAfter, undo) | True = case justInjective raw of
              Refl => AdvanceSourceIter Refl found
                (targetMatchesExact nameEq _ view matches)

0 advanceRuntimeEffectMapAtFound :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor fibers = Just fiber ->
  (state : EffectState name key value world) ->
  advanceRuntimeEffectMap nameEq keyEq actor
    (the (SystemState name key value world error)
      (MkSystemState ambient fibers)) state =
  fiberAdvanceRuntimeEffectMap nameEq keyEq actor fiber state
advanceRuntimeEffectMapAtFound nameEq keyEq actor ambient fibers fiber found
  state = rewrite found in Refl

record MovedStepEffectSuccess
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (component : Component key value world error)
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))
  (view : View name (dependencies (componentDependencies component)))
  (state : EffectState name key value world)
  (moved : EffectState name key value world) where
  constructor MkMovedStepEffectSuccess
  movedCapability : DepValues key value
    (dependencies (componentDependencies component))
  0 movedCapabilityResolved : resolveEffectValues @{keyEq}
    (dependencies (componentDependencies component)) view state =
    Just movedCapability
  movedLocalAfter : LocalState key value world
    (componentProvisions component)
  movedUndo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)
  0 movedStepRuns : runStepEffect step movedCapability
    (MkLocalState (effectAmbient state)
      (restrictOwnedPreservingOrder (componentProvisions component)
        (effectTables state actor))) = Right (movedLocalAfter, movedUndo)

0 invertMovedStepEffect :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world
      (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (state, moved : EffectState name key value world) ->
  fiberAdvanceRuntimeEffectMap nameEq keyEq actor
    (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view)) state = Just moved ->
  MovedStepEffectSuccess name key world error value nameEq keyEq actor component
    step view state moved
invertMovedStepEffect nameEq keyEq actor component parent retiredFlag table step
  rest accumulator view state moved mapRuns
  with (resolveEffectValues @{keyEq}
    (dependencies (componentDependencies component)) view state) proof resolved
  invertMovedStepEffect nameEq keyEq actor component parent retiredFlag table step
    rest accumulator view state moved mapRuns | Nothing =
      void (nothingIsNotJust mapRuns)
  invertMovedStepEffect nameEq keyEq actor component parent retiredFlag table step
    rest accumulator view state moved mapRuns | Just capability
    with (runStepEffect step capability
      (MkLocalState (effectAmbient state)
        (restrictOwnedPreservingOrder (componentProvisions component)
          (effectTables state actor)))) proof ran
    invertMovedStepEffect nameEq keyEq actor component parent retiredFlag table
      step rest accumulator view state moved mapRuns | Just capability |
      Left failure = void (nothingIsNotJust mapRuns)
    invertMovedStepEffect nameEq keyEq actor component parent retiredFlag table
      step rest accumulator view state moved mapRuns | Just capability |
      Right (localAfter, undo) = MkMovedStepEffectSuccess capability resolved
        localAfter undo ran

0 movedStepSuccessIteratorOutcome :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (state, moved : EffectState name key value world) ->
  (success : MovedStepEffectSuccess name key world error value nameEq keyEq actor
    component step view state moved) ->
  iteratorStageOutcomeComponentData nameEq keyEq actor component view step rest
    state = Just (IteratorYielded
      (setEffectTable @{nameEq} actor
        (ownedValues (localTable (movedLocalAfter success)))
        (setEffectAmbient (localWorld (movedLocalAfter success)) state))
      (yieldedInverseEffectMap nameEq keyEq actor
        (componentProvisions component) (movedUndo success))
      (MkIteratorContinuation rest))
movedStepSuccessIteratorOutcome nameEq keyEq actor component step rest view state
  moved (MkMovedStepEffectSuccess capability resolved localAfter undo ran) =
    rewrite resolved in rewrite ran in Refl

0 successfulOutcomeAgreementUndoMaps :
  (movedOutcome, sourceOutcome :
    Maybe (IteratorStageOutcome name key value world error)) ->
  (movedAfter, sourceAfter : EffectState name key value world) ->
  (movedUndo, sourceUndo : PartialEffectMap name key value world) ->
  (movedContinuation, sourceContinuation :
    IteratorContinuation key value world error) ->
  movedOutcome = Just (IteratorYielded movedAfter movedUndo movedContinuation) ->
  sourceOutcome = Just
    (IteratorYielded sourceAfter sourceUndo sourceContinuation) ->
  IteratorOutcomeAgreement name key value world error keyEq movedOutcome
    sourceOutcome ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq) movedUndo sourceUndo
successfulOutcomeAgreementUndoMaps
  (Just (IteratorYielded movedAfter movedUndo movedContinuation))
  (Just (IteratorYielded sourceAfter sourceUndo sourceContinuation))
  movedAfter sourceAfter movedUndo sourceUndo movedContinuation sourceContinuation
  Refl Refl (IteratorSuccessfulYieldsAgree continuationSame undoMaps) = undoMaps

0 applyActionTagTransport :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {action : Action name key value world error} ->
  {before, afterState : SystemState name key value world error} ->
  {leftTag, rightTag : RuleTag} ->
  leftTag = rightTag ->
  applyAction @{nameEq} @{keyEq} action before = Just (leftTag, afterState) ->
  applyAction @{nameEq} @{keyEq} action before = Just (rightTag, afterState)
applyActionTagTransport Refl raw = raw

data TaggedPaperAdvanceSource :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) -> (before : SystemState name key value world error) -> Type where
  TaggedIterSource : tag = LIterTag ->
    PaperAdvanceSource name key world error value nameEq keyEq actor LIterTag
      before ->
    TaggedPaperAdvanceSource name key world error value nameEq keyEq actor tag
      before
  TaggedFinishSource : tag = LFinishTag ->
    PaperAdvanceSource name key world error value nameEq keyEq actor LFinishTag
      before ->
    TaggedPaperAdvanceSource name key world error value nameEq keyEq actor tag
      before

0 taggedPaperAdvanceSource :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  (paperTag : Either (tag = LIterTag) (tag = LFinishTag)) ->
  TaggedPaperAdvanceSource name key world error value nameEq keyEq actor tag
    before
taggedPaperAdvanceSource nameEq keyEq actor {before} {afterState} tag raw
  (Left tagIsIter) = case tagIsIter of
    Refl => TaggedIterSource Refl
      (paperAdvanceSource nameEq keyEq actor {before} {afterState} LIterTag raw
        (Left Refl))
taggedPaperAdvanceSource nameEq keyEq actor {before} {afterState} tag raw
  (Right tagIsFinish) = case tagIsFinish of
    Refl => TaggedFinishSource Refl
      (paperAdvanceSource nameEq keyEq actor {before} {afterState} LFinishTag raw
        (Right Refl))

0 paperAdvanceSourcePaperTag :
  PaperAdvanceSource name key world error value nameEq keyEq actor tag before ->
  Either (tag = LIterTag) (tag = LFinishTag)
paperAdvanceSourcePaperTag (AdvanceSourceIter _ _ _) = Left Refl
paperAdvanceSourcePaperTag (AdvanceSourceFinishEmpty _ _ _) = Right Refl
paperAdvanceSourcePaperTag (AdvanceSourceFinishOne _ _ _) = Right Refl

0 paperAdvanceRuntimeEffectRun :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) -> Either (tag = LIterTag) (tag = LFinishTag) ->
  (state : SystemState name key value world error) ->
  (output : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag state
    (projectEffectState @{nameEq} state) = Just output ->
  advanceRuntimeEffectMap nameEq keyEq actor state
    (projectEffectState @{nameEq} state) = Just output
paperAdvanceRuntimeEffectRun nameEq keyEq actor tag (Left tagIsIter) state output
  runs = case tagIsIter of Refl => runs
paperAdvanceRuntimeEffectRun nameEq keyEq actor tag (Right tagIsFinish) state output
  runs = case tagIsFinish of Refl => runs

0 paperAdvanceTargetAtKnownFiber :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (source : PaperAdvanceSource name key world error value nameEq keyEq actor tag
    (MkSystemState ambient fibers)) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} actor fibers = Just
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) fibers = Just view
paperAdvanceTargetAtKnownFiber nameEq keyEq actor ambient fibers source
  component parent retiredFlag table remaining accumulator view found =
    case source of
      AdvanceSourceFinishEmpty {ambient = observedAmbient}
        {fibers = observedFibers} {component = observedComponent}
        {parent = observedParent} {retiredFlag = observedRetired}
        {table = observedTable} {accumulator = observedAccumulator}
        {view = observedView} sourceShape observedFound observedTarget =>
          case sourceShape of
            Refl =>
              let 0 fiberSame = justInjective (trans (sym found) observedFound)
              in case fiberSame of Refl => observedTarget
      AdvanceSourceFinishOne {ambient = observedAmbient}
        {fibers = observedFibers} {component = observedComponent}
        {parent = observedParent} {retiredFlag = observedRetired}
        {table = observedTable} {step = observedStep}
        {accumulator = observedAccumulator} {view = observedView}
        sourceShape observedFound observedTarget =>
          case sourceShape of
            Refl =>
              let 0 fiberSame = justInjective (trans (sym found) observedFound)
              in case fiberSame of Refl => observedTarget
      AdvanceSourceIter {ambient = observedAmbient} {fibers = observedFibers}
        {component = observedComponent} {parent = observedParent}
        {retiredFlag = observedRetired} {table = observedTable}
        {step = observedStep} {next = observedNext} {more = observedMore}
        {accumulator = observedAccumulator} {view = observedView}
        sourceShape observedFound observedTarget =>
          case sourceShape of
            Refl =>
              let 0 fiberSame = justInjective (trans (sym found) observedFound)
              in case fiberSame of Refl => observedTarget

record PairedAdvanceYield
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (component : Component key value world error)
  (table : OwnedTable key value (componentProvisions component))
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)))
  (view : View name (dependencies (componentDependencies component)))
  (sourceAmbient, movedAmbient : world)
  (sourceRegistry, movedRegistry : Registry name key value world error) where
  constructor MkPairedAdvanceYield
  pairedSourceCapability : DepValues key value
    (dependencies (componentDependencies component))
  pairedMovedCapability : DepValues key value
    (dependencies (componentDependencies component))
  pairedSourceAfter : LocalState key value world (componentProvisions component)
  pairedMovedAfter : LocalState key value world (componentProvisions component)
  pairedSourceUndo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)
  pairedMovedUndo : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)
  0 pairedSourceResolved : resolveCommittedValues @{nameEq} @{keyEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view sourceRegistry =
    Just pairedSourceCapability
  0 pairedMovedResolved : resolveCommittedValues @{nameEq} @{keyEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view movedRegistry =
    Just pairedMovedCapability
  0 pairedSourceRan : runStepEffect step pairedSourceCapability
    (MkLocalState sourceAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues table))) = Right (pairedSourceAfter, pairedSourceUndo)
  0 pairedMovedRan : runStepEffect step pairedMovedCapability
    (MkLocalState movedAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues table))) = Right (pairedMovedAfter, pairedMovedUndo)
  0 pairedUndoMaps : PartialMapsEquivalent (EffectStateEquivalence keyEq)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) pairedMovedUndo)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) pairedSourceUndo)

0 pairedAdvanceYieldFromRuns :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
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
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (sourceOutput, movedOutput : EffectState name key value world) ->
  (sourceFound : lookupFiber @{nameEq} actor sourceRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view))) ->
  (movedFound : lookupFiber @{nameEq} actor movedRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view))) ->
  advanceRuntimeEffectMap nameEq keyEq actor
    (the (SystemState name key value world error)
      (MkSystemState sourceAmbient sourceRegistry))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState sourceAmbient sourceRegistry))) = Just sourceOutput ->
  advanceRuntimeEffectMap nameEq keyEq actor
    (the (SystemState name key value world error)
      (MkSystemState movedAmbient movedRegistry))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState movedAmbient movedRegistry))) = Just movedOutput ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcomeComponentData nameEq keyEq actor component view step rest
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState movedAmbient movedRegistry))))
    (iteratorStageOutcomeComponentData nameEq keyEq actor component view step rest
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState sourceAmbient sourceRegistry)))) ->
  PairedAdvanceYield nameEq keyEq actor component table step rest view
    sourceAmbient movedAmbient sourceRegistry movedRegistry
pairedAdvanceYieldFromRuns nameEq keyEq actor component parent retiredFlag
  table step rest accumulator view sourceAmbient movedAmbient
  sourceRegistry movedRegistry sourceOutput movedOutput sourceFound movedFound
  sourceMapRuns movedMapRuns agreement =
    let exactFiber : Fiber name key value world error
        exactFiber = MkFiber component parent retiredFlag table
          (Reloading (step :: rest) accumulator view)
        sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceAmbient sourceRegistry
        movedState : SystemState name key value world error
        movedState = MkSystemState movedAmbient movedRegistry
        0 sourceFiberRuns : fiberAdvanceRuntimeEffectMap nameEq keyEq actor
          exactFiber (projectEffectState @{nameEq} sourceState) = Just sourceOutput
        sourceFiberRuns = trans
          (sym (advanceRuntimeEffectMapAtFound nameEq keyEq actor sourceAmbient
            sourceRegistry exactFiber sourceFound
            (projectEffectState @{nameEq} sourceState))) sourceMapRuns
        0 movedFiberRuns : fiberAdvanceRuntimeEffectMap nameEq keyEq actor
          exactFiber (projectEffectState @{nameEq} movedState) = Just movedOutput
        movedFiberRuns = trans
          (sym (advanceRuntimeEffectMapAtFound nameEq keyEq actor movedAmbient
            movedRegistry exactFiber movedFound
            (projectEffectState @{nameEq} movedState))) movedMapRuns
        0 sourceSuccess : MovedStepEffectSuccess name key world error value
          nameEq keyEq actor component step view
          (projectEffectState @{nameEq} sourceState) sourceOutput
        sourceSuccess = invertMovedStepEffect nameEq keyEq actor component parent
          retiredFlag table step rest accumulator view
          (projectEffectState @{nameEq} sourceState) sourceOutput sourceFiberRuns
        0 movedSuccess : MovedStepEffectSuccess name key world error value
          nameEq keyEq actor component step view
          (projectEffectState @{nameEq} movedState) movedOutput
        movedSuccess = invertMovedStepEffect nameEq keyEq actor component parent
          retiredFlag table step rest accumulator view
          (projectEffectState @{nameEq} movedState) movedOutput movedFiberRuns
        0 sourceResolved : resolveCommittedValues @{nameEq} @{keyEq}
          {name = name} {key = key} {value = value} {world = world}
          {error = error}
          (dependencies (componentDependencies component)) view sourceRegistry =
          Just (movedCapability sourceSuccess)
        sourceResolved = trans
          (sym (resolveEffectValuesProjected nameEq keyEq
            (dependencies (componentDependencies component)) view sourceState))
          (movedCapabilityResolved sourceSuccess)
        0 movedResolved : resolveCommittedValues @{nameEq} @{keyEq}
          {name = name} {key = key} {value = value} {world = world}
          {error = error}
          (dependencies (componentDependencies component)) view movedRegistry =
          Just (movedCapability movedSuccess)
        movedResolved = trans
          (sym (resolveEffectValuesProjected nameEq keyEq
            (dependencies (componentDependencies component)) view movedState))
          (movedCapabilityResolved movedSuccess)
        0 sourceRan : runStepEffect step (movedCapability sourceSuccess)
          (MkLocalState sourceAmbient
            (restrictOwnedPreservingOrder @{keyEq}
              (componentProvisions component) (ownedValues table))) =
          Right (movedLocalAfter sourceSuccess, movedUndo sourceSuccess)
        sourceRan = replace
          {p = \actorTable => runStepEffect step (movedCapability sourceSuccess)
            (MkLocalState sourceAmbient
              (restrictOwnedPreservingOrder @{keyEq}
                (componentProvisions component) actorTable)) =
            Right (movedLocalAfter sourceSuccess, movedUndo sourceSuccess)}
          (projectedActorTable nameEq actor sourceState exactFiber sourceFound)
          (movedStepRuns sourceSuccess)
        0 movedRan : runStepEffect step (movedCapability movedSuccess)
          (MkLocalState movedAmbient
            (restrictOwnedPreservingOrder @{keyEq}
              (componentProvisions component) (ownedValues table))) =
          Right (movedLocalAfter movedSuccess, movedUndo movedSuccess)
        movedRan = replace
          {p = \actorTable => runStepEffect step (movedCapability movedSuccess)
            (MkLocalState movedAmbient
              (restrictOwnedPreservingOrder @{keyEq}
                (componentProvisions component) actorTable)) =
            Right (movedLocalAfter movedSuccess, movedUndo movedSuccess)}
          (projectedActorTable nameEq actor movedState exactFiber movedFound)
          (movedStepRuns movedSuccess)
        0 sourceOutcome : iteratorStageOutcomeComponentData nameEq keyEq actor
          component view step rest (projectEffectState @{nameEq} sourceState) =
          Just (IteratorYielded
            (setEffectTable @{nameEq} actor
              (ownedValues (localTable (movedLocalAfter sourceSuccess)))
              (setEffectAmbient (localWorld (movedLocalAfter sourceSuccess))
                (projectEffectState @{nameEq} sourceState)))
            (yieldedInverseEffectMap nameEq keyEq actor
              (componentProvisions component) (movedUndo sourceSuccess))
            (MkIteratorContinuation rest))
        sourceOutcome = movedStepSuccessIteratorOutcome nameEq keyEq actor
          component step rest view (projectEffectState @{nameEq} sourceState)
          sourceOutput sourceSuccess
        0 movedOutcome : iteratorStageOutcomeComponentData nameEq keyEq actor
          component view step rest (projectEffectState @{nameEq} movedState) =
          Just (IteratorYielded
            (setEffectTable @{nameEq} actor
              (ownedValues (localTable (movedLocalAfter movedSuccess)))
              (setEffectAmbient (localWorld (movedLocalAfter movedSuccess))
                (projectEffectState @{nameEq} movedState)))
            (yieldedInverseEffectMap nameEq keyEq actor
              (componentProvisions component) (movedUndo movedSuccess))
            (MkIteratorContinuation rest))
        movedOutcome = movedStepSuccessIteratorOutcome nameEq keyEq actor
          component step rest view (projectEffectState @{nameEq} movedState)
          movedOutput movedSuccess
        0 undoMaps : PartialMapsEquivalent (EffectStateEquivalence keyEq)
          (yieldedInverseEffectMap nameEq keyEq actor
            (componentProvisions component) (movedUndo movedSuccess))
          (yieldedInverseEffectMap nameEq keyEq actor
            (componentProvisions component) (movedUndo sourceSuccess))
        undoMaps = successfulOutcomeAgreementUndoMaps
          (iteratorStageOutcomeComponentData nameEq keyEq actor component view
            step rest (projectEffectState @{nameEq} movedState))
          (iteratorStageOutcomeComponentData nameEq keyEq actor component view
            step rest (projectEffectState @{nameEq} sourceState))
          (setEffectTable @{nameEq} actor
            (ownedValues (localTable (movedLocalAfter movedSuccess)))
            (setEffectAmbient (localWorld (movedLocalAfter movedSuccess))
              (projectEffectState @{nameEq} movedState)))
          (setEffectTable @{nameEq} actor
            (ownedValues (localTable (movedLocalAfter sourceSuccess)))
            (setEffectAmbient (localWorld (movedLocalAfter sourceSuccess))
              (projectEffectState @{nameEq} sourceState)))
          (yieldedInverseEffectMap nameEq keyEq actor
            (componentProvisions component) (movedUndo movedSuccess))
          (yieldedInverseEffectMap nameEq keyEq actor
            (componentProvisions component) (movedUndo sourceSuccess))
          (MkIteratorContinuation rest) (MkIteratorContinuation rest)
          movedOutcome sourceOutcome agreement
    in MkPairedAdvanceYield (movedCapability sourceSuccess)
      (movedCapability movedSuccess) (movedLocalAfter sourceSuccess)
      (movedLocalAfter movedSuccess) (movedUndo sourceSuccess)
      (movedUndo movedSuccess) sourceResolved movedResolved sourceRan movedRan
      undoMaps

0 localSystemStateEta : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
localSystemStateEta (MkSystemState ambient fibers) = Refl

0 advanceRawAfterForeignState :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (leftActor : name) ->
  {first, middle, earlyRightFinal : SystemState name key value world error} ->
  (leftTag : RuleTag) ->
  (foreignAction : Action name key value world error) ->
  (foreignTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance leftActor)
    first = Just (leftTag, middle)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, earlyRightFinal)) ->
  Not (leftActor = actionOwner foreignAction) ->
  ((fiber : Fiber name key value world error) ->
    (view : View name (dependencies
      (componentDependencies (fiberComponent fiber)))) ->
    targetFiber @{nameEq} @{keyEq} fiber (registry first) = Just view ->
    targetFiber @{nameEq} @{keyEq} fiber
      (registry earlyRightFinal) = Just view) ->
  (paperTag : Either (leftTag = LIterTag) (leftTag = LFinishTag)) ->
  (movedEffect : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance leftActor) leftTag earlyRightFinal
    (projectEffectState @{nameEq} earlyRightFinal) = Just movedEffect ->
  RawActivationMove nameEq keyEq (LAdvance leftActor) leftTag earlyRightFinal
advanceRawAfterForeignState {name} {key} {world} {error} {value}
  nameEq keyEq leftActor {first} {middle} {earlyRightFinal} leftTag
  foreignAction foreignTag leftChecked foreignChecked distinct targets paperTag
  movedEffect mapRuns =
    let sourceAmbient : world
        sourceAmbient = worldState first
        sourceFibers : Registry name key value world error
        sourceFibers = registry first
        movedAmbient : world
        movedAmbient = worldState earlyRightFinal
        movedFibers : Registry name key value world error
        movedFibers = registry earlyRightFinal
        0 firstShape : (MkSystemState sourceAmbient sourceFibers = first)
        firstShape = localSystemStateEta first
        0 earlyShape : (MkSystemState movedAmbient movedFibers =
          earlyRightFinal)
        earlyShape = localSystemStateEta earlyRightFinal
        0 concreteMapRuns : (partialEffectMapFor nameEq keyEq
          (LAdvance leftActor) leftTag
          (the (SystemState name key value world error)
            (MkSystemState movedAmbient movedFibers))
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState movedAmbient movedFibers))) = Just movedEffect)
        concreteMapRuns = replace
          {p = \state => partialEffectMapFor nameEq keyEq
            (LAdvance leftActor) leftTag state
            (projectEffectState @{nameEq} state) = Just movedEffect}
          (sym earlyShape) mapRuns
        0 leftRaw : (applyAction @{nameEq} @{keyEq} (LAdvance leftActor)
          first = Just (leftTag, middle))
        leftRaw = checkedActionProjects nameEq keyEq (LAdvance leftActor)
          first middle leftTag leftChecked
    in case paperAdvanceSource nameEq keyEq leftActor {before = first}
      {afterState = middle} leftTag leftRaw paperTag of
      AdvanceSourceFinishEmpty {ambient = observedAmbient}
        {fibers = observedFibers} {component} {parent} {retiredFlag} {table}
        {accumulator} {view} sourceShape sourceFound sourceTarget =>
          let exactFiber : Fiber name key value world error
              exactFiber = MkFiber component parent retiredFlag table
                (Reloading [] accumulator view)
              0 observedSourceShape :
                ((the (SystemState name key value world error)
                  (MkSystemState observedAmbient observedFibers)) =
                 (the (SystemState name key value world error)
                  (MkSystemState sourceAmbient sourceFibers)))
              observedSourceShape = trans sourceShape (sym firstShape)
              0 sourceFoundAtFirst : (lookupFiber @{nameEq} leftActor
                sourceFibers = Just exactFiber)
              sourceFoundAtFirst = replace
                {p = \state => lookupFiber @{nameEq} leftActor
                  (registry state) = Just exactFiber}
                observedSourceShape sourceFound
              0 sourceTargetAtFirst : (targetFiber @{nameEq} @{keyEq}
                exactFiber sourceFibers = Just view)
              sourceTargetAtFirst = replace
                {p = \state => targetFiber @{nameEq} @{keyEq} exactFiber
                  (registry state) = Just view}
                observedSourceShape sourceTarget
              0 foundAtMoved : (lookupFiber @{nameEq} leftActor movedFibers =
                Just exactFiber)
              foundAtMoved = trans
                (transitionForeignLookup nameEq keyEq leftActor foreignAction
                  foreignTag foreignChecked distinct)
                sourceFoundAtFirst
              0 targetAtMoved : (targetFiber @{nameEq} @{keyEq} exactFiber
                movedFibers = Just view)
              targetAtMoved = targets exactFiber view sourceTargetAtFirst
              movedAfter : SystemState name key value world error
              movedAfter = MkSystemState movedAmbient
                (replaceBinding @{nameEq} leftActor
                  (setFiberLifecycle exactFiber (Active accumulator view))
                  movedFibers)
              0 movedRawConcrete : (applyAction @{nameEq} @{keyEq}
                (LAdvance leftActor) (MkSystemState movedAmbient movedFibers) =
                Just (LFinishTag, movedAfter))
              movedRawConcrete = rewrite foundAtMoved in rewrite targetAtMoved in
                rewrite localViewEqRefl nameEq view in Refl
              0 movedRaw : (applyAction @{nameEq} @{keyEq}
                (LAdvance leftActor) earlyRightFinal =
                Just (LFinishTag, movedAfter))
              movedRaw = replace
                {p = \state => applyAction @{nameEq} @{keyEq}
                  (LAdvance leftActor) state = Just (LFinishTag, movedAfter)}
                earlyShape movedRawConcrete
          in MkRawActivationMove movedAfter movedRaw
      AdvanceSourceFinishOne {ambient = observedAmbient}
        {fibers = observedFibers} {component} {parent} {retiredFlag} {table}
        {step} {accumulator} {view} sourceShape sourceFound sourceTarget =>
          let exactFiber : Fiber name key value world error
              exactFiber = MkFiber component parent retiredFlag table
                (Reloading [step] accumulator view)
              0 observedSourceShape :
                ((the (SystemState name key value world error)
                  (MkSystemState observedAmbient observedFibers)) =
                 (the (SystemState name key value world error)
                  (MkSystemState sourceAmbient sourceFibers)))
              observedSourceShape = trans sourceShape (sym firstShape)
              0 sourceFoundAtFirst : (lookupFiber @{nameEq} leftActor
                sourceFibers = Just exactFiber)
              sourceFoundAtFirst = replace
                {p = \state => lookupFiber @{nameEq} leftActor
                  (registry state) = Just exactFiber}
                observedSourceShape sourceFound
              0 sourceTargetAtFirst : (targetFiber @{nameEq} @{keyEq}
                exactFiber sourceFibers = Just view)
              sourceTargetAtFirst = replace
                {p = \state => targetFiber @{nameEq} @{keyEq} exactFiber
                  (registry state) = Just view}
                observedSourceShape sourceTarget
              0 foundAtMoved : (lookupFiber @{nameEq} leftActor movedFibers =
                Just exactFiber)
              foundAtMoved = trans
                (transitionForeignLookup nameEq keyEq leftActor foreignAction
                  foreignTag foreignChecked distinct)
                sourceFoundAtFirst
              0 fiberMapRuns : (fiberAdvanceRuntimeEffectMap nameEq keyEq
                leftActor exactFiber
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState movedAmbient movedFibers))) =
                Just movedEffect)
              fiberMapRuns = trans
                (sym (advanceRuntimeEffectMapAtFound nameEq keyEq leftActor
                  movedAmbient movedFibers exactFiber foundAtMoved
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState movedAmbient movedFibers)))))
                concreteMapRuns
              0 targetAtMoved : (targetFiber @{nameEq} @{keyEq} exactFiber
                movedFibers = Just view)
              targetAtMoved = targets exactFiber view sourceTargetAtFirst
          in case invertMovedStepEffect nameEq keyEq leftActor component parent
            retiredFlag table step [] accumulator view
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState movedAmbient movedFibers))) movedEffect
            fiberMapRuns of
            MkMovedStepEffectSuccess capability effectResolved localAfter undo
              effectStepRuns =>
                let 0 committedResolved :
                      (resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
                        {value = value} {world = world} {error = error}
                        (dependencies (componentDependencies component)) view
                        movedFibers = Just capability)
                    committedResolved = trans
                      (sym (resolveEffectValuesProjected nameEq keyEq
                        (dependencies (componentDependencies component)) view
                        (MkSystemState movedAmbient movedFibers)))
                      effectResolved
                    0 ranAtTable : (runStepEffect step capability
                      (MkLocalState movedAmbient
                        (restrictOwnedPreservingOrder
                          (componentProvisions component) (ownedValues table))) =
                      Right (localAfter, undo))
                    ranAtTable = replace
                      {p = \actorTable => runStepEffect step capability
                        (MkLocalState movedAmbient
                          (restrictOwnedPreservingOrder
                            (componentProvisions component) actorTable)) =
                        Right (localAfter, undo)}
                      (projectedActorTable nameEq leftActor
                        (MkSystemState movedAmbient movedFibers) exactFiber
                        foundAtMoved) effectStepRuns
                    movedAfter : SystemState name key value world error
                    movedAfter = MkSystemState (localWorld localAfter)
                      (replaceBinding @{nameEq} leftActor
                        (setFiberRuntime exactFiber (localTable localAfter)
                          (Active
                            (pushLocalUndo (componentProvisions component)
                              accumulator undo) view)) movedFibers)
                    0 movedRawConcrete : (applyAction @{nameEq} @{keyEq}
                      (LAdvance leftActor)
                      (MkSystemState movedAmbient movedFibers) =
                      Just (LFinishTag, movedAfter))
                    movedRawConcrete = rewrite foundAtMoved in
                      rewrite committedResolved in rewrite ranAtTable in
                      rewrite targetAtMoved in
                      rewrite localViewEqRefl nameEq view in Refl
                    0 movedRaw : (applyAction @{nameEq} @{keyEq}
                      (LAdvance leftActor) earlyRightFinal =
                      Just (LFinishTag, movedAfter))
                    movedRaw = replace
                      {p = \state => applyAction @{nameEq} @{keyEq}
                        (LAdvance leftActor) state =
                        Just (LFinishTag, movedAfter)}
                      earlyShape movedRawConcrete
                in MkRawActivationMove movedAfter movedRaw
      AdvanceSourceIter {ambient = observedAmbient}
        {fibers = observedFibers} {component} {parent} {retiredFlag} {table}
        {step} {next} {more} {accumulator} {view} sourceShape sourceFound
        sourceTarget =>
          let exactFiber : Fiber name key value world error
              exactFiber = MkFiber component parent retiredFlag table
                (Reloading (step :: next :: more) accumulator view)
              0 observedSourceShape :
                ((the (SystemState name key value world error)
                  (MkSystemState observedAmbient observedFibers)) =
                 (the (SystemState name key value world error)
                  (MkSystemState sourceAmbient sourceFibers)))
              observedSourceShape = trans sourceShape (sym firstShape)
              0 sourceFoundAtFirst : (lookupFiber @{nameEq} leftActor
                sourceFibers = Just exactFiber)
              sourceFoundAtFirst = replace
                {p = \state => lookupFiber @{nameEq} leftActor
                  (registry state) = Just exactFiber}
                observedSourceShape sourceFound
              0 sourceTargetAtFirst : (targetFiber @{nameEq} @{keyEq}
                exactFiber sourceFibers = Just view)
              sourceTargetAtFirst = replace
                {p = \state => targetFiber @{nameEq} @{keyEq} exactFiber
                  (registry state) = Just view}
                observedSourceShape sourceTarget
              0 foundAtMoved : (lookupFiber @{nameEq} leftActor movedFibers =
                Just exactFiber)
              foundAtMoved = trans
                (transitionForeignLookup nameEq keyEq leftActor foreignAction
                  foreignTag foreignChecked distinct)
                sourceFoundAtFirst
              0 fiberMapRuns : (fiberAdvanceRuntimeEffectMap nameEq keyEq
                leftActor exactFiber
                (projectEffectState @{nameEq}
                  (the (SystemState name key value world error)
                    (MkSystemState movedAmbient movedFibers))) =
                Just movedEffect)
              fiberMapRuns = trans
                (sym (advanceRuntimeEffectMapAtFound nameEq keyEq leftActor
                  movedAmbient movedFibers exactFiber foundAtMoved
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState movedAmbient movedFibers)))))
                concreteMapRuns
              0 targetAtMoved : (targetFiber @{nameEq} @{keyEq} exactFiber
                movedFibers = Just view)
              targetAtMoved = targets exactFiber view sourceTargetAtFirst
          in case invertMovedStepEffect nameEq keyEq leftActor component parent
            retiredFlag table step (next :: more) accumulator view
            (projectEffectState @{nameEq}
              (the (SystemState name key value world error)
                (MkSystemState movedAmbient movedFibers))) movedEffect
            fiberMapRuns of
            MkMovedStepEffectSuccess capability effectResolved localAfter undo
              effectStepRuns =>
                let 0 committedResolved :
                      (resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
                        {value = value} {world = world} {error = error}
                        (dependencies (componentDependencies component)) view
                        movedFibers = Just capability)
                    committedResolved = trans
                      (sym (resolveEffectValuesProjected nameEq keyEq
                        (dependencies (componentDependencies component)) view
                        (MkSystemState movedAmbient movedFibers)))
                      effectResolved
                    0 ranAtTable : (runStepEffect step capability
                      (MkLocalState movedAmbient
                        (restrictOwnedPreservingOrder
                          (componentProvisions component) (ownedValues table))) =
                      Right (localAfter, undo))
                    ranAtTable = replace
                      {p = \actorTable => runStepEffect step capability
                        (MkLocalState movedAmbient
                          (restrictOwnedPreservingOrder
                            (componentProvisions component) actorTable)) =
                        Right (localAfter, undo)}
                      (projectedActorTable nameEq leftActor
                        (MkSystemState movedAmbient movedFibers) exactFiber
                        foundAtMoved) effectStepRuns
                    movedAfter : SystemState name key value world error
                    movedAfter = MkSystemState (localWorld localAfter)
                      (replaceBinding @{nameEq} leftActor
                        (setFiberRuntime exactFiber (localTable localAfter)
                          (Reloading (next :: more)
                            (pushLocalUndo (componentProvisions component)
                              accumulator undo) view)) movedFibers)
                    0 movedRawConcrete : (applyAction @{nameEq} @{keyEq}
                      (LAdvance leftActor)
                      (MkSystemState movedAmbient movedFibers) =
                      Just (LIterTag, movedAfter))
                    movedRawConcrete = rewrite foundAtMoved in
                      rewrite committedResolved in rewrite ranAtTable in
                      rewrite targetAtMoved in
                      rewrite localViewEqRefl nameEq view in Refl
                    0 movedRaw : (applyAction @{nameEq} @{keyEq}
                      (LAdvance leftActor) earlyRightFinal =
                      Just (LIterTag, movedAfter))
                    movedRaw = replace
                      {p = \state => applyAction @{nameEq} @{keyEq}
                        (LAdvance leftActor) state =
                        Just (LIterTag, movedAfter)}
                      earlyShape movedRawConcrete
                in MkRawActivationMove movedAfter movedRaw

0 advanceRawAfterForeignActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (leftActor : name) ->
  {first, middle, earlyRightFinal : SystemState name key value world error} ->
  (leftTag : RuleTag) ->
  (foreignAction : Action name key value world error) ->
  (foreignTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance leftActor)
    first = Just (leftTag, middle)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, earlyRightFinal)) ->
  (foreignActivation : PaperActivationStep
    (Fired {before = first} {afterState = earlyRightFinal}
      nameEq keyEq foreignAction foreignTag foreignChecked)) ->
  Not (leftActor = actionOwner foreignAction) ->
  registryWellFormed @{nameEq} @{keyEq} earlyRightFinal = True ->
  (paperTag : Either (leftTag = LIterTag) (leftTag = LFinishTag)) ->
  (movedEffect : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance leftActor) leftTag earlyRightFinal
    (projectEffectState @{nameEq} earlyRightFinal) = Just movedEffect ->
  RawActivationMove nameEq keyEq (LAdvance leftActor) leftTag earlyRightFinal
advanceRawAfterForeignActivation nameEq keyEq leftActor leftTag foreignAction
  foreignTag leftChecked foreignChecked foreignActivation distinct
  earlyWellFormed paperTag movedEffect mapRuns =
    advanceRawAfterForeignState nameEq keyEq leftActor leftTag foreignAction
      foreignTag leftChecked foreignChecked distinct
      (\fiber, view, sourceTarget =>
        targetFiberStableAfterForeignActivation nameEq keyEq fiber view
          foreignAction foreignTag foreignChecked foreignActivation
          earlyWellFormed sourceTarget)
      paperTag movedEffect mapRuns

0 activationRawAfterForeignState :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, movedBefore : SystemState name key value world error} ->
  (leftAction, foreignAction : Action name key value world error) ->
  (leftTag, foreignTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, movedBefore)) ->
  (leftActivation : PaperActivationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  Not (actionOwner leftAction = actionOwner foreignAction) ->
  ((fiber : Fiber name key value world error) ->
    (view : View name (dependencies
      (componentDependencies (fiberComponent fiber)))) ->
    targetFiber @{nameEq} @{keyEq} fiber (registry first) = Just view ->
    targetFiber @{nameEq} @{keyEq} fiber (registry movedBefore) = Just view) ->
  (movedEffect : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq leftAction leftTag movedBefore
    (projectEffectState @{nameEq} movedBefore) = Just movedEffect ->
  RawActivationMove nameEq keyEq leftAction leftTag movedBefore
activationRawAfterForeignState nameEq keyEq leftAction foreignAction leftTag
  foreignTag leftChecked foreignChecked
  (PaperBeginStep actionSame tagSame) distinct targets movedEffect mapRuns =
    case actionSame of
      Refl => case tagSame of
        Refl => beginRawAfterForeignState nameEq keyEq _ foreignAction foreignTag
          leftChecked foreignChecked distinct targets
activationRawAfterForeignState nameEq keyEq leftAction foreignAction leftTag
  foreignTag leftChecked foreignChecked
  (PaperIterStep actionSame tagSame) distinct targets movedEffect mapRuns =
    case actionSame of
      Refl => case tagSame of
        Refl => advanceRawAfterForeignState nameEq keyEq _ LIterTag
          foreignAction foreignTag leftChecked foreignChecked distinct targets
          (Left Refl) movedEffect mapRuns
activationRawAfterForeignState nameEq keyEq leftAction foreignAction leftTag
  foreignTag leftChecked foreignChecked
  (PaperFinishStep actionSame tagSame) distinct targets movedEffect mapRuns =
    case actionSame of
      Refl => case tagSame of
        Refl => advanceRawAfterForeignState nameEq keyEq _ LFinishTag
          foreignAction foreignTag leftChecked foreignChecked distinct targets
          (Right Refl) movedEffect mapRuns

0 activationRawAfterForeignActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, earlyRightFinal : SystemState name key value world error} ->
  (leftAction, foreignAction : Action name key value world error) ->
  (leftTag, foreignTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, earlyRightFinal)) ->
  (leftActivation : PaperActivationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  (foreignActivation : PaperActivationStep
    (Fired {before = first} {afterState = earlyRightFinal}
      nameEq keyEq foreignAction foreignTag foreignChecked)) ->
  Not (actionOwner leftAction = actionOwner foreignAction) ->
  registryWellFormed @{nameEq} @{keyEq} earlyRightFinal = True ->
  (movedEffect : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
    (projectEffectState @{nameEq} earlyRightFinal) = Just movedEffect ->
  RawActivationMove nameEq keyEq leftAction leftTag earlyRightFinal
activationRawAfterForeignActivation nameEq keyEq leftAction foreignAction
  leftTag foreignTag leftChecked foreignChecked
  (PaperBeginStep actionSame tagSame) foreignActivation distinct earlyWellFormed
  movedEffect mapRuns = case actionSame of
    Refl => case tagSame of
      Refl => beginRawAfterForeignActivation nameEq keyEq _ foreignAction
        foreignTag leftChecked foreignChecked foreignActivation distinct
        earlyWellFormed
activationRawAfterForeignActivation nameEq keyEq leftAction foreignAction
  leftTag foreignTag leftChecked foreignChecked
  (PaperIterStep actionSame tagSame) foreignActivation distinct earlyWellFormed
  movedEffect mapRuns = case actionSame of
    Refl => case tagSame of
      Refl => advanceRawAfterForeignActivation nameEq keyEq _ LIterTag
        foreignAction foreignTag leftChecked foreignChecked foreignActivation
        distinct earlyWellFormed (Left Refl) movedEffect mapRuns
activationRawAfterForeignActivation nameEq keyEq leftAction foreignAction
  leftTag foreignTag leftChecked foreignChecked
  (PaperFinishStep actionSame tagSame) foreignActivation distinct earlyWellFormed
  movedEffect mapRuns = case actionSame of
    Refl => case tagSame of
      Refl => advanceRawAfterForeignActivation nameEq keyEq _ LFinishTag
        foreignAction foreignTag leftChecked foreignChecked foreignActivation
        distinct earlyWellFormed (Right Refl) movedEffect mapRuns

record CheckedActivationMove
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error) (tag : RuleTag)
  (before : SystemState name key value world error) where
  constructor MkCheckedActivationMove
  checkedActivationAfter : SystemState name key value world error
  0 checkedActivationRuns : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, checkedActivationAfter)
  checkedActivationTransition : Transition before checkedActivationAfter

0 checkRawActivationMove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  RawActivationMove nameEq keyEq action tag before ->
  CheckedActivationMove nameEq keyEq action tag before
checkRawActivationMove nameEq keyEq action tag before sourceWellFormed
  (MkRawActivationMove afterState raw) =
    let 0 afterWellFormed = preservationTheoremProof nameEq keyEq action before
          afterState tag sourceWellFormed raw
        0 checked : (checkedApplyAction @{nameEq} @{keyEq} action before =
          Just (tag, afterState))
        checked = rewrite raw in rewrite afterWellFormed in Refl
    in MkCheckedActivationMove afterState checked
      (Fired nameEq keyEq action tag checked)

0 advanceTransitionMapOriginCong :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState, other : SystemState name key value world error} ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry before) =
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor (registry other) ->
  (state : EffectState name key value world) ->
  partialEffectMap
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq (LAdvance actor) tag checked) state =
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag other state
advanceTransitionMapOriginCong nameEq keyEq actor LIterTag checked same state =
  advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor before other same
    state
advanceTransitionMapOriginCong nameEq keyEq actor LFinishTag checked same state =
  advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor before other same
    state
advanceTransitionMapOriginCong nameEq keyEq actor LDivertTag checked same state =
  advanceRuntimeEffectMapOriginLookupCong nameEq keyEq actor before other same
    state
advanceTransitionMapOriginCong nameEq keyEq actor LRaiseTag checked same state =
  Refl
advanceTransitionMapOriginCong nameEq keyEq actor OInsertTag checked same state =
  Refl
advanceTransitionMapOriginCong nameEq keyEq actor ORetireTag checked same state =
  Refl
advanceTransitionMapOriginCong nameEq keyEq actor ORemoveTag checked same state =
  Refl
advanceTransitionMapOriginCong nameEq keyEq actor LBeginTag checked same state =
  Refl
advanceTransitionMapOriginCong nameEq keyEq actor LLeaveTag checked same state =
  Refl
advanceTransitionMapOriginCong nameEq keyEq actor LUnloadTag checked same state =
  Refl

0 activationTransitionMapOriginCong :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState, other : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  PaperActivationStep
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} (actionOwner action) (registry before) =
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} (actionOwner action) (registry other) ->
  (state : EffectState name key value world) ->
  partialEffectMap
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) state =
  partialEffectMapFor nameEq keyEq action tag other state
activationTransitionMapOriginCong nameEq keyEq action tag checked
  (PaperBeginStep actionSame tagSame) lookupSame state =
    case actionSame of
      Refl => case tagSame of
        Refl => Refl
activationTransitionMapOriginCong nameEq keyEq action tag checked
  (PaperIterStep actionSame tagSame) lookupSame state =
    case actionSame of
      Refl => case tagSame of
        Refl => advanceTransitionMapOriginCong nameEq keyEq _ LIterTag checked
          lookupSame state
activationTransitionMapOriginCong nameEq keyEq action tag checked
  (PaperFinishStep actionSame tagSame) lookupSame state =
    case actionSame of
      Refl => case tagSame of
        Refl => advanceTransitionMapOriginCong nameEq keyEq _ LFinishTag checked
          lookupSame state

0 activationMapStableAfterForeignTransition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, activationAfter, foreignAfter :
    SystemState name key value world error} ->
  (activationAction, foreignAction : Action name key value world error) ->
  (activationTag, foreignTag : RuleTag) ->
  (activationChecked : checkedApplyAction @{nameEq} @{keyEq} activationAction
    first = Just (activationTag, activationAfter)) ->
  (foreignChecked : checkedApplyAction @{nameEq} @{keyEq} foreignAction first =
    Just (foreignTag, foreignAfter)) ->
  PaperActivationStep
    (Fired {before = first} {afterState = activationAfter}
      nameEq keyEq activationAction activationTag activationChecked) ->
  Not (actionOwner activationAction = actionOwner foreignAction) ->
  (state : EffectState name key value world) ->
  partialEffectMap
    (Fired {before = first} {afterState = activationAfter}
      nameEq keyEq activationAction activationTag activationChecked) state =
  partialEffectMapFor nameEq keyEq activationAction activationTag foreignAfter
    state
activationMapStableAfterForeignTransition nameEq keyEq activationAction
  foreignAction activationTag foreignTag activationChecked foreignChecked
  activation distinct state =
    activationTransitionMapOriginCong nameEq keyEq activationAction activationTag
      activationChecked activation
      (sym (transitionForeignLookup nameEq keyEq (actionOwner activationAction)
        foreignAction foreignTag foreignChecked distinct)) state

0 actualForwardGeneratorMapSame :
  (before, afterState : SystemState name key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) trace) ->
  (ownerSame : actionOwner action = actor) ->
  (state : EffectState name key value world) ->
  traceGeneratorMap
    (ActualForwardGenerator before afterState nameEq keyEq action tag checked
      occurs ownerSame) state =
  partialEffectMapFor nameEq keyEq action tag before state
actualForwardGeneratorMapSame before afterState nameEq keyEq action tag checked
  occurs ownerSame state = Refl

0 advanceSourceReloadingSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  (tagIsPaper : Either (tag = LIterTag) (tag = LFinishTag)) ->
  (providers : List name ** ReloadingSnapshot name key world error value nameEq
    actor providers before)
advanceSourceReloadingSnapshot nameEq keyEq actor {before} {afterState} tag
  checked tagIsPaper =
    let raw = checkedActionProjects nameEq keyEq (LAdvance actor) before
          afterState tag checked
        structure = advanceStructureTheorem nameEq keyEq actor before afterState
          tag raw
    in case structure of
      IterAdvance fiber found
        (remaining ** (accumulator ** (view ** (lifecycle, matches)))) endpoint =>
          (viewProviders view ** MkReloadingSnapshot fiber found remaining
            accumulator view lifecycle Refl)
      FinishAdvance fiber found
        (remaining ** (accumulator ** (view ** (lifecycle, matches)))) endpoint =>
          (viewProviders view ** MkReloadingSnapshot fiber found remaining
            accumulator view lifecycle Refl)
      DivertAdvance endpoint => case tagIsPaper of
        Left Refl impossible
        Right Refl impossible
      RaiseAdvance endpoint => case tagIsPaper of
        Left Refl impossible
        Right Refl impossible

0 reloadingSnapshotAfterForeignTransition :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  Not (selected = actionOwner action) ->
  ReloadingSnapshot name key world error value nameEq selected providers before ->
  ReloadingSnapshot name key world error value nameEq selected providers afterState
reloadingSnapshotAfterForeignTransition nameEq keyEq selected providers action tag
  checked distinct snapshot =
    MkReloadingSnapshot (snapshotFiber snapshot)
      (trans (transitionForeignLookup nameEq keyEq selected action tag checked
        distinct) (snapshotLookup snapshot))
      (snapshotRemaining snapshot) (snapshotAccumulator snapshot)
      (snapshotView snapshot) (snapshotReloading snapshot)
      (snapshotProviders snapshot)

0 advanceSourceSnapshotAfterForeignActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftActor, rightActor : name) -> Not (leftActor = rightActor) ->
  {first, middle, earlyRightFinal :
    SystemState name key value world error} ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance leftActor)
    first = Just (leftTag, middle)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (LAdvance rightActor) first = Just (rightTag, earlyRightFinal)) ->
  Either (leftTag = LIterTag) (leftTag = LFinishTag) ->
  (providers : List name ** ReloadingSnapshot name key world error value nameEq
    leftActor providers earlyRightFinal)
advanceSourceSnapshotAfterForeignActivation nameEq keyEq leftActor rightActor
  distinct leftTag rightTag leftChecked earlyRightChecked paperTag =
    case advanceSourceReloadingSnapshot nameEq keyEq leftActor leftTag
      leftChecked paperTag of
        (providers ** snapshot) =>
          (providers ** reloadingSnapshotAfterForeignTransition nameEq keyEq
            leftActor providers (LAdvance rightActor) rightTag earlyRightChecked
            distinct snapshot)

record ActivationPairEffectOutput
  (nameEq : DecEq name) (keyEq : DecEq key)
  (leftAction : Action name key value world error) (leftTag : RuleTag)
  (earlyRightFinal, originalFinal : SystemState name key value world error) where
  constructor MkActivationPairEffectOutput
  0 activationPairEffectState : EffectState name key value world
  0 movedLeftEffectMapRuns :
    partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
      (projectEffectState @{nameEq} earlyRightFinal) =
    Just activationPairEffectState
  0 originalToMovedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal) activationPairEffectState

0 activationPairEffectOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  PaperActivationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked) ->
  PaperActivationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = middle}
        nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions
        (Fired {before = middle} {afterState = originalFinal}
          nameEq keyEq rightAction rightTag rightChecked)
        NoTransitions)) ->
  ActivationPairEffectOutput nameEq keyEq leftAction leftTag earlyRightFinal
    originalFinal
activationPairEffectOutput nameEq keyEq {first} {middle} {originalFinal}
  {earlyRightFinal} leftAction rightAction leftTag rightTag leftChecked
  rightChecked earlyRightChecked leftActivation rightActivation distinct
  independent =
    let 0 pairTrace : Transitions first originalFinal
        pairTrace = MoreTransitions
          (Fired {before = first} {afterState = middle}
            nameEq keyEq leftAction leftTag leftChecked)
          (MoreTransitions
            (Fired {before = middle} {afterState = originalFinal}
              nameEq keyEq rightAction rightTag rightChecked)
            NoTransitions)
        0 leftOccurs : OccursIn
          (Fired {before = first} {afterState = middle}
            nameEq keyEq leftAction leftTag leftChecked) pairTrace
        leftOccurs = OccursHere
        0 rightOccurs : OccursIn
          (Fired {before = middle} {afterState = originalFinal}
            nameEq keyEq rightAction rightTag rightChecked) pairTrace
        rightOccurs = OccursLater OccursHere
        0 leftGenerator : TraceEffectGenerator name key world error value
          (actionOwner leftAction) pairTrace
        leftGenerator = ActualForwardGenerator first middle nameEq keyEq
          leftAction leftTag leftChecked leftOccurs Refl
        0 rightGenerator : TraceEffectGenerator name key world error value
          (actionOwner rightAction) pairTrace
        rightGenerator = ActualForwardGenerator middle originalFinal nameEq keyEq
          rightAction rightTag rightChecked rightOccurs Refl
        0 rightLookup :
          lookupFiber @{nameEq} {key = key} {value = value} {world = world}
            {error = error} (actionOwner rightAction) (registry middle) =
          lookupFiber @{nameEq} {key = key} {value = value} {world = world}
            {error = error} (actionOwner rightAction) (registry first)
        rightLookup = transitionForeignLookup nameEq keyEq
          (actionOwner rightAction) leftAction leftTag leftChecked
          (\same => distinct (sym same))
        0 leftMap : PartialEffectMap name key value world
        leftMap = partialEffectMapFor nameEq keyEq leftAction leftTag first
        0 rightMap : PartialEffectMap name key value world
        rightMap = partialEffectMapFor nameEq keyEq rightAction rightTag middle
        0 earlyRightMap : PartialEffectMap name key value world
        earlyRightMap = partialEffectMapFor nameEq keyEq rightAction rightTag first
        0 rightOriginSame : (state : EffectState name key value world) ->
          rightMap state = earlyRightMap state
        rightOriginSame = activationTransitionMapOriginCong nameEq keyEq
          rightAction rightTag rightChecked rightActivation rightLookup
        0 leftGeneratorMapSame : (state : EffectState name key value world) ->
          traceGeneratorMap leftGenerator state = leftMap state
        leftGeneratorMapSame = actualForwardGeneratorMapSame first middle nameEq
          keyEq leftAction leftTag leftChecked leftOccurs Refl
        0 rightGeneratorMapSame : (state : EffectState name key value world) ->
          traceGeneratorMap rightGenerator state = rightMap state
        rightGeneratorMapSame = actualForwardGeneratorMapSame middle originalFinal
          nameEq keyEq rightAction rightTag rightChecked rightOccurs Refl
        0 generatorCommute : PartialCommute (EffectStateEquivalence keyEq)
          (traceGeneratorMap leftGenerator) (traceGeneratorMap rightGenerator)
        generatorCommute = generatedMonoidsCommute independent
          (actionOwner leftAction) (actionOwner rightAction) distinct
          (TraceGenerator leftGenerator) (TraceGenerator rightGenerator)
        0 commute : PartialCommute (EffectStateEquivalence keyEq) leftMap rightMap
        commute = replayPartialCommuteTransport
          (traceGeneratorMap leftGenerator) leftMap
          (traceGeneratorMap rightGenerator) rightMap
          leftGeneratorMapSame rightGeneratorMapSame generatorCommute
        0 leftFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (leftMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} middle))
        leftFrame = checkedEffectFrameRelation nameEq keyEq leftAction leftTag
          first middle leftChecked
        0 rightFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (rightMap (projectEffectState @{nameEq} middle))
          (Just (projectEffectState @{nameEq} originalFinal))
        rightFrame = checkedEffectFrameRelation nameEq keyEq rightAction rightTag
          middle originalFinal rightChecked
        0 rawEarlyFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (earlyRightMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} earlyRightFinal))
        rawEarlyFrame = checkedEffectFrameRelation nameEq keyEq rightAction rightTag
          first earlyRightFinal earlyRightChecked
        0 earlyFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (rightMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} earlyRightFinal))
        earlyFrame = localPartialRelatedRewrite
          {leftBefore = earlyRightMap (projectEffectState @{nameEq} first)}
          {leftAfter = rightMap (projectEffectState @{nameEq} first)}
          {rightBefore = Just (projectEffectState @{nameEq} earlyRightFinal)}
          {rightAfter = Just (projectEffectState @{nameEq} earlyRightFinal)}
          (sym (rightOriginSame (projectEffectState @{nameEq} first))) Refl
          rawEarlyFrame
        0 commuted : CommutedEffectOutput keyEq leftMap rightMap
          (projectEffectState @{nameEq} first)
          (projectEffectState @{nameEq} middle)
          (projectEffectState @{nameEq} originalFinal)
          (projectEffectState @{nameEq} earlyRightFinal)
        commuted = commuteEffectFrames keyEq leftMap rightMap
          (partialEffectMapForRespects nameEq keyEq leftAction leftTag first)
          (partialEffectMapForRespects nameEq keyEq rightAction rightTag middle)
          commute (projectEffectState @{nameEq} first)
          (projectEffectState @{nameEq} middle)
          (projectEffectState @{nameEq} originalFinal)
          (projectEffectState @{nameEq} earlyRightFinal)
          leftFrame rightFrame earlyFrame
        0 movedMapSame : (state : EffectState name key value world) ->
          leftMap state =
            partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
              state
        movedMapSame = activationMapStableAfterForeignTransition nameEq keyEq
          leftAction rightAction leftTag rightTag leftChecked earlyRightChecked
          leftActivation distinct
        0 movedRuns :
          partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
            (projectEffectState @{nameEq} earlyRightFinal) =
          Just (commutedOutput commuted)
        movedRuns = trans
          (sym (movedMapSame (projectEffectState @{nameEq} earlyRightFinal)))
          (commutedLeftRuns commuted)
    in MkActivationPairEffectOutput (commutedOutput commuted) movedRuns
      (originalFinalToCommuted commuted)

0 orchestrationTransitionMapOriginCong :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  PaperOrchestrationStep
    (Fired {before} {afterState} nameEq keyEq action tag checked) ->
  (left, right : SystemState name key value world error) ->
  (state : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq action tag left state =
    partialEffectMapFor nameEq keyEq action tag right state
orchestrationTransitionMapOriginCong nameEq keyEq action tag checked
  (PaperInsertStep actionSame) left right state = case actionSame of
    Refl => Refl
orchestrationTransitionMapOriginCong nameEq keyEq action tag checked
  (PaperRetireStep actionSame) left right state = case actionSame of
    Refl => Refl
orchestrationTransitionMapOriginCong nameEq keyEq action tag checked
  (PaperRemoveStep actionSame) left right state = case actionSame of
    Refl => Refl


0 localSetEffectTableDistinctLookup :
  (nameEq : DecEq name) -> (candidate, left, right : name) ->
  Not (left = right) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  effectTables
    (setEffectTable @{nameEq} left leftTable
      (setEffectTable @{nameEq} right rightTable state)) candidate =
  effectTables
    (setEffectTable @{nameEq} right rightTable
      (setEffectTable @{nameEq} left leftTable state)) candidate
localSetEffectTableDistinctLookup nameEq candidate left right distinct leftTable
  rightTable state with (decEq @{nameEq} candidate left)
  localSetEffectTableDistinctLookup nameEq left left right distinct leftTable
    rightTable state | Yes Refl with (decEq @{nameEq} left right)
    localSetEffectTableDistinctLookup nameEq right right right distinct leftTable
      rightTable state | Yes Refl | Yes Refl = void (distinct Refl)
    localSetEffectTableDistinctLookup nameEq left left right distinct leftTable
      rightTable state | Yes Refl | No different
      with (decEq @{nameEq} left left)
      localSetEffectTableDistinctLookup nameEq left left right distinct leftTable
        rightTable state | Yes Refl | No different | Yes Refl = Refl
      localSetEffectTableDistinctLookup nameEq left left right distinct leftTable
        rightTable state | Yes Refl | No different | No absurd =
          void (absurd Refl)
  localSetEffectTableDistinctLookup nameEq candidate left right distinct leftTable
    rightTable state | No notLeft with (decEq @{nameEq} candidate right)
    localSetEffectTableDistinctLookup nameEq right left right distinct leftTable
      rightTable state | No notLeft | Yes Refl with (decEq @{nameEq} right left)
      localSetEffectTableDistinctLookup nameEq left left left distinct leftTable
        rightTable state | No notLeft | Yes Refl | Yes Refl =
          void (notLeft Refl)
      localSetEffectTableDistinctLookup nameEq right left right distinct leftTable
        rightTable state | No notLeft | Yes Refl | No different
        with (decEq @{nameEq} right right)
        localSetEffectTableDistinctLookup nameEq right left right distinct
          leftTable rightTable state | No notLeft | Yes Refl | No different |
          Yes Refl = Refl
        localSetEffectTableDistinctLookup nameEq right left right distinct
          leftTable rightTable state | No notLeft | Yes Refl | No different |
          No absurd = void (absurd Refl)
    localSetEffectTableDistinctLookup nameEq candidate left right distinct
      leftTable rightTable state | No notLeft | No notRight
      with (decEq @{nameEq} candidate left)
      localSetEffectTableDistinctLookup nameEq left left right distinct leftTable
        rightTable state | No notLeft | No notRight | Yes Refl =
          void (notLeft Refl)
      localSetEffectTableDistinctLookup nameEq candidate left right distinct
        leftTable rightTable state | No notLeft | No notRight | No stillNotLeft
        with (decEq @{nameEq} candidate right)
        localSetEffectTableDistinctLookup nameEq right left right distinct
          leftTable rightTable state | No notLeft | No notRight |
          No stillNotLeft | Yes Refl = void (notRight Refl)
        localSetEffectTableDistinctLookup nameEq candidate left right distinct
          leftTable rightTable state | No notLeft | No notRight |
          No stillNotLeft | No stillNotRight = Refl

0 setEffectTablesDistinctRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : name) -> Not (left = right) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} left leftTable
      (setEffectTable @{nameEq} right rightTable state))
    (setEffectTable @{nameEq} right rightTable
      (setEffectTable @{nameEq} left leftTable state))
setEffectTablesDistinctRelated nameEq keyEq left right distinct leftTable
  rightTable state = MkEffectStateRelated Refl
    (\candidate => cong bindings
      (localSetEffectTableDistinctLookup nameEq candidate left right distinct
        leftTable rightTable state))

0 effectSetTablesDistinctCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : name) -> Not (left = right) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (\state => Just (setEffectTable @{nameEq} left leftTable state))
    (\state => Just (setEffectTable @{nameEq} right rightTable state))
effectSetTablesDistinctCommute nameEq keyEq left right distinct leftTable
  rightTable state = PartialDefined
    (setEffectTablesDistinctRelated nameEq keyEq left right distinct leftTable
      rightTable state)

0 orchestrationEffectMapsCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  (rightPaper : PaperOrchestrationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked)) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (partialEffectMapFor nameEq keyEq leftAction leftTag first)
    (partialEffectMapFor nameEq keyEq rightAction rightTag middle)
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperInsertStep {actor = leftActor} {parent = leftParent}
    {component = leftComponent} leftSame)
  (PaperInsertStep {actor = rightActor} rightSame) distinct =
    case leftSame of
      Refl => case rightSame of
        Refl => effectSetTablesDistinctCommute nameEq keyEq leftActor rightActor
          distinct emptyContext emptyContext
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperInsertStep {actor = leftActor} {parent = leftParent}
    {component = leftComponent} leftSame)
  (PaperRetireStep {actor = rightActor} rightSame) distinct =
    case leftSame of
      Refl => case rightSame of
        Refl => effectIdentityOnRightCommutes keyEq
          (partialEffectMapFor nameEq keyEq
            (OInsert leftActor leftParent leftComponent) leftTag first)
          (partialEffectMapFor nameEq keyEq (ORetire rightActor) rightTag middle)
          (\state => Refl)
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperInsertStep {actor = leftActor} leftSame)
  (PaperRemoveStep {actor = rightActor} rightSame) distinct =
    case leftSame of
      Refl => case rightSame of
        Refl => effectSetTablesDistinctCommute nameEq keyEq leftActor rightActor
          distinct emptyContext emptyContext
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperRetireStep {actor = leftActor} leftSame) rightPaper distinct =
    case leftSame of
      Refl => effectIdentityOnLeftCommutes keyEq
        (partialEffectMapFor nameEq keyEq (ORetire leftActor) leftTag first)
        (\state => Refl)
        (partialEffectMapFor nameEq keyEq rightAction rightTag middle)
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperRemoveStep {actor = leftActor} leftSame)
  (PaperInsertStep {actor = rightActor} rightSame) distinct =
    case leftSame of
      Refl => case rightSame of
        Refl => effectSetTablesDistinctCommute nameEq keyEq leftActor rightActor
          distinct emptyContext emptyContext
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperRemoveStep {actor = leftActor} leftSame)
  (PaperRetireStep {actor = rightActor} rightSame) distinct =
    case leftSame of
      Refl => case rightSame of
        Refl => effectIdentityOnRightCommutes keyEq
          (partialEffectMapFor nameEq keyEq (ORemove leftActor) leftTag first)
          (partialEffectMapFor nameEq keyEq (ORetire rightActor) rightTag middle)
          (\state => Refl)
orchestrationEffectMapsCommute nameEq keyEq leftAction rightAction leftTag
  rightTag leftChecked rightChecked
  (PaperRemoveStep {actor = leftActor} leftSame)
  (PaperRemoveStep {actor = rightActor} rightSame) distinct =
    case leftSame of
      Refl => case rightSame of
        Refl => effectSetTablesDistinctCommute nameEq keyEq leftActor rightActor
          distinct emptyContext emptyContext

0 orchestrationPairEffectOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  (rightPaper : PaperOrchestrationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked)) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  ActivationPairEffectOutput nameEq keyEq leftAction leftTag earlyRightFinal
    originalFinal
orchestrationPairEffectOutput nameEq keyEq {first} {middle} {originalFinal}
  {earlyRightFinal} leftAction rightAction leftTag rightTag leftChecked
  rightChecked earlyRightChecked leftPaper rightPaper distinct =
    let 0 leftMap : PartialEffectMap name key value world
        leftMap = partialEffectMapFor nameEq keyEq leftAction leftTag first
        0 rightMap : PartialEffectMap name key value world
        rightMap = partialEffectMapFor nameEq keyEq rightAction rightTag middle
        0 earlyRightMap : PartialEffectMap name key value world
        earlyRightMap = partialEffectMapFor nameEq keyEq rightAction rightTag first
        0 leftFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (leftMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} middle))
        leftFrame = checkedEffectFrameRelation nameEq keyEq leftAction leftTag
          first middle leftChecked
        0 rightFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (rightMap (projectEffectState @{nameEq} middle))
          (Just (projectEffectState @{nameEq} originalFinal))
        rightFrame = checkedEffectFrameRelation nameEq keyEq rightAction rightTag
          middle originalFinal rightChecked
        0 rawEarlyFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (earlyRightMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} earlyRightFinal))
        rawEarlyFrame = checkedEffectFrameRelation nameEq keyEq rightAction
          rightTag first earlyRightFinal earlyRightChecked
        0 rightOriginSame : (state : EffectState name key value world) ->
          rightMap state = earlyRightMap state
        rightOriginSame = orchestrationTransitionMapOriginCong nameEq keyEq
          rightAction rightTag rightChecked rightPaper middle first
        0 earlyFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (rightMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} earlyRightFinal))
        earlyFrame = localPartialRelatedRewrite
          (sym (rightOriginSame (projectEffectState @{nameEq} first))) Refl
          rawEarlyFrame
        0 commute : PartialCommute (EffectStateEquivalence keyEq) leftMap rightMap
        commute = orchestrationEffectMapsCommute nameEq keyEq leftAction
          rightAction leftTag rightTag leftChecked rightChecked leftPaper
          rightPaper distinct
        0 commuted : CommutedEffectOutput keyEq leftMap rightMap
          (projectEffectState @{nameEq} first)
          (projectEffectState @{nameEq} middle)
          (projectEffectState @{nameEq} originalFinal)
          (projectEffectState @{nameEq} earlyRightFinal)
        commuted = commuteEffectFrames keyEq leftMap rightMap
          (partialEffectMapForRespects nameEq keyEq leftAction leftTag first)
          (partialEffectMapForRespects nameEq keyEq rightAction rightTag middle)
          commute (projectEffectState @{nameEq} first)
          (projectEffectState @{nameEq} middle)
          (projectEffectState @{nameEq} originalFinal)
          (projectEffectState @{nameEq} earlyRightFinal)
          leftFrame rightFrame earlyFrame
        0 leftMovedSame : (state : EffectState name key value world) ->
          leftMap state =
            partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
              state
        leftMovedSame = orchestrationTransitionMapOriginCong nameEq keyEq
          leftAction leftTag leftChecked leftPaper first earlyRightFinal
        0 movedRuns :
          partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
            (projectEffectState @{nameEq} earlyRightFinal) =
          Just (commutedOutput commuted)
        movedRuns = trans
          (sym (leftMovedSame (projectEffectState @{nameEq} earlyRightFinal)))
          (commutedLeftRuns commuted)
    in MkActivationPairEffectOutput (commutedOutput commuted) movedRuns
      (originalFinalToCommuted commuted)

0 pairEffectOutputFromOriginCong :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  ((state : EffectState name key value world) ->
    partialEffectMapFor nameEq keyEq rightAction rightTag middle state =
      partialEffectMapFor nameEq keyEq rightAction rightTag first state) ->
  ((state : EffectState name key value world) ->
    partialEffectMapFor nameEq keyEq leftAction leftTag first state =
      partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal state) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = middle}
        nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions
        (Fired {before = middle} {afterState = originalFinal}
          nameEq keyEq rightAction rightTag rightChecked)
        NoTransitions)) ->
  ActivationPairEffectOutput nameEq keyEq leftAction leftTag earlyRightFinal
    originalFinal
pairEffectOutputFromOriginCong nameEq keyEq {first} {middle} {originalFinal}
  {earlyRightFinal} leftAction rightAction leftTag rightTag leftChecked
  rightChecked earlyRightChecked rightOriginSame leftMovedSame distinct
  independent =
    let pairTrace : Transitions first originalFinal
        pairTrace = MoreTransitions
          (Fired {before = first} {afterState = middle}
            nameEq keyEq leftAction leftTag leftChecked)
          (MoreTransitions
            (Fired {before = middle} {afterState = originalFinal}
              nameEq keyEq rightAction rightTag rightChecked)
            NoTransitions)
        0 leftOccurs : OccursIn
          (Fired {before = first} {afterState = middle}
            nameEq keyEq leftAction leftTag leftChecked) pairTrace
        leftOccurs = OccursHere
        0 rightOccurs : OccursIn
          (Fired {before = middle} {afterState = originalFinal}
            nameEq keyEq rightAction rightTag rightChecked) pairTrace
        rightOccurs = OccursLater OccursHere
        0 leftGenerator : TraceEffectGenerator name key world error value
          (actionOwner leftAction) pairTrace
        leftGenerator = ActualForwardGenerator first middle nameEq keyEq
          leftAction leftTag leftChecked leftOccurs Refl
        0 rightGenerator : TraceEffectGenerator name key world error value
          (actionOwner rightAction) pairTrace
        rightGenerator = ActualForwardGenerator middle originalFinal nameEq keyEq
          rightAction rightTag rightChecked rightOccurs Refl
        0 leftMap : PartialEffectMap name key value world
        leftMap = partialEffectMapFor nameEq keyEq leftAction leftTag first
        0 rightMap : PartialEffectMap name key value world
        rightMap = partialEffectMapFor nameEq keyEq rightAction rightTag middle
        0 earlyRightMap : PartialEffectMap name key value world
        earlyRightMap = partialEffectMapFor nameEq keyEq rightAction rightTag first
        0 leftGeneratorMapSame : (state : EffectState name key value world) ->
          traceGeneratorMap leftGenerator state = leftMap state
        leftGeneratorMapSame = actualForwardGeneratorMapSame first middle nameEq
          keyEq leftAction leftTag leftChecked leftOccurs Refl
        0 rightGeneratorMapSame : (state : EffectState name key value world) ->
          traceGeneratorMap rightGenerator state = rightMap state
        rightGeneratorMapSame = actualForwardGeneratorMapSame middle originalFinal
          nameEq keyEq rightAction rightTag rightChecked rightOccurs Refl
        0 generatorCommute : PartialCommute (EffectStateEquivalence keyEq)
          (traceGeneratorMap leftGenerator) (traceGeneratorMap rightGenerator)
        generatorCommute = generatedMonoidsCommute independent
          (actionOwner leftAction) (actionOwner rightAction) distinct
          (TraceGenerator leftGenerator) (TraceGenerator rightGenerator)
        0 commute : PartialCommute (EffectStateEquivalence keyEq) leftMap rightMap
        commute = replayPartialCommuteTransport
          (traceGeneratorMap leftGenerator) leftMap
          (traceGeneratorMap rightGenerator) rightMap
          leftGeneratorMapSame rightGeneratorMapSame generatorCommute
        0 leftFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (leftMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} middle))
        leftFrame = checkedEffectFrameRelation nameEq keyEq leftAction leftTag
          first middle leftChecked
        0 rightFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (rightMap (projectEffectState @{nameEq} middle))
          (Just (projectEffectState @{nameEq} originalFinal))
        rightFrame = checkedEffectFrameRelation nameEq keyEq rightAction rightTag
          middle originalFinal rightChecked
        0 rawEarlyFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (earlyRightMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} earlyRightFinal))
        rawEarlyFrame = checkedEffectFrameRelation nameEq keyEq rightAction rightTag
          first earlyRightFinal earlyRightChecked
        0 earlyFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (rightMap (projectEffectState @{nameEq} first))
          (Just (projectEffectState @{nameEq} earlyRightFinal))
        earlyFrame = localPartialRelatedRewrite
          (sym (rightOriginSame (projectEffectState @{nameEq} first))) Refl
          rawEarlyFrame
        0 commuted : CommutedEffectOutput keyEq leftMap rightMap
          (projectEffectState @{nameEq} first)
          (projectEffectState @{nameEq} middle)
          (projectEffectState @{nameEq} originalFinal)
          (projectEffectState @{nameEq} earlyRightFinal)
        commuted = commuteEffectFrames keyEq leftMap rightMap
          (partialEffectMapForRespects nameEq keyEq leftAction leftTag first)
          (partialEffectMapForRespects nameEq keyEq rightAction rightTag middle)
          commute (projectEffectState @{nameEq} first)
          (projectEffectState @{nameEq} middle)
          (projectEffectState @{nameEq} originalFinal)
          (projectEffectState @{nameEq} earlyRightFinal)
          leftFrame rightFrame earlyFrame
        0 movedRuns :
          partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal
            (projectEffectState @{nameEq} earlyRightFinal) =
          Just (commutedOutput commuted)
        movedRuns = trans
          (sym (leftMovedSame (projectEffectState @{nameEq} earlyRightFinal)))
          (commutedLeftRuns commuted)
    in MkActivationPairEffectOutput (commutedOutput commuted) movedRuns
      (originalFinalToCommuted commuted)

0 activationOrchestrationPairEffectOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  PaperActivationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked) ->
  PaperOrchestrationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = middle}
        nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions
        (Fired {before = middle} {afterState = originalFinal}
          nameEq keyEq rightAction rightTag rightChecked)
        NoTransitions)) ->
  ActivationPairEffectOutput nameEq keyEq leftAction leftTag earlyRightFinal
    originalFinal
activationOrchestrationPairEffectOutput nameEq keyEq leftAction rightAction
  leftTag rightTag leftChecked rightChecked earlyRightChecked leftActivation
  rightOrchestration distinct independent =
    pairEffectOutputFromOriginCong nameEq keyEq leftAction rightAction leftTag
      rightTag leftChecked rightChecked earlyRightChecked
      (orchestrationTransitionMapOriginCong nameEq keyEq rightAction rightTag
        rightChecked rightOrchestration middle first)
      (activationMapStableAfterForeignTransition nameEq keyEq leftAction
        rightAction leftTag rightTag leftChecked earlyRightChecked leftActivation
        distinct)
      distinct independent

0 orchestrationActivationPairEffectOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked) ->
  PaperActivationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = middle}
        nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions
        (Fired {before = middle} {afterState = originalFinal}
          nameEq keyEq rightAction rightTag rightChecked)
        NoTransitions)) ->
  ActivationPairEffectOutput nameEq keyEq leftAction leftTag earlyRightFinal
    originalFinal
orchestrationActivationPairEffectOutput nameEq keyEq leftAction rightAction
  leftTag rightTag leftChecked rightChecked earlyRightChecked leftOrchestration
  rightActivation distinct independent =
    let 0 rightLookup : (lookupFiber @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error}
          (actionOwner rightAction) (registry middle) =
        lookupFiber @{nameEq} {name = name} {key = key} {value = value}
          {world = world} {error = error} (actionOwner rightAction)
          (registry first))
        rightLookup = transitionForeignLookup nameEq keyEq
          (actionOwner rightAction) leftAction leftTag leftChecked
          (\same => distinct (sym same))
        0 rightOriginSame : (state : EffectState name key value world) ->
          partialEffectMapFor nameEq keyEq rightAction rightTag middle state =
          partialEffectMapFor nameEq keyEq rightAction rightTag first state
        rightOriginSame = activationTransitionMapOriginCong nameEq keyEq
          rightAction rightTag rightChecked rightActivation rightLookup
        0 leftMovedSame : (state : EffectState name key value world) ->
          partialEffectMapFor nameEq keyEq leftAction leftTag first state =
          partialEffectMapFor nameEq keyEq leftAction leftTag earlyRightFinal state
        leftMovedSame = orchestrationTransitionMapOriginCong nameEq keyEq
          leftAction leftTag leftChecked leftOrchestration first earlyRightFinal
    in pairEffectOutputFromOriginCong nameEq keyEq leftAction rightAction leftTag
      rightTag leftChecked rightChecked earlyRightChecked rightOriginSame
      leftMovedSame distinct independent

record CheckedActivationEndpoint
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error) (tag : RuleTag)
  (before, originalFinal : SystemState name key value world error) where
  constructor MkCheckedActivationEndpoint
  checkedEndpointAfter : SystemState name key value world error
  checkedEndpointTransition : Transition before checkedEndpointAfter
  0 checkedEndpointEquation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, checkedEndpointAfter)
  0 checkedEndpointTransitionExact : checkedEndpointTransition =
    Fired nameEq keyEq action tag checkedEndpointEquation
  0 checkedEndpointAction :
    transitionAction checkedEndpointTransition = action
  0 checkedEndpointTag : transitionTag checkedEndpointTransition = tag
  0 checkedEndpointEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} checkedEndpointAfter)
  0 checkedEndpointWellFormed : registryWellFormed @{nameEq} @{keyEq}
    checkedEndpointAfter = True

0 checkActivationEndpoint :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, originalFinal : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  (effectOutput : ActivationPairEffectOutput nameEq keyEq action tag before
    originalFinal) ->
  RawActivationMove nameEq keyEq action tag before ->
  CheckedActivationEndpoint nameEq keyEq action tag before originalFinal
checkActivationEndpoint nameEq keyEq action tag before originalFinal
  sourceWellFormed effectOutput rawMove =
    case checkRawActivationMove nameEq keyEq action tag before sourceWellFormed
      rawMove of
      MkCheckedActivationMove afterState checked transition =>
        let 0 actualFrame = checkedEffectFrameRelation nameEq keyEq action tag
              before afterState checked
            0 exactFrame : PartialRelated (EffectState name key value world)
              (EffectStateRelated keyEq)
              (Just (activationPairEffectState effectOutput))
              (Just (projectEffectState @{nameEq} afterState))
            exactFrame = localPartialRelatedRewrite
              (movedLeftEffectMapRuns effectOutput) Refl actualFrame
            0 commutedToActual : EffectStateRelated keyEq
              (activationPairEffectState effectOutput)
              (projectEffectState @{nameEq} afterState)
            commutedToActual = localPartialDefinedRelation exactFrame
            0 originalToActual : EffectStateRelated keyEq
              (projectEffectState @{nameEq} originalFinal)
              (projectEffectState @{nameEq} afterState)
            originalToActual = localEffectStateTransitive
              (originalToMovedEffects effectOutput) commutedToActual
            0 afterWellFormed : (registryWellFormed @{nameEq} @{keyEq}
              afterState = True)
            afterWellFormed = preservationTheoremProof nameEq keyEq action
              before afterState tag sourceWellFormed
              (checkedActionProjects nameEq keyEq action before afterState tag
                checked)
            exactTransition : Transition before afterState
            exactTransition = Fired nameEq keyEq action tag checked
        in MkCheckedActivationEndpoint afterState exactTransition checked Refl
          Refl Refl originalToActual afterWellFormed

0 paperActivationStepTransport :
  {left : Transition leftBefore leftAfter} ->
  {right : Transition rightBefore rightAfter} ->
  transitionAction right = transitionAction left ->
  transitionTag right = transitionTag left ->
  PaperActivationStep left -> PaperActivationStep right
paperActivationStepTransport actionSame tagSame
  (PaperBeginStep actionIsBegin tagIsBegin) =
    PaperBeginStep (trans actionSame actionIsBegin) (trans tagSame tagIsBegin)
paperActivationStepTransport actionSame tagSame
  (PaperIterStep actionIsAdvance tagIsIter) =
    PaperIterStep (trans actionSame actionIsAdvance) (trans tagSame tagIsIter)
paperActivationStepTransport actionSame tagSame
  (PaperFinishStep actionIsAdvance tagIsFinish) =
    PaperFinishStep (trans actionSame actionIsAdvance) (trans tagSame tagIsFinish)

0 paperOrchestrationStepTransport :
  {left : Transition leftBefore leftAfter} ->
  {right : Transition rightBefore rightAfter} ->
  transitionAction right = transitionAction left ->
  transitionTag right = transitionTag left ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right
paperOrchestrationStepTransport actionSame tagSame
  (PaperInsertStep actionIsInsert) =
    PaperInsertStep (trans actionSame actionIsInsert)
paperOrchestrationStepTransport actionSame tagSame
  (PaperRetireStep actionIsRetire) =
    PaperRetireStep (trans actionSame actionIsRetire)
paperOrchestrationStepTransport actionSame tagSame
  (PaperRemoveStep actionIsRemove) =
    PaperRemoveStep (trans actionSame actionIsRemove)

0 paperActivationOrchestrationImpossible :
  PaperActivationStep transition -> PaperOrchestrationStep transition -> Void
paperActivationOrchestrationImpossible (PaperBeginStep activationAction tag)
  (PaperInsertStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperBeginStep activationAction tag)
  (PaperRetireStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperBeginStep activationAction tag)
  (PaperRemoveStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperIterStep activationAction tag)
  (PaperInsertStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperIterStep activationAction tag)
  (PaperRetireStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperIterStep activationAction tag)
  (PaperRemoveStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperFinishStep activationAction tag)
  (PaperInsertStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperFinishStep activationAction tag)
  (PaperRetireStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible
paperActivationOrchestrationImpossible (PaperFinishStep activationAction tag)
  (PaperRemoveStep orchestrationAction) =
    case trans (sym activationAction) orchestrationAction of Refl impossible

0 checkedActivationEquationTransport :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fromAction, toAction : Action name key value world error) ->
  fromAction = toAction ->
  (fromTag, toTag : RuleTag) -> fromTag = toTag ->
  {before, afterState : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} fromAction before =
    Just (fromTag, afterState) ->
  checkedApplyAction @{nameEq} @{keyEq} toAction before =
    Just (toTag, afterState)
checkedActivationEquationTransport nameEq keyEq fromAction fromAction Refl
  fromTag fromTag Refl checked = checked

0 transitionActorFiredActionOwner :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  transitionActor (Fired {before} {afterState}
    nameEq keyEq action tag checked) = actionOwner action
transitionActorFiredActionOwner nameEq keyEq (OInsert actor parent component)
  tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (ORetire actor) tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (ORemove actor) tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (LBegin actor) tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (LAdvance actor) tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (LDivert actor) tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (LLeave actor) tag checked = Refl
transitionActorFiredActionOwner nameEq keyEq (LUnload actor) tag checked = Refl

record ActivationReplacementComparison
  (nameEq : DecEq name) (actor : name)
  (sourceBefore, sourceAfter, movedBefore, movedAfter :
    SystemState name key value world error) where
  constructor MkActivationReplacementComparison
  sourceReplacementFiber : Fiber name key value world error
  movedReplacementFiber : Fiber name key value world error
  sourcePreviousFiber : Fiber name key value world error
  movedPreviousFiber : Fiber name key value world error
  0 sourcePreviousFound : lookupFiber @{nameEq} actor (registry sourceBefore) =
    Just sourcePreviousFiber
  0 movedPreviousFound : lookupFiber @{nameEq} actor (registry movedBefore) =
    Just movedPreviousFiber
  0 sourceReplacementStaticComponent :
    fiberComponent sourceReplacementFiber = fiberComponent sourcePreviousFiber
  0 movedReplacementStaticComponent :
    fiberComponent movedReplacementFiber = fiberComponent movedPreviousFiber
  0 sourceReplacementStaticParent :
    fiberParent sourceReplacementFiber = fiberParent sourcePreviousFiber
  0 movedReplacementStaticParent :
    fiberParent movedReplacementFiber = fiberParent movedPreviousFiber
  0 replacementFibersRelated : FiberControlRelated sourceReplacementFiber
    movedReplacementFiber
  0 sourceReplacementRegistry : registry sourceAfter =
    replaceBinding @{nameEq} actor sourceReplacementFiber
      (registry sourceBefore)
  0 movedReplacementRegistry : registry movedAfter =
    replaceBinding @{nameEq} actor movedReplacementFiber
      (registry movedBefore)
  0 sourceReplacementBindings : bindings (registry sourceAfter) =
    replaceEntries @{nameEq} actor sourceReplacementFiber
      (bindings (registry sourceBefore))
  0 movedReplacementBindings : bindings (registry movedAfter) =
    replaceEntries @{nameEq} actor movedReplacementFiber
      (bindings (registry movedBefore))

0 activationReplacementComparisonSymmetric :
  ActivationReplacementComparison nameEq actor sourceBefore sourceAfter
    movedBefore movedAfter ->
  ActivationReplacementComparison nameEq actor movedBefore movedAfter
    sourceBefore sourceAfter
activationReplacementComparisonSymmetric
  (MkActivationReplacementComparison sourceNext movedNext sourceOld movedOld
    sourceFound movedFound sourceComponent movedComponent sourceParent
    movedParent related sourceRegistry movedRegistry sourceBindings
    movedBindings) =
      MkActivationReplacementComparison movedNext sourceNext movedOld sourceOld
        movedFound sourceFound movedComponent sourceComponent movedParent
        sourceParent (fiberControlSymmetric related) movedRegistry sourceRegistry
        movedBindings sourceBindings

0 beginReplacementComparison :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (sourceFound : lookupFiber @{nameEq} actor sourceRegistry = Just
    (MkFiber component parent False table (Inactive Nothing))) ->
  (movedFound : lookupFiber @{nameEq} actor movedRegistry = Just
    (MkFiber component parent False table (Inactive Nothing))) ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent False table (Inactive Nothing)) sourceRegistry =
    Just view ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent False table (Inactive Nothing)) movedRegistry =
    Just view ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState sourceAmbient sourceRegistry) =
    Just (LBeginTag, sourceAfter) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState movedAmbient movedRegistry) =
    Just (LBeginTag, movedAfter) ->
  ActivationReplacementComparison nameEq actor
    (MkSystemState sourceAmbient sourceRegistry) sourceAfter
    (MkSystemState movedAmbient movedRegistry) movedAfter
beginReplacementComparison nameEq keyEq actor sourceAmbient movedAmbient
  sourceRegistry movedRegistry component parent table view sourceAfter movedAfter
  sourceFound movedFound sourceTarget movedTarget sourceRaw movedRaw =
    let oldFiber : Fiber name key value world error
        oldFiber = MkFiber component parent False table (Inactive Nothing)
        nextFiber : Fiber name key value world error
        nextFiber = setFiberLifecycle oldFiber
          (Reloading (componentProgram component) id view)
        sourceExpected : SystemState name key value world error
        sourceExpected = MkSystemState sourceAmbient
          (replaceBinding @{nameEq} actor nextFiber sourceRegistry)
        movedExpected : SystemState name key value world error
        movedExpected = MkSystemState movedAmbient
          (replaceBinding @{nameEq} actor nextFiber movedRegistry)
        0 sourceConcrete : applyAction @{nameEq} @{keyEq} (LBegin actor)
          (MkSystemState sourceAmbient sourceRegistry) =
          Just (LBeginTag, sourceExpected)
        sourceConcrete = rewrite sourceFound in rewrite sourceTarget in Refl
        0 movedConcrete : applyAction @{nameEq} @{keyEq} (LBegin actor)
          (MkSystemState movedAmbient movedRegistry) =
          Just (LBeginTag, movedExpected)
        movedConcrete = rewrite movedFound in rewrite movedTarget in Refl
        0 sourcePairSame : (LBeginTag, sourceExpected) =
          (LBeginTag, sourceAfter)
        sourcePairSame = justInjective (trans (sym sourceConcrete) sourceRaw)
        0 movedPairSame : (LBeginTag, movedExpected) =
          (LBeginTag, movedAfter)
        movedPairSame = justInjective (trans (sym movedConcrete) movedRaw)
    in case sourcePairSame of
      Refl => case movedPairSame of
        Refl => MkActivationReplacementComparison nextFiber nextFiber
          oldFiber oldFiber sourceFound movedFound Refl Refl Refl Refl
          (fiberControlReflexive nextFiber) Refl Refl
          (replaceBindingRuntimeBindings nameEq actor nextFiber sourceRegistry)
          (replaceBindingRuntimeBindings nameEq actor nextFiber movedRegistry)

0 emptyFinishReplacementComparison :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (sourceFound : lookupFiber @{nameEq} actor sourceRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading [] accumulator view))) ->
  (movedFound : lookupFiber @{nameEq} actor movedRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading [] accumulator view))) ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading [] accumulator view)) sourceRegistry = Just view ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading [] accumulator view)) movedRegistry = Just view ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState sourceAmbient sourceRegistry) =
    Just (LFinishTag, sourceAfter) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState movedAmbient movedRegistry) =
    Just (LFinishTag, movedAfter) ->
  ActivationReplacementComparison nameEq actor
    (MkSystemState sourceAmbient sourceRegistry) sourceAfter
    (MkSystemState movedAmbient movedRegistry) movedAfter
emptyFinishReplacementComparison nameEq keyEq actor sourceAmbient movedAmbient
  sourceRegistry movedRegistry component parent retiredFlag table accumulator view
  sourceAfter movedAfter sourceFound movedFound sourceTarget movedTarget sourceRaw
  movedRaw =
    let oldFiber : Fiber name key value world error
        oldFiber = MkFiber component parent retiredFlag table
          (Reloading [] accumulator view)
        nextFiber : Fiber name key value world error
        nextFiber = setFiberLifecycle oldFiber (Active accumulator view)
        sourceExpected : SystemState name key value world error
        sourceExpected = MkSystemState sourceAmbient
          (replaceBinding @{nameEq} actor nextFiber sourceRegistry)
        movedExpected : SystemState name key value world error
        movedExpected = MkSystemState movedAmbient
          (replaceBinding @{nameEq} actor nextFiber movedRegistry)
        0 sourceConcrete : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          (MkSystemState sourceAmbient sourceRegistry) =
          Just (LFinishTag, sourceExpected)
        sourceConcrete = rewrite sourceFound in rewrite sourceTarget in
          rewrite localViewEqRefl nameEq view in Refl
        0 movedConcrete : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          (MkSystemState movedAmbient movedRegistry) =
          Just (LFinishTag, movedExpected)
        movedConcrete = rewrite movedFound in rewrite movedTarget in
          rewrite localViewEqRefl nameEq view in Refl
        0 sourcePairSame : (LFinishTag, sourceExpected) =
          (LFinishTag, sourceAfter)
        sourcePairSame = justInjective (trans (sym sourceConcrete) sourceRaw)
        0 movedPairSame : (LFinishTag, movedExpected) =
          (LFinishTag, movedAfter)
        movedPairSame = justInjective (trans (sym movedConcrete) movedRaw)
    in case sourcePairSame of
      Refl => case movedPairSame of
        Refl => MkActivationReplacementComparison nextFiber nextFiber
          oldFiber oldFiber sourceFound movedFound Refl Refl Refl Refl
          (fiberControlReflexive nextFiber) Refl Refl
          (replaceBindingRuntimeBindings nameEq actor nextFiber sourceRegistry)
          (replaceBindingRuntimeBindings nameEq actor nextFiber movedRegistry)

0 localPartialEffectRelatedSymmetric :
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    left right ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    right left
localPartialEffectRelatedSymmetric PartialUndefined = PartialUndefined
localPartialEffectRelatedSymmetric (PartialDefined related) =
  PartialDefined (localEffectStateSymmetric related)

0 localPartialMapsEquivalentSymmetric :
  PartialMapsEquivalent (EffectStateEquivalence keyEq) left right ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq) right left
localPartialMapsEquivalentSymmetric maps input =
  localPartialEffectRelatedSymmetric (maps input)

0 pushedAccumulatorRelatedFromMovedUndoMaps :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (sourceUndo, movedUndo : LocalState key value world provision ->
    LocalState key value world provision) ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq)
    (yieldedInverseEffectMap nameEq keyEq actor provision movedUndo)
    (yieldedInverseEffectMap nameEq keyEq actor provision sourceUndo) ->
  AccumulatorRelated
    (pushLocalUndo @{keyEq} provision accumulator sourceUndo)
    (pushLocalUndo @{keyEq} provision accumulator movedUndo)
pushedAccumulatorRelatedFromMovedUndoMaps nameEq keyEq actor provision
  accumulator sourceUndo movedUndo movedToSourceUndo =
    let 0 sourceToMovedUndo : PartialMapsEquivalent
          (EffectStateEquivalence keyEq)
          (yieldedInverseEffectMap nameEq keyEq actor provision sourceUndo)
          (yieldedInverseEffectMap nameEq keyEq actor provision movedUndo)
        sourceToMovedUndo = localPartialMapsEquivalentSymmetric movedToSourceUndo
        0 undosRelated : (input : LocalState key value world provision) ->
          LocalStateRuntimeRelated
            (sourceUndo (normalizeLocal @{keyEq} provision input))
            (movedUndo (normalizeLocal @{keyEq} provision input))
        undosRelated = yieldedMapsGiveLocalUndoRuntimeRelated nameEq keyEq actor
          provision sourceUndo movedUndo sourceToMovedUndo
    in pushLocalUndoRuntimeRelated keyEq provision accumulator accumulator
      sourceUndo movedUndo (\input => localStateRuntimeReflexive _) undosRelated

0 successfulFinishReplacementComparison :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (sourceFound : lookupFiber @{nameEq} actor sourceRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading [step] accumulator view))) ->
  (movedFound : lookupFiber @{nameEq} actor movedRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading [step] accumulator view))) ->
  (sourceCapability, movedCapability : DepValues key value
    (dependencies (componentDependencies component))) ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view sourceRegistry =
    Just sourceCapability ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view movedRegistry =
    Just movedCapability ->
  (sourceLocalAfter, movedLocalAfter :
    LocalState key value world (componentProvisions component)) ->
  (sourceUndo, movedUndo :
    LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  runStepEffect step sourceCapability
    (MkLocalState sourceAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues table))) = Right (sourceLocalAfter, sourceUndo) ->
  runStepEffect step movedCapability
    (MkLocalState movedAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues table))) = Right (movedLocalAfter, movedUndo) ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) movedUndo)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) sourceUndo) ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading [step] accumulator view)) sourceRegistry = Just view ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading [step] accumulator view)) movedRegistry = Just view ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState sourceAmbient sourceRegistry) =
    Just (LFinishTag, sourceAfter) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState movedAmbient movedRegistry) =
    Just (LFinishTag, movedAfter) ->
  ActivationReplacementComparison nameEq actor
    (MkSystemState sourceAmbient sourceRegistry) sourceAfter
    (MkSystemState movedAmbient movedRegistry) movedAfter
successfulFinishReplacementComparison nameEq keyEq actor sourceAmbient
  movedAmbient sourceRegistry movedRegistry component parent retiredFlag table
  step accumulator view sourceAfter movedAfter sourceFound movedFound
  sourceCapability movedCapability sourceResolved movedResolved sourceLocalAfter
  movedLocalAfter sourceUndo movedUndo sourceRan movedRan movedToSourceUndo
  sourceTarget movedTarget sourceRaw movedRaw =
    let oldFiber : Fiber name key value world error
        oldFiber = MkFiber component parent retiredFlag table
          (Reloading [step] accumulator view)
        sourcePushed = pushLocalUndo @{keyEq}
          (componentProvisions component) accumulator sourceUndo
        movedPushed = pushLocalUndo @{keyEq}
          (componentProvisions component) accumulator movedUndo
        sourceNext : Fiber name key value world error
        sourceNext = setFiberRuntime oldFiber (localTable sourceLocalAfter)
          (Active sourcePushed view)
        movedNext : Fiber name key value world error
        movedNext = setFiberRuntime oldFiber (localTable movedLocalAfter)
          (Active movedPushed view)
        0 pushedRelated : AccumulatorRelated
          (pushLocalUndo @{keyEq} (componentProvisions component) accumulator
            sourceUndo)
          (pushLocalUndo @{keyEq} (componentProvisions component) accumulator
            movedUndo)
        pushedRelated = pushedAccumulatorRelatedFromMovedUndoMaps nameEq keyEq
          actor (componentProvisions component) accumulator sourceUndo movedUndo
          movedToSourceUndo
        0 nextRelated : FiberControlRelated sourceNext movedNext
        nextRelated = FibersControlRelated parent parent retiredFlag retiredFlag
          (localTable sourceLocalAfter) (localTable movedLocalAfter)
          (Active sourcePushed view) (Active movedPushed view)
          Refl Refl (ActiveControls {error = error} pushedRelated Refl)
        sourceExpected : SystemState name key value world error
        sourceExpected = MkSystemState (localWorld sourceLocalAfter)
          (replaceBinding @{nameEq} actor sourceNext sourceRegistry)
        movedExpected : SystemState name key value world error
        movedExpected = MkSystemState (localWorld movedLocalAfter)
          (replaceBinding @{nameEq} actor movedNext movedRegistry)
        0 sourceConcrete : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          (MkSystemState sourceAmbient sourceRegistry) =
          Just (LFinishTag, sourceExpected)
        sourceConcrete = rewrite sourceFound in rewrite sourceResolved in
          rewrite sourceRan in rewrite sourceTarget in
          rewrite localViewEqRefl nameEq view in Refl
        0 movedConcrete : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          (MkSystemState movedAmbient movedRegistry) =
          Just (LFinishTag, movedExpected)
        movedConcrete = rewrite movedFound in rewrite movedResolved in
          rewrite movedRan in rewrite movedTarget in
          rewrite localViewEqRefl nameEq view in Refl
        0 sourcePairSame : (LFinishTag, sourceExpected) =
          (LFinishTag, sourceAfter)
        sourcePairSame = justInjective (trans (sym sourceConcrete) sourceRaw)
        0 movedPairSame : (LFinishTag, movedExpected) =
          (LFinishTag, movedAfter)
        movedPairSame = justInjective (trans (sym movedConcrete) movedRaw)
    in case sourcePairSame of
      Refl => case movedPairSame of
        Refl => MkActivationReplacementComparison sourceNext movedNext
          oldFiber oldFiber sourceFound movedFound Refl Refl Refl Refl
          nextRelated Refl Refl
          (replaceBindingRuntimeBindings nameEq actor sourceNext sourceRegistry)
          (replaceBindingRuntimeBindings nameEq actor movedNext movedRegistry)

0 successfulIterReplacementComparison :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step, next : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (more : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (sourceFound : lookupFiber @{nameEq} actor sourceRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading (step :: next :: more) accumulator view))) ->
  (movedFound : lookupFiber @{nameEq} actor movedRegistry = Just
    (MkFiber component parent retiredFlag table
      (Reloading (step :: next :: more) accumulator view))) ->
  (sourceCapability, movedCapability : DepValues key value
    (dependencies (componentDependencies component))) ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view sourceRegistry =
    Just sourceCapability ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view movedRegistry =
    Just movedCapability ->
  (sourceLocalAfter, movedLocalAfter :
    LocalState key value world (componentProvisions component)) ->
  (sourceUndo, movedUndo :
    LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  runStepEffect step sourceCapability
    (MkLocalState sourceAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues table))) = Right (sourceLocalAfter, sourceUndo) ->
  runStepEffect step movedCapability
    (MkLocalState movedAmbient
      (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component)
        (ownedValues table))) = Right (movedLocalAfter, movedUndo) ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) movedUndo)
    (yieldedInverseEffectMap nameEq keyEq actor
      (componentProvisions component) sourceUndo) ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading (step :: next :: more) accumulator view)) sourceRegistry =
    Just view ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table
      (Reloading (step :: next :: more) accumulator view)) movedRegistry =
    Just view ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState sourceAmbient sourceRegistry) = Just (LIterTag, sourceAfter) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor)
    (MkSystemState movedAmbient movedRegistry) = Just (LIterTag, movedAfter) ->
  ActivationReplacementComparison nameEq actor
    (MkSystemState sourceAmbient sourceRegistry) sourceAfter
    (MkSystemState movedAmbient movedRegistry) movedAfter
successfulIterReplacementComparison nameEq keyEq actor sourceAmbient movedAmbient
  sourceRegistry movedRegistry component parent retiredFlag table step next more
  accumulator view sourceAfter movedAfter sourceFound movedFound sourceCapability
  movedCapability sourceResolved movedResolved sourceLocalAfter movedLocalAfter
  sourceUndo movedUndo sourceRan movedRan movedToSourceUndo sourceTarget
  movedTarget sourceRaw movedRaw =
    let oldFiber : Fiber name key value world error
        oldFiber = MkFiber component parent retiredFlag table
          (Reloading (step :: next :: more) accumulator view)
        sourcePushed = pushLocalUndo @{keyEq}
          (componentProvisions component) accumulator sourceUndo
        movedPushed = pushLocalUndo @{keyEq}
          (componentProvisions component) accumulator movedUndo
        sourceNext : Fiber name key value world error
        sourceNext = setFiberRuntime oldFiber (localTable sourceLocalAfter)
          (Reloading (next :: more) sourcePushed view)
        movedNext : Fiber name key value world error
        movedNext = setFiberRuntime oldFiber (localTable movedLocalAfter)
          (Reloading (next :: more) movedPushed view)
        0 pushedRelated : AccumulatorRelated
          (pushLocalUndo @{keyEq} (componentProvisions component) accumulator
            sourceUndo)
          (pushLocalUndo @{keyEq} (componentProvisions component) accumulator
            movedUndo)
        pushedRelated = pushedAccumulatorRelatedFromMovedUndoMaps nameEq keyEq
          actor (componentProvisions component) accumulator sourceUndo movedUndo
          movedToSourceUndo
        0 nextRelated : FiberControlRelated sourceNext movedNext
        nextRelated = FibersControlRelated parent parent retiredFlag retiredFlag
          (localTable sourceLocalAfter) (localTable movedLocalAfter)
          (Reloading (next :: more) sourcePushed view)
          (Reloading (next :: more) movedPushed view) Refl Refl
          (ReloadingControls Refl pushedRelated Refl)
        sourceExpected : SystemState name key value world error
        sourceExpected = MkSystemState (localWorld sourceLocalAfter)
          (replaceBinding @{nameEq} actor sourceNext sourceRegistry)
        movedExpected : SystemState name key value world error
        movedExpected = MkSystemState (localWorld movedLocalAfter)
          (replaceBinding @{nameEq} actor movedNext movedRegistry)
        0 sourceConcrete : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          (MkSystemState sourceAmbient sourceRegistry) =
          Just (LIterTag, sourceExpected)
        sourceConcrete = rewrite sourceFound in rewrite sourceResolved in
          rewrite sourceRan in rewrite sourceTarget in
          rewrite localViewEqRefl nameEq view in Refl
        0 movedConcrete : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          (MkSystemState movedAmbient movedRegistry) =
          Just (LIterTag, movedExpected)
        movedConcrete = rewrite movedFound in rewrite movedResolved in
          rewrite movedRan in rewrite movedTarget in
          rewrite localViewEqRefl nameEq view in Refl
        0 sourcePairSame : (LIterTag, sourceExpected) = (LIterTag, sourceAfter)
        sourcePairSame = justInjective (trans (sym sourceConcrete) sourceRaw)
        0 movedPairSame : (LIterTag, movedExpected) = (LIterTag, movedAfter)
        movedPairSame = justInjective (trans (sym movedConcrete) movedRaw)
    in case sourcePairSame of
      Refl => case movedPairSame of
        Refl => MkActivationReplacementComparison sourceNext movedNext
          oldFiber oldFiber sourceFound movedFound Refl Refl Refl Refl
          nextRelated Refl Refl
          (replaceBindingRuntimeBindings nameEq actor sourceNext sourceRegistry)
          (replaceBindingRuntimeBindings nameEq actor movedNext movedRegistry)

0 beginReplacementComparisonFromChecked :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState sourceAmbient sourceRegistry) =
    Just (LBeginTag, sourceAfter)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState movedAmbient movedRegistry) =
    Just (LBeginTag, movedAfter)) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor movedRegistry =
    lookupFiber @{nameEq} actor sourceRegistry ->
  ((fiber : Fiber name key value world error) ->
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    targetFiber @{nameEq} @{keyEq} fiber sourceRegistry = Just view ->
    targetFiber @{nameEq} @{keyEq} fiber movedRegistry = Just view) ->
  ActivationReplacementComparison nameEq actor
    (MkSystemState sourceAmbient sourceRegistry) sourceAfter
    (MkSystemState movedAmbient movedRegistry) movedAfter
beginReplacementComparisonFromChecked nameEq keyEq actor sourceAmbient
  movedAmbient sourceRegistry movedRegistry sourceAfter movedAfter sourceChecked
  movedChecked lookupSame targetPreserved =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceAmbient sourceRegistry
        movedState : SystemState name key value world error
        movedState = MkSystemState movedAmbient movedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (LBegin actor) sourceState =
          Just (LBeginTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (LBegin actor) sourceState
          sourceAfter LBeginTag sourceChecked
        0 movedRaw : applyAction @{nameEq} @{keyEq} (LBegin actor) movedState =
          Just (LBeginTag, movedAfter)
        movedRaw = checkedActionProjects nameEq keyEq (LBegin actor) movedState
          movedAfter LBeginTag movedChecked
    in case beginSourceOwnerNotActive nameEq keyEq actor
      {before = sourceState} {afterState = sourceAfter} LBeginTag sourceChecked of
      (sourceFiber ** (sourceFound, sourceInactive)) =>
        case foreignBeginPlanView nameEq keyEq actor sourceAmbient sourceRegistry
          sourceFiber sourceFound LBeginTag sourceAfter sourceRaw of
          MkForeignBeginPlanView {component} {parent} {table} view ownerShape
            sourceTarget sourceTagShape sourceAfterShape =>
              case ownerShape of
                Refl =>
                  let exactFiber : Fiber name key value world error
                      exactFiber = MkFiber component parent False table
                        (Inactive Nothing)
                      0 movedFound : lookupFiber @{nameEq} actor movedRegistry =
                        Just exactFiber
                      movedFound = trans lookupSame sourceFound
                      0 movedTarget : targetFiber @{nameEq} @{keyEq} exactFiber
                        movedRegistry = Just view
                      movedTarget = targetPreserved exactFiber view sourceTarget
                  in beginReplacementComparison nameEq keyEq actor sourceAmbient
                    movedAmbient sourceRegistry movedRegistry component parent
                    table view sourceAfter movedAfter sourceFound movedFound
                    sourceTarget movedTarget sourceRaw movedRaw

0 advanceReplacementComparisonFromAgreement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {traceFirst, traceLast : SystemState name key value world error} ->
  (trace : Transitions traceFirst traceLast) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor)
    (the (SystemState name key value world error)
      (MkSystemState sourceAmbient sourceRegistry)) = Just (tag, sourceAfter)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor)
    (the (SystemState name key value world error)
      (MkSystemState movedAmbient movedRegistry)) = Just (tag, movedAfter)) ->
  (0 stageOccurs : Either
    (OccursIn
      (Fired {before = the (SystemState name key value world error)
        (MkSystemState sourceAmbient sourceRegistry)}
        {afterState = sourceAfter} nameEq keyEq (LAdvance actor) tag sourceChecked)
      trace)
    (OccursIn
      (Fired {before = the (SystemState name key value world error)
        (MkSystemState movedAmbient movedRegistry)}
        {afterState = movedAfter} nameEq keyEq (LAdvance actor) tag movedChecked)
      trace)) ->
  (paperTag : Either (tag = LIterTag) (tag = LFinishTag)) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor movedRegistry =
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor sourceRegistry ->
  ((stage : IteratorStage name key world error value actor trace) ->
    IteratorOutcomeAgreement name key value world error keyEq
      (iteratorStageOutcome stage
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState movedAmbient movedRegistry))))
      (iteratorStageOutcome stage
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState sourceAmbient sourceRegistry))))) ->
  ActivationReplacementComparison nameEq actor
    (the (SystemState name key value world error)
      (MkSystemState sourceAmbient sourceRegistry)) sourceAfter
    (the (SystemState name key value world error)
      (MkSystemState movedAmbient movedRegistry)) movedAfter
advanceReplacementComparisonFromAgreement nameEq keyEq actor trace sourceAmbient
  movedAmbient sourceRegistry movedRegistry sourceAfter movedAfter tag
  sourceChecked movedChecked stageOccurs paperTag lookupSame outcomeAgreement =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceAmbient sourceRegistry
        movedState : SystemState name key value world error
        movedState = MkSystemState movedAmbient movedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          sourceState = Just (tag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (LAdvance actor)
          sourceState sourceAfter tag sourceChecked
        0 movedRaw : applyAction @{nameEq} @{keyEq} (LAdvance actor)
          movedState = Just (tag, movedAfter)
        movedRaw = checkedActionProjects nameEq keyEq (LAdvance actor)
          movedState movedAfter tag movedChecked
        0 sourceFrame : FramedEffectOutput keyEq
          (partialEffectMapFor nameEq keyEq (LAdvance actor) tag sourceState)
          (projectEffectState @{nameEq} sourceState)
          (projectEffectState @{nameEq} sourceAfter)
        sourceFrame = framedEffectOutput keyEq
          (partialEffectMapFor nameEq keyEq (LAdvance actor) tag sourceState)
          (projectEffectState @{nameEq} sourceState)
          (projectEffectState @{nameEq} sourceAfter)
          (checkedEffectFrameRelation nameEq keyEq (LAdvance actor) tag
            sourceState sourceAfter sourceChecked)
        0 movedFrame : FramedEffectOutput keyEq
          (partialEffectMapFor nameEq keyEq (LAdvance actor) tag movedState)
          (projectEffectState @{nameEq} movedState)
          (projectEffectState @{nameEq} movedAfter)
        movedFrame = framedEffectOutput keyEq
          (partialEffectMapFor nameEq keyEq (LAdvance actor) tag movedState)
          (projectEffectState @{nameEq} movedState)
          (projectEffectState @{nameEq} movedAfter)
          (checkedEffectFrameRelation nameEq keyEq (LAdvance actor) tag
            movedState movedAfter movedChecked)
        0 sourceAdvanceRuns : advanceRuntimeEffectMap nameEq keyEq actor
          sourceState (projectEffectState @{nameEq} sourceState) =
          Just (framedOutput sourceFrame)
        sourceAdvanceRuns = paperAdvanceRuntimeEffectRun nameEq keyEq actor tag
          paperTag sourceState (framedOutput sourceFrame)
          (framedMapRuns sourceFrame)
        0 movedAdvanceRuns : advanceRuntimeEffectMap nameEq keyEq actor movedState
          (projectEffectState @{nameEq} movedState) =
          Just (framedOutput movedFrame)
        movedAdvanceRuns = paperAdvanceRuntimeEffectRun nameEq keyEq actor tag
          paperTag movedState (framedOutput movedFrame) (framedMapRuns movedFrame)
        0 movedPaper : PaperAdvanceSource name key world error value nameEq keyEq
          actor tag movedState
        movedPaper = paperAdvanceSource nameEq keyEq actor {before = movedState}
          {afterState = movedAfter} tag movedRaw paperTag
    in case taggedPaperAdvanceSource nameEq keyEq actor {before = sourceState}
      {afterState = sourceAfter} tag sourceRaw paperTag of
      TaggedFinishSource exactTag sourcePaper => case sourcePaper of
        AdvanceSourceFinishEmpty {ambient = observedAmbient}
          {fibers = observedFibers} {component} {parent} {retiredFlag} {table}
          {accumulator} {view} sourceShape sourceFound sourceTarget =>
            case sourceShape of
              Refl =>
                let exactFiber : Fiber name key value world error
                    exactFiber = MkFiber component parent retiredFlag table
                      (Reloading [] accumulator view)
                    0 movedFound : lookupFiber @{nameEq} actor movedRegistry =
                      Just exactFiber
                    movedFound = trans lookupSame sourceFound
                    0 movedTarget : targetFiber @{nameEq} @{keyEq} exactFiber
                      movedRegistry = Just view
                    movedTarget = paperAdvanceTargetAtKnownFiber nameEq keyEq actor
                      movedAmbient movedRegistry movedPaper component parent
                      retiredFlag table [] accumulator view movedFound
                    0 sourceFinishRaw : applyAction @{nameEq} @{keyEq}
                      (LAdvance actor) sourceState = Just (LFinishTag, sourceAfter)
                    sourceFinishRaw = applyActionTagTransport {nameEq = nameEq} {keyEq = keyEq}
                      {action = LAdvance actor} {before = sourceState}
                      {afterState = sourceAfter} exactTag sourceRaw
                    0 movedFinishRaw : applyAction @{nameEq} @{keyEq}
                      (LAdvance actor) movedState = Just (LFinishTag, movedAfter)
                    movedFinishRaw = applyActionTagTransport {nameEq = nameEq} {keyEq = keyEq}
                      {action = LAdvance actor} {before = movedState}
                      {afterState = movedAfter} exactTag movedRaw
                in emptyFinishReplacementComparison nameEq keyEq actor
                  sourceAmbient movedAmbient sourceRegistry movedRegistry component
                  parent retiredFlag table accumulator view sourceAfter movedAfter
                  sourceFound movedFound sourceTarget movedTarget sourceFinishRaw
                  movedFinishRaw
        AdvanceSourceFinishOne {ambient = observedAmbient}
          {fibers = observedFibers} {component} {parent} {retiredFlag} {table}
          {step} {accumulator} {view} sourceShape sourceFound sourceTarget =>
            case sourceShape of
              Refl =>
                let exactFiber : Fiber name key value world error
                    exactFiber = MkFiber component parent retiredFlag table
                      (Reloading [step] accumulator view)
                    0 movedFound : lookupFiber @{nameEq} actor movedRegistry =
                      Just exactFiber
                    movedFound = trans lookupSame sourceFound
                    0 movedTarget : targetFiber @{nameEq} @{keyEq} exactFiber
                      movedRegistry = Just view
                    movedTarget = paperAdvanceTargetAtKnownFiber nameEq keyEq actor
                      movedAmbient movedRegistry movedPaper component parent
                      retiredFlag table [step] accumulator view movedFound
                    0 stage : IteratorStage name key world error value actor trace
                    stage = case stageOccurs of
                      Left sourceOccurs => StageFromAdvance nameEq keyEq actor tag
                        sourceChecked sourceOccurs exactFiber sourceFound [step]
                        accumulator view Refl step [] SuffixHere
                      Right movedOccurs => StageFromAdvance nameEq keyEq actor tag
                        movedChecked movedOccurs exactFiber movedFound [step]
                        accumulator view Refl step [] SuffixHere
                    0 agreement : IteratorOutcomeAgreement name key value world
                      error keyEq
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} movedState))
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} sourceState))
                    agreement = outcomeAgreement stage
                    0 movedOutcomeSame : iteratorStageOutcome stage
                      (projectEffectState @{nameEq} movedState) =
                      iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step []
                        (projectEffectState @{nameEq} movedState)
                    movedOutcomeSame = case stageOccurs of
                      Left sourceOccurs => Refl
                      Right movedOccurs => Refl
                    0 sourceOutcomeSame : iteratorStageOutcome stage
                      (projectEffectState @{nameEq} sourceState) =
                      iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step []
                        (projectEffectState @{nameEq} sourceState)
                    sourceOutcomeSame = case stageOccurs of
                      Left sourceOccurs => Refl
                      Right movedOccurs => Refl
                    0 componentAgreement : IteratorOutcomeAgreement name key value
                      world error keyEq
                      (iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step []
                        (projectEffectState @{nameEq} movedState))
                      (iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step []
                        (projectEffectState @{nameEq} sourceState))
                    componentAgreement = replace
                      {p = \leftOutcome => IteratorOutcomeAgreement name key value
                        world error keyEq leftOutcome
                          (iteratorStageOutcomeComponentData nameEq keyEq actor
                            component view step []
                            (projectEffectState @{nameEq} sourceState))}
                      movedOutcomeSame
                      (replace
                        {p = \rightOutcome => IteratorOutcomeAgreement name key
                          value world error keyEq
                            (iteratorStageOutcome stage
                              (projectEffectState @{nameEq} movedState))
                            rightOutcome}
                        sourceOutcomeSame agreement)
                    0 sourceFinishRaw : applyAction @{nameEq} @{keyEq}
                      (LAdvance actor) sourceState = Just (LFinishTag, sourceAfter)
                    sourceFinishRaw = applyActionTagTransport {nameEq = nameEq} {keyEq = keyEq}
                      {action = LAdvance actor} {before = sourceState}
                      {afterState = sourceAfter} exactTag sourceRaw
                    0 movedFinishRaw : applyAction @{nameEq} @{keyEq}
                      (LAdvance actor) movedState = Just (LFinishTag, movedAfter)
                    movedFinishRaw = applyActionTagTransport {nameEq = nameEq} {keyEq = keyEq}
                      {action = LAdvance actor} {before = movedState}
                      {afterState = movedAfter} exactTag movedRaw
                    0 paired : PairedAdvanceYield nameEq keyEq actor component
                      table step [] view sourceAmbient movedAmbient sourceRegistry
                      movedRegistry
                    paired = pairedAdvanceYieldFromRuns nameEq keyEq actor
                      component parent retiredFlag table step [] accumulator view
                      sourceAmbient movedAmbient sourceRegistry movedRegistry
                      (framedOutput sourceFrame) (framedOutput movedFrame)
                      sourceFound movedFound sourceAdvanceRuns movedAdvanceRuns
                      componentAgreement
                in successfulFinishReplacementComparison nameEq keyEq actor
                  sourceAmbient movedAmbient sourceRegistry movedRegistry component
                  parent retiredFlag table step accumulator view sourceAfter
                  movedAfter sourceFound movedFound
                  (pairedSourceCapability paired) (pairedMovedCapability paired)
                  (pairedSourceResolved paired) (pairedMovedResolved paired)
                  (pairedSourceAfter paired) (pairedMovedAfter paired)
                  (pairedSourceUndo paired) (pairedMovedUndo paired)
                  (pairedSourceRan paired) (pairedMovedRan paired)
                  (pairedUndoMaps paired) sourceTarget movedTarget sourceFinishRaw
                  movedFinishRaw

      TaggedIterSource exactTag sourcePaper => case sourcePaper of
        AdvanceSourceIter {ambient = observedAmbient}
          {fibers = observedFibers} {component} {parent} {retiredFlag} {table}
          {step} {next} {more} {accumulator} {view} sourceShape sourceFound
          sourceTarget =>
            case sourceShape of
              Refl =>
                let exactFiber : Fiber name key value world error
                    exactFiber = MkFiber component parent retiredFlag table
                      (Reloading (step :: next :: more) accumulator view)
                    0 movedFound : lookupFiber @{nameEq} actor movedRegistry =
                      Just exactFiber
                    movedFound = trans lookupSame sourceFound
                    0 movedTarget : targetFiber @{nameEq} @{keyEq} exactFiber
                      movedRegistry = Just view
                    movedTarget = paperAdvanceTargetAtKnownFiber nameEq keyEq actor
                      movedAmbient movedRegistry movedPaper component parent
                      retiredFlag table (step :: next :: more) accumulator view
                      movedFound
                    0 stage : IteratorStage name key world error value actor trace
                    stage = case stageOccurs of
                      Left sourceOccurs => StageFromAdvance nameEq keyEq actor tag
                        sourceChecked sourceOccurs exactFiber sourceFound
                        (step :: next :: more) accumulator view Refl step
                        (next :: more) SuffixHere
                      Right movedOccurs => StageFromAdvance nameEq keyEq actor tag
                        movedChecked movedOccurs exactFiber movedFound
                        (step :: next :: more) accumulator view Refl step
                        (next :: more) SuffixHere
                    0 agreement : IteratorOutcomeAgreement name key value world
                      error keyEq
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} movedState))
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} sourceState))
                    agreement = outcomeAgreement stage
                    0 movedOutcomeSame : iteratorStageOutcome stage
                      (projectEffectState @{nameEq} movedState) =
                      iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step (next :: more)
                        (projectEffectState @{nameEq} movedState)
                    movedOutcomeSame = case stageOccurs of
                      Left sourceOccurs => Refl
                      Right movedOccurs => Refl
                    0 sourceOutcomeSame : iteratorStageOutcome stage
                      (projectEffectState @{nameEq} sourceState) =
                      iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step (next :: more)
                        (projectEffectState @{nameEq} sourceState)
                    sourceOutcomeSame = case stageOccurs of
                      Left sourceOccurs => Refl
                      Right movedOccurs => Refl
                    0 componentAgreement : IteratorOutcomeAgreement name key value
                      world error keyEq
                      (iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step (next :: more)
                        (projectEffectState @{nameEq} movedState))
                      (iteratorStageOutcomeComponentData nameEq keyEq actor
                        component view step (next :: more)
                        (projectEffectState @{nameEq} sourceState))
                    componentAgreement = replace
                      {p = \leftOutcome => IteratorOutcomeAgreement name key value
                        world error keyEq leftOutcome
                          (iteratorStageOutcomeComponentData nameEq keyEq actor
                            component view step (next :: more)
                            (projectEffectState @{nameEq} sourceState))}
                      movedOutcomeSame
                      (replace
                        {p = \rightOutcome => IteratorOutcomeAgreement name key
                          value world error keyEq
                            (iteratorStageOutcome stage
                              (projectEffectState @{nameEq} movedState))
                            rightOutcome}
                        sourceOutcomeSame agreement)
                    0 sourceIterRaw : applyAction @{nameEq} @{keyEq}
                      (LAdvance actor) sourceState = Just (LIterTag, sourceAfter)
                    sourceIterRaw = applyActionTagTransport {nameEq = nameEq} {keyEq = keyEq}
                      {action = LAdvance actor} {before = sourceState}
                      {afterState = sourceAfter} exactTag sourceRaw
                    0 movedIterRaw : applyAction @{nameEq} @{keyEq}
                      (LAdvance actor) movedState = Just (LIterTag, movedAfter)
                    movedIterRaw = applyActionTagTransport {nameEq = nameEq} {keyEq = keyEq}
                      {action = LAdvance actor} {before = movedState}
                      {afterState = movedAfter} exactTag movedRaw
                    0 paired : PairedAdvanceYield nameEq keyEq actor component
                      table step (next :: more) view sourceAmbient movedAmbient
                      sourceRegistry movedRegistry
                    paired = pairedAdvanceYieldFromRuns nameEq keyEq actor
                      component parent retiredFlag table step (next :: more)
                      accumulator view sourceAmbient movedAmbient sourceRegistry
                      movedRegistry (framedOutput sourceFrame)
                      (framedOutput movedFrame) sourceFound movedFound
                      sourceAdvanceRuns movedAdvanceRuns componentAgreement
                in successfulIterReplacementComparison nameEq keyEq actor
                  sourceAmbient movedAmbient sourceRegistry movedRegistry component
                  parent retiredFlag table step next more accumulator view sourceAfter
                  movedAfter sourceFound movedFound
                  (pairedSourceCapability paired) (pairedMovedCapability paired)
                  (pairedSourceResolved paired) (pairedMovedResolved paired)
                  (pairedSourceAfter paired) (pairedMovedAfter paired)
                  (pairedSourceUndo paired) (pairedMovedUndo paired)
                  (pairedSourceRan paired) (pairedMovedRan paired)
                  (pairedUndoMaps paired) sourceTarget movedTarget sourceIterRaw
                  movedIterRaw

0 activationReplacementComparisonAcrossForeign :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  {traceFirst, traceLast : SystemState name key value world error} ->
  (trace : Transitions traceFirst traceLast) ->
  (sourceAmbient, movedAmbient : world) ->
  (sourceRegistry, movedRegistry : Registry name key value world error) ->
  (sourceAfter, movedAfter : SystemState name key value world error) ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action
    (MkSystemState sourceAmbient sourceRegistry) = Just (tag, sourceAfter)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq} action
    (MkSystemState movedAmbient movedRegistry) = Just (tag, movedAfter)) ->
  (0 stageOccurs : Either
    (OccursIn
      (Fired {before = MkSystemState sourceAmbient sourceRegistry}
        {afterState = sourceAfter} nameEq keyEq action tag sourceChecked) trace)
    (OccursIn
      (Fired {before = MkSystemState movedAmbient movedRegistry}
        {afterState = movedAfter} nameEq keyEq action tag movedChecked) trace)) ->
  (sourceActivation : PaperActivationStep
    (Fired {before = MkSystemState sourceAmbient sourceRegistry}
      {afterState = sourceAfter} nameEq keyEq action tag sourceChecked)) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (actionOwner action) movedRegistry =
    lookupFiber @{nameEq} (actionOwner action) sourceRegistry ->
  ((fiber : Fiber name key value world error) ->
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    targetFiber @{nameEq} @{keyEq} fiber sourceRegistry = Just view ->
    targetFiber @{nameEq} @{keyEq} fiber movedRegistry = Just view) ->
  ((stage : IteratorStage name key world error value (actionOwner action) trace) ->
    IteratorOutcomeAgreement name key value world error keyEq
      (iteratorStageOutcome stage
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState movedAmbient movedRegistry))))
      (iteratorStageOutcome stage
        (projectEffectState @{nameEq}
          (the (SystemState name key value world error)
            (MkSystemState sourceAmbient sourceRegistry))))) ->
  ActivationReplacementComparison nameEq (actionOwner action)
    (MkSystemState sourceAmbient sourceRegistry) sourceAfter
    (MkSystemState movedAmbient movedRegistry) movedAfter
activationReplacementComparisonAcrossForeign nameEq keyEq action tag trace
  sourceAmbient movedAmbient sourceRegistry movedRegistry sourceAfter movedAfter
  sourceChecked movedChecked stageOccurs sourceActivation lookupSame
  targetPreserved outcomeAgreement = case sourceActivation of
    PaperBeginStep actionIsBegin tagIsBegin => case actionIsBegin of
      Refl => case tagIsBegin of
        Refl => beginReplacementComparisonFromChecked nameEq keyEq _
          sourceAmbient movedAmbient sourceRegistry movedRegistry sourceAfter
          movedAfter sourceChecked movedChecked lookupSame targetPreserved
    PaperIterStep actionIsAdvance tagIsIter => case actionIsAdvance of
      Refl => case tagIsIter of
        Refl => advanceReplacementComparisonFromAgreement nameEq keyEq _ trace
          sourceAmbient movedAmbient sourceRegistry movedRegistry sourceAfter
          movedAfter LIterTag sourceChecked movedChecked stageOccurs (Left Refl)
          lookupSame outcomeAgreement
    PaperFinishStep actionIsAdvance tagIsFinish => case actionIsAdvance of
      Refl => case tagIsFinish of
        Refl => advanceReplacementComparisonFromAgreement nameEq keyEq _ trace
          sourceAmbient movedAmbient sourceRegistry movedRegistry sourceAfter
          movedAfter LFinishTag sourceChecked movedChecked stageOccurs
          (Right Refl) lookupSame outcomeAgreement

0 activationReplacementComparisonAcrossForeignStates :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  {traceFirst, traceLast : SystemState name key value world error} ->
  (trace : Transitions traceFirst traceLast) ->
  {sourceBefore, movedBefore, sourceAfter, movedAfter :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} action sourceBefore =
    Just (tag, sourceAfter)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq} action movedBefore =
    Just (tag, movedAfter)) ->
  (0 stageOccurs : Either
    (OccursIn (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq action tag sourceChecked) trace)
    (OccursIn (Fired {before = movedBefore} {afterState = movedAfter}
      nameEq keyEq action tag movedChecked) trace)) ->
  (sourceActivation : PaperActivationStep
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq action tag sourceChecked)) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (actionOwner action)
    (registry movedBefore) =
    lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (actionOwner action)
      (registry sourceBefore) ->
  ((fiber : Fiber name key value world error) ->
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    targetFiber @{nameEq} @{keyEq} fiber (registry sourceBefore) = Just view ->
    targetFiber @{nameEq} @{keyEq} fiber (registry movedBefore) = Just view) ->
  ((stage : IteratorStage name key world error value (actionOwner action) trace) ->
    IteratorOutcomeAgreement name key value world error keyEq
      (iteratorStageOutcome stage (projectEffectState @{nameEq} movedBefore))
      (iteratorStageOutcome stage (projectEffectState @{nameEq} sourceBefore))) ->
  ActivationReplacementComparison nameEq (actionOwner action) sourceBefore
    sourceAfter movedBefore movedAfter
activationReplacementComparisonAcrossForeignStates nameEq keyEq action tag trace
  {sourceBefore = MkSystemState sourceAmbient sourceRegistry}
  {movedBefore = MkSystemState movedAmbient movedRegistry}
  {sourceAfter} {movedAfter} sourceChecked movedChecked stageOccurs
  sourceActivation lookupSame targetPreserved outcomeAgreement =
    activationReplacementComparisonAcrossForeign nameEq keyEq action tag trace
      sourceAmbient movedAmbient sourceRegistry movedRegistry sourceAfter movedAfter
      sourceChecked movedChecked stageOccurs sourceActivation lookupSame
      targetPreserved outcomeAgreement

0 activationSelfReplacementComparison :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  PaperActivationStep
    (Fired {before} {afterState} nameEq keyEq action tag checked) ->
  ActivationReplacementComparison nameEq (actionOwner action) before afterState
    before afterState
activationSelfReplacementComparison nameEq keyEq {before} {afterState} action
  tag checked paper =
    let trace : Transitions before afterState
        trace = MoreTransitions
          (Fired {before} {afterState} nameEq keyEq action tag checked)
          NoTransitions
    in activationReplacementComparisonAcrossForeignStates nameEq keyEq action tag
      trace checked checked (Left OccursHere) paper Refl
      (\fiber, view, target => target)
      (\stage => iteratorOutcomeAgreementReflexive keyEq stage
        (projectEffectState @{nameEq} before))

0 orchestrationRawAfterCheckedActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, orchestrationAfter, activationAfter :
    SystemState name key value world error} ->
  (orchestrationAction, activationAction : Action name key value world error) ->
  (orchestrationTag, activationTag : RuleTag) ->
  (orchestrationChecked : checkedApplyAction @{nameEq} @{keyEq}
    orchestrationAction first = Just (orchestrationTag, orchestrationAfter)) ->
  (activationChecked : checkedApplyAction @{nameEq} @{keyEq}
    activationAction first = Just (activationTag, activationAfter)) ->
  (orchestration : PaperOrchestrationStep
    (Fired {before = first} {afterState = orchestrationAfter}
      nameEq keyEq orchestrationAction orchestrationTag
      orchestrationChecked)) ->
  (activation : PaperActivationStep
    (Fired {before = first} {afterState = activationAfter}
      nameEq keyEq activationAction activationTag activationChecked)) ->
  Not (actionOwner orchestrationAction = actionOwner activationAction) ->
  RawActivationMove nameEq keyEq orchestrationAction orchestrationTag
    activationAfter
orchestrationRawAfterCheckedActivation nameEq keyEq
  {first = MkSystemState sourceAmbient sourceRegistry} {orchestrationAfter}
  {activationAfter} orchestrationAction activationAction orchestrationTag
  activationTag orchestrationChecked activationChecked orchestration activation
  distinct =
    let 0 comparison : ActivationReplacementComparison nameEq
          (actionOwner activationAction)
          (MkSystemState sourceAmbient sourceRegistry) activationAfter
          (MkSystemState sourceAmbient sourceRegistry) activationAfter
        comparison = activationSelfReplacementComparison nameEq keyEq
          activationAction activationTag activationChecked activation
        movedAmbient : world
        movedAmbient = worldState activationAfter
        canonicalBefore : SystemState name key value world error
        canonicalBefore = MkSystemState movedAmbient
          (replaceBinding @{nameEq} (actionOwner activationAction)
            (sourceReplacementFiber comparison) sourceRegistry)
        0 canonicalSame : canonicalBefore = activationAfter
        canonicalSame = case activationAfter of
          MkSystemState observedAmbient observedRegistry =>
            cong (MkSystemState observedAmbient)
              (sym (sourceReplacementRegistry comparison))
        0 canonicalRaw : RawActivationMove nameEq keyEq orchestrationAction
          orchestrationTag canonicalBefore
        canonicalRaw = orchestrationRawAfterForeignReplacement nameEq keyEq
          orchestrationAction orchestrationTag sourceAmbient movedAmbient
          sourceRegistry (actionOwner activationAction)
          (sourceReplacementFiber comparison) (sourcePreviousFiber comparison)
          (sourcePreviousFound comparison)
          (sourceReplacementStaticComponent comparison)
          (sourceReplacementStaticParent comparison) orchestrationChecked
          orchestration distinct
    in replace
      {p = \before => RawActivationMove nameEq keyEq orchestrationAction
        orchestrationTag before}
      canonicalSame canonicalRaw

0 localBoolAndLeftTrue : (left, right : Bool) ->
  left && right = True -> left = True
localBoolAndLeftTrue False right both = case both of Refl impossible
localBoolAndLeftTrue True right both = Refl

0 localBoolAndRightTrue : (left, right : Bool) ->
  left && right = True -> right = True
localBoolAndRightTrue False right both = case both of Refl impossible
localBoolAndRightTrue True False both = case both of Refl impossible
localBoolAndRightTrue True True both = Refl

0 localBoolAndTrue : (left, right : Bool) ->
  left = True -> right = True -> left && right = True
localBoolAndTrue False right leftTrue rightTrue = case leftTrue of Refl impossible
localBoolAndTrue True False leftTrue rightTrue = case rightTrue of Refl impossible
localBoolAndTrue True True leftTrue rightTrue = Refl

0 orchestrationRawBeforeCheckedActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (activationAction, orchestrationAction : Action name key value world error) ->
  (activationTag, orchestrationTag : RuleTag) ->
  (activationChecked : checkedApplyAction @{nameEq} @{keyEq}
    activationAction first = Just (activationTag, middle)) ->
  (orchestrationChecked : checkedApplyAction @{nameEq} @{keyEq}
    orchestrationAction middle = Just (orchestrationTag, originalFinal)) ->
  (activation : PaperActivationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq activationAction activationTag activationChecked)) ->
  (orchestration : PaperOrchestrationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq orchestrationAction orchestrationTag
      orchestrationChecked)) ->
  Not (actionOwner activationAction = actionOwner orchestrationAction) ->
  RawActivationMove nameEq keyEq orchestrationAction orchestrationTag first
orchestrationRawBeforeCheckedActivation {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState firstAmbient firstRegistry} {middle}
  {originalFinal} activationAction orchestrationAction activationTag
  orchestrationTag activationChecked orchestrationChecked activation
  (PaperInsertStep {actor} {parent} {component} actionSame) distinct =
    case actionSame of
      Refl =>
        let 0 comparison : ActivationReplacementComparison nameEq
              (actionOwner activationAction)
              (MkSystemState firstAmbient firstRegistry) middle
              (MkSystemState firstAmbient firstRegistry) middle
            comparison = activationSelfReplacementComparison nameEq keyEq
              activationAction activationTag activationChecked activation
            0 reverseDistinct : Not (actor = actionOwner activationAction)
            reverseDistinct same = distinct (sym same)
            0 sourceRaw : applyAction @{nameEq} @{keyEq}
              (OInsert actor parent component) middle =
              Just (orchestrationTag, originalFinal)
            sourceRaw = checkedActionProjects nameEq keyEq
              (OInsert actor parent component) middle originalFinal
              orchestrationTag orchestrationChecked
            0 concreteSourceRaw : applyAction @{nameEq} @{keyEq}
              (OInsert actor parent component)
              (MkSystemState (worldState middle) (registry middle)) =
              Just (orchestrationTag, originalFinal)
            concreteSourceRaw = trans
              (cong (applyAction @{nameEq} @{keyEq}
                (OInsert actor parent component)) (localSystemStateEta middle))
              sourceRaw
        in case foreignInsertPlanView nameEq keyEq actor parent component
          (worldState middle) (registry middle) orchestrationTag originalFinal
          concreteSourceRaw of
          MkForeignInsertPlanView sourceAbsent sourceGuards =>
            let 0 beforeAbsent = trans
                  (lookupBeforeForeignReplacement nameEq actor
                    (actionOwner activationAction) reverseDistinct
                    (sourceReplacementFiber comparison) firstRegistry
                    (registry middle) (sourceReplacementRegistry comparison))
                  sourceAbsent
                0 parentMiddleToFirst = trans
                  (cong (parentPresent @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} parent)
                    (sourceReplacementRegistry comparison))
                  (parentPresentStaticReplacement nameEq parent
                    (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (sourcePreviousFiber comparison) firstRegistry
                    (sourcePreviousFound comparison))
                0 provisionsMiddleToFirst = trans
                  (cong (\registry => provisionsDisjointFrom @{keyEq}
                    {name = name} {key = key} {value = value} {world = world}
                    {error = error} (componentProvisions component)
                    (bindings registry)) (sourceReplacementRegistry comparison))
                  (provisionsDisjointStaticReplacement nameEq keyEq
                    (componentProvisions component)
                    (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (sourcePreviousFiber comparison) firstRegistry
                    (sourcePreviousFound comparison)
                    (sourceReplacementStaticComponent comparison))
                0 parentBeforeTrue = trans (sym parentMiddleToFirst)
                  (localBoolAndLeftTrue _ _ sourceGuards)
                0 provisionsBeforeTrue = trans (sym provisionsMiddleToFirst)
                  (localBoolAndRightTrue _ _ sourceGuards)
                0 beforeGuards = localBoolAndTrue _ _ parentBeforeTrue
                  provisionsBeforeTrue
            in case setFreshFromAbsent nameEq actor (freshFiber component parent)
              firstRegistry beforeAbsent of
              (applied ** inserted) =>
                let earlyAfter : SystemState name key value world error
                    earlyAfter = MkSystemState firstAmbient (coeffectAfter applied)
                    0 earlyRaw : applyAction @{nameEq} @{keyEq}
                      (OInsert actor parent component)
                      (MkSystemState firstAmbient firstRegistry) =
                      Just (OInsertTag, earlyAfter)
                    earlyRaw = rewrite beforeGuards in rewrite inserted in Refl
                in MkRawActivationMove earlyAfter earlyRaw
orchestrationRawBeforeCheckedActivation {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState firstAmbient firstRegistry} {middle}
  {originalFinal} activationAction orchestrationAction activationTag
  orchestrationTag activationChecked orchestrationChecked activation
  (PaperRetireStep {actor} actionSame) distinct = case actionSame of
    Refl =>
      let 0 comparison : ActivationReplacementComparison nameEq
            (actionOwner activationAction)
            (MkSystemState firstAmbient firstRegistry) middle
            (MkSystemState firstAmbient firstRegistry) middle
          comparison = activationSelfReplacementComparison nameEq keyEq
            activationAction activationTag activationChecked activation
          0 reverseDistinct : Not (actor = actionOwner activationAction)
          reverseDistinct same = distinct (sym same)
          0 sourceRaw : applyAction @{nameEq} @{keyEq} (ORetire actor) middle =
            Just (orchestrationTag, originalFinal)
          sourceRaw = checkedActionProjects nameEq keyEq (ORetire actor) middle
            originalFinal orchestrationTag orchestrationChecked
          0 concreteSourceRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
            (MkSystemState (worldState middle) (registry middle)) =
            Just (orchestrationTag, originalFinal)
          concreteSourceRaw = trans
            (cong (applyAction @{nameEq} @{keyEq} (ORetire actor))
              (localSystemStateEta middle)) sourceRaw
      in case retireSuccessView nameEq keyEq actor (worldState middle)
        (registry middle) orchestrationTag originalFinal concreteSourceRaw of
        MkRetireSuccessView actorFiber sourceFound =>
          let 0 beforeFound = trans
                (lookupBeforeForeignReplacement nameEq actor
                  (actionOwner activationAction) reverseDistinct
                  (sourceReplacementFiber comparison) firstRegistry
                  (registry middle) (sourceReplacementRegistry comparison))
                sourceFound
              earlyAfter : SystemState name key value world error
              earlyAfter = MkSystemState firstAmbient
                (replaceBinding @{nameEq} actor (retireFiber actorFiber)
                  firstRegistry)
              0 earlyRaw : applyAction @{nameEq} @{keyEq} (ORetire actor)
                (MkSystemState firstAmbient firstRegistry) =
                Just (ORetireTag, earlyAfter)
              earlyRaw = rewrite beforeFound in Refl
          in MkRawActivationMove earlyAfter earlyRaw
orchestrationRawBeforeCheckedActivation {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState firstAmbient firstRegistry} {middle}
  {originalFinal} activationAction orchestrationAction activationTag
  orchestrationTag activationChecked orchestrationChecked activation
  (PaperRemoveStep {actor} actionSame) distinct = case actionSame of
    Refl =>
      let 0 comparison : ActivationReplacementComparison nameEq
            (actionOwner activationAction)
            (MkSystemState firstAmbient firstRegistry) middle
            (MkSystemState firstAmbient firstRegistry) middle
          comparison = activationSelfReplacementComparison nameEq keyEq
            activationAction activationTag activationChecked activation
          0 reverseDistinct : Not (actor = actionOwner activationAction)
          reverseDistinct same = distinct (sym same)
          0 sourceRaw : applyAction @{nameEq} @{keyEq} (ORemove actor) middle =
            Just (orchestrationTag, originalFinal)
          sourceRaw = checkedActionProjects nameEq keyEq (ORemove actor) middle
            originalFinal orchestrationTag orchestrationChecked
          0 concreteSourceRaw : applyAction @{nameEq} @{keyEq} (ORemove actor)
            (MkSystemState (worldState middle) (registry middle)) =
            Just (orchestrationTag, originalFinal)
          concreteSourceRaw = trans
            (cong (applyAction @{nameEq} @{keyEq} (ORemove actor))
              (localSystemStateEta middle)) sourceRaw
      in case removeSuccessView nameEq keyEq actor (worldState middle)
        (registry middle) orchestrationTag originalFinal concreteSourceRaw of
        MkRemoveSuccessView actorFiber sourceFound removable sourceNoChild =>
          let 0 beforeFound = trans
                (lookupBeforeForeignReplacement nameEq actor
                  (actionOwner activationAction) reverseDistinct
                  (sourceReplacementFiber comparison) firstRegistry
                  (registry middle) (sourceReplacementRegistry comparison))
                sourceFound
              0 childMiddleToFirst = trans
                (cong (hasChild @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor)
                  (sourceReplacementRegistry comparison))
                (hasChildStaticReplacement nameEq actor
                  (actionOwner activationAction)
                  (sourceReplacementFiber comparison)
                  (sourcePreviousFiber comparison) firstRegistry
                  (sourcePreviousFound comparison)
                  (sourceReplacementStaticParent comparison))
              0 beforeNoChild = trans (sym childMiddleToFirst) sourceNoChild
              0 normalizedGuard = replace
                {p = \child => retired actorFiber &&
                  isInactive (fiberLifecycle actorFiber) && not child = True}
                sourceNoChild removable
              0 beforeGuard : Equal
                (retired actorFiber && isInactive (fiberLifecycle actorFiber) &&
                  not (hasChild @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    firstRegistry)) True
              beforeGuard = rewrite beforeNoChild in normalizedGuard
              earlyAfter : SystemState name key value world error
              earlyAfter = MkSystemState firstAmbient
                (deleteBinding @{nameEq} actor firstRegistry)
              0 earlyRaw : applyAction @{nameEq} @{keyEq} (ORemove actor)
                (MkSystemState firstAmbient firstRegistry) =
                Just (ORemoveTag, earlyAfter)
              earlyRaw = rewrite beforeFound in rewrite beforeGuard in Refl
          in MkRawActivationMove earlyAfter earlyRaw

record RetireBindingObservation
  (nameEq : DecEq name) (actor : name)
  (source : Registry name key value world error)
  (afterState : SystemState name key value world error) where
  constructor MkRetireBindingObservation
  retiredSourceFiber : Fiber name key value world error
  0 retiredSourceFound : lookupFiber @{nameEq} actor source =
    Just retiredSourceFiber
  0 retiredObservedBindings : bindings (registry afterState) =
    replaceEntries @{nameEq} actor (retireFiber retiredSourceFiber)
      (bindings source)

0 retireBindingObservation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor)
    (MkSystemState ambient source) = Just (tag, afterState) ->
  RetireBindingObservation nameEq actor source afterState
retireBindingObservation nameEq keyEq actor ambient source tag afterState raw =
  case retireSuccessView nameEq keyEq actor ambient source tag afterState raw of
    MkRetireSuccessView oldFiber found =>
      MkRetireBindingObservation oldFiber found
        (replaceBindingRuntimeBindings nameEq actor (retireFiber oldFiber) source)

record RemoveBindingObservation
  (nameEq : DecEq name) (actor : name)
  (source : Registry name key value world error)
  (afterState : SystemState name key value world error) where
  constructor MkRemoveBindingObservation
  removedSourceFiber : Fiber name key value world error
  0 removedSourceFound : lookupFiber @{nameEq} actor source =
    Just removedSourceFiber
  0 removedObservedBindings : bindings (registry afterState) =
    deleteEntries @{nameEq} actor (bindings source)

0 removeBindingObservation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORemove actor)
    (MkSystemState ambient source) = Just (tag, afterState) ->
  RemoveBindingObservation nameEq actor source afterState
removeBindingObservation nameEq keyEq actor ambient source tag afterState raw =
  case removeSuccessView nameEq keyEq actor ambient source tag afterState raw of
    MkRemoveSuccessView oldFiber found guard noChild =>
      MkRemoveBindingObservation oldFiber found
        (deleteBindingRuntimeBindings nameEq actor source)

||| Indexed source capital for the pointwise O-Remove producer. All executable
||| guards come from one operational view; in particular `sourceNoChild` is not
||| rebuilt from an independently oriented `with` proof.
record PointwiseRemoveSourceObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name) (ambient : world)
  (source : Registry name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkPointwiseRemoveSourceObservation
  observedRemoveFiber : Fiber name key value world error
  0 observedRemoveFound : lookupFiber @{nameEq} actor source =
    Just observedRemoveFiber
  0 observedRemoveGuard :
    (retired observedRemoveFiber &&
      isInactive (fiberLifecycle observedRemoveFiber) &&
      not (hasChild @{nameEq} {name = name} {key = key} {value = value}
        {world = world} {error = error} actor source) = True)
  0 observedRemoveNoChild : hasChild @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} actor source = False
  0 observedRemoveTag : tag = ORemoveTag
  0 observedRemoveAfter : MkSystemState ambient
    (deleteBinding @{nameEq} actor source) = afterState

0 pointwiseRemoveSourceObservation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORemove actor)
    (MkSystemState ambient source) = Just (tag, afterState) ->
  PointwiseRemoveSourceObservation name key world error value nameEq actor
    ambient source tag afterState
pointwiseRemoveSourceObservation nameEq keyEq actor ambient source tag afterState
  raw = case removeSuccessView nameEq keyEq actor ambient source tag afterState
    raw of
      MkRemoveSuccessView oldFiber found guard noChild =>
        MkPointwiseRemoveSourceObservation oldFiber found guard noChild Refl Refl

||| Complete pointwise O-Remove head. Its source owner, composite guard,
||| childlessness, and delete endpoint all originate in one indexed operational
||| observation; the target delete owns its checked transition and replay capital.
0 replayPointwiseRemoveHead :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {sourceBefore, sourceAfter, replayedBefore :
    SystemState name key value world error} ->
  (sourceChecked : checkedApplyAction @{nameEq} @{keyEq} (ORemove actor)
    sourceBefore = Just (ORemoveTag, sourceAfter)) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceBefore
    replayedBefore ->
  PointwiseRelationalHeadReplay name key world error value nameEq keyEq
    (Fired {before = sourceBefore} {afterState = sourceAfter}
      nameEq keyEq (ORemove actor) ORemoveTag sourceChecked)
    replayedBefore
replayPointwiseRemoveHead nameEq keyEq actor
  {sourceBefore = MkSystemState sourceWorld sourceRegistry}
  {sourceAfter} {replayedBefore = MkSystemState replayedWorld replayedRegistry}
  sourceChecked sourceWellFormed beforeEndpoint =
    let sourceState : SystemState name key value world error
        sourceState = MkSystemState sourceWorld sourceRegistry
        replayedState : SystemState name key value world error
        replayedState = MkSystemState replayedWorld replayedRegistry
        0 sourceRaw : applyAction @{nameEq} @{keyEq} (ORemove actor)
          sourceState = Just (ORemoveTag, sourceAfter)
        sourceRaw = checkedActionProjects nameEq keyEq (ORemove actor) sourceState
          sourceAfter ORemoveTag sourceChecked
        0 sourceObservation : PointwiseRemoveSourceObservation name key world
          error value nameEq actor sourceWorld sourceRegistry ORemoveTag
          sourceAfter
        sourceObservation = pointwiseRemoveSourceObservation nameEq keyEq actor
          sourceWorld sourceRegistry ORemoveTag sourceAfter sourceRaw
        0 sourceFiber : Fiber name key value world error
        sourceFiber = observedRemoveFiber sourceObservation
        0 sourceFound : lookupFiber @{nameEq} actor sourceRegistry =
          Just sourceFiber
        sourceFound = observedRemoveFound sourceObservation
        0 sourceNoChild : (hasChild @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} actor sourceRegistry =
          False)
        sourceNoChild = observedRemoveNoChild sourceObservation
        0 sourceGuard : (retired sourceFiber &&
          isInactive (fiberLifecycle sourceFiber) &&
          not (hasChild @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor sourceRegistry) = True)
        sourceGuard = observedRemoveGuard sourceObservation
        0 sourceAfterShape : MkSystemState sourceWorld
          (deleteBinding @{nameEq} actor sourceRegistry) = sourceAfter
        sourceAfterShape = observedRemoveAfter sourceObservation
    in case pointwiseControlLookupFound nameEq actor sourceState replayedState
      (replayedControls beforeEndpoint) sourceFiber sourceFound of
      (replayedFiber ** (replayedFound, fibersRelated)) =>
        let 0 targetNoChild :
              (hasChild @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} actor replayedRegistry = False)
            targetNoChild = pointwiseNoChildPreserved nameEq actor sourceState
              replayedState (replayedControls beforeEndpoint) sourceNoChild
            0 targetGuard : (retired replayedFiber &&
              isInactive (fiberLifecycle replayedFiber) &&
              not (hasChild @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} actor replayedRegistry) = True)
            targetGuard = pointwiseRemovalGuardRelated nameEq actor sourceState
              replayedState sourceFiber replayedFiber fibersRelated sourceNoChild
              targetNoChild sourceGuard
            targetState : SystemState name key value world error
            targetState = MkSystemState replayedWorld
              (deleteBinding @{nameEq} actor replayedRegistry)
            0 targetRaw : applyAction @{nameEq} @{keyEq} (ORemove actor)
              replayedState = Just (ORemoveTag, targetState)
            targetRaw = rewrite replayedFound in rewrite targetGuard in Refl
            0 targetWellFormed : registryWellFormed @{nameEq} @{keyEq}
              targetState = True
            targetWellFormed = preservationTheoremProof nameEq keyEq
              (ORemove actor) replayedState targetState ORemoveTag
              (replayedWellFormed beforeEndpoint) targetRaw
            0 targetChecked : checkedApplyAction @{nameEq} @{keyEq}
              (ORemove actor) replayedState = Just (ORemoveTag, targetState)
            targetChecked = rewrite targetRaw in
              rewrite targetWellFormed in Refl
            empty : CoeffectContext key value
            empty = emptyContext {key = key} {value = value}
            0 setRelated : EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor empty
                (projectEffectState @{nameEq} sourceState))
              (setEffectTable @{nameEq} actor empty
                (projectEffectState @{nameEq} replayedState))
            setRelated = setRelatedEffectTables nameEq keyEq actor empty empty
              Refl (replayedEffects beforeEndpoint)
            0 sourceFrame : EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor empty
                (projectEffectState @{nameEq} sourceState))
              (projectEffectState @{nameEq} sourceAfter)
            sourceFrame = removeEffectFrameRelated nameEq keyEq actor sourceState
              sourceAfter sourceChecked
            0 targetFrame : EffectStateRelated keyEq
              (setEffectTable @{nameEq} actor empty
                (projectEffectState @{nameEq} replayedState))
              (projectEffectState @{nameEq} targetState)
            targetFrame = removeEffectFrameRelated nameEq keyEq actor
              replayedState targetState targetChecked
            0 nextEffects : EffectStateRelated keyEq
              (projectEffectState @{nameEq} sourceAfter)
              (projectEffectState @{nameEq} targetState)
            nextEffects = effectStateRelatedTransitive
              (effectStateRelatedSymmetric sourceFrame)
              (effectStateRelatedTransitive setRelated targetFrame)
            0 nextControlsConcrete : ControlEquivalent name key world error
              value nameEq
              (MkSystemState sourceWorld
                (deleteBinding @{nameEq} actor sourceRegistry)) targetState
            nextControlsConcrete = pointwiseControlAfterDelete nameEq actor
              sourceWorld replayedWorld sourceRegistry replayedRegistry
              (replayedControls beforeEndpoint)
            0 nextControls : ControlEquivalent name key world error value nameEq
              sourceAfter targetState
            nextControls = replace
              {p = \observed => ControlEquivalent name key world error value
                nameEq observed targetState}
              sourceAfterShape nextControlsConcrete
            sourceStep : Transition sourceState sourceAfter
            sourceStep = Fired nameEq keyEq (ORemove actor) ORemoveTag
              sourceChecked
            replayedStep : Transition replayedState targetState
            replayedStep = Fired nameEq keyEq (ORemove actor) ORemoveTag
              targetChecked
            0 mapPreserved : (state : EffectState name key value world) ->
              partialEffectMap sourceStep state =
                partialEffectMap replayedStep state
            mapPreserved state = Refl
            0 mapsRelated : PartialMapsRelated
              (EffectStateEquivalence keyEq) (partialEffectMap sourceStep)
              (partialEffectMap replayedStep)
            mapsRelated = replayExactTransitionMapsRelated keyEq sourceStep
              replayedStep mapPreserved
            0 notAdvance : (selected : name) -> Not
              (the (Action name key value world error) (ORemove actor) =
                LAdvance selected)
            notAdvance selected Refl impossible
            0 rar : RelationalReplayCorrespondence name key world error value
              (MoreTransitions sourceStep NoTransitions)
              (MoreTransitions replayedStep NoTransitions)
            rar = singletonNonAdvanceRAR nameEq keyEq (ORemove actor)
              ORemoveTag sourceState sourceAfter replayedState targetState
              sourceChecked targetChecked notAdvance mapsRelated
            0 nextEndpoint : RelationalReplayEndpoint name key world error value
              nameEq keyEq sourceAfter targetState
            nextEndpoint = MkRelationalReplayEndpoint nextEffects nextControls
              targetWellFormed
            sourceAligned : AlignedTransitions name key world error value nameEq
              keyEq (MoreTransitions sourceStep NoTransitions)
            sourceAligned = AlignedStep (ORemove actor) ORemoveTag sourceChecked
              NoTransitions AlignedEnd
        in packagePointwiseRelationalHeadReplay nameEq keyEq sourceStep
          sourceAligned targetState (ORemove actor) ORemoveTag targetChecked Refl
          Refl rar mapsRelated nextEndpoint

0 localReplaceEntriesOtherHead :
  (nameEq : DecEq name) -> (changed, current : name) ->
  Not (changed = current) ->
  (next : Fiber name key value world error) ->
  (old : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  replaceEntries @{nameEq} changed next (Bind current old :: rest) =
    Bind current old :: replaceEntries @{nameEq} changed next rest
localReplaceEntriesOtherHead nameEq changed current distinct next old rest
  with (decEq @{nameEq} changed current)
  localReplaceEntriesOtherHead nameEq current current distinct next old rest |
    Yes Refl = void (distinct Refl)
  localReplaceEntriesOtherHead nameEq changed current distinct next old rest |
    No different = Refl

0 orderedControlsAfterOrchestrationActivation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, orchestrationAfter, activationAfter, originalFinal, swappedFinal :
    SystemState name key value world error} ->
  (orchestrationAction, activationAction : Action name key value world error) ->
  (orchestrationTag, activationTag : RuleTag) ->
  (orchestrationChecked : checkedApplyAction @{nameEq} @{keyEq}
    orchestrationAction first =
      Just (orchestrationTag, orchestrationAfter)) ->
  (activationChecked : checkedApplyAction @{nameEq} @{keyEq}
    activationAction orchestrationAfter = Just (activationTag, originalFinal)) ->
  (earlyActivationChecked : checkedApplyAction @{nameEq} @{keyEq}
    activationAction first = Just (activationTag, activationAfter)) ->
  (movedOrchestrationChecked : checkedApplyAction @{nameEq} @{keyEq}
    orchestrationAction activationAfter =
      Just (orchestrationTag, swappedFinal)) ->
  (orchestration : PaperOrchestrationStep
    (Fired {before = first} {afterState = orchestrationAfter}
      nameEq keyEq orchestrationAction orchestrationTag
      orchestrationChecked)) ->
  Not (actionOwner orchestrationAction = actionOwner activationAction) ->
  (comparison : ActivationReplacementComparison nameEq
    (actionOwner activationAction) orchestrationAfter originalFinal first
    activationAfter) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry originalFinal)) (bindings (registry swappedFinal))
orderedControlsAfterOrchestrationActivation {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState sourceAmbient sourceRegistry}
  {orchestrationAfter} {activationAfter} {originalFinal} {swappedFinal}
  orchestrationAction activationAction orchestrationTag activationTag
  orchestrationChecked activationChecked earlyActivationChecked
  movedOrchestrationChecked
  (PaperInsertStep {actor} {parent} {component} actionSame) distinct comparison =
    case actionSame of
      Refl =>
        let sourceRaw = checkedActionProjects nameEq keyEq
              (OInsert actor parent component)
              (MkSystemState sourceAmbient sourceRegistry) orchestrationAfter
              orchestrationTag orchestrationChecked
            0 sourceObservation : InsertRuntimeObservation name key world error
              value actor component parent sourceAmbient sourceRegistry
              orchestrationTag orchestrationAfter
            sourceObservation = insertRuntimeObservation nameEq keyEq actor parent
              component sourceAmbient sourceRegistry orchestrationTag
              orchestrationAfter sourceRaw
        in case activationAfter of
          MkSystemState movedAmbient movedRegistry =>
            let movedRaw = checkedActionProjects nameEq keyEq
                  (OInsert actor parent component)
                  (MkSystemState movedAmbient movedRegistry) swappedFinal
                  orchestrationTag movedOrchestrationChecked
                0 movedObservation : InsertRuntimeObservation name key world
                  error value actor component parent movedAmbient movedRegistry
                  orchestrationTag swappedFinal
                movedObservation = insertRuntimeObservation nameEq keyEq actor
                  parent component movedAmbient movedRegistry orchestrationTag
                  swappedFinal movedRaw
                insertedFiber : Fiber name key value world error
                insertedFiber = freshFiber component parent
                0 sourceInsertShape : bindings (registry orchestrationAfter) =
                  Bind actor insertedFiber :: bindings sourceRegistry
                sourceInsertShape = insertObservedBindings sourceObservation
                0 movedInsertShape : bindings (registry swappedFinal) =
                  Bind actor insertedFiber :: bindings movedRegistry
                movedInsertShape = insertObservedBindings movedObservation
                reverseDistinct : Not (actionOwner activationAction = actor)
                reverseDistinct = \same => distinct (sym same)
                0 replacedSourceShape : replaceEntries @{nameEq}
                    (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (bindings (registry orchestrationAfter)) =
                  replaceEntries @{nameEq} (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (Bind actor insertedFiber :: bindings sourceRegistry)
                replacedSourceShape = cong (replaceEntries @{nameEq}
                  (actionOwner activationAction)
                  (sourceReplacementFiber comparison)) sourceInsertShape
                0 originalShape : bindings (registry originalFinal) =
                  Bind actor insertedFiber :: replaceEntries @{nameEq}
                    (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (bindings sourceRegistry)
                originalShape = trans (sourceReplacementBindings comparison)
                  (trans replacedSourceShape
                    (localReplaceEntriesOtherHead nameEq
                      (actionOwner activationAction) actor reverseDistinct
                      (sourceReplacementFiber comparison) insertedFiber
                      (bindings sourceRegistry)))
                0 swappedShape : bindings (registry swappedFinal) =
                  Bind actor insertedFiber :: replaceEntries @{nameEq}
                    (actionOwner activationAction)
                    (movedReplacementFiber comparison)
                    (bindings sourceRegistry)
                swappedShape = trans movedInsertShape
                  (cong (Bind actor insertedFiber ::)
                    (movedReplacementBindings comparison))
                0 canonical : OrderedRegistryControlsRelated name key world error
                  value
                  (Bind actor insertedFiber :: replaceEntries @{nameEq}
                    (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (bindings sourceRegistry))
                  (Bind actor insertedFiber :: replaceEntries @{nameEq}
                    (actionOwner activationAction)
                    (movedReplacementFiber comparison)
                    (bindings sourceRegistry))
                canonical = OrderedControlsCons actor
                  (fiberControlReflexive insertedFiber)
                  (orderedControlsReplace nameEq (actionOwner activationAction)
                    (sourceReplacementFiber comparison)
                    (movedReplacementFiber comparison)
                    (replacementFibersRelated comparison)
                    (bindings sourceRegistry) (bindings sourceRegistry)
                    (orderedControlsReflexive (bindings sourceRegistry)))
            in orderedControlsTransport (sym originalShape) (sym swappedShape)
              canonical
orderedControlsAfterOrchestrationActivation {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState sourceAmbient sourceRegistry}
  {orchestrationAfter} {activationAfter} {originalFinal} {swappedFinal}
  orchestrationAction activationAction orchestrationTag activationTag
  orchestrationChecked activationChecked earlyActivationChecked
  movedOrchestrationChecked (PaperRetireStep {actor} actionSame) distinct
  comparison = case actionSame of
    Refl =>
      let sourceRaw = checkedActionProjects nameEq keyEq (ORetire actor)
            (MkSystemState sourceAmbient sourceRegistry) orchestrationAfter
            orchestrationTag orchestrationChecked
          0 sourceObservation : RetireBindingObservation nameEq actor
            sourceRegistry orchestrationAfter
          sourceObservation = retireBindingObservation nameEq keyEq actor
            sourceAmbient sourceRegistry orchestrationTag orchestrationAfter
            sourceRaw
      in case activationAfter of
        MkSystemState movedAmbient movedRegistry =>
          let movedRaw = checkedActionProjects nameEq keyEq (ORetire actor)
                (MkSystemState movedAmbient movedRegistry) swappedFinal
                orchestrationTag movedOrchestrationChecked
              0 movedObservation : RetireBindingObservation nameEq actor
                movedRegistry swappedFinal
              movedObservation = retireBindingObservation nameEq keyEq actor
                movedAmbient movedRegistry orchestrationTag swappedFinal movedRaw
              0 lookupSame : (lookupFiber @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    movedRegistry = lookupFiber @{nameEq} {name = name}
                    {key = key} {value = value} {world = world} {error = error}
                    actor sourceRegistry)
              lookupSame = transitionForeignLookup nameEq keyEq actor
                activationAction activationTag earlyActivationChecked distinct
              0 fiberSame : retiredSourceFiber movedObservation =
                retiredSourceFiber sourceObservation
              fiberSame = justInjective
                (trans (sym (retiredSourceFound movedObservation))
                  (trans lookupSame (retiredSourceFound sourceObservation)))
          in let sourceRetired : Fiber name key value world error
                 sourceRetired = retireFiber
                   (retiredSourceFiber sourceObservation)
                 movedRetired : Fiber name key value world error
                 movedRetired = retireFiber
                   (retiredSourceFiber movedObservation)
                 0 retiredSame : movedRetired = sourceRetired
                 retiredSame = cong retireFiber fiberSame
                 0 retiredRelated : FiberControlRelated sourceRetired movedRetired
                 retiredRelated = replace
                   {p = \candidate => FiberControlRelated sourceRetired candidate}
                   (sym retiredSame) (fiberControlReflexive sourceRetired)
                 0 sourceShape : (bindings (registry orchestrationAfter) =
                   replaceEntries @{nameEq} actor sourceRetired
                     (bindings sourceRegistry))
                 sourceShape = retiredObservedBindings sourceObservation
                 0 movedShape : (bindings (registry swappedFinal) =
                   replaceEntries @{nameEq} actor movedRetired
                     (bindings movedRegistry))
                 movedShape = retiredObservedBindings movedObservation
                 0 originalShape : bindings (registry originalFinal) =
                   replaceEntries @{nameEq} (actionOwner activationAction)
                     (sourceReplacementFiber comparison)
                     (replaceEntries @{nameEq} actor sourceRetired
                       (bindings sourceRegistry))
                 originalShape = trans (sourceReplacementBindings comparison)
                   (cong (replaceEntries @{nameEq}
                     (actionOwner activationAction)
                     (sourceReplacementFiber comparison)) sourceShape)
                 0 swappedShape : bindings (registry swappedFinal) =
                   replaceEntries @{nameEq} actor movedRetired
                     (replaceEntries @{nameEq} (actionOwner activationAction)
                       (movedReplacementFiber comparison)
                       (bindings sourceRegistry))
                 swappedShape = trans movedShape
                   (cong (replaceEntries @{nameEq} actor movedRetired)
                     (movedReplacementBindings comparison))
             in orderedControlsAfterDistinctReplacements nameEq actor
               (actionOwner activationAction) distinct (bindings sourceRegistry)
               (bindings (registry originalFinal))
               (bindings (registry swappedFinal)) sourceRetired movedRetired
               (sourceReplacementFiber comparison)
               (movedReplacementFiber comparison) retiredRelated
               (replacementFibersRelated comparison) originalShape swappedShape

orderedControlsAfterOrchestrationActivation {name} {key} {world} {error} {value}
  nameEq keyEq {first = MkSystemState sourceAmbient sourceRegistry}
  {orchestrationAfter} {activationAfter} {originalFinal} {swappedFinal}
  orchestrationAction activationAction orchestrationTag activationTag
  orchestrationChecked activationChecked earlyActivationChecked
  movedOrchestrationChecked (PaperRemoveStep {actor} actionSame) distinct
  comparison = case actionSame of
    Refl =>
      let sourceRaw = checkedActionProjects nameEq keyEq (ORemove actor)
            (MkSystemState sourceAmbient sourceRegistry) orchestrationAfter
            orchestrationTag orchestrationChecked
          0 sourceObservation : RemoveBindingObservation nameEq actor
            sourceRegistry orchestrationAfter
          sourceObservation = removeBindingObservation nameEq keyEq actor
            sourceAmbient sourceRegistry orchestrationTag orchestrationAfter
            sourceRaw
      in case activationAfter of
        MkSystemState movedAmbient movedRegistry =>
          let movedRaw = checkedActionProjects nameEq keyEq (ORemove actor)
                (MkSystemState movedAmbient movedRegistry) swappedFinal
                orchestrationTag movedOrchestrationChecked
              0 movedObservation : RemoveBindingObservation nameEq actor
                movedRegistry swappedFinal
              movedObservation = removeBindingObservation nameEq keyEq actor
                movedAmbient movedRegistry orchestrationTag swappedFinal movedRaw
              0 sourceShape : (bindings (registry orchestrationAfter) =
                deleteEntries @{nameEq} actor (bindings sourceRegistry))
              sourceShape = removedObservedBindings sourceObservation
              0 movedShape : (bindings (registry swappedFinal) =
                deleteEntries @{nameEq} actor (bindings movedRegistry))
              movedShape = removedObservedBindings movedObservation
              reverseDistinct : Not (actionOwner activationAction = actor)
              reverseDistinct = \same => distinct (sym same)
              0 originalShape : bindings (registry originalFinal) =
                replaceEntries @{nameEq} (actionOwner activationAction)
                  (sourceReplacementFiber comparison)
                  (deleteEntries @{nameEq} actor (bindings sourceRegistry))
              originalShape = trans (sourceReplacementBindings comparison)
                (cong (replaceEntries @{nameEq} (actionOwner activationAction)
                  (sourceReplacementFiber comparison)) sourceShape)
              0 swappedShape : bindings (registry swappedFinal) =
                replaceEntries @{nameEq} (actionOwner activationAction)
                  (movedReplacementFiber comparison)
                  (deleteEntries @{nameEq} actor (bindings sourceRegistry))
              swappedShape = trans movedShape
                (trans
                  (cong (deleteEntries @{nameEq} actor)
                    (movedReplacementBindings comparison))
                  (deleteEntriesAfterDistinctReplace nameEq
                    (actionOwner activationAction) actor reverseDistinct
                    (movedReplacementFiber comparison)
                    (bindings sourceRegistry)))
              0 canonical : OrderedRegistryControlsRelated name key world error
                value
                (replaceEntries @{nameEq} (actionOwner activationAction)
                  (sourceReplacementFiber comparison)
                  (deleteEntries @{nameEq} actor (bindings sourceRegistry)))
                (replaceEntries @{nameEq} (actionOwner activationAction)
                  (movedReplacementFiber comparison)
                  (deleteEntries @{nameEq} actor (bindings sourceRegistry)))
              canonical = orderedControlsReplace nameEq
                (actionOwner activationAction)
                (sourceReplacementFiber comparison)
                (movedReplacementFiber comparison)
                (replacementFibersRelated comparison)
                (deleteEntries @{nameEq} actor (bindings sourceRegistry))
                (deleteEntries @{nameEq} actor (bindings sourceRegistry))
                (orderedControlsReflexive
                  (deleteEntries @{nameEq} actor (bindings sourceRegistry)))
          in orderedControlsTransport (sym originalShape) (sym swappedShape)
            canonical

record ActivationActivationCheckedCore
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal)
  (earlyRight : Transition first earlyRightFinal) where
  constructor MkActivationActivationCheckedCore
  checkedCoreFinal : SystemState name key value world error
  checkedCoreMovedLeft : Transition earlyRightFinal checkedCoreFinal
  0 checkedCoreMovedLeftChecked : checkedApplyAction @{nameEq} @{keyEq}
    (transitionAction left) earlyRightFinal =
    Just (transitionTag left, checkedCoreFinal)
  0 checkedCoreMovedLeftAction :
    transitionAction checkedCoreMovedLeft = transitionAction left
  0 checkedCoreMovedLeftTag :
    transitionTag checkedCoreMovedLeft = transitionTag left
  0 checkedCoreMovedRightActivation : PaperActivationStep earlyRight
  0 checkedCoreMovedLeftActivation : PaperActivationStep checkedCoreMovedLeft
  0 checkedCoreEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq} checkedCoreFinal)
  0 checkedCoreWellFormed : registryWellFormed @{nameEq} @{keyEq}
    checkedCoreFinal = True

0 activationActivationCheckedCore :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight NoTransitions) ->
  transitionAction earlyRight = transitionAction right ->
  transitionTag earlyRight = transitionTag right ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  ActivationActivationCheckedCore nameEq keyEq left right earlyRight
activationActivationCheckedCore nameEq keyEq left right earlyRight
  sourceAligned earlyRightAligned sameAction sameTag leftActivation
  rightActivation distinct sourceWellFormed independent =
    case sourceAligned of
      AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ AlignedEnd) =>
          case earlyRightAligned of
            AlignedStep earlyAction earlyTag earlyChecked _ AlignedEnd =>
              let 0 earlyCheckedRight = checkedActivationEquationTransport
                    nameEq keyEq earlyAction rightAction sameAction earlyTag
                    rightTag sameTag earlyChecked
                  0 earlyActivation = paperActivationStepTransport sameAction
                    sameTag rightActivation
                  0 earlyWellFormed = preservationTheoremProof nameEq keyEq
                    rightAction first earlyRightFinal rightTag sourceWellFormed
                    (checkedActionProjects nameEq keyEq rightAction first
                      earlyRightFinal rightTag earlyCheckedRight)
                  0 distinctOwners :
                    Not (actionOwner leftAction = actionOwner rightAction)
                  distinctOwners sameOwner = distinct
                    (trans
                      (transitionActorFiredActionOwner nameEq keyEq leftAction
                        leftTag leftChecked)
                      (trans sameOwner
                        (sym (transitionActorFiredActionOwner nameEq keyEq
                          rightAction rightTag rightChecked))))
                  0 effectOutput : ActivationPairEffectOutput nameEq keyEq
                    leftAction leftTag earlyRightFinal originalFinal
                  effectOutput = activationPairEffectOutput nameEq keyEq
                    leftAction rightAction leftTag rightTag leftChecked
                    rightChecked earlyCheckedRight leftActivation rightActivation
                    distinctOwners independent
                  0 rawMove : RawActivationMove nameEq keyEq leftAction leftTag
                    earlyRightFinal
                  rawMove = activationRawAfterForeignActivation nameEq keyEq
                    leftAction rightAction leftTag rightTag leftChecked
                    earlyCheckedRight leftActivation
                    (paperActivationStepTransport Refl Refl rightActivation)
                    distinctOwners earlyWellFormed
                    (activationPairEffectState effectOutput)
                    (movedLeftEffectMapRuns effectOutput)
                  0 endpoint : CheckedActivationEndpoint nameEq keyEq leftAction
                    leftTag earlyRightFinal originalFinal
                  endpoint = checkActivationEndpoint nameEq keyEq leftAction
                    leftTag earlyRightFinal originalFinal earlyWellFormed
                    effectOutput rawMove
                  0 movedLeftActivation : PaperActivationStep
                    (checkedEndpointTransition endpoint)
                  movedLeftActivation = paperActivationStepTransport
                    (checkedEndpointAction endpoint)
                    (checkedEndpointTag endpoint) leftActivation
              in MkActivationActivationCheckedCore
                (checkedEndpointAfter endpoint)
                (checkedEndpointTransition endpoint)
                (checkedEndpointEquation endpoint)
                (checkedEndpointAction endpoint)
                (checkedEndpointTag endpoint) earlyActivation
                movedLeftActivation (checkedEndpointEffects endpoint)
                (checkedEndpointWellFormed endpoint)

||| Candidate for paper Lemma 71(1).
public export
0 activationActivationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight NoTransitions)) ->
  transitionAction earlyRight = transitionAction right ->
  transitionTag earlyRight = transitionTag right ->
  PaperActivationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
activationActivationDiamondSpike nameEq keyEq left right earlyRight
  sourceAligned earlyRightAligned sameAction sameTag leftActivation
  rightActivation distinct sourceWellFormed independent =
    case sourceAligned of
      AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ AlignedEnd) =>
          case earlyRightAligned of
            AlignedStep earlyAction earlyTag earlyChecked _ AlignedEnd =>
              let 0 earlyCheckedRight = checkedActivationEquationTransport
                    nameEq keyEq earlyAction rightAction sameAction earlyTag
                    rightTag sameTag earlyChecked
                  0 earlyActivation : PaperActivationStep
                    (Fired {before = first} {afterState = earlyRightFinal}
                      nameEq keyEq rightAction rightTag earlyCheckedRight)
                  earlyActivation = paperActivationStepTransport Refl Refl
                    rightActivation
                  0 middleWellFormed : registryWellFormed @{nameEq} @{keyEq}
                    middle = True
                  middleWellFormed = preservationTheoremProof nameEq keyEq
                    leftAction first middle leftTag sourceWellFormed
                    (checkedActionProjects nameEq keyEq leftAction first middle
                      leftTag leftChecked)
                  0 earlyWellFormed : registryWellFormed @{nameEq} @{keyEq}
                    earlyRightFinal = True
                  earlyWellFormed = preservationTheoremProof nameEq keyEq
                    rightAction first earlyRightFinal rightTag sourceWellFormed
                    (checkedActionProjects nameEq keyEq rightAction first
                      earlyRightFinal rightTag earlyCheckedRight)
                  0 distinctOwners :
                    Not (actionOwner leftAction = actionOwner rightAction)
                  distinctOwners sameOwner = distinct
                    (trans
                      (transitionActorFiredActionOwner nameEq keyEq leftAction
                        leftTag leftChecked)
                      (trans sameOwner
                        (sym (transitionActorFiredActionOwner nameEq keyEq
                          rightAction rightTag rightChecked))))
                  0 reverseDistinctOwners :
                    Not (actionOwner rightAction = actionOwner leftAction)
                  reverseDistinctOwners sameOwner = distinctOwners (sym sameOwner)
                  pairTrace : Transitions first originalFinal
                  pairTrace = MoreTransitions
                    (Fired {before = first} {afterState = middle}
                      nameEq keyEq leftAction leftTag leftChecked)
                    (MoreTransitions
                      (Fired {before = middle} {afterState = originalFinal}
                        nameEq keyEq rightAction rightTag rightChecked)
                      NoTransitions)
                  0 leftOccurs : OccursIn
                    (Fired {before = first} {afterState = middle}
                      nameEq keyEq leftAction leftTag leftChecked) pairTrace
                  leftOccurs = OccursHere
                  0 rightOccurs : OccursIn
                    (Fired {before = middle} {afterState = originalFinal}
                      nameEq keyEq rightAction rightTag rightChecked) pairTrace
                  rightOccurs = OccursLater OccursHere
                  leftGenerator : TraceEffectGenerator name key world error value
                    (actionOwner leftAction) pairTrace
                  leftGenerator = ActualForwardGenerator first middle nameEq keyEq
                    leftAction leftTag leftChecked leftOccurs Refl
                  rightGenerator : TraceEffectGenerator name key world error value
                    (actionOwner rightAction) pairTrace
                  rightGenerator = ActualForwardGenerator middle originalFinal
                    nameEq keyEq rightAction rightTag rightChecked rightOccurs Refl
                  leftMap : PartialEffectMap name key value world
                  leftMap = partialEffectMapFor nameEq keyEq leftAction leftTag first
                  rightMap : PartialEffectMap name key value world
                  rightMap = partialEffectMapFor nameEq keyEq rightAction rightTag
                    middle
                  earlyRightMap : PartialEffectMap name key value world
                  earlyRightMap = partialEffectMapFor nameEq keyEq rightAction
                    rightTag first
                  0 rightLookup : lookupFiber @{nameEq} {name = name}
                    {key = key} {value = value} {world = world} {error = error}
                    (actionOwner rightAction) (registry middle) =
                    lookupFiber @{nameEq} {name = name} {key = key}
                      {value = value} {world = world} {error = error}
                      (actionOwner rightAction) (registry first)
                  rightLookup = transitionForeignLookup nameEq keyEq
                    (actionOwner rightAction) leftAction leftTag leftChecked
                    reverseDistinctOwners
                  0 rightOriginSame : (state : EffectState name key value world) ->
                    rightMap state = earlyRightMap state
                  rightOriginSame = activationTransitionMapOriginCong nameEq keyEq
                    rightAction rightTag rightChecked rightActivation rightLookup
                  0 leftGeneratorMapSame :
                    (state : EffectState name key value world) ->
                    traceGeneratorMap leftGenerator state = leftMap state
                  leftGeneratorMapSame = actualForwardGeneratorMapSame first middle
                    nameEq keyEq leftAction leftTag leftChecked leftOccurs Refl
                  0 rightGeneratorMapSame :
                    (state : EffectState name key value world) ->
                    traceGeneratorMap rightGenerator state = rightMap state
                  rightGeneratorMapSame = actualForwardGeneratorMapSame middle
                    originalFinal nameEq keyEq rightAction rightTag rightChecked
                    rightOccurs Refl
                  0 leftFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (leftMap (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} middle))
                  leftFrame = checkedEffectFrameRelation nameEq keyEq leftAction
                    leftTag first middle leftChecked
                  0 rawEarlyFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (earlyRightMap (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} earlyRightFinal))
                  rawEarlyFrame = checkedEffectFrameRelation nameEq keyEq
                    rightAction rightTag first earlyRightFinal earlyCheckedRight
                  0 earlyFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (rightMap (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} earlyRightFinal))
                  earlyFrame = localPartialRelatedRewrite
                    (sym (rightOriginSame (projectEffectState @{nameEq} first)))
                    Refl rawEarlyFrame
                  0 leftGeneratorFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (traceGeneratorMap leftGenerator
                      (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} middle))
                  leftGeneratorFrame = localPartialRelatedRewrite
                    (leftGeneratorMapSame (projectEffectState @{nameEq} first))
                    Refl leftFrame
                  0 rightGeneratorFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (traceGeneratorMap rightGenerator
                      (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} earlyRightFinal))
                  rightGeneratorFrame = localPartialRelatedRewrite
                    (rightGeneratorMapSame (projectEffectState @{nameEq} first))
                    Refl earlyFrame
                  0 effectOutput : ActivationPairEffectOutput nameEq keyEq
                    leftAction leftTag earlyRightFinal originalFinal
                  effectOutput = activationPairEffectOutput nameEq keyEq
                    leftAction rightAction leftTag rightTag leftChecked
                    rightChecked earlyCheckedRight leftActivation rightActivation
                    distinctOwners independent
                  0 rawMove : RawActivationMove nameEq keyEq leftAction leftTag
                    earlyRightFinal
                  rawMove = activationRawAfterForeignActivation nameEq keyEq
                    leftAction rightAction leftTag rightTag leftChecked
                    earlyCheckedRight leftActivation earlyActivation distinctOwners
                    earlyWellFormed (activationPairEffectState effectOutput)
                    (movedLeftEffectMapRuns effectOutput)
                  0 endpoint : CheckedActivationEndpoint nameEq keyEq leftAction
                    leftTag earlyRightFinal originalFinal
                  endpoint = checkActivationEndpoint nameEq keyEq leftAction
                    leftTag earlyRightFinal originalFinal earlyWellFormed
                    effectOutput rawMove
                  swappedFinal : SystemState name key value world error
                  swappedFinal = checkedEndpointAfter endpoint
                  0 movedCheckedLeft : checkedApplyAction @{nameEq} @{keyEq}
                    leftAction earlyRightFinal = Just (leftTag, swappedFinal)
                  movedCheckedLeft = checkedEndpointEquation endpoint
                  0 movedRightActivation : PaperActivationStep
                    (Fired {before = first} {afterState = earlyRightFinal}
                      nameEq keyEq rightAction rightTag earlyCheckedRight)
                  movedRightActivation = earlyActivation
                  0 movedLeftActivation : PaperActivationStep
                    (Fired {before = earlyRightFinal} {afterState = swappedFinal}
                      nameEq keyEq leftAction leftTag movedCheckedLeft)
                  movedLeftActivation = paperActivationStepTransport Refl Refl
                    leftActivation
                  0 effectsRelated : EffectStateRelated keyEq
                    (projectEffectState @{nameEq} originalFinal)
                    (projectEffectState @{nameEq} swappedFinal)
                  effectsRelated = checkedEndpointEffects endpoint
                  0 finalWellFormed : registryWellFormed @{nameEq} @{keyEq}
                    swappedFinal = True
                  finalWellFormed = checkedEndpointWellFormed endpoint
                  0 leftLookup : (lookupFiber @{nameEq} {name = name}
                    {key = key} {value = value} {world = world}
                    {error = error} (actionOwner leftAction)
                    (registry earlyRightFinal) = lookupFiber @{nameEq}
                      {name = name} {key = key} {value = value}
                      {world = world} {error = error}
                      (actionOwner leftAction) (registry first))
                  leftLookup = transitionForeignLookup nameEq keyEq
                    (actionOwner leftAction) rightAction rightTag
                    earlyCheckedRight distinctOwners
                  0 movedRightLookup : (lookupFiber @{nameEq}
                    {name = name} {key = key} {value = value}
                    {world = world} {error = error}
                    (actionOwner rightAction) (registry middle) =
                    lookupFiber @{nameEq} {name = name} {key = key}
                      {value = value} {world = world} {error = error}
                      (actionOwner rightAction) (registry first))
                  movedRightLookup = rightLookup
                  0 leftTargets : (fiber : Fiber name key value world error) ->
                    (view : View name (dependencies
                      (componentDependencies
                        (fiberComponent fiber)))) ->
                    targetFiber @{nameEq} @{keyEq} fiber
                      (registry first) = Just view ->
                    targetFiber @{nameEq} @{keyEq} fiber
                      (registry earlyRightFinal) = Just view
                  leftTargets = \fiber, view, target =>
                    targetFiberStableAfterForeignActivation nameEq
                      keyEq fiber view rightAction rightTag
                      earlyCheckedRight earlyActivation earlyWellFormed
                      target
                  0 rightTargets : (fiber : Fiber name key value world error) ->
                    (view : View name (dependencies
                      (componentDependencies
                        (fiberComponent fiber)))) ->
                    targetFiber @{nameEq} @{keyEq} fiber
                      (registry first) = Just view ->
                    targetFiber @{nameEq} @{keyEq} fiber
                      (registry middle) = Just view
                  rightTargets = \fiber, view, target =>
                    targetFiberStableAfterForeignActivation nameEq
                      keyEq fiber view leftAction leftTag leftChecked
                      leftActivation middleWellFormed target
                  0 leftOutcomes : (stage : IteratorStage name key
                    world error value (actionOwner leftAction)
                    pairTrace) -> IteratorOutcomeAgreement name key
                      value world error keyEq
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq}
                          earlyRightFinal))
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} first))
                  leftOutcomes = \stage =>
                    iteratorOutcomeAfterFramedForeign keyEq independent
                      (actionOwner leftAction)
                      (actionOwner rightAction) distinctOwners stage
                      (TraceGenerator rightGenerator)
                      (projectEffectState @{nameEq} first)
                      (projectEffectState @{nameEq} earlyRightFinal)
                      rightGeneratorFrame
                  0 rightOutcomes : (stage : IteratorStage name key
                    world error value (actionOwner rightAction)
                    pairTrace) -> IteratorOutcomeAgreement name key
                      value world error keyEq
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} middle))
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} first))
                  rightOutcomes = \stage =>
                    iteratorOutcomeAfterFramedForeign keyEq independent
                      (actionOwner rightAction)
                      (actionOwner leftAction) reverseDistinctOwners
                      stage (TraceGenerator leftGenerator)
                      (projectEffectState @{nameEq} first)
                      (projectEffectState @{nameEq} middle)
                      leftGeneratorFrame
                  0 leftComparison : ActivationReplacementComparison
                    nameEq (actionOwner leftAction) first middle
                    earlyRightFinal swappedFinal
                  leftComparison =
                    activationReplacementComparisonAcrossForeignStates
                      nameEq keyEq leftAction leftTag pairTrace
                      {sourceBefore = first}
                      {movedBefore = earlyRightFinal}
                      {sourceAfter = middle} {movedAfter = swappedFinal}
                      leftChecked movedCheckedLeft (Left leftOccurs)
                      leftActivation leftLookup leftTargets leftOutcomes
                  0 rightComparison : ActivationReplacementComparison
                    nameEq (actionOwner rightAction) first
                    earlyRightFinal middle originalFinal
                  rightComparison =
                    activationReplacementComparisonAcrossForeignStates
                      nameEq keyEq rightAction rightTag pairTrace
                      {sourceBefore = first} {movedBefore = middle}
                      {sourceAfter = earlyRightFinal}
                      {movedAfter = originalFinal} earlyCheckedRight
                      rightChecked (Right rightOccurs) earlyActivation
                      movedRightLookup rightTargets rightOutcomes
                  0 originalShape : bindings (registry originalFinal) =
                    replaceEntries @{nameEq} (actionOwner rightAction)
                      (movedReplacementFiber rightComparison)
                      (replaceEntries @{nameEq} (actionOwner leftAction)
                        (sourceReplacementFiber leftComparison)
                        (bindings (registry first)))
                  originalShape = trans
                    (movedReplacementBindings rightComparison)
                    (cong (replaceEntries @{nameEq}
                      (actionOwner rightAction)
                      (movedReplacementFiber rightComparison))
                      (sourceReplacementBindings leftComparison))
                  0 swappedShape : bindings (registry swappedFinal) =
                    replaceEntries @{nameEq} (actionOwner leftAction)
                      (movedReplacementFiber leftComparison)
                      (replaceEntries @{nameEq} (actionOwner rightAction)
                        (sourceReplacementFiber rightComparison)
                        (bindings (registry first)))
                  swappedShape = trans
                    (movedReplacementBindings leftComparison)
                    (cong (replaceEntries @{nameEq}
                      (actionOwner leftAction)
                      (movedReplacementFiber leftComparison))
                      (sourceReplacementBindings rightComparison))
                  0 controls : OrderedRegistryControlsRelated name key world
                    error value (bindings (registry originalFinal))
                      (bindings (registry swappedFinal))
                  controls = orderedControlsAfterDistinctReplacements
                    nameEq (actionOwner leftAction)
                    (actionOwner rightAction) distinctOwners
                    (bindings (registry first))
                    (bindings (registry originalFinal))
                    (bindings (registry swappedFinal))
                    (sourceReplacementFiber leftComparison)
                    (movedReplacementFiber leftComparison)
                    (movedReplacementFiber rightComparison)
                    (sourceReplacementFiber rightComparison)
                    (replacementFibersRelated leftComparison)
                    (fiberControlSymmetric
                      (replacementFibersRelated rightComparison))
                    originalShape swappedShape
              in MkLocalRelationalDiamond earlyRightFinal swappedFinal
                earlyRight
                (Fired nameEq keyEq leftAction leftTag movedCheckedLeft)
                (alignedMovedPairWithCheckedTail nameEq keyEq earlyRight
                  earlyRightAligned leftAction leftTag movedCheckedLeft)
                sameAction sameTag Refl Refl
                (\_ => paperActivationStepTransport sameAction sameTag
                  rightActivation)
                (\_ => paperActivationStepTransport Refl Refl
                  leftActivation)
                (\orchestration => void
                  (paperActivationOrchestrationImpossible
                    rightActivation orchestration))
                (\orchestration => void
                  (paperActivationOrchestrationImpossible
                    leftActivation orchestration))
                effectsRelated
                (orderedControlsGiveControlEquivalent nameEq originalFinal
                  swappedFinal controls)
                finalWellFormed

||| Candidate for paper Lemma 71(2).
public export
0 activationOrchestrationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  PaperActivationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction right = OInsert child (ChildOf parent) component ->
    Not (transitionActor left = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
activationOrchestrationDiamondSpike nameEq keyEq left right sourceAligned
  leftActivation rightOrchestration distinct parentSafe sourceWellFormed
  independent =
    case sourceAligned of
      AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ AlignedEnd) =>
          let 0 distinctOwners :
                Not (actionOwner leftAction = actionOwner rightAction)
              distinctOwners sameOwner = distinct
                (trans
                  (transitionActorFiredActionOwner nameEq keyEq leftAction
                    leftTag leftChecked)
                  (trans sameOwner
                    (sym (transitionActorFiredActionOwner nameEq keyEq
                      rightAction rightTag rightChecked))))
              0 reverseDistinctOwners :
                Not (actionOwner rightAction = actionOwner leftAction)
              reverseDistinctOwners sameOwner = distinctOwners (sym sameOwner)
              0 rawEarlyRight : RawActivationMove nameEq keyEq rightAction
                rightTag first
              rawEarlyRight = orchestrationRawBeforeCheckedActivation nameEq
                keyEq leftAction rightAction leftTag rightTag leftChecked
                rightChecked leftActivation rightOrchestration distinctOwners
          in case checkRawActivationMove nameEq keyEq rightAction rightTag first
            sourceWellFormed rawEarlyRight of
            MkCheckedActivationMove earlyRightFinal earlyRightChecked _ =>
                let earlyRightTransition : Transition first earlyRightFinal
                    earlyRightTransition = Fired nameEq keyEq rightAction
                      rightTag earlyRightChecked
                    0 earlyRightOrchestration : PaperOrchestrationStep
                      earlyRightTransition
                    earlyRightOrchestration = paperOrchestrationStepTransport
                      Refl Refl rightOrchestration
                    0 earlyRightWellFormed : registryWellFormed @{nameEq}
                      @{keyEq} earlyRightFinal = True
                    earlyRightWellFormed = preservationTheoremProof nameEq keyEq
                      rightAction first earlyRightFinal rightTag sourceWellFormed
                      (checkedActionProjects nameEq keyEq rightAction first
                        earlyRightFinal rightTag earlyRightChecked)
                    pairTrace : Transitions first originalFinal
                    pairTrace = MoreTransitions
                      (Fired {before = first} {afterState = middle}
                        nameEq keyEq leftAction leftTag leftChecked)
                      (MoreTransitions
                        (Fired {before = middle} {afterState = originalFinal}
                          nameEq keyEq rightAction rightTag rightChecked)
                        NoTransitions)
                    0 leftOccurs : OccursIn
                      (Fired {before = first} {afterState = middle}
                        nameEq keyEq leftAction leftTag leftChecked) pairTrace
                    leftOccurs = OccursHere
                    0 rightOccurs : OccursIn
                      (Fired {before = middle} {afterState = originalFinal}
                        nameEq keyEq rightAction rightTag rightChecked) pairTrace
                    rightOccurs = OccursLater OccursHere
                    rightGenerator : TraceEffectGenerator name key world error
                      value (actionOwner rightAction) pairTrace
                    rightGenerator = ActualForwardGenerator middle originalFinal
                      nameEq keyEq rightAction rightTag rightChecked rightOccurs
                      Refl
                    0 rightGeneratorMapSame :
                      (state : EffectState name key value world) ->
                      traceGeneratorMap rightGenerator state =
                        partialEffectMapFor nameEq keyEq rightAction rightTag
                          middle state
                    rightGeneratorMapSame = actualForwardGeneratorMapSame middle
                      originalFinal nameEq keyEq rightAction rightTag rightChecked
                      rightOccurs Refl
                    0 rightOriginSame :
                      (state : EffectState name key value world) ->
                      partialEffectMapFor nameEq keyEq rightAction rightTag
                        middle state =
                      partialEffectMapFor nameEq keyEq rightAction rightTag
                        first state
                    rightOriginSame = orchestrationTransitionMapOriginCong
                      nameEq keyEq rightAction rightTag rightChecked
                      rightOrchestration middle first
                    0 earlyRightFrame : PartialRelated
                      (EffectState name key value world)
                      (EffectStateRelated keyEq)
                      (partialEffectMapFor nameEq keyEq rightAction rightTag first
                        (projectEffectState @{nameEq} first))
                      (Just (projectEffectState @{nameEq} earlyRightFinal))
                    earlyRightFrame = checkedEffectFrameRelation nameEq keyEq
                      rightAction rightTag first earlyRightFinal
                      earlyRightChecked
                    0 rightGeneratorAtFirst : Equal
                      (traceGeneratorMap rightGenerator
                        (projectEffectState @{nameEq} first))
                      (partialEffectMapFor nameEq keyEq rightAction rightTag first
                        (projectEffectState @{nameEq} first))
                    rightGeneratorAtFirst = trans
                      (rightGeneratorMapSame
                        (projectEffectState @{nameEq} first))
                      (rightOriginSame
                        (projectEffectState @{nameEq} first))
                    0 rightGeneratorFrame : PartialRelated
                      (EffectState name key value world)
                      (EffectStateRelated keyEq)
                      (traceGeneratorMap rightGenerator
                        (projectEffectState @{nameEq} first))
                      (Just (projectEffectState @{nameEq} earlyRightFinal))
                    rightGeneratorFrame = localPartialRelatedRewrite
                      (sym rightGeneratorAtFirst) Refl earlyRightFrame
                    0 targetPreserved :
                      (fiber : Fiber name key value world error) ->
                      (view : View name (dependencies
                        (componentDependencies (fiberComponent fiber)))) ->
                      targetFiber @{nameEq} @{keyEq} fiber (registry first) =
                        Just view ->
                      targetFiber @{nameEq} @{keyEq} fiber
                        (registry earlyRightFinal) = Just view
                    targetPreserved = \fiber, view, sourceTarget =>
                      trans
                        (targetFiberStableAfterPaperOrchestration nameEq keyEq
                          rightAction rightTag earlyRightChecked
                          earlyRightOrchestration fiber)
                        sourceTarget
                    0 effectOutput : ActivationPairEffectOutput nameEq keyEq
                      leftAction leftTag earlyRightFinal originalFinal
                    effectOutput = activationOrchestrationPairEffectOutput nameEq
                      keyEq leftAction rightAction leftTag rightTag leftChecked
                      rightChecked earlyRightChecked leftActivation
                      rightOrchestration distinctOwners independent
                    0 rawMovedLeft : RawActivationMove nameEq keyEq leftAction
                      leftTag earlyRightFinal
                    rawMovedLeft = activationRawAfterForeignState nameEq keyEq
                      leftAction rightAction leftTag rightTag leftChecked
                      earlyRightChecked leftActivation distinctOwners
                      targetPreserved (activationPairEffectState effectOutput)
                      (movedLeftEffectMapRuns effectOutput)
                    0 endpoint : CheckedActivationEndpoint nameEq keyEq
                      leftAction leftTag earlyRightFinal originalFinal
                    endpoint = checkActivationEndpoint nameEq keyEq leftAction
                      leftTag earlyRightFinal originalFinal earlyRightWellFormed
                      effectOutput rawMovedLeft
                    swappedFinal : SystemState name key value world error
                    swappedFinal = checkedEndpointAfter endpoint
                    0 movedLeftChecked : checkedApplyAction @{nameEq} @{keyEq}
                      leftAction earlyRightFinal = Just (leftTag, swappedFinal)
                    movedLeftChecked = checkedEndpointEquation endpoint
                    0 movedLeftActivation : PaperActivationStep
                      (checkedEndpointTransition endpoint)
                    movedLeftActivation = paperActivationStepTransport
                      (checkedEndpointAction endpoint)
                      (checkedEndpointTag endpoint) leftActivation
                    0 leftLookup : lookupFiber @{nameEq} {name = name}
                      {key = key} {value = value} {world = world}
                      {error = error} (actionOwner leftAction)
                      (registry earlyRightFinal) = lookupFiber @{nameEq}
                      (actionOwner leftAction) (registry first)
                    leftLookup = transitionForeignLookup nameEq keyEq
                      (actionOwner leftAction) rightAction rightTag
                      earlyRightChecked distinctOwners
                    0 leftOutcomes :
                      (stage : IteratorStage name key world error value
                        (actionOwner leftAction) pairTrace) ->
                      IteratorOutcomeAgreement name key value world error keyEq
                        (iteratorStageOutcome stage
                          (projectEffectState @{nameEq} earlyRightFinal))
                        (iteratorStageOutcome stage
                          (projectEffectState @{nameEq} first))
                    leftOutcomes = \stage => iteratorOutcomeAfterFramedForeign
                      keyEq independent (actionOwner leftAction)
                      (actionOwner rightAction) distinctOwners stage
                      (TraceGenerator rightGenerator)
                      (projectEffectState @{nameEq} first)
                      (projectEffectState @{nameEq} earlyRightFinal)
                      rightGeneratorFrame
                    0 leftComparison : ActivationReplacementComparison nameEq
                      (actionOwner leftAction) first middle earlyRightFinal
                      swappedFinal
                    leftComparison =
                      activationReplacementComparisonAcrossForeignStates nameEq
                        keyEq leftAction leftTag pairTrace leftChecked
                        movedLeftChecked (Left leftOccurs) leftActivation
                        leftLookup targetPreserved leftOutcomes
                    0 reverseControls : OrderedRegistryControlsRelated name key
                      world error value (bindings (registry swappedFinal))
                      (bindings (registry originalFinal))
                    reverseControls = orderedControlsAfterOrchestrationActivation
                      nameEq keyEq rightAction leftAction rightTag leftTag
                      earlyRightChecked movedLeftChecked leftChecked rightChecked
                      earlyRightOrchestration reverseDistinctOwners
                      (activationReplacementComparisonSymmetric leftComparison)
                    0 controls : OrderedRegistryControlsRelated name key world
                      error value (bindings (registry originalFinal))
                      (bindings (registry swappedFinal))
                    controls = orderedControlsSymmetric reverseControls
                in MkLocalRelationalDiamond earlyRightFinal swappedFinal
                  earlyRightTransition (checkedEndpointTransition endpoint)
                  (rewrite checkedEndpointTransitionExact endpoint in
                    AlignedStep rightAction rightTag earlyRightChecked
                      (MoreTransitions
                        (Fired nameEq keyEq leftAction leftTag
                          (checkedEndpointEquation endpoint))
                        NoTransitions)
                      (AlignedStep leftAction leftTag
                        (checkedEndpointEquation endpoint) NoTransitions
                        AlignedEnd))
                  Refl Refl (checkedEndpointAction endpoint)
                  (checkedEndpointTag endpoint)
                  (\activation => void
                    (paperActivationOrchestrationImpossible activation
                      rightOrchestration))
                  (\_ => movedLeftActivation)
                  (\_ => earlyRightOrchestration)
                  (\orchestration => void
                    (paperActivationOrchestrationImpossible leftActivation
                      orchestration))
                  (checkedEndpointEffects endpoint)
                  (orderedControlsGiveControlEquivalent nameEq originalFinal
                    swappedFinal controls)
                  (checkedEndpointWellFormed endpoint)

||| The reverse mixed orientation needed when a yielded O-Insert at the end of
||| one actor block crosses the following block's activation while bubbling that
||| block left.  `earlyRight` is the checked activation at the pre-orchestration
||| source; child/parent exclusions keep the activation independent of the
||| insertion generation and its licensing parent.
public export
0 orchestrationActivationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight NoTransitions)) ->
  transitionAction earlyRight = transitionAction right ->
  transitionTag earlyRight = transitionTag right ->
  PaperOrchestrationStep left -> PaperActivationStep right ->
  Not (transitionActor left = transitionActor right) ->
  ((child : name) -> (parent : Parent name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child parent component ->
    Not (transitionActor right = child)) ->
  ((child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child (ChildOf parent) component ->
    Not (transitionActor right = parent)) ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
orchestrationActivationDiamondSpike nameEq keyEq left right earlyRight
  sourceAligned earlyRightAligned sameAction sameTag leftOrchestration
  rightActivation distinct childSafe parentSafe sourceWellFormed independent =
    case sourceAligned of
      AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ AlignedEnd) =>
          case earlyRightAligned of
            AlignedStep earlyAction earlyTag earlyChecked _ AlignedEnd =>
              let 0 earlyCheckedRight = checkedActivationEquationTransport
                    nameEq keyEq earlyAction rightAction sameAction earlyTag
                    rightTag sameTag earlyChecked
                  0 earlyActivation : PaperActivationStep
                    (Fired {before = first} {afterState = earlyRightFinal}
                      nameEq keyEq rightAction rightTag earlyCheckedRight)
                  earlyActivation = paperActivationStepTransport Refl Refl
                    rightActivation
                  0 earlyWellFormed : registryWellFormed @{nameEq} @{keyEq}
                    earlyRightFinal = True
                  earlyWellFormed = preservationTheoremProof nameEq keyEq
                    rightAction first earlyRightFinal rightTag sourceWellFormed
                    (checkedActionProjects nameEq keyEq rightAction first
                      earlyRightFinal rightTag earlyCheckedRight)
                  0 distinctOwners :
                    Not (actionOwner leftAction = actionOwner rightAction)
                  distinctOwners sameOwner = distinct
                    (trans
                      (transitionActorFiredActionOwner nameEq keyEq leftAction
                        leftTag leftChecked)
                      (trans sameOwner
                        (sym (transitionActorFiredActionOwner nameEq keyEq
                          rightAction rightTag rightChecked))))
                  0 reverseDistinctOwners :
                    Not (actionOwner rightAction = actionOwner leftAction)
                  reverseDistinctOwners sameOwner = distinctOwners (sym sameOwner)
                  pairTrace : Transitions first originalFinal
                  pairTrace = MoreTransitions
                    (Fired {before = first} {afterState = middle}
                      nameEq keyEq leftAction leftTag leftChecked)
                    (MoreTransitions
                      (Fired {before = middle} {afterState = originalFinal}
                        nameEq keyEq rightAction rightTag rightChecked)
                      NoTransitions)
                  0 leftOccurs : OccursIn
                    (Fired {before = first} {afterState = middle}
                      nameEq keyEq leftAction leftTag leftChecked) pairTrace
                  leftOccurs = OccursHere
                  0 rightOccurs : OccursIn
                    (Fired {before = middle} {afterState = originalFinal}
                      nameEq keyEq rightAction rightTag rightChecked) pairTrace
                  rightOccurs = OccursLater OccursHere
                  leftGenerator : TraceEffectGenerator name key world error value
                    (actionOwner leftAction) pairTrace
                  leftGenerator = ActualForwardGenerator first middle nameEq keyEq
                    leftAction leftTag leftChecked leftOccurs Refl
                  0 leftGeneratorMapSame :
                    (state : EffectState name key value world) ->
                    traceGeneratorMap leftGenerator state =
                      partialEffectMapFor nameEq keyEq leftAction leftTag first state
                  leftGeneratorMapSame = actualForwardGeneratorMapSame first middle
                    nameEq keyEq leftAction leftTag leftChecked leftOccurs Refl
                  0 leftFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (partialEffectMapFor nameEq keyEq leftAction leftTag first
                      (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} middle))
                  leftFrame = checkedEffectFrameRelation nameEq keyEq leftAction
                    leftTag first middle leftChecked
                  0 leftGeneratorFrame : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (traceGeneratorMap leftGenerator
                      (projectEffectState @{nameEq} first))
                    (Just (projectEffectState @{nameEq} middle))
                  leftGeneratorFrame = localPartialRelatedRewrite
                    (leftGeneratorMapSame (projectEffectState @{nameEq} first))
                    Refl leftFrame
                  0 rightLookup : (lookupFiber @{nameEq} {name = name}
                    {key = key} {value = value} {world = world} {error = error}
                    (actionOwner rightAction) (registry first) =
                    lookupFiber @{nameEq} {name = name} {key = key}
                      {value = value} {world = world} {error = error}
                      (actionOwner rightAction) (registry middle))
                  rightLookup = sym (transitionForeignLookup nameEq keyEq
                    (actionOwner rightAction) leftAction leftTag leftChecked
                    reverseDistinctOwners)
                  0 rightTargets : (fiber : Fiber name key value world error) ->
                    (view : View name (dependencies
                      (componentDependencies (fiberComponent fiber)))) ->
                    targetFiber @{nameEq} @{keyEq} fiber
                      (registry middle) = Just view ->
                    targetFiber @{nameEq} @{keyEq} fiber
                      (registry first) = Just view
                  rightTargets = \fiber, view, sourceTarget =>
                    trans
                      (sym (targetFiberStableAfterPaperOrchestration nameEq keyEq
                        leftAction leftTag leftChecked leftOrchestration fiber))
                      sourceTarget
                  0 rightOutcomes : (stage : IteratorStage name key world error
                    value (actionOwner rightAction) pairTrace) ->
                    IteratorOutcomeAgreement name key value world error keyEq
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} first))
                      (iteratorStageOutcome stage
                        (projectEffectState @{nameEq} middle))
                  rightOutcomes = \stage => localIteratorOutcomeAgreementSymmetric
                    (iteratorOutcomeAfterFramedForeign keyEq independent
                      (actionOwner rightAction) (actionOwner leftAction)
                      reverseDistinctOwners stage (TraceGenerator leftGenerator)
                      (projectEffectState @{nameEq} first)
                      (projectEffectState @{nameEq} middle) leftGeneratorFrame)
                  0 comparison : ActivationReplacementComparison nameEq
                    (actionOwner rightAction) middle originalFinal first
                    earlyRightFinal
                  comparison = activationReplacementComparisonAcrossForeignStates
                    nameEq keyEq rightAction rightTag pairTrace
                    {sourceBefore = middle} {movedBefore = first}
                    {sourceAfter = originalFinal} {movedAfter = earlyRightFinal}
                    rightChecked earlyCheckedRight (Left rightOccurs)
                    rightActivation rightLookup rightTargets rightOutcomes
                  0 effectOutput : ActivationPairEffectOutput nameEq keyEq
                    leftAction leftTag earlyRightFinal originalFinal
                  effectOutput = orchestrationActivationPairEffectOutput nameEq
                    keyEq leftAction rightAction leftTag rightTag leftChecked
                    rightChecked earlyCheckedRight leftOrchestration
                    rightActivation distinctOwners independent
                  0 rawMove : RawActivationMove nameEq keyEq leftAction leftTag
                    earlyRightFinal
                  rawMove = orchestrationRawAfterCheckedActivation nameEq keyEq
                    leftAction rightAction leftTag rightTag leftChecked
                    earlyCheckedRight leftOrchestration earlyActivation
                    distinctOwners
                  0 endpoint : CheckedActivationEndpoint nameEq keyEq leftAction
                    leftTag earlyRightFinal originalFinal
                  endpoint = checkActivationEndpoint nameEq keyEq leftAction
                    leftTag earlyRightFinal originalFinal earlyWellFormed
                    effectOutput rawMove
                  swappedFinal : SystemState name key value world error
                  swappedFinal = checkedEndpointAfter endpoint
                  0 movedCheckedLeft : checkedApplyAction @{nameEq} @{keyEq}
                    leftAction earlyRightFinal = Just (leftTag, swappedFinal)
                  movedCheckedLeft = checkedEndpointEquation endpoint
                  0 movedLeftOrchestration : PaperOrchestrationStep
                    (Fired {before = earlyRightFinal} {afterState = swappedFinal}
                      nameEq keyEq leftAction leftTag movedCheckedLeft)
                  movedLeftOrchestration = paperOrchestrationStepTransport Refl
                    Refl leftOrchestration
                  0 controls : OrderedRegistryControlsRelated name key world
                    error value (bindings (registry originalFinal))
                      (bindings (registry swappedFinal))
                  controls = orderedControlsAfterOrchestrationActivation nameEq
                    keyEq leftAction rightAction leftTag rightTag leftChecked
                    rightChecked earlyCheckedRight movedCheckedLeft
                    leftOrchestration distinctOwners comparison
              in MkLocalRelationalDiamond earlyRightFinal swappedFinal earlyRight
                (Fired nameEq keyEq leftAction leftTag movedCheckedLeft)
                (alignedMovedPairWithCheckedTail nameEq keyEq earlyRight
                  earlyRightAligned leftAction leftTag movedCheckedLeft)
                sameAction sameTag Refl Refl
                (\_ => paperActivationStepTransport sameAction sameTag
                  rightActivation)
                (\activation => void
                  (paperActivationOrchestrationImpossible activation
                    leftOrchestration))
                (\orchestration => void
                  (paperActivationOrchestrationImpossible rightActivation
                    orchestration))
                (\_ => movedLeftOrchestration)
                (checkedEndpointEffects endpoint)
                (orderedControlsGiveControlEquivalent nameEq originalFinal
                  swappedFinal controls)
                (checkedEndpointWellFormed endpoint)


0 fiberControlMaybeFromEqual :
  (left, right : Maybe (Fiber name key value world error)) ->
  left = right -> FiberControlMaybeRelated left right
fiberControlMaybeFromEqual left left Refl = fiberControlMaybeReflexive left

0 orchestrationPairControlEquivalent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal, swappedFinal :
    SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first =
    Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle =
    Just (rightTag, originalFinal)) ->
  (earlyRightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, earlyRightFinal)) ->
  (movedLeftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction
    earlyRightFinal = Just (leftTag, swappedFinal)) ->
  (leftPaper : PaperOrchestrationStep
    (Fired {before = first} {afterState = middle}
      nameEq keyEq leftAction leftTag leftChecked)) ->
  (rightPaper : PaperOrchestrationStep
    (Fired {before = middle} {afterState = originalFinal}
      nameEq keyEq rightAction rightTag rightChecked)) ->
  Not (actionOwner leftAction = actionOwner rightAction) ->
  ControlEquivalent name key world error value nameEq originalFinal swappedFinal
orchestrationPairControlEquivalent nameEq keyEq {first} {middle}
  {originalFinal} {earlyRightFinal} {swappedFinal} leftAction rightAction
  leftTag rightTag leftChecked rightChecked earlyRightChecked movedLeftChecked
  leftPaper rightPaper distinctOwners = MkControlEquivalent pointwise
  where
  0 reverseDistinct : Not (actionOwner rightAction = actionOwner leftAction)
  reverseDistinct same = distinctOwners (sym same)

  0 leftOwnerRelated : FiberControlMaybeRelated
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry originalFinal))
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry swappedFinal))
  leftOwnerRelated =
    let 0 sourceSame : Equal
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry first))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction)
            (registry earlyRightFinal))
        sourceSame = sym (transitionForeignLookup nameEq keyEq
          (actionOwner leftAction) rightAction rightTag earlyRightChecked
          distinctOwners)
        0 ownerRelated : FiberControlMaybeRelated
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} (actionOwner leftAction)
              (registry middle))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} (actionOwner leftAction)
              (registry swappedFinal))
        ownerRelated = orchestrationOwnerOutputsRelated nameEq keyEq leftAction
          leftTag leftChecked movedLeftChecked leftPaper sourceSame
        0 originalFrame : Equal
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction)
            (registry originalFinal))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction) (registry middle))
        originalFrame = transitionForeignLookup nameEq keyEq
          (actionOwner leftAction) rightAction rightTag rightChecked
          distinctOwners
    in replace
      {p = \observed => FiberControlMaybeRelated observed
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner leftAction)
          (registry swappedFinal))}
      (sym originalFrame) ownerRelated

  0 rightOwnerRelated : FiberControlMaybeRelated
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction) (registry originalFinal))
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction) (registry swappedFinal))
  rightOwnerRelated =
    let 0 sourceSame : Equal
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction) (registry middle))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction) (registry first))
        sourceSame = transitionForeignLookup nameEq keyEq
          (actionOwner rightAction) leftAction leftTag leftChecked reverseDistinct
        0 ownerRelated : FiberControlMaybeRelated
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} (actionOwner rightAction)
              (registry originalFinal))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} (actionOwner rightAction)
              (registry earlyRightFinal))
        ownerRelated = orchestrationOwnerOutputsRelated nameEq keyEq rightAction
          rightTag rightChecked earlyRightChecked rightPaper sourceSame
        0 swappedFrame : Equal
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction)
            (registry swappedFinal))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction)
            (registry earlyRightFinal))
        swappedFrame = transitionForeignLookup nameEq keyEq
          (actionOwner rightAction) leftAction leftTag movedLeftChecked
          reverseDistinct
    in replace
      {p = \observed => FiberControlMaybeRelated
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner rightAction)
          (registry originalFinal)) observed}
      (sym swappedFrame) ownerRelated

  0 outsideRelated : (selected : name) ->
    Not (selected = actionOwner leftAction) ->
    Not (selected = actionOwner rightAction) ->
    FiberControlMaybeRelated
      (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry originalFinal))
      (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry swappedFinal))
  outsideRelated selected notLeft notRight =
    let 0 originalRightFrame = transitionForeignLookup nameEq keyEq selected
          rightAction rightTag rightChecked notRight
        0 originalLeftFrame = transitionForeignLookup nameEq keyEq selected
          leftAction leftTag leftChecked notLeft
        0 swappedLeftFrame = transitionForeignLookup nameEq keyEq selected
          leftAction leftTag movedLeftChecked notLeft
        0 swappedRightFrame = transitionForeignLookup nameEq keyEq selected
          rightAction rightTag earlyRightChecked notRight
        0 sameLookup : Equal
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry originalFinal))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry swappedFinal))
        sameLookup = trans originalRightFrame
          (trans originalLeftFrame
            (sym (trans swappedLeftFrame swappedRightFrame)))
    in fiberControlMaybeFromEqual _ _ sameLookup

  0 pointwise : (selected : name) -> FiberControlMaybeRelated
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected (registry originalFinal))
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected (registry swappedFinal))
  pointwise selected = case decEq @{nameEq} selected (actionOwner leftAction) of
    Yes selectedLeft => replace
      {p = \actor => FiberControlMaybeRelated
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry originalFinal))
        (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry swappedFinal))}
      (sym selectedLeft) leftOwnerRelated
    No notLeft => case decEq @{nameEq} selected (actionOwner rightAction) of
      Yes selectedRight => replace
        {p = \actor => FiberControlMaybeRelated
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry originalFinal))
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry swappedFinal))}
        (sym selectedRight) rightOwnerRelated
      No notRight => outsideRelated selected notLeft notRight

||| Missing Lemma-71 case exposed by yielded child registrations: two checked
||| orchestration rules, including O-Insert/O-Insert, must transpose under the
||| exact source freshness/generation/licensing package above.
public export
0 orchestrationOrchestrationDiamondSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  (safety : OrchestrationSwapSafety name key world error value protocol nameEq
    keyEq left right) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq
    keyEq (MoreTransitions (earlyRight safety) NoTransitions)) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right
  sourceAligned leftOrchestration rightOrchestration distinct safety
  earlyRightAligned =
    case localAlignedHeadView sourceAligned of
      MkLocalAlignedHeadView leftAction leftTag leftChecked leftActionProjection
        leftTagProjection =>
          case localAlignedHeadView (localAlignedTail sourceAligned) of
            MkLocalAlignedHeadView rightAction rightTag rightChecked
              rightActionProjection rightTagProjection =>
                case localAlignedHeadView earlyRightAligned of
                  MkLocalAlignedHeadView earlyAction earlyTag earlyChecked
                    earlyActionProjection earlyTagProjection =>
                      let 0 sameAction : Equal earlyAction rightAction
                          sameAction = trans (sym earlyActionProjection)
                            (trans (earlyRightAction safety)
                              rightActionProjection)
                          0 sameTag : Equal earlyTag rightTag
                          sameTag = trans (sym earlyTagProjection)
                            (trans (earlyRightTag safety) rightTagProjection)
                          0 leftOuter : PaperOrchestrationStep
                            (Fired {before = first} {afterState = middle}
                              nameEq keyEq leftAction leftTag leftChecked)
                          leftOuter = paperOrchestrationStepTransport
                            (sym leftActionProjection) (sym leftTagProjection)
                            leftOrchestration
                          0 rightOuter : PaperOrchestrationStep
                            (Fired {before = middle} {afterState = originalFinal}
                              nameEq keyEq rightAction rightTag rightChecked)
                          rightOuter = paperOrchestrationStepTransport
                            (sym rightActionProjection) (sym rightTagProjection)
                            rightOrchestration
                          0 earlyCheckedRight : checkedApplyAction @{nameEq}
                            @{keyEq} rightAction first =
                            Just (rightTag, earlyRightFinal safety)
                          earlyCheckedRight = checkedActivationEquationTransport
                            nameEq keyEq earlyAction rightAction sameAction
                            earlyTag rightTag sameTag earlyChecked
                          0 earlyRightOuter : PaperOrchestrationStep
                            (Fired {before = first}
                              {afterState = earlyRightFinal safety}
                              nameEq keyEq rightAction rightTag
                              earlyCheckedRight)
                          earlyRightOuter = paperOrchestrationStepTransport Refl
                            Refl rightOuter
                          0 movedRightOrchestration : PaperOrchestrationStep
                            (earlyRight safety)
                          movedRightOrchestration = paperOrchestrationStepTransport
                            (earlyRightAction safety) (earlyRightTag safety)
                            rightOrchestration
                          0 earlyWellFormed : registryWellFormed @{nameEq}
                            @{keyEq} (earlyRightFinal safety) = True
                          earlyWellFormed = checkedTargetWellFormed nameEq keyEq
                            rightAction first (earlyRightFinal safety) rightTag
                            earlyCheckedRight
                          0 distinctOwners : Not
                            (actionOwner leftAction = actionOwner rightAction)
                          distinctOwners sameOwner = distinct
                            (trans (localTransitionActorActionOwner left)
                              (trans (cong actionOwner leftActionProjection)
                                (trans sameOwner
                                  (sym (trans
                                    (localTransitionActorActionOwner right)
                                    (cong actionOwner
                                      rightActionProjection))))))
                          0 effectOutput : ActivationPairEffectOutput nameEq keyEq
                            leftAction leftTag (earlyRightFinal safety)
                            originalFinal
                          effectOutput = orchestrationPairEffectOutput nameEq
                            keyEq leftAction rightAction leftTag rightTag
                            leftChecked rightChecked earlyCheckedRight leftOuter
                            rightOuter distinctOwners
                          0 rawMove : RawActivationMove nameEq keyEq leftAction
                            leftTag (earlyRightFinal safety)
                          rawMove = orchestrationRawAfterCheckedOrchestration
                            nameEq keyEq leftAction rightAction leftTag rightTag
                            leftChecked rightChecked earlyCheckedRight leftOuter
                            rightOuter distinctOwners
                          0 endpoint : CheckedActivationEndpoint nameEq keyEq
                            leftAction leftTag (earlyRightFinal safety)
                            originalFinal
                          endpoint = checkActivationEndpoint nameEq keyEq
                            leftAction leftTag (earlyRightFinal safety)
                            originalFinal earlyWellFormed effectOutput rawMove
                          swappedFinal : SystemState name key value world error
                          swappedFinal = checkedEndpointAfter endpoint
                          0 movedLeftChecked : checkedApplyAction @{nameEq}
                            @{keyEq} leftAction (earlyRightFinal safety) =
                            Just (leftTag, swappedFinal)
                          movedLeftChecked = checkedEndpointEquation endpoint
                          0 movedLeftOrchestration : PaperOrchestrationStep
                            (Fired {before = earlyRightFinal safety}
                              {afterState = swappedFinal}
                              nameEq keyEq leftAction leftTag movedLeftChecked)
                          movedLeftOrchestration = paperOrchestrationStepTransport
                            Refl Refl leftOuter
                          0 controlEquivalent : ControlEquivalent name key world
                            error value nameEq originalFinal swappedFinal
                          controlEquivalent = orchestrationPairControlEquivalent
                            nameEq keyEq leftAction rightAction leftTag rightTag
                            leftChecked rightChecked earlyCheckedRight
                            movedLeftChecked leftOuter rightOuter distinctOwners
                      in MkLocalRelationalDiamond
                        (earlyRightFinal safety) swappedFinal
                        (earlyRight safety)
                        (Fired nameEq keyEq leftAction leftTag movedLeftChecked)
                        (alignedMovedPairWithCheckedTail nameEq keyEq
                          (earlyRight safety) earlyRightAligned
                          leftAction leftTag movedLeftChecked)
                        (earlyRightAction safety) (earlyRightTag safety)
                        (sym leftActionProjection) (sym leftTagProjection)
                        (\activation => void
                          (paperActivationOrchestrationImpossible activation
                            rightOrchestration))
                        (\activation => void
                          (paperActivationOrchestrationImpossible activation
                            leftOrchestration))
                        (\_ => movedRightOrchestration)
                        (\_ => movedLeftOrchestration)
                        (checkedEndpointEffects endpoint)
                        controlEquivalent
                        (checkedEndpointWellFormed endpoint)

||| Same-external-input relations compose across exact trace concatenation.
||| This is the structural capital used by O6: prefix identity, the authorized
||| pair-local crossing, and recursive suffix replay stay separately indexed.
public export
0 sameExternalAppendSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightMiddle, rightFinal :
    SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  {leftPrefix : Transitions leftFirst leftMiddle} ->
  {leftSuffix : Transitions leftMiddle leftFinal} ->
  {rightPrefix : Transitions rightFirst rightMiddle} ->
  {rightSuffix : Transitions rightMiddle rightFinal} ->
  SameExternalOrchestration nameEq leftPrefix rightPrefix ->
  SameExternalOrchestration nameEq leftSuffix rightSuffix ->
  SameExternalOrchestration nameEq
    (appendTransitions leftPrefix leftSuffix)
    (appendTransitions rightPrefix rightSuffix)
sameExternalAppendSpike nameEq SameExternalOrchestrationEnd suffixRelation =
  suffixRelation
sameExternalAppendSpike nameEq
  (SkipLeftInternal transition rest internal remaining) suffixRelation =
    SkipLeftInternal transition (appendTransitions rest leftSuffix) internal
      (sameExternalAppendSpike nameEq remaining suffixRelation)
sameExternalAppendSpike nameEq
  (SkipRightInternal transition rest internal remaining) suffixRelation =
    SkipRightInternal transition (appendTransitions rest rightSuffix) internal
      (sameExternalAppendSpike nameEq remaining suffixRelation)
sameExternalAppendSpike nameEq
  (MatchExternalInput action leftTransition leftRest leftExternal
    rightTransition rightRest rightExternal leftAction rightAction remaining)
  suffixRelation =
    MatchExternalInput action leftTransition
      (appendTransitions leftRest leftSuffix) leftExternal rightTransition
      (appendTransitions rightRest rightSuffix) rightExternal leftAction
      rightAction (sameExternalAppendSpike nameEq remaining suffixRelation)

||| Exact whole-trace framing for the narrowed revision-18 premise. Neither the
||| prefix nor suffix relation can describe a different pair or endpoint.
public export
0 framePairExternalOrderSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal, swappedMiddle,
    swappedFinal, replayedFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (tracePrefix : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (movedRight : Transition pairFirst swappedMiddle) ->
  (movedLeft : Transition swappedMiddle swappedFinal) ->
  (replayedSuffix : Transitions swappedFinal replayedFinal) ->
  SameExternalOrchestration nameEq tracePrefix tracePrefix ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions)) ->
  SameExternalOrchestration nameEq suffix replayedSuffix ->
  SameExternalOrchestration nameEq
    (appendTransitions tracePrefix
      (MoreTransitions left (MoreTransitions right suffix)))
    (appendTransitions tracePrefix
      (MoreTransitions movedRight (MoreTransitions movedLeft replayedSuffix)))
framePairExternalOrderSpike nameEq tracePrefix left right suffix movedRight
  movedLeft replayedSuffix prefixExternal pairExternal suffixExternal =
    sameExternalAppendSpike nameEq prefixExternal
      (sameExternalAppendSpike nameEq pairExternal suffixExternal)

||| Checked suffix-splice interface consumed by sorting.  It is generic over the
||| local diamond case (A/A, A/O, O/A, or O/O) and returns all recursive capital.
public export
0 adjacentSwapSuffixSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (tracePrefix : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  appendTransitions tracePrefix (MoreTransitions left (MoreTransitions right suffix)) =
    original ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (0 pairExternalOrder : SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))) ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq original
    tracePrefix left right suffix diamond
adjacentSwapSuffixSpike = ?adjacentSwapSuffixSpike_rhs
