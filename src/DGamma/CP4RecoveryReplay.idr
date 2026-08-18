module DGamma.CP4RecoveryReplay

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RecoveryForeignCommute
import DGamma.CP4RecoveryModelTrace
import DGamma.CP4RecoverySelectedReplayStep
import DGamma.CP4RecoveryTrace
import DGamma.Unified
import Decidable.Equality

%default total

0 partialNothingJustImpossible :
  PartialRelated state rel Nothing (Just right) -> Void
partialNothingJustImpossible relation impossible

0 partialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewrite Refl Refl related = related

replayAccumulatorResult :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  AccumulatorHandle key value world -> EffectState name key value world ->
  EffectState name key value world
replayAccumulatorResult nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator) state =
    let restored = accumulator
          (MkLocalState (effectAmbient state)
            (restrictOwnedPreservingOrder provision
              (effectTables state selected)))
    in setEffectTable @{nameEq} selected (ownedValues (localTable restored))
      (setEffectAmbient (localWorld restored) state)

0 replayAccumulatorResultRuns :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (handle : AccumulatorHandle key value world) ->
  (state : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected handle state =
    Just (replayAccumulatorResult nameEq keyEq selected handle state)
replayAccumulatorResultRuns nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator)
  (MkEffectState ambient tables) = Refl

||| Foreign replay is congruent in its initial effect state. Every foreign map
||| respects Finding-#10 ordered equality; own steps skip the state unchanged.
public export
0 foreignReplayInitialRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first last) ->
  InstalledTrace name key world error value nameEq keyEq selected trace ->
  (left, right, final : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  ForeignReplay name key world error value keyEq selected trace right final ->
  ForeignReplay name key world error value keyEq selected trace left final
foreignReplayInitialRelated nameEq keyEq selected NoTransitions
  (InstalledEnd installed) left right final leftToRight
  (ReplayDone rightToFinal) = ReplayDone
    (transitive (EffectStateEquivalence keyEq) leftToRight rightToFinal)
foreignReplayInitialRelated nameEq keyEq selected
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  left right final leftToRight (ReplayOwn _ owner tail) = ReplayOwn (Fired nameEq keyEq action tag checked) owner
    (foreignReplayInitialRelated nameEq keyEq selected rest tailInstalled left right
      final leftToRight tail)
foreignReplayInitialRelated nameEq keyEq selected
  (MoreTransitions
    (Fired {before} {afterState} nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  left right final leftToRight (ReplayForeign {nextEffect = rightNext} _ foreign rightRuns tail)
  with (partialEffectMap (Fired nameEq keyEq action tag checked) left) proof leftResult
  foreignReplayInitialRelated nameEq keyEq selected
    (MoreTransitions
      (Fired {before} {afterState} nameEq keyEq action tag checked) rest)
    (InstalledStep action tag checked rest sourceInstalled tailInstalled)
    left right final leftToRight
    (ReplayForeign {nextEffect = rightNext} _ foreign rightRuns tail) | Nothing =
      let 0 respected = partialEffectMapRespects nameEq keyEq
            action tag before afterState checked left right leftToRight
      in case partialRelatedRewrite leftResult rightRuns respected of
        _ impossible
  foreignReplayInitialRelated nameEq keyEq selected
    (MoreTransitions
      (Fired {before} {afterState} nameEq keyEq action tag checked) rest)
    (InstalledStep action tag checked rest sourceInstalled tailInstalled)
    left right final leftToRight
    (ReplayForeign {nextEffect = rightNext} _ foreign rightRuns tail) | Just leftNext =
      let 0 respected = partialEffectMapRespects nameEq keyEq
            action tag before afterState checked left right leftToRight
          0 outputsRelated : EffectStateRelated keyEq leftNext rightNext
          outputsRelated = case partialRelatedRewrite leftResult rightRuns
            respected of PartialDefined relation => relation
          0 nextTail : ForeignReplay name key world error value keyEq selected
            rest leftNext final
          nextTail = foreignReplayInitialRelated nameEq keyEq selected rest
            tailInstalled leftNext rightNext final outputsRelated tail
      in ReplayForeign (Fired nameEq keyEq action tag checked) foreign leftResult nextTail

public export
record AccumulatorReplaySegment
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, last : SystemState name key value world error}
  (segment : Transitions first last)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (sourceModel : AccumulatorModel name key world error value nameEq keyEq selected
    whole first) where
  constructor MkAccumulatorReplaySegment
  finalModel : AccumulatorModel name key world error value nameEq keyEq selected
    whole last
  0 sourceRecovered : EffectState name key value world
  0 finalRecovered : EffectState name key value world
  0 sourceRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle sourceModel) (projectEffectState @{nameEq} first) =
    Just sourceRecovered
  0 finalRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle finalModel) (projectEffectState @{nameEq} last) =
    Just finalRecovered
  0 replay : ForeignReplay name key world error value keyEq selected segment
    sourceRecovered finalRecovered

0 transitionActorFired :
  {before, afterState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  transitionActor (Fired {before = before} {afterState = afterState}
    nameEq keyEq action tag checked) = actionOwner action
transitionActorFired nameEq keyEq (OInsert actor parent component) tag checked =
  Refl
transitionActorFired nameEq keyEq (ORetire actor) tag checked = Refl
transitionActorFired nameEq keyEq (ORemove actor) tag checked = Refl
transitionActorFired nameEq keyEq (LBegin actor) tag checked = Refl
transitionActorFired nameEq keyEq (LAdvance actor) tag checked = Refl
transitionActorFired nameEq keyEq (LDivert actor) tag checked = Refl
transitionActorFired nameEq keyEq (LLeave actor) tag checked = Refl
transitionActorFired nameEq keyEq (LUnload actor) tag checked = Refl

0 replaceReplayInitial : left = right ->
  ForeignReplay name key world error value keyEq selected trace left final ->
  ForeignReplay name key world error value keyEq selected trace right final
replaceReplayInitial Refl replay = replay

public export
0 beginAccumulatorRecovery :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {preStart, start : SystemState name key value world error} ->
  (whole : Transitions start wholeLast) ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  (restored : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected
    (modelHandle (beginAccumulatorModel nameEq keyEq selected whole opening))
    (projectEffectState @{nameEq} start) = Just restored ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} start) restored
beginAccumulatorRecovery nameEq keyEq selected {start} whole opening restored
  equation =
    let model = beginAccumulatorModel nameEq keyEq selected whole opening
        0 tableAt = projectedActorTable nameEq selected start (modelFiber model)
          (modelFound model)
        0 normalizerRuns : (actorNormalizationMap nameEq keyEq selected (componentProvisions (fiberComponent (modelFiber model)))
          (projectEffectState @{nameEq} start) = Just restored)
        normalizerRuns = trans
          (sym (beginAccumulatorModelMapIsNormalizer nameEq keyEq selected whole
            opening (projectEffectState @{nameEq} start))) equation
        0 normalizedIsRestored :
          (setEffectTable @{nameEq} selected
            (ownedValues (restrictOwnedPreservingOrder (componentProvisions (fiberComponent (modelFiber model)))
              (effectTables (projectEffectState @{nameEq} start) selected)))
            (projectEffectState @{nameEq} start) = restored)
        normalizedIsRestored = justInjective normalizerRuns
    in case actorNormalizationAtOwnedTable nameEq keyEq selected (componentProvisions (fiberComponent (modelFiber model)))
      (fiberTable (modelFiber model)) (projectEffectState @{nameEq} start)
      tableAt of
      PartialDefined normalizedToStart => replace
        {p = \observed => EffectStateRelated keyEq
          (projectEffectState @{nameEq} start) observed}
        normalizedIsRestored
        (symmetric (EffectStateEquivalence keyEq) normalizedToStart)

0 replaceReplayFinal : left = right ->
  ForeignReplay name key world error value keyEq selected trace initial left ->
  ForeignReplay name key world error value keyEq selected trace initial right
replaceReplayFinal Refl replay = replay

||| Simultaneous temporal induction: carry the exact accumulator model and the
||| foreign-only replay equation through every installed episode boundary.
public export
0 accumulatorReplayAlongSegment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (segment : Transitions first last) ->
  OccurrenceEmbedding segment whole ->
  InstalledTrace name key world error value nameEq keyEq selected segment ->
  TraceIndependent name key world error value keyEq whole ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    first) ->
  AccumulatorReplaySegment name key world error value nameEq keyEq selected
    segment whole model
accumulatorReplayAlongSegment nameEq keyEq selected whole NoTransitions embedding
  (InstalledEnd installed) independent model =
    let 0 runs : (accumulatorEffectMap nameEq keyEq selected (modelHandle model)
          (projectEffectState @{nameEq} first) =
        Just (replayAccumulatorResult nameEq keyEq selected (modelHandle model)
          (projectEffectState @{nameEq} first)))
        runs = replayAccumulatorResultRuns nameEq keyEq selected
          (modelHandle model) (projectEffectState @{nameEq} first)
    in MkAccumulatorReplaySegment model
      (replayAccumulatorResult nameEq keyEq selected (modelHandle model)
        (projectEffectState @{nameEq} first))
      (replayAccumulatorResult nameEq keyEq selected (modelHandle model)
        (projectEffectState @{nameEq} first))
      runs runs (ReplayDone (effectStateReflexive keyEq
        (replayAccumulatorResult nameEq keyEq selected (modelHandle model)
          (projectEffectState @{nameEq} first))))
accumulatorReplayAlongSegment nameEq keyEq selected whole
  segment@(MoreTransitions {middle}
    (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest)
  embedding (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  independent model
  with (decEq @{nameEq} selected (actionOwner action))
  accumulatorReplayAlongSegment nameEq keyEq selected whole
    segment@(MoreTransitions {middle}
      (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest)
    embedding (InstalledStep action tag checked rest sourceInstalled tailInstalled)
    independent model | No distinct =
      let 0 headOccurs = embedding (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) OccursHere
          step = foreignAccumulatorStep nameEq keyEq selected action tag _ _
            checked distinct whole headOccurs independent model
          tailEmbedding = tailOccurrenceEmbedding (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest whole embedding
          tail = accumulatorReplayAlongSegment nameEq keyEq selected whole rest
            tailEmbedding tailInstalled independent
            (foreignStepPreservesAccumulatorModel nameEq keyEq selected action tag
              _ _ whole checked distinct model)
          0 targetMapSame = foreignStepPreservesAccumulatorMap nameEq keyEq
            selected action tag _ _ whole checked distinct model
            (projectEffectState @{nameEq} middle)
          0 tailRunsWithSource : (accumulatorEffectMap nameEq keyEq selected
              (modelHandle model) (projectEffectState @{nameEq} middle) =
            Just (sourceRecovered tail))
          tailRunsWithSource = trans (sym targetMapSame) (sourceRuns tail)
          0 targetSame :
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered step =
             sourceRecovered tail)
          targetSame = justInjective (trans
            (sym (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetAccumulatorRuns step))
            tailRunsWithSource)
          0 tailAtTarget : ForeignReplay name key world error value keyEq selected
            rest
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered step)
            (finalRecovered tail)
          tailAtTarget = replaceReplayInitial (sym targetSame) (replay tail)
          0 foreignToTarget : EffectStateRelated keyEq
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.foreignRecovered step)
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered step)
          foreignToTarget = symmetric (EffectStateEquivalence keyEq)
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecoveredRelated step)
          0 tailAtForeign : ForeignReplay name key world error value keyEq selected
            rest
            (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.foreignRecovered step)
            (finalRecovered tail)
          tailAtForeign = foreignReplayInitialRelated nameEq keyEq selected rest
            tailInstalled (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.foreignRecovered step) (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.targetRecovered step)
            (finalRecovered tail)
            foreignToTarget tailAtTarget
          0 actorAtHead : transitionActor
            (Fired {before = first} {afterState = middle} nameEq keyEq action tag
              checked) = actionOwner action
          actorAtHead = transitionActorFired nameEq keyEq action tag checked
          0 transitionForeign : Not (transitionActor
            (Fired {before = first} {afterState = middle} nameEq keyEq action tag
              checked) = selected)
          transitionForeign actorIsSelected = distinct
            (trans (sym actorIsSelected) actorAtHead)
      in MkAccumulatorReplaySegment (finalModel tail) (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceRecovered step)
        (finalRecovered tail) (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.sourceAccumulatorRuns step) (finalRuns tail)
        (ReplayForeign (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) transitionForeign (DGamma.CP4RecoveryForeignCommute.ForeignAccumulatorStep.foreignRecoveredRuns step)
          tailAtForeign)
  accumulatorReplayAlongSegment nameEq keyEq selected whole
    segment@(MoreTransitions {middle}
      (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest)
    embedding (InstalledStep action tag checked rest sourceInstalled tailInstalled)
    independent model | Yes same =
      let 0 headOccurs = embedding (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) OccursHere
          0 targetInstalled = installedTraceStartEvidence rest tailInstalled
          step = selectedInstalledAccumulatorStep nameEq keyEq selected action tag
            _ _ checked (sym same) whole headOccurs targetInstalled model
          tailEmbedding = tailOccurrenceEmbedding (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest whole embedding
          tail = accumulatorReplayAlongSegment nameEq keyEq selected whole rest
            tailEmbedding tailInstalled independent (targetModel step)
          0 targetSame : (targetRecovered step = sourceRecovered tail)
          targetSame = justInjective (trans (sym (targetAccumulatorRuns step))
            (sourceRuns tail))
          0 tailAtTarget : ForeignReplay name key world error value keyEq selected
            rest (targetRecovered step) (finalRecovered tail)
          tailAtTarget = replaceReplayInitial (sym targetSame) (replay tail)
          0 tailAtSource : ForeignReplay name key world error value keyEq selected
            rest (sourceRecovered step) (finalRecovered tail)
          tailAtSource = foreignReplayInitialRelated nameEq keyEq selected rest
            tailInstalled (sourceRecovered step) (targetRecovered step)
            (finalRecovered tail)
            (recoveredRelated step) tailAtTarget
          0 actorAtHead : transitionActor
            (Fired {before = first} {afterState = middle} nameEq keyEq action tag
              checked) = actionOwner action
          actorAtHead = transitionActorFired nameEq keyEq action tag checked
          0 transitionOwn : transitionActor
            (Fired {before = first} {afterState = middle} nameEq keyEq action tag
              checked) = selected
          transitionOwn = trans actorAtHead (sym same)
      in MkAccumulatorReplaySegment (finalModel tail) (sourceRecovered step)
        (finalRecovered tail) (sourceAccumulatorRuns step) (finalRuns tail)
        (ReplayOwn (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) transitionOwn tailAtSource)

||| Complete constructive paper-Theorem-61 proof for an installed episode
||| prefix. The simultaneous induction above composes selected recovery and
||| foreign commutation; the opening identity accumulator and final public
||| handle equations close the two endpoints.
public export
0 recoveryExactnessTheoremProof :
  recoveryExactnessTheorem name key value world error
recoveryExactnessTheoremProof nameEq keyEq selected pre current episode handle
  handleAt independent restored restoredRuns =
    let 0 segmentResult : AccumulatorReplaySegment name key world error value
          nameEq keyEq selected (inside episode) (inside episode)
          (beginAccumulatorModel nameEq keyEq selected (inside episode)
            (opening episode))
        segmentResult = accumulatorReplayAlongSegment nameEq keyEq selected
          (inside episode) (inside episode)
          (identityOccurrenceEmbedding (inside episode)) (insideInstalled episode)
          independent (beginAccumulatorModel nameEq keyEq selected
            (inside episode) (opening episode))
        0 beginRelated : EffectStateRelated keyEq
          (projectEffectState @{nameEq} (episodeStartState episode))
          (sourceRecovered segmentResult)
        beginRelated = beginAccumulatorRecovery nameEq keyEq selected
          (inside episode) (opening episode) (sourceRecovered segmentResult)
          (sourceRuns segmentResult)
        0 replayedFromStart : ForeignReplay name key world error value keyEq
          selected (inside episode)
          (projectEffectState @{nameEq} (episodeStartState episode))
          (finalRecovered segmentResult)
        replayedFromStart = foreignReplayInitialRelated nameEq keyEq selected
          (inside episode) (insideInstalled episode)
          (projectEffectState @{nameEq} (episodeStartState episode))
          (sourceRecovered segmentResult) (finalRecovered segmentResult)
          beginRelated (replay segmentResult)
        0 handleSame : handle = modelHandle (finalModel segmentResult)
        handleSame = justInjective (trans (sym handleAt)
          (modelHandleAt (finalModel segmentResult)))
        0 restoredWithModel : (accumulatorEffectMap nameEq keyEq selected
          (modelHandle (finalModel segmentResult))
          (projectEffectState @{nameEq} current) = Just restored)
        restoredWithModel = replace
          {p = \observed => accumulatorEffectMap nameEq keyEq selected observed
            (projectEffectState @{nameEq} current) = Just restored}
          handleSame restoredRuns
        0 restoredIsFinal : restored = finalRecovered segmentResult
        restoredIsFinal = justInjective (trans (sym restoredWithModel)
          (finalRuns segmentResult))
    in replaceReplayFinal (sym restoredIsFinal) replayedFromStart
