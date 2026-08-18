module DGamma.CP4TerminalRecovery

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Core
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrameUnload
import DGamma.CP4RecoveryModelTrace
import DGamma.CP4RecoveryReplay
import DGamma.CP4RecoveryTrace
import Decidable.Equality

%default total

0 partialRelatedLeftEquation :
  {leftBefore, leftAfter, right : Maybe state} ->
  leftBefore = leftAfter ->
  PartialRelated state rel leftBefore right ->
  PartialRelated state rel leftAfter right
partialRelatedLeftEquation Refl related = related

0 replaceRelatedLeft :
  {name, key, world : Type} -> {value : key -> Type} ->
  {keyEq : DecEq key} ->
  {left, right, final : EffectState name key value world} ->
  left = right -> EffectStateRelated keyEq left final ->
  EffectStateRelated keyEq right final
replaceRelatedLeft Refl related = related

||| The exact runtime accumulator consumed by one checked L-Unload, together
||| with its full-effect result and the relational concrete-target frame.
public export
record ClosingAccumulatorResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkClosingAccumulatorResult
  closingHandle : AccumulatorHandle key value world
  0 closingHandleAt : actualAccumulatorAt @{nameEq} selected before =
    Just closingHandle
  closingRecovered : EffectState name key value world
  0 closingAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    closingHandle (projectEffectState @{nameEq} before) = Just closingRecovered
  0 closingRecoveredRelated : EffectStateRelated keyEq closingRecovered
    (projectEffectState @{nameEq} afterState)

0 closingRawAccumulatorResult :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (raw : applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (LUnloadTag, afterState)) ->
  ActualEffectFrame nameEq keyEq (LUnload selected) LUnloadTag before afterState ->
  ClosingAccumulatorResult name key world error value nameEq keyEq selected
    before afterState
closingRawAccumulatorResult {name} {key} {world} {error} {value}
  nameEq keyEq selected (MkSystemState ambient fibers) afterState raw frame
  with (lookupFiber @{nameEq} selected fibers) proof found
  closingRawAccumulatorResult nameEq keyEq selected
    (MkSystemState ambient fibers) afterState raw frame | Nothing =
      void (nothingIsNotJust raw)
  closingRawAccumulatorResult nameEq keyEq selected
    (MkSystemState ambient fibers) afterState raw frame |
      Just (MkFiber component parent retiredFlag table lifecycle)
    with (fiberLifecycle
      (MkFiber component parent retiredFlag table lifecycle)) proof life
    closingRawAccumulatorResult nameEq keyEq selected
      (MkSystemState ambient fibers) afterState raw frame |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Inactive outcome = void (nothingIsNotJust raw)
    closingRawAccumulatorResult nameEq keyEq selected
      (MkSystemState ambient fibers) afterState raw frame |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Reloading remaining accumulator view = void (nothingIsNotJust raw)
    closingRawAccumulatorResult nameEq keyEq selected
      (MkSystemState ambient fibers) afterState raw frame |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Active accumulator view = void (nothingIsNotJust raw)
    closingRawAccumulatorResult nameEq keyEq selected
      (MkSystemState ambient fibers) afterState raw frame |
        Just (MkFiber component parent retiredFlag table lifecycle) |
          Unloading accumulator view outcome =
      let effectSource : EffectState name key value world
          effectSource = projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState ambient fibers))
          handle : AccumulatorHandle key value world
          handle = MkAccumulatorHandle (componentProvisions component) table
            accumulator
          recovered : EffectState name key value world
          recovered = case accumulatorEffectMap nameEq keyEq selected handle
            effectSource of
              Nothing => effectSource
              Just effect => effect
          0 handleAt : actualAccumulatorAt @{nameEq} selected
            (the (SystemState name key value world error)
              (MkSystemState ambient fibers)) = Just handle
          handleAt = rewrite found in Refl
          0 accumulatorRuns : accumulatorEffectMap nameEq keyEq selected handle
            effectSource = Just recovered
          accumulatorRuns = Refl
          0 mapSame : partialEffectMapFor nameEq keyEq (LUnload selected)
              LUnloadTag
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)) effectSource =
            accumulatorEffectMap nameEq keyEq selected handle effectSource
          mapSame = rewrite found in
            rewrite projectedActorTable nameEq selected
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers))
              (MkFiber component parent retiredFlag table
                (Unloading accumulator view outcome)) found in Refl
          0 partialRuns : partialEffectMapFor nameEq keyEq (LUnload selected)
              LUnloadTag
              (the (SystemState name key value world error)
                (MkSystemState ambient fibers)) effectSource = Just recovered
          partialRuns = trans mapSame accumulatorRuns
          0 recoveredRelated : EffectStateRelated keyEq recovered
            (projectEffectState @{nameEq} afterState)
          recoveredRelated = case frame of
            MkActualEffectFrame related =>
              case partialRelatedLeftEquation partialRuns related of
                PartialDefined outputRelated => outputRelated
      in MkClosingAccumulatorResult handle handleAt recovered accumulatorRuns
        recoveredRelated

||| Extract the handle/result used by L-Unload itself.  The actual-effect frame
||| avoids any function-extensional equality between projected table functions.
public export
0 closingStepAccumulatorResult :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  UnloadStep nameEq keyEq selected before afterState ->
  ClosingAccumulatorResult name key world error value nameEq keyEq selected
    before afterState
closingStepAccumulatorResult nameEq keyEq selected before afterState closing =
  let 0 raw = checkedActionProjects nameEq keyEq (LUnload selected) before
        afterState LUnloadTag (unloadEquation closing)
      0 frame = unloadActualEffectFrame nameEq keyEq selected before afterState
        LUnloadTag raw
  in closingRawAccumulatorResult nameEq keyEq selected before afterState raw frame

||| Every occurrence in a left prefix remains an occurrence after appending a
||| suffix.  Corollary 62 uses it to run the Theorem-61 simultaneous induction
||| on `closedInside` while retaining the closing step in the whole monoid.
public export
0 appendLeftOccurrenceEmbedding :
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  OccurrenceEmbedding left (appendTransitions left right)
appendLeftOccurrenceEmbedding NoTransitions right transition occurs impossible
appendLeftOccurrenceEmbedding (MoreTransitions transition rest) right
  transition OccursHere = OccursHere
appendLeftOccurrenceEmbedding (MoreTransitions head rest) right transition
  (OccursLater later) = OccursLater
    (appendLeftOccurrenceEmbedding rest right transition later)

||| Append one selected-actor step to a foreign replay.  The step is skipped;
||| its concrete recovery relation is composed only at the empty tail.
public export
0 appendOwnReplay :
  (selected : name) ->
  (left : Transitions first middle) ->
  (own : Transition middle finalState) ->
  transitionActor own = selected ->
  ForeignReplay name key world error value keyEq selected left initial recovered ->
  EffectStateRelated keyEq recovered final ->
  ForeignReplay name key world error value keyEq selected
    (appendTransitions left (MoreTransitions own NoTransitions)) initial final
appendOwnReplay selected NoTransitions own ownActor
  (ReplayDone initialToRecovered) recoveredToFinal =
    ReplayOwn own ownActor (ReplayDone
      (transitive (EffectStateEquivalence keyEq) initialToRecovered
        recoveredToFinal))
appendOwnReplay selected (MoreTransitions head rest) own ownActor
  (ReplayOwn head actor tail) recoveredToFinal =
    ReplayOwn head actor
      (appendOwnReplay selected rest own ownActor tail recoveredToFinal)
appendOwnReplay selected (MoreTransitions head rest) own ownActor
  (ReplayForeign head actor runs tail) recoveredToFinal =
    ReplayForeign head actor runs
      (appendOwnReplay selected rest own ownActor tail recoveredToFinal)

0 unloadTransitionActor :
  (closing : UnloadStep nameEq keyEq selected before afterState) ->
  transitionActor (unloadTransition closing) = selected
unloadTransitionActor closing = Refl

||| Constructive Corollary 62.  Theorem 61's simultaneous accumulator/replay
||| induction is run on the installed body with the complete closed trace as its
||| generator universe; the checked L-Unload exposes the same final handle and
||| relates its concrete target to that recovered effect state.
public export
0 terminalRecoveryTheoremProof :
  terminalRecoveryTheorem name key value world error
terminalRecoveryTheoremProof nameEq keyEq selected pre afterState episode
  independent =
    let closingTrace : Transitions (lastInstalledState episode) afterState
        closingTrace = MoreTransitions (unloadTransition (closing episode))
          NoTransitions
        whole : Transitions (closedStartState episode) afterState
        whole = closedTransitions episode
        initialModel : AccumulatorModel name key world error value nameEq keyEq
          selected whole (closedStartState episode)
        initialModel = beginAccumulatorModel nameEq keyEq selected whole
          (closedOpening episode)
        segmentResult : AccumulatorReplaySegment name key world error value
          nameEq keyEq selected (closedInside episode) whole initialModel
        segmentResult = accumulatorReplayAlongSegment nameEq keyEq selected whole
          (closedInside episode)
          (appendLeftOccurrenceEmbedding (closedInside episode) closingTrace)
          (closedInsideInstalled episode) independent initialModel
        0 beginRelated : EffectStateRelated keyEq
          (projectEffectState @{nameEq} (closedStartState episode))
          (sourceRecovered segmentResult)
        beginRelated = beginAccumulatorRecovery nameEq keyEq selected whole
          (closedOpening episode) (sourceRecovered segmentResult)
          (sourceRuns segmentResult)
        0 replayedFromStart : ForeignReplay name key world error value keyEq
          selected (closedInside episode)
          (projectEffectState @{nameEq} (closedStartState episode))
          (finalRecovered segmentResult)
        replayedFromStart = foreignReplayInitialRelated nameEq keyEq selected
          (closedInside episode) (closedInsideInstalled episode)
          (projectEffectState @{nameEq} (closedStartState episode))
          (sourceRecovered segmentResult) (finalRecovered segmentResult)
          beginRelated (replay segmentResult)
        closingResult : ClosingAccumulatorResult name key world error value
          nameEq keyEq selected (lastInstalledState episode) afterState
        closingResult = closingStepAccumulatorResult nameEq keyEq selected
          (lastInstalledState episode) afterState (closing episode)
        0 handleSame : closingHandle closingResult =
          modelHandle (finalModel segmentResult)
        handleSame = justInjective (trans (sym (closingHandleAt closingResult))
          (modelHandleAt (finalModel segmentResult)))
        0 closingRunsWithModel : accumulatorEffectMap nameEq keyEq selected
            (modelHandle (finalModel segmentResult))
            (projectEffectState @{nameEq} (lastInstalledState episode)) =
          Just (closingRecovered closingResult)
        closingRunsWithModel = replace
          {p = \handle => accumulatorEffectMap nameEq keyEq selected handle
            (projectEffectState @{nameEq} (lastInstalledState episode)) =
              Just (closingRecovered closingResult)}
          handleSame (closingAccumulatorRuns closingResult)
        0 recoveredSame : closingRecovered closingResult =
          finalRecovered segmentResult
        recoveredSame = justInjective (trans (sym closingRunsWithModel)
          (finalRuns segmentResult))
        0 segmentFinalRelated : EffectStateRelated keyEq
          (finalRecovered segmentResult) (projectEffectState @{nameEq} afterState)
        segmentFinalRelated = replaceRelatedLeft recoveredSame
          (closingRecoveredRelated closingResult)
    in appendOwnReplay selected (closedInside episode)
      (unloadTransition (closing episode))
      (unloadTransitionActor (closing episode)) replayedFromStart
      segmentFinalRelated
