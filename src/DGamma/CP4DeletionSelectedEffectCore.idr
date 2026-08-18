module DGamma.CP4DeletionSelectedEffectCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameBegin
import DGamma.CP4DeletionFrameCore
import DGamma.CP4RecoveryReplay
import DGamma.CP4RecoverySelectedReplayStep
import DGamma.CP4RecoveryTrace
import DGamma.Unified
import Decidable.Equality

%default total

||| Effect half of the selected-episode quotient at one installed boundary.
||| The original state still contains the selected activation; applying its
||| concrete accumulated inverse yields the effect state observed by the replay
||| that omitted selected lifecycle steps.  Control/registry deletion is kept in
||| a separate boundary layer so this relation can reuse Theorem 61 verbatim.
public export
record SelectedEffectReplayBoundary
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (original, survivor : SystemState name key value world error) where
  constructor MkSelectedEffectReplayBoundary
  0 selectedBoundaryModel : AccumulatorModel name key world error value nameEq
    keyEq selected whole original
  0 selectedBoundaryRecovered : EffectState name key value world
  0 selectedBoundaryRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle selectedBoundaryModel) (projectEffectState @{nameEq} original) =
    Just selectedBoundaryRecovered
  0 survivorMatchesRecovered : EffectStateRelated keyEq
    (projectEffectState @{nameEq} survivor) selectedBoundaryRecovered

0 accumulatorRunResult :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (handle : AccumulatorHandle key value world) ->
  (state : EffectState name key value world) ->
  (recovered : EffectState name key value world **
    accumulatorEffectMap nameEq keyEq selected handle state = Just recovered)
accumulatorRunResult nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator)
  state@(MkEffectState ambient tables) =
    (setEffectTable @{nameEq} selected
      (ownedValues (localTable (accumulator
        (MkLocalState ambient
          (restrictOwnedPreservingOrder provision (tables selected))))))
      (setEffectAmbient (localWorld (accumulator
        (MkLocalState ambient
          (restrictOwnedPreservingOrder provision (tables selected))))) state) **
      Refl)

0 beginProjectsSameEffects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {preStart, start : SystemState name key value world error} ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} preStart)
    (projectEffectState @{nameEq} start)
beginProjectsSameEffects nameEq keyEq selected {preStart} {start} opening =
  let 0 raw = checkedActionProjects nameEq keyEq (LBegin selected) preStart start
        LBeginTag (beginEquation opening)
  in case beginActualEffectFrame nameEq keyEq selected preStart start LBeginTag
    raw of
    MkActualEffectFrame (PartialDefined related) => related

||| L-Begin is the left boundary of the quotient.  It changes no effect field,
||| and the identity accumulator established by the checked opening normalizes
||| exactly the selected table already stored by the evaluator.
public export
0 beginSelectedEffectReplayBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {preStart, start : SystemState name key value world error} ->
  (whole : Transitions start wholeLast) ->
  (opening : BeginStep nameEq keyEq selected preStart start) ->
  SelectedEffectReplayBoundary name key world error value nameEq keyEq selected
    whole start preStart
beginSelectedEffectReplayBoundary nameEq keyEq selected {preStart} {start} whole
  opening =
    case accumulatorRunResult nameEq keyEq selected
      (modelHandle (beginAccumulatorModel nameEq keyEq selected whole opening))
      (projectEffectState @{nameEq} start) of
      (recovered ** runs) =>
        let 0 startToRecovered = beginAccumulatorRecovery nameEq keyEq selected
              whole opening recovered runs
            0 preToStart = beginProjectsSameEffects nameEq keyEq selected opening
            0 preToRecovered = transitive (EffectStateEquivalence keyEq)
              preToStart startToRecovered
        in MkSelectedEffectReplayBoundary
          (beginAccumulatorModel nameEq keyEq selected whole opening)
          recovered runs preToRecovered

||| Any selected installed step whose survivor is intentionally left fixed
||| preserves the effect quotient.  This is the direct per-boundary consumer of
||| the selected retirement/advance/divert/leave recovery proofs; the caller
||| separately establishes that the step is one of the lifecycle actions erased
||| by Lemma 72.
public export
0 selectedStepPreservesEffectReplayBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {before, afterState, survivor : SystemState name key value world error} ->
  (transition : Transition before afterState) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (boundary : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole before survivor) ->
  (step : SelectedAccumulatorStep name key world error value nameEq keyEq
    selected transition whole (selectedBoundaryModel boundary)) ->
  SelectedEffectReplayBoundary name key world error value nameEq keyEq selected
    whole afterState survivor
selectedStepPreservesEffectReplayBoundary nameEq keyEq selected transition whole
  (MkSelectedEffectReplayBoundary model boundaryRecovered boundaryRuns
    survivorToBoundary)
  (MkSelectedAccumulatorStep target sourceRecoveredValue targetRecoveredValue
    sourceRuns targetRuns sourceToTarget) =
    let 0 sourceSame = justInjective (trans (sym boundaryRuns) sourceRuns)
        0 survivorToSource : EffectStateRelated keyEq
          (projectEffectState @{nameEq} survivor) sourceRecoveredValue
        survivorToSource = replace
          {p = \observed => EffectStateRelated keyEq
            (projectEffectState @{nameEq} survivor) observed}
          sourceSame survivorToBoundary
        0 survivorToTarget : EffectStateRelated keyEq
          (projectEffectState @{nameEq} survivor) targetRecoveredValue
        survivorToTarget = transitive (EffectStateEquivalence keyEq)
          survivorToSource sourceToTarget
    in MkSelectedEffectReplayBoundary target targetRecoveredValue targetRuns
      survivorToTarget
