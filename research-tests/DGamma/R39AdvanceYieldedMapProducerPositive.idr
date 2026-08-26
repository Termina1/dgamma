module DGamma.R39AdvanceYieldedMapProducerPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R39RelationalMapAlgebraPositive
import Decidable.Equality

%default total

||| L-Advance producer scoping now discharges the landed all-generator theorem.
public export
0 r39LandedAdvanceGeneratorRespects :
  (keyEq : DecEq key) ->
  (generator : TraceEffectGenerator name key world error value actor trace) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (traceGeneratorMap generator) (traceGeneratorMap generator)
r39LandedAdvanceGeneratorRespects = replayTraceGeneratorMapRespects

0 r39EquivalentMapsSymmetric :
  PartialMapsEquivalent (EffectStateEquivalence keyEq) left right ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq) right left
r39EquivalentMapsSymmetric maps input =
  r39EffectPartialSymmetric (maps input)

0 r39EquivalentThenRespectful :
  (source, target : PartialEffectMap name key value world) ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq) source target ->
  EffectPartialMapRespects keyEq target ->
  PartialMapsRelated (EffectStateEquivalence keyEq) source target
r39EquivalentThenRespectful source target sameInput targetRespects
  {x} {y} inputs = r39EffectPartialTransitive (sameInput x)
    (targetRespects x y inputs)

||| Executable successful-forward projection used by an iterator generator.
public export
r39RuntimeForwardProjection :
  Maybe (IteratorStageOutcome name key value world error) ->
  Maybe (EffectState name key value world)
r39RuntimeForwardProjection Nothing = Nothing
r39RuntimeForwardProjection (Just (IteratorRaised failure)) = Nothing
r39RuntimeForwardProjection (Just (IteratorYielded after undo continuation)) =
  Just after

||| Executable yielded-inverse projection. Undefined/failure outcomes generate
||| no inverse and are represented by the everywhere-undefined partial map.
public export
r39RuntimeYieldedProjection :
  Maybe (IteratorStageOutcome name key value world error) ->
  PartialEffectMap name key value world
r39RuntimeYieldedProjection Nothing = \state => Nothing
r39RuntimeYieldedProjection (Just (IteratorRaised failure)) = \state => Nothing
r39RuntimeYieldedProjection
  (Just (IteratorYielded after undo continuation)) = undo

public export
0 r39RuntimeForwardAgreementProjection :
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    targetOutcome sourceOutcome ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (r39RuntimeForwardProjection sourceOutcome)
    (r39RuntimeForwardProjection targetOutcome)
r39RuntimeForwardAgreementProjection RuntimeOutcomesUndefined = PartialUndefined
r39RuntimeForwardAgreementProjection (RuntimeFailuresAgree errorsSame) =
  PartialUndefined
r39RuntimeForwardAgreementProjection
  (RuntimeYieldsAgree afterRelated undoMaps) = PartialDefined afterRelated

||| All runtime L-Advance outcome branches supply the relational forward-map
||| observation.  `RuntimeYieldsAgree` already orients `afterRelated` from the
||| source (second outcome) to the target (first outcome).
public export
0 r39RuntimeAdvanceForwardMapsRelated :
  (sourceOutcome, targetOutcome :
    EffectState name key value world ->
      Maybe (IteratorStageOutcome name key value world error)) ->
  ({sourceInput, targetInput : EffectState name key value world} ->
    EffectStateRelated keyEq sourceInput targetInput ->
    RuntimeIteratorOutcomeAgreement name key value world error keyEq
      (targetOutcome targetInput) (sourceOutcome sourceInput)) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (\state => r39RuntimeForwardProjection (sourceOutcome state))
    (\state => r39RuntimeForwardProjection (targetOutcome state))
r39RuntimeAdvanceForwardMapsRelated sourceOutcome targetOutcome agreement
  inputs = r39RuntimeForwardAgreementProjection (agreement inputs)

||| A yielded local inverse is definitionally the accumulator runtime map, so
||| its strong cross-input respect proof already exists for every callback
||| result.  This is the L-Advance analogue of the L-Unload producer proof.
public export
0 r39YieldedInverseEffectMapRespects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  EffectPartialMapRespects keyEq
    (yieldedInverseEffectMap nameEq keyEq actor provision undo)
r39YieldedInverseEffectMapRespects nameEq keyEq actor provision undo =
  accumulatorRuntimeEffectMapRespects nameEq keyEq actor provision undo

||| Successful yielded outcomes need no exact inverse-function equality.  The
||| existing `PartialMapsEquivalent` field plus target inverse respect upgrades
||| to the strong relational map shape consumed by transformation composition.
public export
0 r39RuntimeAdvanceYieldedMapsRelated :
  (sourceAfter, targetAfter : EffectState name key value world) ->
  (sourceUndo, targetUndo : PartialEffectMap name key value world) ->
  (continuation : IteratorContinuation key value world error) ->
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    (Just (IteratorYielded targetAfter targetUndo continuation))
    (Just (IteratorYielded sourceAfter sourceUndo continuation)) ->
  EffectPartialMapRespects keyEq targetUndo ->
  PartialMapsRelated (EffectStateEquivalence keyEq) sourceUndo targetUndo
r39RuntimeAdvanceYieldedMapsRelated sourceAfter targetAfter sourceUndo targetUndo
  continuation (RuntimeYieldsAgree afterRelated targetToSourceUndo)
  targetRespects = r39EquivalentThenRespectful sourceUndo targetUndo
    (r39EquivalentMapsSymmetric targetToSourceUndo) targetRespects

||| Branch-total projection for the generated yielded map.  Undefined and
||| failure branches are constructively trivial; the successful branch uses
||| the previous theorem.  The respect callback is producer-owned and, for a
||| real iterator stage, is discharged by
||| `r39YieldedInverseEffectMapRespects` at the callback result.
public export
0 r39RuntimeAdvanceYieldedProjectionRelated :
  (sourceOutcome, targetOutcome :
    Maybe (IteratorStageOutcome name key value world error)) ->
  RuntimeIteratorOutcomeAgreement name key value world error keyEq
    targetOutcome sourceOutcome ->
  EffectPartialMapRespects keyEq (r39RuntimeYieldedProjection targetOutcome) ->
  PartialMapsRelated (EffectStateEquivalence keyEq)
    (r39RuntimeYieldedProjection sourceOutcome)
    (r39RuntimeYieldedProjection targetOutcome)
r39RuntimeAdvanceYieldedProjectionRelated Nothing Nothing
  RuntimeOutcomesUndefined targetRespects = \inputs => PartialUndefined
r39RuntimeAdvanceYieldedProjectionRelated
  (Just (IteratorRaised sourceError)) (Just (IteratorRaised targetError))
  (RuntimeFailuresAgree errorsSame) targetRespects = \inputs => PartialUndefined
r39RuntimeAdvanceYieldedProjectionRelated
  (Just (IteratorYielded sourceAfter sourceUndo sourceContinuation))
  (Just (IteratorYielded targetAfter targetUndo sourceContinuation))
  agreement@(RuntimeYieldsAgree afterRelated undoMaps) targetRespects =
    r39RuntimeAdvanceYieldedMapsRelated sourceAfter targetAfter sourceUndo
      targetUndo sourceContinuation agreement targetRespects
