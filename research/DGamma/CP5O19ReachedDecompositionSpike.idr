module DGamma.CP5O19ReachedDecompositionSpike

import DGamma.CP5O19ReachedBlocksSpike
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19ActualCartesianSpike
import DGamma.CP5O19GridCertificationSpike
import DGamma.CP5O19WholeBlockSpike
import DGamma.CP5O19CartesianLengthSpike
import DGamma.CP5O19PaperBranchCompletenessSpike
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19SameChainAssemblySpike
import Data.List
import Data.List.Elem
import Data.List.HasLength as HL
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Ordered half-open numeric ranges cannot share a position. The upper
||| boundary is supplied by genuine BlockBefore in the next lemma.
export
0 o19OrderedRangeSeparation :
  (earlyStart, earlySize, lateStart, earlyPosition, latePosition : Nat) ->
  LTE (earlyStart + earlySize) lateStart ->
  LTE (S earlyPosition) earlySize ->
  Not ((earlyStart + earlyPosition) = (lateStart + latePosition))
o19OrderedRangeSeparation earlyStart earlySize lateStart earlyPosition latePosition ordered bounded exact =
  succNotLTEpred
    (replace {p = LTE (S (earlyStart + earlyPosition))} (sym exact)
      (transitive
        (replace {p = \count => LTE count (earlyStart + earlySize)}
          (sym (plusSuccRightSucc earlyStart earlyPosition))
          (plusLteMonotoneLeft earlyStart (S earlyPosition) earlySize bounded))
        (transitive ordered (lteAddRight lateStart))))

||| Genuine same-trace BlockBefore entails disjoint selected transition
||| ranges. No caller-supplied numeric boundary or injectivity assumption.
export
0 o19OrderedBlockRangesDisjoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {early, late : name} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (earlyBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq early trace) ->
  (lateBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq late trace) ->
  BlockBefore name key world error value nameEq keyEq trace early late earlyBlock lateBlock ->
  (earlyPosition, latePosition : Nat) ->
  LTE (S earlyPosition) (S (transitionCount (blockBody earlyBlock))) ->
  LTE (S latePosition) (S (transitionCount (blockBody lateBlock))) ->
  Not ((transitionCount (traceBeforeBlock earlyBlock) + earlyPosition) =
    (transitionCount (traceBeforeBlock lateBlock) + latePosition))
o19OrderedBlockRangesDisjoint trace earlyBlock lateBlock ordered earlyPosition latePosition earlyBound lateBound =
  o19OrderedRangeSeparation (transitionCount (traceBeforeBlock earlyBlock))
    (S (transitionCount (blockBody earlyBlock))) (transitionCount (traceBeforeBlock lateBlock))
    earlyPosition latePosition
    (replace {p = \count => LTE count (transitionCount (traceBeforeBlock lateBlock))}
      (o19PrefixThroughCount earlyBlock) (o19OrderedBoundaryLTE trace earlyBlock lateBlock ordered)) earlyBound

||| Observe lifecycle coverage at an actual dependent cut, retaining the
||| selected Transition rather than looking up an action label in a word.
export
0 o19LifecycleCoveredAtCut :
  {name, key, world, error : Type} -> {value : key -> Type} -> {order : List name} ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (earlier : Transitions initial before) -> (selected : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  LifecycleActorsCovered order (appendTransitions earlier (MoreTransitions selected later)) ->
  (isLifecycleAction (transitionAction selected) = True) -> Elem (transitionActor selected) order
o19LifecycleCoveredAtCut NoTransitions selected later (CoveredLifecycleStep _ _ lifecycle member rest) observed = member
o19LifecycleCoveredAtCut NoTransitions selected later (CoveredOrchestrationStep _ _ orchestration rest) observed =
  void (uninhabited (trans (sym orchestration) observed))
o19LifecycleCoveredAtCut (MoreTransitions head tail) selected later (CoveredLifecycleStep _ _ lifecycle member rest) observed =
  o19LifecycleCoveredAtCut tail selected later rest observed
o19LifecycleCoveredAtCut (MoreTransitions head tail) selected later (CoveredOrchestrationStep _ _ orchestration rest) observed =
  o19LifecycleCoveredAtCut tail selected later rest observed

||| Genuine LocatedActionOccurrence observation: recover actor membership
||| through the OWN exact trace decomposition and OWN action equation.
export
0 o19LocatedLifecycleCovered :
  {name, key, world, error : Type} -> {value : key -> Type} -> {order : List name} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> LifecycleActorsCovered order trace ->
  (action : Action name key value world error) -> LocatedActionOccurrence action trace ->
  (isLifecycleAction action = True) -> Elem (actionOwner action) order
o19LocatedLifecycleCovered trace covered action (MkLocatedActionOccurrence before afterState earlier selected later actionExact decomposition) lifecycle =
  replace {p = \actor => Elem actor order}
    (trans (o19TransitionActorOwner selected) (cong actionOwner actionExact))
    (o19LifecycleCoveredAtCut earlier selected later
      (replace {p = LifecycleActorsCovered order} (sym decomposition) covered)
      (trans (cong isLifecycleAction actionExact) lifecycle))
