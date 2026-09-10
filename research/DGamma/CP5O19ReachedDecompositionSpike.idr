module DGamma.CP5O19ReachedDecompositionSpike

import DGamma.CP5O19ReachedBlocksSpike
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
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

||| Typed Boolean boundary for one actual reached head. An explicit observed
||| Bool and equation avoid lazy conditional reduction over a replay builder.
export
0 o19CoveredHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} -> {order : List name} ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (head : Transition initial middle) -> (tail : Transitions middle finalState) ->
  LifecycleActorsCovered order tail -> (observed : Bool) ->
  (isLifecycleAction (transitionAction head) = observed) ->
  ((isLifecycleAction (transitionAction head) = True) -> Elem (actionOwner (transitionAction head)) order) ->
  LifecycleActorsCovered order (MoreTransitions head tail)
o19CoveredHeadObserved head tail covered True observed membership =
  CoveredLifecycleStep head tail observed
    (replace {p = \actor => Elem actor order} (sym (o19TransitionActorOwner head)) (membership observed)) covered
o19CoveredHeadObserved head tail covered False observed membership = CoveredOrchestrationStep head tail observed covered

||| Structural target coverage through genuine located-action origins.
||| The enumeration transport is separate from occurrence correspondence.
export
0 o19LifecycleCoverageFromOrigins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {sourceOrder, targetOrder : List name} ->
  {sourceFirst, sourceLast, targetFirst, targetLast : SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceLast) -> (target : Transitions targetFirst targetLast) ->
  ({action : Action name key value world error} -> LocatedActionOccurrence action target -> LocatedActionOccurrence action source) ->
  ((selected : name) -> Elem selected sourceOrder -> Elem selected targetOrder) ->
  LifecycleActorsCovered sourceOrder source -> LifecycleActorsCovered targetOrder target
o19LifecycleCoverageFromOrigins source NoTransitions origins membership covered = LifecycleActorsCoveredEnd
o19LifecycleCoverageFromOrigins {targetFirst} source (MoreTransitions {middle} head tail) origins membership covered =
  o19CoveredHeadObserved head tail
    (o19LifecycleCoverageFromOrigins source tail
      (\occurrence => origins (MkLocatedActionOccurrence (actionBeforeState occurrence) (actionAfterState occurrence)
        (MoreTransitions head (beforeActionOccurrence occurrence)) (locatedTransition occurrence) (afterActionOccurrence occurrence)
        (locatedAction occurrence) (cong (MoreTransitions head) (actionOccurrenceDecomposition occurrence)))) membership covered)
    (isLifecycleAction (transitionAction head)) Refl
    (\lifecycle => membership (actionOwner (transitionAction head))
      (o19LocatedLifecycleCovered source covered (transitionAction head)
        (origins (MkLocatedActionOccurrence targetFirst middle NoTransitions head tail Refl Refl)) lifecycle))

||| Source-to-target actor enumeration membership for the exact order swap.
||| This list fact is not used as a substitute for trace occurrence origins.
export
0 o19SwapActorMembership :
  {name : Type} -> {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  (selected : name) -> Elem selected sourceOrder -> Elem selected targetOrder
o19SwapActorMembership swap selected member =
  replace {p = Elem selected} (sym (actorAfterExact swap))
    (o19ElemAppendCases (actorPrefix swap) ((actorLeft swap) :: (actorRight swap) :: (actorSuffix swap))
      (fst (o19ElemAppendInjections (actorPrefix swap) ((actorRight swap) :: (actorLeft swap) :: (actorSuffix swap))))
      (\tailMember => snd (o19ElemAppendInjections (actorPrefix swap) ((actorRight swap) :: (actorLeft swap) :: (actorSuffix swap)))
        (o19SwapTailMember tailMember))
      (replace {p = Elem selected} (actorBeforeExact swap) member))

||| LEGACY-CONDITIONAL lifecycle coverage for the SAME actual Cartesian reached trace.
||| The finite chain supplies real origins; the source decomposition supplies
||| coverage; the exact actor transposition supplies enumeration membership.
export
0 o19ActualTargetLifecycleCoverage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (legacyBlocks : (selected : name) -> (member : Elem selected sourceOrder) ->
    LegacyActorOnly selected (blockBody (decomposedBlock blocks selected member))) ->
  LifecycleActorsCovered targetOrder
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
o19ActualTargetLifecycleCoverage nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks =
  o19LifecycleCoverageFromOrigins source
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
    (replayActionOrigin (finiteDerivationOccurrenceCorrespondence
      (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))))
    (o19SwapActorMembership swap) (decomposedLifecycleCoverage blocks)

||| LEGACY-CONDITIONAL ActorBlockDecomposition on the SAME actual reached trace.
||| Every individual block, physical order, disjointness and lifecycle
||| coverage field is constructed from original O19 inputs plus legacy body evidence.
export
0 o19ActualTargetDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (legacyBlocks : (selected : name) -> (member : Elem selected sourceOrder) ->
    LegacyActorOnly selected (blockBody (decomposedBlock blocks selected member))) ->
  ActorBlockDecomposition name key world error value nameEq keyEq targetOrder
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
o19ActualTargetDecomposition nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks =
  MkActorBlockDecomposition
    (o19ActualTargetBlock nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks)
    (o19ActualTargetBlocksFollowOrder nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks)
    (\early, late, earlyIn, lateIn, ordered =>
      o19OrderedBlockRangesDisjoint
        (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
        (o19ActualTargetBlock nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks early earlyIn)
        (o19ActualTargetBlock nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks late lateIn)
        (o19ActualTargetBlocksFollowOrder nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks early late earlyIn lateIn ordered))
    (o19ActualTargetLifecycleCoverage nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks)

||| OPEN R207 expanded-production obligation, not an inhabitant. This states
||| the full reached decomposition for the SAME hypothetical expanded run.
||| The original exact signature is archived in O6-R207-CROSSTRACE-NEEDS.json.
public export
0 O19ReachedDecompositionUnconditionalObligation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (expanded : O19WholeBlockUnconditionalObligation name key world error value nameEq keyEq protocol swap source blocks premises safety unique) -> Type
O19ReachedDecompositionUnconditionalObligation {name} {key} {world} {error} {value} {targetOrder}
  nameEq keyEq protocol swap source blocks premises safety unique expanded =
  ActorBlockDecomposition name key world error value nameEq keyEq targetOrder
    (cursorTrace (columnCursor (expandedRun expanded)))
