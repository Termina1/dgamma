module DGamma.CP5O19ActualCartesianSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import DGamma.CP5O19CartesianLengthSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O19CartesianWordRowSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19CartesianSitePlanSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19PaperBranchCompletenessSpike
import DGamma.CP5O19CartesianColumnsSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Observe the actual between-block gap. Its zero count forces the empty
||| constructor, then instantiate E14 with A12's DERIVED original classes.
||| The word equations only identify these explicit spines with the selected
||| source blocks and are Refl at the actual block entry point below.
export
0 o19CartesianAdjacentObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal, before, leftAfter, leftEnd, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (earlier : Transitions initial before) -> (firstLeft : Transition before leftAfter) -> (leftRest : Transitions leftAfter leftEnd) ->
  (gap : Transitions leftEnd rightBefore) -> (rightSpine : Transitions rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions (MoreTransitions firstLeft leftRest) (appendTransitions gap (appendTransitions rightSpine later))) = source) ->
  (transitionCount gap = 0) ->
  (o19ActionWord (MoreTransitions firstLeft leftRest) = o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  (o19ActionWord rightSpine = o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  O19ColumnRun name key world error value protocol nameEq keyEq source earlier
    (o19ActionWord (MoreTransitions firstLeft leftRest)) (o19ActionWord rightSpine) (o19ActionWord later)
o19CartesianAdjacentObserved nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest
  NoTransitions rightSpine later decomposition adjacent leftWord rightWord =
    o19CartesianSourceSpines nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest rightSpine later decomposition
      (\leftOrigin, rightOrigin, leftMember, rightMember =>
        o19OriginalClasses nameEq keyEq protocol swap source blocks premises safety unique leftOrigin rightOrigin
          (replace {p = Elem _} leftWord leftMember) (replace {p = Elem _} rightWord rightMember))
o19CartesianAdjacentObserved nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest
  (MoreTransitions step rest) rightSpine later decomposition adjacent leftWord rightWord = void (uninhabited adjacent)

||| Actual five-piece source equation from BlockBefore, not a caller's
||| guessed cut. The existing opening-prefix equation is normalized by
||| dependent append associativity and the actual right decomposition.
export
0 o19ActualBlockSpines :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {source : Transitions initial finalState} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock) ->
  (appendTransitions (traceBeforeBlock leftBlock)
    (appendTransitions (actorBlockTrace leftBlock)
      (appendTransitions (betweenBlocks ordered)
        (appendTransitions (actorBlockTrace rightBlock) (traceAfterBlock rightBlock)))) = source)
o19ActualBlockSpines leftBlock rightBlock ordered =
  trans (sym (appendTransitionsAssociative (traceBeforeBlock leftBlock)
    (MoreTransitions (beginTransition (blockOpening leftBlock)) NoTransitions)
    (appendTransitions (blockBody leftBlock)
      (appendTransitions (betweenBlocks ordered) (appendTransitions (actorBlockTrace rightBlock) (traceAfterBlock rightBlock))))))
  (trans (sym (appendTransitionsAssociative (prefixToBlockOpening leftBlock) (blockBody leftBlock)
    (appendTransitions (betweenBlocks ordered) (appendTransitions (actorBlockTrace rightBlock) (traceAfterBlock rightBlock)))))
  (trans (cong (appendTransitions (prefixThroughBlock leftBlock))
    (sym (appendTransitionsAssociative (betweenBlocks ordered)
      (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)
      (appendTransitions (blockBody rightBlock) (traceAfterBlock rightBlock)))))
  (trans (sym (appendTransitionsAssociative (prefixThroughBlock leftBlock)
    (appendTransitions (betweenBlocks ordered) (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions))
    (appendTransitions (blockBody rightBlock) (traceAfterBlock rightBlock))))
  (trans (cong (\leading => appendTransitions leading (appendTransitions (blockBody rightBlock) (traceAfterBlock rightBlock)))
    (sym (blocksOrderedInGlobal ordered)))
  (trans (appendTransitionsAssociative (traceBeforeBlock rightBlock)
    (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)
    (appendTransitions (blockBody rightBlock) (traceAfterBlock rightBlock)))
    (blockDecomposition rightBlock))))))

||| The ACTUAL O19 Cartesian loop, with NO internal classification, cut,
||| row, or decomposition premise. All spines come from the selected original
||| blocks, the gap is the sanctioned actual adjacency, and A12 produces every
||| original class. This yields the actual reached bundle/unique/relative
||| finite chain/product count, NOT yet the ordinal WholeBlockSwapDerivation
||| or the target installed ActorBlockDecomposition.
export
0 o19CartesianActualBlocks :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  O19ColumnRun name key world error value protocol nameEq keyEq source
    (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
    (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
    (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
    (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique =
  o19CartesianAdjacentObserved nameEq keyEq protocol swap source blocks premises safety unique
    (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
    (beginTransition (blockOpening (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
    (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
    (betweenBlocks (safetyBlocksOrdered safety))
    (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
    (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
    (o19ActualBlockSpines (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
      (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))
    (safetyBlocksAdjacent safety) Refl Refl

||| Instantiate the true GLOBAL origin-plan producer on the SAME actual
||| O19 Cartesian chain, starting at identity. No rows, cuts, static classes
||| or source-ordinal equations are supplied by the caller. This exact plan
||| is not yet a proof of selected-block-local Cartesian bounds/coverage.
export
0 o19ActualGlobalOriginPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  O19GlobalPlanResult name key world error value protocol nameEq keyEq source
    (identityActionRegistrationReplayCorrespondence source)
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique =
  o19BuildGlobalOriginPlan (identityActionRegistrationReplayCorrespondence source) (o19IdentityOrdinalMap source)
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))

||| The AUTHENTIC global-origin list has the actual selected-block product
||| cardinality. This consumes the SAME plan's count and SAME run's product
||| equation; it is not a Refl observer of an independently rebuilt replay.
||| Cardinality alone still does not prove Cartesian coverage or uniqueness.
export
0 o19ActualGlobalOriginProductCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (length (globalCrossingPositions (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique)) =
    actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) *
    actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
o19ActualGlobalOriginProductCount nameEq keyEq protocol swap source blocks premises safety unique =
  trans (globalCrossingCount (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique))
    (trans (columnNodeCount (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))
      (cong2 (*)
        (o19ActionWordLength (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
        (o19ActionWordLength (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))))

||| Reduce B13's SAME actual global-origin list to numerical execution of
||| its ACTUAL finite-chain sites. The initial map is the field of B8's
||| actual identity producer; this is not a caller-selected numeric oracle.
||| The Cartesian closed form of these sites/coordinates is still to prove.
export
0 o19ActualGlobalOriginSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (globalCrossingPositions (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique) =
    o19OriginsAtSites (ordinalOrigin (o19IdentityOrdinalMap source))
      (o19CrossingSites (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))))
o19ActualGlobalOriginSites nameEq keyEq protocol swap source blocks premises safety unique =
  o19GlobalPlanSites (identityActionRegistrationReplayCorrespondence source) (o19IdentityOrdinalMap source)
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))

||| Actual empty-gap site adapter, discharging static classes with A12.
export
0 o19CartesianAdjacentObservedSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal, before, leftAfter, leftEnd, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (earlier : Transitions initial before) -> (firstLeft : Transition before leftAfter) -> (leftRest : Transitions leftAfter leftEnd) ->
  (gap : Transitions leftEnd rightBefore) -> (rightSpine : Transitions rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (decomposition : appendTransitions earlier (appendTransitions (MoreTransitions firstLeft leftRest) (appendTransitions gap (appendTransitions rightSpine later))) = source) ->
  (adjacent : transitionCount gap = 0) ->
  (leftWord : o19ActionWord (MoreTransitions firstLeft leftRest) = o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  (rightWord : o19ActionWord rightSpine = o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  (o19CrossingSites (cursorDerivation (columnCursor (o19CartesianAdjacentObserved nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest gap rightSpine later decomposition adjacent leftWord rightWord))) =
    o19ColumnSites (transitionCount earlier) (transitionCount (MoreTransitions firstLeft leftRest)) (transitionCount rightSpine))
o19CartesianAdjacentObservedSites nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest
  NoTransitions rightSpine later decomposition adjacent leftWord rightWord =
    o19CartesianSourceSpinesSites nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest rightSpine later decomposition
      (\leftOrigin, rightOrigin, leftMember, rightMember =>
        o19OriginalClasses nameEq keyEq protocol swap source blocks premises safety unique leftOrigin rightOrigin
          (replace {p = Elem _} leftWord leftMember) (replace {p = Elem _} rightWord rightMember))
o19CartesianAdjacentObservedSites nameEq keyEq protocol swap source blocks premises safety unique earlier firstLeft leftRest
  (MoreTransitions step rest) rightSpine later decomposition adjacent leftWord rightWord = void (uninhabited adjacent)

||| B3 ACTUAL O19 site closed form: no internal class/cut/site premise.
export
0 o19CartesianActualBlocksSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (o19CrossingSites (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) =
    o19ColumnSites (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
      (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
      (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
o19CartesianActualBlocksSites nameEq keyEq protocol swap source blocks premises safety unique =
  o19CartesianAdjacentObservedSites nameEq keyEq protocol swap source blocks premises safety unique
    (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
    (beginTransition (blockOpening (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
    (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
    (betweenBlocks (safetyBlocksOrdered safety))
    (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
    (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
    (o19ActualBlockSpines (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
      (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))
    (safetyBlocksAdjacent safety) Refl Refl

||| The SAME B13 global origins are the numeric execution of the now-proved
||| ACTUAL Cartesian site pattern. Only the numeric closed-form calculation
||| and its local coverage/uniqueness remain at this ordinal seam.
export
0 o19ActualGlobalCartesianSites :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (globalCrossingPositions (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique) =
    o19OriginsAtSites (ordinalOrigin (o19IdentityOrdinalMap source))
      (o19ColumnSites (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
        (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))
o19ActualGlobalCartesianSites nameEq keyEq protocol swap source blocks premises safety unique =
  trans (o19ActualGlobalOriginSites nameEq keyEq protocol swap source blocks premises safety unique)
    (cong (o19OriginsAtSites (ordinalOrigin (o19IdentityOrdinalMap source)))
      (o19CartesianActualBlocksSites nameEq keyEq protocol swap source blocks premises safety unique))

||| Authenticate the right block's ORIGINAL start from the actual ordered
||| opening-prefix equation and the actual sanctioned empty gap. This is a
||| dependent-source count theorem, not a caller-supplied coordinate offset.
export
0 o19AdjacentBlockStartCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock) ->
  (transitionCount (betweenBlocks ordered) = 0) ->
  (transitionCount (traceBeforeBlock rightBlock) = transitionCount (traceBeforeBlock leftBlock) + actorBlockTransitionCount leftBlock)
o19AdjacentBlockStartCount leftBlock rightBlock ordered adjacent =
  successorEqualityInjective
    (trans (sym (transitionPrefixLength (traceBeforeBlock rightBlock) (beginTransition (blockOpening rightBlock))))
    (trans (cong transitionCount (blocksOrderedInGlobal ordered))
    (trans (o19TransitionCountAppend (prefixThroughBlock leftBlock)
      (appendTransitions (betweenBlocks ordered) (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)))
    (trans (cong (\count => transitionCount (prefixThroughBlock leftBlock) + count)
      (transitionPrefixLength (betweenBlocks ordered) (beginTransition (blockOpening rightBlock))))
    (trans (cong (\gapCount => transitionCount (prefixThroughBlock leftBlock) + S gapCount) adjacent)
    (trans (plusCommutative (transitionCount (prefixThroughBlock leftBlock)) 1)
      (cong S (trans (o19TransitionCountAppend (prefixToBlockOpening leftBlock) (blockBody leftBlock))
        (trans (cong (\openingCount => openingCount + transitionCount (blockBody leftBlock))
          (transitionPrefixLength (traceBeforeBlock leftBlock) (beginTransition (blockOpening leftBlock))))
          (plusSuccRightSucc (transitionCount (traceBeforeBlock leftBlock)) (transitionCount (blockBody leftBlock))))))))))))

||| SAME ACTUAL B13 source origins = the explicit Cartesian grid of the
||| ACTUAL selected source-block coordinates. Both map bands come from the
||| owning identity producer and the authenticated original right start.
export
0 o19ActualGlobalGrid :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (globalCrossingPositions (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique) =
    o19GridPairs (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
      (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
      (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
      (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
o19ActualGlobalGrid nameEq keyEq protocol swap source blocks premises safety unique =
  trans (o19ActualGlobalCartesianSites nameEq keyEq protocol swap source blocks premises safety unique)
    (o19NumericColumnGrid (ordinalOrigin (o19IdentityOrdinalMap source))
      (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
      (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
      (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
      (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
      (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
      (\index, bound => o19IdentityOrdinalMapPoint source
        (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) + index))
      (\index, bound => trans
        (o19IdentityOrdinalMapPoint source
          ((transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) +
            actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) + index))
        (cong (\start => start + index)
          (sym (o19AdjacentBlockStartCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
            (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety) (safetyBlocksAdjacent safety))))))

||| ACTUAL source-local Cartesian origin plan on the SAME B3 finite chain.
||| B14's offset-list equation is now DERIVED from actual numeric grid
||| equality and coordinate shifting; NO offset/plan oracle is supplied.
||| Complete/sound membership, UniqueKeys and nonempty whole-block assembly
||| remain separate certification obligations; no O19 body is claimed.
export
0 o19ActualLocalOriginPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  BlockCrossingOriginPlan name key world error value protocol nameEq keyEq source
    (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
    (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
    (identityActionRegistrationReplayCorrespondence source)
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (o19GridPairs Z Z (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
o19ActualLocalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique =
  o19LocalizeGlobalPlan (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
    (globalCrossingPlan (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique)) (o19GridPairs Z Z (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
    (trans (o19ActualGlobalGrid nameEq keyEq protocol swap source blocks premises safety unique)
      (sym (trans (o19GridPairsShift (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) Z Z (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
        (cong2 (\leftSource, rightSource => o19GridPairs leftSource rightSource (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
          (plusZeroRightNeutral (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))) (plusZeroRightNeutral (transitionCount (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))))))
