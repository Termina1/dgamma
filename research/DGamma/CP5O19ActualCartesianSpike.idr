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
