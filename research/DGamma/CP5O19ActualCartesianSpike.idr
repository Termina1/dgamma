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
