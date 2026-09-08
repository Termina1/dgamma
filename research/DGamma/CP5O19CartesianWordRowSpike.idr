module DGamma.CP5O19CartesianWordRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import DGamma.CP5O19MixedActivationRowSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O19CartesianLengthSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Cartesian row boundary strengthens the actual unified row by retaining
||| its exact residual source action word. Length alone cannot identify the
||| next left/right segment, and a separate scalar observer of a row builder
||| would not justify this equation. The row recursion must construct BOTH.
public export
record O19WordRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal) (earlier : Transitions initial before)
  (spine : Transitions before rightBefore) (right : Transition rightBefore rightAfter)
  (later : Transitions rightAfter sourceFinal) where
  constructor MkO19WordRow
  wordRow : O19MixedRow name key world error value protocol nameEq keyEq source earlier right (transitionCount spine)
  0 wordRowRest : o19ActionWord (mixedRowRest wordRow) = o19ActionWord spine ++ o19ActionWord later

||| Simultaneously extend the ACTUAL reached row AND residual word through
||| one EXPLICIT produced node. This is not a scalar theorem about a separately
||| evaluated builder. The same sealed result produces every new field.
export
0 o19WordRowStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (rest : Transitions middle rightBefore) ->
  (right : Transition rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (previous : O19WordRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) rest right later) ->
  (orientation : AdjacentSwapOrientationEvidence left (mixedRowRight (wordRow previous))) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left (mixedRowRight (wordRow previous)) **
    AdjacentSwapResult name key world error value protocol nameEq keyEq
      (cursorTrace (mixedRowCursor (wordRow previous))) earlier left (mixedRowRight (wordRow previous)) (mixedRowRest (wordRow previous)) diamond) ->
  O19WordRow name key world error value protocol nameEq keyEq source earlier (MoreTransitions left rest) right later
o19WordRowStepObserved {name} {key} {world} {error} {value} nameEq keyEq protocol source earlier left rest right later previous
  orientation (diamond ** result) =
    MkO19WordRow
      (MkO19MixedRow
        (MkO19ReachedCursor (replayedFinal result) (swappedTrace result) (swappedPremises result)
          (uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq (FiniteAdjacentSwapStep (cursorTrace (mixedRowCursor (wordRow previous))) earlier left (mixedRowRight (wordRow previous)) (mixedRowRest (wordRow previous)) orientation diamond result (swappedTrace result) FiniteAdjacentSwapDone) (cursorUnique (mixedRowCursor (wordRow previous))))
          (o19AppendFinite (cursorDerivation (mixedRowCursor (wordRow previous))) (FiniteAdjacentSwapStep (cursorTrace (mixedRowCursor (wordRow previous))) earlier left (mixedRowRight (wordRow previous)) (mixedRowRest (wordRow previous)) orientation diamond result (swappedTrace result) FiniteAdjacentSwapDone)))
        (swappedMiddle diamond) (movedRight diamond) (MoreTransitions (movedLeft diamond) (replayedSuffix result))
        (sym (swappedDecomposition result))
        (trans (movedRightAction diamond) (mixedRowAction (wordRow previous)))
        (trans (movedRightTag diamond) (mixedRowTag (wordRow previous)))
        (trans (o19TransitionActorOwner (movedRight diamond))
          (trans (cong actionOwner (trans (movedRightAction diamond) (mixedRowAction (wordRow previous)))) (sym (o19TransitionActorOwner right))))
        (case mixedRowClass (wordRow previous) of
          Left activation => Left (movedRightActivationBranch diamond activation)
          Right orchestration => Right (movedRightOrchestrationBranch diamond orchestration))
        (trans (o19AppendFiniteCount (cursorDerivation (mixedRowCursor (wordRow previous))) (FiniteAdjacentSwapStep (cursorTrace (mixedRowCursor (wordRow previous))) earlier left (mixedRowRight (wordRow previous)) (mixedRowRest (wordRow previous)) orientation diamond result (swappedTrace result) FiniteAdjacentSwapDone))
          (trans (cong (\count => count + 1) (mixedRowNodeCount (wordRow previous))) (plusCommutative (transitionCount rest) 1))))
      (trans (cong (\action => action :: o19ActionWord (replayedSuffix result)) (movedLeftAction diamond))
        (cong ((transitionAction left) ::) (trans (o19SealedActionWord nameEq keyEq (sealedSuffixReplay result)) (wordRowRest previous))))

||| Consume the EXPLICIT reached pair observation, then pass the real produced
||| node ordinarily to D2's simultaneous row/word constructor. The composed
||| original origin map uses the same current cursor; no reached safety input.
export
0 o19WordRowAtObservedPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (source : Transitions initial sourceFinal) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original source ->
  (earlier : Transitions initial before) -> (left : Transition before middle) -> (rest : Transitions middle rightBefore) ->
  (right : Transition rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (previous : O19WordRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) rest right later) ->
  (orientation : AdjacentSwapOrientationEvidence left (mixedRowRight (wordRow previous)) **
    O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left (mixedRowRight (wordRow previous)) orientation) ->
  O19WordRow name key world error value protocol nameEq keyEq source earlier (MoreTransitions left rest) right later
o19WordRowAtObservedPair nameEq keyEq protocol swap original blocks premises safety unique source prior earlier left rest right later previous
  (orientation ** observed) =
    o19WordRowStepObserved nameEq keyEq protocol source earlier left rest right later previous orientation
      (o19ObservedPairReplay nameEq keyEq protocol swap original blocks premises safety unique (MkO19ReachedCursor (cursorFinal (mixedRowCursor (wordRow previous))) (cursorTrace (mixedRowCursor (wordRow previous))) (cursorBundle (mixedRowCursor (wordRow previous))) (cursorUnique (mixedRowCursor (wordRow previous))) (o19AppendFinite prior (cursorDerivation (mixedRowCursor (wordRow previous)))))
        earlier left (mixedRowRight (wordRow previous)) (mixedRowRest (wordRow previous)) (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions) (MoreTransitions (mixedRowRight (wordRow previous)) (mixedRowRest (wordRow previous))))) (mixedRowDecomposition (wordRow previous))) observed)

||| Derive the ACTUAL pair observation from the flat separated-source values
||| and the SAME previous row's labels, then produce its actual crossing,
||| suffix replay, reached bundle, uniqueness, derivation, count and word.
export
0 o19WordRowStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (source : Transitions initial sourceFinal) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original source ->
  (earlier : Transitions initial before) -> (left : Transition before middle) -> (rest : Transitions middle rightBefore) ->
  (right : Transition rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (previous : O19WordRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) rest right later) ->
  O19SourcePairObservation name key world error value (actorLeft swap) (actorRight swap) left right ->
  O19WordRow name key world error value protocol nameEq keyEq source earlier (MoreTransitions left rest) right later
o19WordRowStep nameEq keyEq protocol swap original blocks premises safety unique source prior earlier left rest right later previous observed =
  o19WordRowAtObservedPair nameEq keyEq protocol swap original blocks premises safety unique source prior earlier left rest right later previous
    (o19SourcePairAtReachedRight (actorLeft swap) (actorRight swap) left right (mixedRowRight (wordRow previous))
      (mixedRowAction (wordRow previous)) (mixedRowTag (wordRow previous)) (mixedRowActor (wordRow previous)) observed)
