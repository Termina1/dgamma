module DGamma.R182O19ThirdCrossingConstruction

import DGamma.R182O19RemainingCrossingFacts
import DGamma.R182O19SecondCrossingPositive
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.R182O19ActualCrossingPositive
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import DGamma.R182O19RevisedSafetyNegative
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B32: construct node3 Finish0/Finish1 from an EXPLICIT observed actual
||| two-node suffix. Its tags and early guard are derived at the reached cut;
||| source bundle + node nonemptiness + uniqueness advance simultaneously.
||| Return the direct produced package: a case on its computed existential
||| crossed the 48GiB guard. Global derivation assembly is a separate consumer.
public export
0 r182ThirdCrossingFromView :
  (firstDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) ->
  (firstResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (r182IndependentTrace False)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) NoTransitions)))
    (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
    (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions) firstDiamond) ->
  (secondDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)) ->
  (secondResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace firstResult)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (movedRight firstDiamond)
    (MoreTransitions (movedLeft firstDiamond) (replayedSuffix firstResult)) secondDiamond) ->
  UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace secondResult) ->
  (observed : ObservedTwoActionTrace Nat R45Key Unit String R45Value r45NameEq r45KeyEq (LAdvance 0) (LAdvance 1) (replayedSuffix secondResult)) ->
  (thirdDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (twoActionFirst observed) (twoActionSecond observed) **
   (thirdResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace secondResult)
     (appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)) (MoreTransitions (movedRight secondDiamond) (MoreTransitions (movedLeft secondDiamond) NoTransitions)))
     (twoActionFirst observed) (twoActionSecond observed) NoTransitions thirdDiamond **
    (NonEmptyFiniteAdjacentSwapDerivation Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace secondResult) (swappedTrace thirdResult),
     UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace thirdResult))))
r182ThirdCrossingFromView firstDiamond firstResult secondDiamond secondResult
  reachedUnique observed =
  o19AdvanceActivationPair r45NameEq r45KeyEq r45Protocol (swappedTrace secondResult)
    (appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)) (MoreTransitions (movedRight secondDiamond) (MoreTransitions (movedLeft secondDiamond) NoTransitions)))
    (twoActionFirst observed) (twoActionSecond observed) NoTransitions
    (trans (cong (\suffix => appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
      (MoreTransitions (movedRight secondDiamond) (MoreTransitions (movedLeft secondDiamond) suffix)))
      (twoActionTraceExact observed)) (sym (swappedDecomposition secondResult)))
    (swappedPremises secondResult) reachedUnique
    (Builtin.fst (r182ThirdPairFacts firstDiamond secondDiamond observed))
    (Builtin.fst (Builtin.snd (r182ThirdPairFacts firstDiamond secondDiamond observed)))
    (\same => uninhabited
      (trans (sym (trans (o19TransitionActorOwner (twoActionFirst observed))
        (cong actionOwner (twoActionFirstExact observed))))
        (trans same (trans (o19TransitionActorOwner (twoActionSecond observed))
          (cong actionOwner (twoActionSecondExact observed))))))
    (Builtin.snd (Builtin.snd (r182ThirdPairFacts firstDiamond secondDiamond observed)))
