module DGamma.R182O19FourthCrossingConstruction

import DGamma.R182O19FourthCrossingFacts
import DGamma.R182O19ThirdCrossingPositive
import DGamma.R182O19ThirdCrossingConstruction
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

||| B37: directly construct the FOURTH actual crossing Begin0/Finish1.
||| All nodes/suffix/bundle are owned by the third reached trace; the guard is
||| derived by B36. No case on a computed existential; no new safety premise.
public export
0 r182FourthCrossingFromReached :
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
  (observed : ObservedTwoActionTrace Nat R45Key Unit String R45Value r45NameEq r45KeyEq (LAdvance 0) (LAdvance 1) (replayedSuffix secondResult)) ->
  (thirdDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (twoActionFirst observed) (twoActionSecond observed)) ->
  (thirdResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace secondResult)
    (appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)) (MoreTransitions (movedRight secondDiamond) (MoreTransitions (movedLeft secondDiamond) NoTransitions)))
    (twoActionFirst observed) (twoActionSecond observed) NoTransitions thirdDiamond) ->
  UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace thirdResult) ->
  (fourthDiamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq (movedLeft secondDiamond) (movedRight thirdDiamond) **
   (fourthResult : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace thirdResult)
     (appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)) (MoreTransitions (movedRight secondDiamond) NoTransitions))
     (movedLeft secondDiamond) (movedRight thirdDiamond)
     (MoreTransitions (movedLeft thirdDiamond) (replayedSuffix thirdResult)) fourthDiamond **
    (NonEmptyFiniteAdjacentSwapDerivation Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq (swappedTrace thirdResult) (swappedTrace fourthResult),
     UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace fourthResult))))
r182FourthCrossingFromReached firstDiamond firstResult secondDiamond secondResult
  observed thirdDiamond thirdResult reachedUnique =
  o19AdvanceActivationPair r45NameEq r45KeyEq r45Protocol (swappedTrace thirdResult)
    (appendTransitions (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)) (MoreTransitions (movedRight secondDiamond) NoTransitions))
    (movedLeft secondDiamond) (movedRight thirdDiamond)
    (MoreTransitions (movedLeft thirdDiamond) (replayedSuffix thirdResult))
    (sym (swappedDecomposition thirdResult)) (swappedPremises thirdResult) reachedUnique
    (movedLeftActivationBranch secondDiamond (PaperBeginStep Refl Refl))
    (movedRightActivationBranch thirdDiamond
      (Builtin.fst (Builtin.snd (r182ThirdPairFacts firstDiamond secondDiamond observed))))
    (\same => uninhabited
      (trans (sym (trans (o19TransitionActorOwner (movedLeft secondDiamond))
        (cong actionOwner (movedLeftAction secondDiamond))))
        (trans same (trans (o19TransitionActorOwner (movedRight thirdDiamond))
          (cong actionOwner (trans (movedRightAction thirdDiamond) (twoActionSecondExact observed)))))))
    (r182FourthPairEarly firstDiamond secondDiamond observed thirdDiamond)
