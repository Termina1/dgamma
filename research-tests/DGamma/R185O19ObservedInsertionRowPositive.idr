module DGamma.R185O19ObservedInsertionRowPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import DGamma.R182O19ActualCrossingPositive
import DGamma.R182O19RevisedSafetyNegative
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Input-free actual insertion/Begin crossing on the admitted R182 2x2
||| source. This exercises the generic observed row, including its reached
||| bundle, uniqueness, finite derivation and count1. It is NOT a four-crossing
||| 2x2 O/A Cartesian fixture, which still needs mixed-spine continuation.
export
0 r185ActualObservedInsertionRow :
  O19ActivationRow Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
    (r182IndependentTrace False)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) NoTransitions)
    (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) 1
r185ActualObservedInsertionRow =
  o19BubbleResolvedInsertionRow r45NameEq r45KeyEq r45Protocol 0
    r45Child Root emptyOwned EmptyView (r182IndependentTrace False)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) NoTransitions)
    (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)
    (MkBeginStep Refl) (MoreTransitions (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (MoreTransitions (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl) (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions))) Refl r182IndependentBundle r182IndependentUnique
    (o19ObserveInsertionCons r45NameEq r45KeyEq 0 [] 1 Root r45Child OInsertTag Refl NoTransitions
      (\same => case same of Refl impossible) (\licensor, same => case same of Refl impossible)
      ObservedInsertionsEnd)
    Refl Refl Refl
