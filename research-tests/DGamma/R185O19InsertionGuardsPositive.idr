module DGamma.R185O19InsertionGuardsPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19InsertionInsertionRowSpike
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

||| Input-free two-insertion O/O GUARD fixture. All source cuts receive
||| checked insertion2 applicability from its actual final-cut execution.
||| No O/O diamond/replay/row or four-node Cartesian result is asserted here.
export
0 r185ActualInsertionGuards :
  (CheckedEarlyApplication Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (r182IndependentState 0) (OInsert 2 Root r45Child) OInsertTag,
   O19EarlyAlong Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (OInsert 2 Root r45Child) OInsertTag
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)))
r185ActualInsertionGuards =
  o19InsertionGuardsAlongObservedSpine r45NameEq r45KeyEq 2 Root r45Child []
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (o19ObserveInsertionCons r45NameEq r45KeyEq 2 [] 0 Root r45Child OInsertTag Refl
      (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions)
      (\same => case same of Refl impossible) (\licensor, same => case same of Refl impossible)
      (o19ObserveInsertionCons r45NameEq r45KeyEq 2 [] 1 Root r45Child OInsertTag Refl NoTransitions
        (\same => case same of Refl impossible) (\licensor, same => case same of Refl impossible)
        ObservedInsertionsEnd))
    (\step, occurs, licensor, same => case same of Refl impossible) Refl
    (MkCheckedEarlyApplication (MkSystemState ()
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (registry (r182IndependentState 2)) Refl)) Refl)
