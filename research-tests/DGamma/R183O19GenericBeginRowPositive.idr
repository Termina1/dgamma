module DGamma.R183O19GenericBeginRowPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
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

||| No inputs: use the GENERIC row induction on R182's admitted two-by-two
||| source. BOTH first-row crossings and exact count2 are produced; every
||| intermediate guard is derived from A14's one sanctioned pre-left guard.
||| No expected final replay is invented and no builder-count observer is used.
export
0 r183ActualGenericBeginRow :
  O19ActivationRow Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
    (r182IndependentTrace False)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl)
      (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl) 2
r183ActualGenericBeginRow =
  o19BubbleBeginRow r45NameEq r45KeyEq r45Protocol 1 (r182IndependentTrace False)
    (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl)
      (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (MoreTransitions (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (MoreTransitions (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) NoTransitions))
    (MkBeginStep Refl) (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions) Refl r182IndependentBundle r182IndependentUnique
    (o19TwoForeignActivationClasses 1 (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
      (PaperBeginStep Refl Refl) (PaperFinishStep Refl Refl)
      (\same => case same of Refl impossible) (\same => case same of Refl impossible))
    (safetyRightOpeningEarly r182IndependentSafety)
