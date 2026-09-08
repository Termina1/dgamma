module DGamma.R185O19ActivationInsertionRowPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.R182O19AdjacencyNegative
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

||| Actual-source insertion ordinal authentication, not a replay-builder
||| scalar observation. The three source birth positions are 0,1,4.
export
0 r185GapBirthPosition : (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat R45Key Unit String R45Value ordinal (Builtin.fst r182GapTrace) = Just selected) ->
  (ordinal = selected * selected)
r185GapBirthPosition selected Z observed = cong (\actual => actual * actual) (justInjective observed)
r185GapBirthPosition selected (S Z) observed = cong (\actual => actual * actual) (justInjective observed)
r185GapBirthPosition selected (S (S Z)) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S Z)))) observed = cong (\actual => actual * actual) (justInjective observed)
r185GapBirthPosition selected (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S Z)))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S (S Z))))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S (S (S Z)))))))) observed = case observed of Refl impossible
r185GapBirthPosition selected (S (S (S (S (S (S (S (S (S later))))))))) observed = case observed of Refl impossible

||| Full original uniqueness for the actual nine-edge fixture.
public export
0 r185GapUnique : UniqueRawNameInsertions Nat R45Key Unit String R45Value
  r45NameEq r45KeyEq (Builtin.fst r182GapTrace)
r185GapUnique = MkUniqueRawNameInsertions
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (r185GapBirthPosition selected (locatedActionOrdinal left)
      (rawInsertionNameAtLocated Nat R45Key Unit String R45Value (Builtin.fst r182GapTrace)
        selected leftParent leftComponent left))
      (sym (r185GapBirthPosition selected (locatedActionOrdinal right)
        (rawInsertionNameAtLocated Nat R45Key Unit String R45Value (Builtin.fst r182GapTrace)
          selected rightParent rightComponent right))))


||| Input-free actual TWO-crossing A/O row; reached bundle, uniqueness,
||| derivation and count2 come from the generic induction. This is 2x1,
||| NOT a full 2x2 Cartesian assertion or scalar observer over a replay.
export
0 r185ActualActivationInsertionRow :
  O19OrchestrationRow Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
    (Builtin.fst r182GapTrace)
    (MoreTransitions (Fired {before = r182GapState 0} {afterState = r182GapState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182GapState 1} {afterState = r182GapState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (Fired {before = r182GapState 4} {afterState = r182GapState 5} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl) 2
r185ActualActivationInsertionRow =
  o19BubbleActivationInsertionRow r45NameEq r45KeyEq r45Protocol 2 Root r45Child
    (Builtin.fst r182GapTrace)
    (MoreTransitions (Fired {before = r182GapState 0} {afterState = r182GapState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182GapState 1} {afterState = r182GapState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) NoTransitions))
    (MoreTransitions (Fired {before = r182GapState 2} {afterState = r182GapState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (MoreTransitions (Fired {before = r182GapState 3} {afterState = r182GapState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) NoTransitions))
    (Fired {before = r182GapState 4} {afterState = r182GapState 5} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182GapState 5} {afterState = r182GapState 6} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl) (MoreTransitions (Fired {before = r182GapState 6} {afterState = r182GapState 7} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) (MoreTransitions (Fired {before = r182GapState 7} {afterState = r182GapState 8} r45NameEq r45KeyEq (LBegin 2) LBeginTag Refl) (MoreTransitions (Fired {before = r182GapState 8} {afterState = r182GapState 9} r45NameEq r45KeyEq (LAdvance 2) LFinishTag Refl) NoTransitions)))) Refl r182GapBundle r185GapUnique Refl
    (o19TwoForeignActivationClasses 2 (Fired {before = r182GapState 2} {afterState = r182GapState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (Fired {before = r182GapState 3} {afterState = r182GapState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
      (PaperBeginStep Refl Refl) (PaperFinishStep Refl Refl)
      (\same => case same of Refl impossible) (\same => case same of Refl impossible))
    (\step, occurs, licensor, same => case same of Refl impossible)
