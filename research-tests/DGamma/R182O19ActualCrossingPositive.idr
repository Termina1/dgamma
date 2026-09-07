module DGamma.R182O19ActualCrossingPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R182O19RevisedSafetyPositive
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B9: executable first CARTESIAN crossing guard at actual cut3: moving
||| right Begin1 left across left Finish0. Both fibers become Reloading;
||| the exact inserted-registry uniqueness token is retained by the producer.
public export
0 r182FirstCrossingEarly : CheckedEarlyApplication Nat R45Key Unit String R45Value
  r45NameEq r45KeyEq (r182IndependentState 3) (LBegin 1) LBeginTag
r182FirstCrossingEarly = MkCheckedEarlyApplication
  (MkSystemState ()
    (MkCoeffectContext
      [Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)),
       Bind 0 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView))]
      (uniqueBindings (registry (r182IndependentState 2))))) Refl

||| B10: actual insertion occurrence classifier (R181 F5 technique), not an
||| assumed uniqueness input or a scalar Maybe-execution-builder observer.
public export
0 r182IndependentBirthPosition : (selected, ordinal : Nat) ->
  (rawInsertionNameAt Nat R45Key Unit String R45Value ordinal (r182IndependentTrace False) =
    Just selected) -> (ordinal = selected)
r182IndependentBirthPosition selected Z observed = justInjective observed
r182IndependentBirthPosition selected (S Z) observed = justInjective observed
r182IndependentBirthPosition selected (S (S Z)) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S Z))) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S (S Z)))) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r182IndependentBirthPosition selected (S (S (S (S (S (S later)))))) observed =
  case observed of Refl impossible

||| B11: whole raw uniqueness is constructed for ALL root/generated located
||| insertion occurrences, and is the exact source premise used by B12.
public export
0 r182IndependentUnique : UniqueRawNameInsertions Nat R45Key Unit String R45Value
  r45NameEq r45KeyEq (r182IndependentTrace False)
r182IndependentUnique = MkUniqueRawNameInsertions
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (r182IndependentBirthPosition selected (locatedActionOrdinal left)
      (rawInsertionNameAtLocated Nat R45Key Unit String R45Value (r182IndependentTrace False)
        selected leftParent leftComponent left))
      (sym (r182IndependentBirthPosition selected (locatedActionOrdinal right)
        (rawInsertionNameAtLocated Nat R45Key Unit String R45Value (r182IndependentTrace False)
          selected rightParent rightComponent right))))

||| B12: NO INPUTS. An actual first crossing of the fully admitted A14 pair,
||| produced through the real local diamond and FROZEN sealed suffix theorem.
||| It owns the complete reached bundle, exact external/registration data,
||| nonempty derivation and transported original uniqueness. No target oracle.
||| Only the first of the required FOUR Cartesian nodes is claimed here.
public export
0 r182ActualFirstCrossing :
  (diamond : LocalRelationalDiamond Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
    (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl) **
   (result : AdjacentSwapResult Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
      (r182IndependentTrace False)
      (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) NoTransitions)))
      (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
      (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
      (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions) diamond **
     (NonEmptyFiniteAdjacentSwapDerivation Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
       (r182IndependentTrace False) (swappedTrace result),
      UniqueRawNameInsertions Nat R45Key Unit String R45Value r45NameEq r45KeyEq (swappedTrace result))))
r182ActualFirstCrossing = o19AdvanceActivationPair r45NameEq r45KeyEq r45Protocol
  (r182IndependentTrace False)
  (MoreTransitions (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) NoTransitions)))
  (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
  (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
  (MoreTransitions (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) NoTransitions)
  Refl r182IndependentBundle r182IndependentUnique
  (PaperFinishStep Refl Refl) (PaperBeginStep Refl Refl)
  uninhabited r182FirstCrossingEarly
