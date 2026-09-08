module DGamma.R192RemovedBirthCurrentNameProbe

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5RawClosingRankSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Genuine removal of the unsupported, retired generated child. Parent0 is
||| still Active; raw names1 and2 are both absent at this physical endpoint.
public export
r192RemovedBirthFinal : SystemState Nat R45Key R45Value Unit String
r192RemovedBirthFinal = MkSystemState () (deleteBinding @{r45NameEq} 1 (registry r178RightFinal))

||| Six actual edges: root Insert, Begin, child Insert, Finish, child Retire,
||| child Remove. This probe supplies no independent canonical capital.
public export
0 r192RemovedBirthTrace : Transitions r45Initial r192RemovedBirthFinal
r192RemovedBirthTrace = appendTransitions r178RightTrace
  (MoreTransitions (Fired r45NameEq r45KeyEq (ORemove 1) ORemoveTag
    (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
      (ORemove 1) r178RightFinal r192RemovedBirthFinal ORemoveTag
      (checkedTransitionTargetValid r178ChildRetire) Refl)) NoTransitions)

||| Changes ONLY absent endpoint names; fixes the live external root0.
public export
r192SwapAbsent : Nat -> Nat
r192SwapAbsent Z = Z
r192SwapAbsent (S Z) = 2
r192SwapAbsent (S (S Z)) = 1
r192SwapAbsent (S (S (S later))) = S (S (S later))

||| Constructive total bijection. This is not an asserted permutation.
public export
r192AbsentBijection : NameBijection Nat
r192AbsentBijection = MkNameBijection r192SwapAbsent r192SwapAbsent
  (\n => case n of Z => Refl
                   S Z => Refl
                   S (S Z) => Refl
                   S (S (S later)) => Refl)
  (\n => case n of Z => Refl
                   S Z => Refl
                   S (S Z) => Refl
                   S (S (S later)) => Refl)
