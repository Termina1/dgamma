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

||| E8's ACTUAL generation-tree scanner matches child generation(1,2) to
||| itself, even though it has subsequently been removed from both endpoints.
public export
0 r192RemovedBirthTree : RegistrationCorrespondenceByGeneration r45NameEq
  identityRegistrationGenerationBijection r192RemovedBirthTrace r192RemovedBirthTrace
r192RemovedBirthTree = MkRegistrationCorrespondenceByGeneration
  (MkRegistrationIndexState [(0, MkRegistrationGeneration 0 0)] [(0, (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1))] [((MkRegistrationActivation (MkRegistrationGeneration 0 0) 1), 1)] [])
  (MkRegistrationIndexState [(0, MkRegistrationGeneration 0 0)] [(0, (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1))] [((MkRegistrationActivation (MkRegistrationGeneration 0 0) 1), 1)] [])
  (SkipLeftNonRegistration (OInsert 0 Root r45Parent) _ _ Refl Refl (SkipRightNonRegistration (OInsert 0 Root r45Parent) _ _ Refl Refl (SkipLeftNonRegistration (LBegin 0) _ _ Refl Refl (SkipRightNonRegistration (LBegin 0) _ _ Refl Refl (QueueLeftGeneratedRegistration _ _ Refl (MkSurvivingRegistration (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl (NoParentUnloadStep _ _ (\same => case same of Refl impossible) (NoParentUnloadStep _ _ (\same => case same of Refl impossible) (NoParentUnloadStep _ _ (\same => case same of Refl impossible) NoParentUnloadEnd)))) (MatchRightWithPendingLeft _ _ Refl (MkSurvivingRegistration (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl (NoParentUnloadStep _ _ (\same => case same of Refl impossible) (NoParentUnloadStep _ _ (\same => case same of Refl impossible) (NoParentUnloadStep _ _ (\same => case same of Refl impossible) NoParentUnloadEnd)))) [] _ [] (MkRegistrationEventMatch Refl (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl Refl Refl Refl Refl) (SkipLeftNonRegistration (LAdvance 0) _ _ Refl Refl (SkipRightNonRegistration (LAdvance 0) _ _ Refl Refl (SkipLeftNonRegistration (ORetire 1) _ _ Refl Refl (SkipRightNonRegistration (ORetire 1) _ _ Refl Refl (SkipLeftNonRegistration (ORemove 1) _ _ Refl Refl (SkipRightNonRegistration (ORemove 1) _ _ Refl Refl (RegistrationCorrespondenceEnd)))))))))))))

||| All FOUR fields of CurrentEndpointRenaming accept the absent-name swap.
||| No vestigial exception is used: the child generation is no longer current.
public export
0 r192RemovedCurrent : CurrentEndpointRenaming r45NameEq r45KeyEq
  identityRegistrationGenerationBijection r192RemovedBirthTrace r192RemovedBirthTrace r192RemovedBirthTree
r192RemovedCurrent = MkCurrentEndpointRenaming r192AbsentBijection
  (\n, fiber, found, root => case n of
    Z => Refl
    S later => void (nothingIsNotJust found))
  (\n, fiber, found, root => case n of
    Z => Refl
    S later => void (nothingIsNotJust found))
  (\n, generation, found => case n of
    Z => Right (generation ** (Refl, found))
    S later => void (nothingIsNotJust found))
  (\n, generation, found => case n of
    Z => Right (generation ** (Refl, found))
    S later => void (nothingIsNotJust found))

||| FULL SameOrchestrationModuloGenerated, not merely a bare bijection:
||| exact external inputs, external root generations, E8 surviving tree, and
||| CurrentEndpointRenaming are all inhabited for the actual trace pair.
public export
0 r192RemovedSameInputs : SameOrchestrationModuloGenerated r45NameEq r45KeyEq
  r192RemovedBirthTrace r192RemovedBirthTrace
r192RemovedSameInputs = MkSameOrchestrationModuloGenerated
  identityRegistrationGenerationBijection
  (sameExternalOrchestrationReflexiveSpike r45NameEq r192RemovedBirthTrace)
  (MatchExternalRootBirth _ _ _ _ Refl Refl Refl (SkipLeftNonExternalRootBirth (LBegin 0) _ _ Refl Refl (SkipRightNonExternalRootBirth (LBegin 0) _ _ Refl Refl (SkipLeftNonExternalRootBirth (OInsert 1 (ChildOf 0) r45Child) _ _ Refl Refl (SkipRightNonExternalRootBirth (OInsert 1 (ChildOf 0) r45Child) _ _ Refl Refl (SkipLeftNonExternalRootBirth (LAdvance 0) _ _ Refl Refl (SkipRightNonExternalRootBirth (LAdvance 0) _ _ Refl Refl (SkipLeftNonExternalRootBirth (ORetire 1) _ _ Refl Refl (SkipRightNonExternalRootBirth (ORetire 1) _ _ Refl Refl (SkipLeftNonExternalRootBirth (ORemove 1) _ _ Refl Refl (SkipRightNonExternalRootBirth (ORemove 1) _ _ Refl Refl (ExternalRootBirthCorrespondenceEnd))))))))))))
  r192RemovedBirthTree r192RemovedCurrent
