module DGamma.R192RemovedBirthCurrentNameProbe

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP4SupportSolution
import DGamma.CP5O20PairedRemovalSpike
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
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

||| Exact nonvacuous original generated birth; its historical name is1.
public export
0 r192RemovedOriginalBirth : LocatedGeneratedRegistration 1 0 r45Child r192RemovedBirthTrace
r192RemovedOriginalBirth = MkLocatedGeneratedRegistration r45AfterBegin r45SourcePairFinal
  (MoreTransitions r45ParentInsert (MoreTransitions r45Begin NoTransitions)) r45ChildInsert
  (MoreTransitions r178ParentFinish (MoreTransitions r178ChildRetire
    (MoreTransitions (Fired r45NameEq r45KeyEq (ORemove 1) ORemoveTag
      (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
        (ORemove 1) r178RightFinal r192RemovedBirthFinal ORemoveTag
        (checkedTransitionTargetValid r178ChildRetire) Refl)) NoTransitions))) Refl Refl

||| Structural observation, NOT normalization of support or canonical builders.
||| No insertion of raw name2 occurs at any position in the actual trace.
export
0 r192NoMappedInsertionAt : (ordinal : Nat) ->
  (rawInsertionNameAt Nat R45Key Unit String R45Value ordinal r192RemovedBirthTrace = Just 2) -> Void
r192NoMappedInsertionAt Z observed = case observed of Refl impossible
r192NoMappedInsertionAt (S Z) observed = case observed of Refl impossible
r192NoMappedInsertionAt (S (S Z)) observed = case observed of Refl impossible
r192NoMappedInsertionAt (S (S (S Z))) observed = case observed of Refl impossible
r192NoMappedInsertionAt (S (S (S (S Z)))) observed = case observed of Refl impossible
r192NoMappedInsertionAt (S (S (S (S (S Z))))) observed = case observed of Refl impossible
r192NoMappedInsertionAt (S (S (S (S (S (S later)))))) observed = case observed of Refl impossible

||| NEGATIVE theorem: E8 plus CurrentEndpointRenaming does NOT identify all
||| historical raw birth names. Exact fixed expectedBridgeBijection sends1->2,
||| but there is no right birth at2. No claim about full canonical capital.
export
0 r192E8CurrentDoesNotGiveHistoricalBirth :
  Not (LocatedGeneratedRegistration
    (renameForward (expectedBridgeBijection r192RemovedSameInputs) 1)
    (renameForward (expectedBridgeBijection r192RemovedSameInputs) 0)
    r45Child r192RemovedBirthTrace)
r192E8CurrentDoesNotGiveHistoricalBirth birth =
  r192NoMappedInsertionAt (locatedActionOrdinal (generatedRegistrationActionOccurrence birth))
    (rawInsertionNameAtLocated Nat R45Key Unit String R45Value r192RemovedBirthTrace
      2 (ChildOf 0) r45Child (generatedRegistrationActionOccurrence birth))

||| Precise retained obstruction: the actual original birth is unsupported;
||| E9 generated Retire/Remove matching ALSO holds (both nonempty domains).
||| These facts still cannot manufacture the fixed-current-map right birth.
||| Support is derived from the deletion lookup theorem, not scalar unfolding.
||| UniqueRawNameInsertions and independent canonical capital are NOT claimed.
export
0 r192RemovedBirthObstruction :
  (isSupported {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
    @{r45NameEq} @{r45KeyEq} 1 r192RemovedBirthFinal = False,
   GeneratedOrchestrationMatched Nat R45Key Unit String R45Value r45NameEq
    r192RemovedBirthTrace r192RemovedBirthTrace (generatedGenerationBijection r192RemovedSameInputs),
   Not (LocatedGeneratedRegistration
    (renameForward (expectedBridgeBijection r192RemovedSameInputs) 1)
    (renameForward (expectedBridgeBijection r192RemovedSameInputs) 0)
    r45Child r192RemovedBirthTrace))
r192RemovedBirthObstruction =
  ((the ((state : SystemState Nat R45Key R45Value Unit String) ->
      (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
        @{r45NameEq} 1 (registry state) = Nothing) ->
      (isSupported @{r45NameEq} @{r45KeyEq} 1 state = False))
      (\state, absent => trans (supportSetIsSolution r45NameEq r45KeyEq state 1)
        (rewrite absent in Refl))) r192RemovedBirthFinal
      (o20DeletedLookupAbsent r45NameEq 1 (registry r178RightFinal)),
   generatedOrchestrationReflexive Nat R45Key Unit String R45Value r45NameEq r192RemovedBirthTrace,
   r192E8CurrentDoesNotGiveHistoricalBirth)

||| C6 DISTINCT grammar probe on already-authenticated R178 edges, not a
||| shrunken retry of C4's failed eleven-edge R191 evaluator construction.
||| Genuine own-child Retire is INSIDE parent0's actual extended body.
export
0 r192ExistingParentBodyRetireExtended :
  ActorLifecycleOnlyExtended r45NameEq 0
    (MoreTransitions r45ChildInsert (MoreTransitions r178ParentFinish
      (MoreTransitions r178ChildRetire NoTransitions)))
r192ExistingParentBodyRetireExtended =
  ExtendedYieldedRegistrationStep _ _ Refl
    (ExtendedLifecycleStep _ _ Refl Refl
      (ExtendedChildRetireStep _ _ 1 r45ChildFresh Refl Refl Refl ExtendedLifecycleEnd))

||| Both generated Retire AND Remove occur in this actual parent0 body.
||| The Remove equation/physical destination are the already-checked A19 cut.
export
0 r192ExistingParentBodyRemoveExtended :
  ActorLifecycleOnlyExtended r45NameEq 0
    (MoreTransitions r45ChildInsert (MoreTransitions r178ParentFinish
      (MoreTransitions r178ChildRetire (MoreTransitions
        (Fired {before = r178RightFinal} {afterState = r192RemovedBirthFinal}
          r45NameEq r45KeyEq (ORemove 1) ORemoveTag
          (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
            (ORemove 1) r178RightFinal r192RemovedBirthFinal ORemoveTag
            (checkedTransitionTargetValid r178ChildRetire) Refl)) NoTransitions))))
r192ExistingParentBodyRemoveExtended =
  ExtendedYieldedRegistrationStep _ _ Refl
    (ExtendedLifecycleStep _ _ Refl Refl
      (ExtendedChildRetireStep _ _ 1 r45ChildFresh Refl Refl Refl
        (ExtendedChildRemoveStep _ _ 1 r45ChildRetired Refl Refl Refl ExtendedLifecycleEnd)))
