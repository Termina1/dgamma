module DGamma.R193VestigialHistoryTransportPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The exact native parent callback result already used by R178's actual
||| checked Finish. This fixture concerns original historical endpoints, not
||| a copied placement grammar or independent canonical capital.
public export
r193HistoricalParentActive : Fiber Nat R45Key R45Value Unit String
r193HistoricalParentActive = setFiberRuntime r45ParentBegun
  (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r45ParentBegun)))
  (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView)

||| Parent retirement follows the actual already-retired child endpoint.
public export
r193HistoricalParentRetired : SystemState Nat R45Key R45Value Unit String
r193HistoricalParentRetired = MkSystemState ()
  (replaceBinding @{r45NameEq} 0 (retireFiber r193HistoricalParentActive) (registry r178RightFinal))

||| The old checked child Retire owns the source well-formedness here.
public export
r193HistoricalRetire : Transition r178RightFinal r193HistoricalParentRetired
r193HistoricalRetire = Fired r45NameEq r45KeyEq (ORetire 0) ORetireTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (ORetire 0) r178RightFinal r193HistoricalParentRetired ORetireTag
    (checkedTransitionTargetValid r178ChildRetire) Refl)

||| The parent leaves its now-invalid target, retaining its authentic undo.
public export
r193HistoricalLeaving : SystemState Nat R45Key R45Value Unit String
r193HistoricalLeaving = MkSystemState ()
  (replaceBinding @{r45NameEq} 0
    (setFiberLifecycle (retireFiber r193HistoricalParentActive)
      (Unloading (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView Nothing))
    (registry r193HistoricalParentRetired))

public export
r193HistoricalLeave : Transition r193HistoricalParentRetired r193HistoricalLeaving
r193HistoricalLeave = Fired r45NameEq r45KeyEq (LLeave 0) LLeaveTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LLeave 0) r193HistoricalParentRetired r193HistoricalLeaving LLeaveTag
    (checkedTransitionTargetValid r193HistoricalRetire) Refl)

||| Native unload applies the actual accumulated inverse to the normalized
||| owner table. Both projections refer to that exact runtime callback result.
public export
r193HistoricalClosed : SystemState Nat R45Key R45Value Unit String
r193HistoricalClosed = MkSystemState
  (localWorld ((pushLocalUndo @{r45KeyEq} r45Spec id id)
    (MkLocalState () (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r193HistoricalParentActive))))))
  (replaceBinding @{r45NameEq} 0
    (setFiberRuntime (retireFiber r193HistoricalParentActive)
      (localTable ((pushLocalUndo @{r45KeyEq} r45Spec id id)
        (MkLocalState () (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r193HistoricalParentActive))))))
      (Inactive Nothing)) (registry r193HistoricalLeaving))

||| Actual parent episode closure; the inert child stays physically present.
public export
r193HistoricalUnload : Transition r193HistoricalLeaving r193HistoricalClosed
r193HistoricalUnload = Fired r45NameEq r45KeyEq (LUnload 0) LUnloadTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LUnload 0) r193HistoricalLeaving r193HistoricalClosed LUnloadTag
    (checkedTransitionTargetValid r193HistoricalLeave) Refl)

||| Actual five-edge continuation after the generated birth, including the
||| authenticated final parent L-Unload used by the discarded-birth scanner.
public export
r193HistoricalContinuation : Transitions r45SourcePairFinal r193HistoricalClosed
r193HistoricalContinuation = MoreTransitions r178ParentFinish
  (MoreTransitions r178ChildRetire (MoreTransitions r193HistoricalRetire
    (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))))

||| Eight actual checked edges from the empty origin. The generated child
||| belongs to a genuinely closing parent episode but has NOT been removed.
public export
r193HistoricalClosedTrace : Transitions r45Initial r193HistoricalClosed
r193HistoricalClosedTrace = MoreTransitions r45ParentInsert
  (MoreTransitions r45Begin (MoreTransitions r45ChildInsert r193HistoricalContinuation))

||| Authentic birth at ordinal2 in the actual closing trace.
public export
0 r193HistoricalBirth : LocatedGeneratedRegistration 1 0 r45Child r193HistoricalClosedTrace
r193HistoricalBirth = MkLocatedGeneratedRegistration r45AfterBegin r45SourcePairFinal
  (MoreTransitions r45ParentInsert (MoreTransitions r45Begin NoTransitions))
  r45ChildInsert r193HistoricalContinuation Refl Refl

||| BOTH actual scanners discard the child's generation because its original
||| parent episode really closes. Discard membership is trace-derived, never
||| inserted by an endpoint predicate or inferred merely from inactivity.
public export
0 r193HistoricalTree : RegistrationCorrespondenceByGeneration r45NameEq
  identityRegistrationGenerationBijection r193HistoricalClosedTrace r193HistoricalClosedTrace
r193HistoricalTree = MkRegistrationCorrespondenceByGeneration
  (MkRegistrationIndexState [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)] [] [] [MkRegistrationGeneration 1 2])
  (MkRegistrationIndexState [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 2)] [] [] [MkRegistrationGeneration 1 2])
  (SkipLeftNonRegistration (OInsert 0 Root r45Parent) r45ParentInsert (MoreTransitions r45Begin (MoreTransitions r45ChildInsert r193HistoricalContinuation)) Refl Refl
    (SkipRightNonRegistration (OInsert 0 Root r45Parent) r45ParentInsert (MoreTransitions r45Begin (MoreTransitions r45ChildInsert r193HistoricalContinuation)) Refl Refl
    (SkipLeftNonRegistration (LBegin 0) r45Begin (MoreTransitions r45ChildInsert r193HistoricalContinuation) Refl Refl
    (SkipRightNonRegistration (LBegin 0) r45Begin (MoreTransitions r45ChildInsert r193HistoricalContinuation) Refl Refl
    (DiscardLeftDeletedRegistration r45ChildInsert r193HistoricalContinuation Refl (MkDeletedClosingRegistration (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl (ActionOccursLater r178ParentFinish (MoreTransitions r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)))) (ActionOccursLater r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))) (ActionOccursLater r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)) (ActionOccursLater r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions) (ActionOccursHere r193HistoricalUnload NoTransitions Refl))))))
    (DiscardRightDeletedRegistration r45ChildInsert r193HistoricalContinuation Refl (MkDeletedClosingRegistration (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl (ActionOccursLater r178ParentFinish (MoreTransitions r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)))) (ActionOccursLater r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))) (ActionOccursLater r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)) (ActionOccursLater r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions) (ActionOccursHere r193HistoricalUnload NoTransitions Refl))))))
    (SkipLeftNonRegistration (LAdvance 0) r178ParentFinish (MoreTransitions r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)))) Refl Refl
    (SkipRightNonRegistration (LAdvance 0) r178ParentFinish (MoreTransitions r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)))) Refl Refl
    (SkipLeftNonRegistration (ORetire 1) r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))) Refl Refl
    (SkipRightNonRegistration (ORetire 1) r178ChildRetire (MoreTransitions r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions))) Refl Refl
    (SkipLeftNonRegistration (ORetire 0) r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)) Refl Refl
    (SkipRightNonRegistration (ORetire 0) r193HistoricalRetire (MoreTransitions r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions)) Refl Refl
    (SkipLeftNonRegistration (LLeave 0) r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions) Refl Refl
    (SkipRightNonRegistration (LLeave 0) r193HistoricalLeave (MoreTransitions r193HistoricalUnload NoTransitions) Refl Refl
    (SkipLeftNonRegistration (LUnload 0) r193HistoricalUnload NoTransitions Refl Refl
    (SkipRightNonRegistration (LUnload 0) r193HistoricalUnload NoTransitions Refl Refl
    (RegistrationCorrespondenceEnd)))))))))))))))))

||| ALL fields of the real present vestigial entry, including discarded-birth
||| membership owned by the actual scanner. Inactivity alone is never used.
public export
0 r193HistoricalVestigial : VestigialEndpointGeneration Nat R45Key Unit String R45Value
  r45NameEq r45KeyEq (leftFinalGenerations r193HistoricalTree)
  (leftDeletedGenerations r193HistoricalTree) 1 r193HistoricalClosed
r193HistoricalVestigial = MkVestigialEndpointGeneration (MkRegistrationGeneration 1 2)
  Refl Here r45ChildRetired Refl Refl Refl Refl Refl Refl

||| Primitive parent-role separation, independent of any computed fiber.
export
0 r193ChildNotRoot : {n : Nat} -> Not (ChildOf n = Root)
r193ChildNotRoot Refl impossible
