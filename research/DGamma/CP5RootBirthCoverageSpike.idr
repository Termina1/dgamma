module DGamma.CP5RootBirthCoverageSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5SupportedBirthCoverageSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Every observed root insertion has an authentic exact-name/component birth
||| in the other trace, selected by the accepted historical root correspondence.
export
0 rootBirthForwardObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (renaming : RegistrationGenerationBijection name) -> (leftOrdinal, rightOrdinal : Nat) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  ExternalRootBirthCorrespondence renaming leftOrdinal left rightOrdinal right ->
  (selected : name) -> (component : Component key value world error) -> (position : Nat) ->
  (rawClosingActionAt name key world error value position left = Just (OInsert selected Root component)) ->
  LocatedActionOccurrence (OInsert selected Root component) right
rootBirthForwardObserved name key world error value renaming leftOrdinal rightOrdinal _ _
  ExternalRootBirthCorrespondenceEnd selected component position observed = case observed of Refl impossible
rootBirthForwardObserved name key world error value renaming leftOrdinal rightOrdinal _ right
  (SkipLeftNonExternalRootBirth action step rest exact notRoot later) selected component Z observed =
    case trans (sym (cong isExternalRootBirthAction (trans (sym exact)
      (coveredHeadActionObserved name key world error value step rest (OInsert selected Root component) observed)))) notRoot of Refl impossible
rootBirthForwardObserved name key world error value renaming leftOrdinal rightOrdinal _ right
  (SkipLeftNonExternalRootBirth action step rest exact notRoot later) selected component (S position) observed =
    rootBirthForwardObserved name key world error value renaming (S leftOrdinal) rightOrdinal rest right later selected component position observed
rootBirthForwardObserved name key world error value renaming leftOrdinal rightOrdinal left _
  (SkipRightNonExternalRootBirth action step rest exact notRoot later) selected component position observed =
    currentBirthPrependLocation name key world error value step rest (OInsert selected Root component)
      (rootBirthForwardObserved name key world error value renaming leftOrdinal (S rightOrdinal) left rest later selected component position observed)
rootBirthForwardObserved name key world error value renaming leftOrdinal rightOrdinal _ _
  (MatchExternalRootBirth leftStep leftRest rightStep rightRest leftExact rightExact mapped later) selected component Z observed =
    MkLocatedActionOccurrence _ _ NoTransitions rightStep rightRest
      (trans rightExact (trans (sym leftExact)
        (coveredHeadActionObserved name key world error value leftStep leftRest (OInsert selected Root component) observed))) Refl
rootBirthForwardObserved name key world error value renaming leftOrdinal rightOrdinal _ _
  (MatchExternalRootBirth leftStep leftRest rightStep rightRest leftExact rightExact mapped later) selected component (S position) observed =
    currentBirthPrependLocation name key world error value rightStep rightRest (OInsert selected Root component)
      (rootBirthForwardObserved name key world error value renaming (S leftOrdinal) (S rightOrdinal) leftRest rightRest later selected component position observed)

||| Symmetric coverage from the SAME accepted correspondence (no free inverse).
export
0 rootBirthBackwardObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (renaming : RegistrationGenerationBijection name) -> (leftOrdinal, rightOrdinal : Nat) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  ExternalRootBirthCorrespondence renaming leftOrdinal left rightOrdinal right ->
  (selected : name) -> (component : Component key value world error) -> (position : Nat) ->
  (rawClosingActionAt name key world error value position right = Just (OInsert selected Root component)) ->
  LocatedActionOccurrence (OInsert selected Root component) left
rootBirthBackwardObserved name key world error value renaming leftOrdinal rightOrdinal _ _
  ExternalRootBirthCorrespondenceEnd selected component position observed = case observed of Refl impossible
rootBirthBackwardObserved name key world error value renaming leftOrdinal rightOrdinal left _
  (SkipRightNonExternalRootBirth action step rest exact notRoot later) selected component Z observed =
    case trans (sym (cong isExternalRootBirthAction (trans (sym exact)
      (coveredHeadActionObserved name key world error value step rest (OInsert selected Root component) observed)))) notRoot of Refl impossible
rootBirthBackwardObserved name key world error value renaming leftOrdinal rightOrdinal left _
  (SkipRightNonExternalRootBirth action step rest exact notRoot later) selected component (S position) observed =
    rootBirthBackwardObserved name key world error value renaming leftOrdinal (S rightOrdinal) left rest later selected component position observed
rootBirthBackwardObserved name key world error value renaming leftOrdinal rightOrdinal _ right
  (SkipLeftNonExternalRootBirth action step rest exact notRoot later) selected component position observed =
    currentBirthPrependLocation name key world error value step rest (OInsert selected Root component)
      (rootBirthBackwardObserved name key world error value renaming (S leftOrdinal) rightOrdinal rest right later selected component position observed)
rootBirthBackwardObserved name key world error value renaming leftOrdinal rightOrdinal _ _
  (MatchExternalRootBirth leftStep leftRest rightStep rightRest leftExact rightExact mapped later) selected component Z observed =
    MkLocatedActionOccurrence _ _ NoTransitions leftStep leftRest
      (trans leftExact (trans (sym rightExact)
        (coveredHeadActionObserved name key world error value rightStep rightRest (OInsert selected Root component) observed))) Refl
rootBirthBackwardObserved name key world error value renaming leftOrdinal rightOrdinal _ _
  (MatchExternalRootBirth leftStep leftRest rightStep rightRest leftExact rightExact mapped later) selected component (S position) observed =
    currentBirthPrependLocation name key world error value leftStep leftRest (OInsert selected Root component)
      (rootBirthBackwardObserved name key world error value renaming (S leftOrdinal) (S rightOrdinal) leftRest rightRest later selected component position observed)

export
0 rootBirthForwardLocated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (renaming : RegistrationGenerationBijection name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  ExternalRootBirthCorrespondence renaming Z left Z right ->
  (selected : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert selected Root component) left) ->
  LocatedActionOccurrence (OInsert selected Root component) right
rootBirthForwardLocated name key world error value renaming left right correspondence selected component birth =
  rootBirthForwardObserved name key world error value renaming Z Z left right correspondence selected component (locatedActionOrdinal birth)
    (rawClosingActionAtLocated name key world error value left (OInsert selected Root component) birth)

export
0 rootBirthBackwardLocated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (renaming : RegistrationGenerationBijection name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  ExternalRootBirthCorrespondence renaming Z left Z right ->
  (selected : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert selected Root component) right) ->
  LocatedActionOccurrence (OInsert selected Root component) left
rootBirthBackwardLocated name key world error value renaming left right correspondence selected component birth =
  rootBirthBackwardObserved name key world error value renaming Z Z left right correspondence selected component (locatedActionOrdinal birth)
    (rawClosingActionAtLocated name key world error value right (OInsert selected Root component) birth)

export
0 rootBirthFromEndpoint :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (bindings (registry first) = []) -> (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry finalState) = Just fiber) ->
  (fiberParent fiber = Root) -> LocatedActionOccurrence (OInsert selected Root (fiberComponent fiber)) trace
rootBirthFromEndpoint name key world error value nameEq keyEq trace aligned empty selected fiber found parentExact =
  replace {p = \owner => LocatedActionOccurrence (OInsert selected owner (fiberComponent fiber)) trace} parentExact
    (rawMetadataBirthAtPrefix name key world error value nameEq keyEq trace trace NoTransitions
      (currentBirthTraceAppendEmpty name key world error value trace) aligned empty selected fiber found)

export
0 rootEndpointMetadataFromBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (bindings (registry first) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (component : Component key value world error) ->
  LocatedActionOccurrence (OInsert selected Root component) trace -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry finalState) = Just fiber) ->
  ((fiberParent fiber, fiberComponent fiber) = (Root, component))
rootEndpointMetadataFromBirth name key world error value nameEq keyEq trace aligned empty unique selected component birth fiber found =
  uniqueRawBirthMetadata name key world error value nameEq keyEq trace unique selected (fiberParent fiber) Root (fiberComponent fiber) component
    (rawMetadataBirthAtPrefix name key world error value nameEq keyEq trace trace NoTransitions
      (currentBirthTraceAppendEmpty name key world error value trace) aligned empty selected fiber found) birth

||| Root-domain coverage plus exact immutable metadata under the ACCEPTED phi.
||| Retirement agreement and destination support remain separate obligations.
export
0 acceptedSupportedRootMetadataForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry initial) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (leftFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry leftFinal) = Just leftFiber) ->
  (fiberParent leftFiber = Root) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (rightFiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry rightFinal) = Just rightFiber,
     (fiberParent rightFiber, fiberComponent rightFiber) = (Root, fiberComponent leftFiber)))
acceptedSupportedRootMetadataForward name key world error value nameEq keyEq {rightFinal} left right sameInputs
  leftAligned rightAligned empty rightUnique selected leftFiber leftFound root supported =
    case acceptedSupportedForwardDomain name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty selected supported of
      (leftGeneration ** rightGeneration ** rightFiber ** (leftCurrent, rightCurrent, mapped, rightFound)) =>
        (rightFiber ** (rightFound,
          rootEndpointMetadataFromBirth name key world error value nameEq keyEq right rightAligned empty rightUnique selected (fiberComponent leftFiber)
            (rootBirthForwardLocated name key world error value (generatedGenerationBijection sameInputs) left right
              (externalRootGenerationsCoupled sameInputs) selected (fiberComponent leftFiber)
              (rootBirthFromEndpoint name key world error value nameEq keyEq left leftAligned empty selected leftFiber leftFound root)) rightFiber
            (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
              @{nameEq} actor (registry rightFinal) = Just rightFiber)} (leftLiveRootFixed (endpointRenaming sameInputs) selected leftFiber leftFound root) rightFound)))

export
0 acceptedSupportedRootMetadataBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry initial) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (rightFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} selected (registry rightFinal) = Just rightFiber) ->
  (fiberParent rightFiber = Root) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected rightFinal = True) ->
  (leftFiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) (registry leftFinal) = Just leftFiber,
     (fiberParent leftFiber, fiberComponent leftFiber) = (Root, fiberComponent rightFiber)))
acceptedSupportedRootMetadataBackward name key world error value nameEq keyEq {leftFinal} left right sameInputs
  leftAligned rightAligned empty leftUnique selected rightFiber rightFound root supported =
    case acceptedSupportedBackwardDomain name key world error value nameEq keyEq left right sameInputs leftAligned rightAligned empty selected supported of
      (rightGeneration ** leftGeneration ** leftFiber ** (rightCurrent, leftCurrent, mapped, leftFound)) =>
        (leftFiber ** (leftFound,
          rootEndpointMetadataFromBirth name key world error value nameEq keyEq left leftAligned empty leftUnique selected (fiberComponent rightFiber)
            (rootBirthBackwardLocated name key world error value (generatedGenerationBijection sameInputs) left right
              (externalRootGenerationsCoupled sameInputs) selected (fiberComponent rightFiber)
              (rootBirthFromEndpoint name key world error value nameEq keyEq right rightAligned empty selected rightFiber rightFound root)) leftFiber
            (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
              @{nameEq} actor (registry leftFinal) = Just leftFiber)} (rightLiveRootFixed (endpointRenaming sameInputs) selected rightFiber rightFound root) leftFound)))
