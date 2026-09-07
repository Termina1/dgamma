module DGamma.CP5RootBirthCoverageSpike

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5SupportedBirthCoverageSpike
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
