module DGamma.CP5O20CanonicalBirthDispositionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5SupportedBirthCoverageSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| ALL canonical births, including unsupported/absent endpoint children, own
||| an authentic original scanner classification. The retained/closing Either
||| remains explicit; this is not a producer of the missing full triangle.
export
0 o20CanonicalOriginCoverage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (renaming : RegistrationGenerationBijection name) ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (selected, parent : name) -> (component : Component key value world error) ->
  LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule capital)) ->
  ClassifiedGeneratedBirth name key world error value Z left
    (leftScannedEvents (acceptedAuthenticatedRegistrationMatching name key world error value nameEq left right renaming registrations)) selected
o20CanonicalOriginCoverage {name} {key} {world} {error} {value} nameEq keyEq protocol renaming left right registrations capital selected parent component birth =
  acceptedLeftBirthCoverage name key world error value nameEq left right renaming registrations selected parent component
    (generatedRegistrationActionOccurrence (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth))

||| Authenticate the classifier's EXACT stamp against the supplied real birth.
||| Unique raw insertion positions close the raw-name-only classifier seam;
||| neither original endpoint presence nor support is needed.
export
0 o20CoveredOriginStamp :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (events : List (RegistrationEvent name key world error value)) ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedGeneratedRegistration selected parent component original) ->
  (coverage : ClassifiedGeneratedBirth name key world error value Z original events selected) ->
  eventChildGeneration (coveredEvent coverage) = registrationGeneration birth
o20CoveredOriginStamp original unique events selected parent component birth
  (MkClassifiedGeneratedBirth event childSame (MkScannedRegistrationBirth scanned stamp) classification) =
    case childSame of
      Refl => trans stamp (cong (MkRegistrationGeneration (eventChild event))
        (uniqueInsertionPosition unique (eventChild event) (ChildOf (eventParent event)) (ChildOf parent)
          (eventComponent event) component scanned (generatedRegistrationActionOccurrence birth)))
