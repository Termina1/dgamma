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
