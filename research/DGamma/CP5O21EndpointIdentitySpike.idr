module DGamma.CP5O21EndpointIdentitySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| R179 O21 identity only: the accepted LEFT scanner and actual endpoint
||| lookup authenticate the current birth BEFORE original uniqueness is used.
||| Any other actual insertion of that raw name has the same exact stamp.
export
0 acceptedLeftEndpointBirthIdentity :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations (generatedRegistrationTree sameInputs)) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just observed) ->
  (otherParent : Parent name) -> (otherComponent : Component key value world error) ->
  (otherBirth : LocatedActionOccurrence (OInsert selected otherParent otherComponent) left) ->
  (generation = MkRegistrationGeneration selected (locatedActionOrdinal otherBirth))
acceptedLeftEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
  selected generation current observed found otherParent otherComponent otherBirth =
    case acceptedLeftEndpointCurrentBirth name key world error value nameEq keyEq left right
      (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
      aligned empty unique selected generation current observed found of
      (parent ** birth ** authenticated) =>
        trans authenticated (cong (MkRegistrationGeneration selected)
          (uniqueInsertionPosition unique selected parent otherParent (fiberComponent observed) otherComponent birth otherBirth))

||| R179 O21 identity only: the accepted RIGHT scanner and actual endpoint
||| lookup authenticate the current birth BEFORE original uniqueness is used.
||| Any other actual insertion of that raw name has the same exact stamp.
export
0 acceptedRightEndpointBirthIdentity :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (rightFinalGenerations (generatedRegistrationTree sameInputs)) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry rightFinal) = Just observed) ->
  (otherParent : Parent name) -> (otherComponent : Component key value world error) ->
  (otherBirth : LocatedActionOccurrence (OInsert selected otherParent otherComponent) right) ->
  (generation = MkRegistrationGeneration selected (locatedActionOrdinal otherBirth))
acceptedRightEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
  selected generation current observed found otherParent otherComponent otherBirth =
    case acceptedRightEndpointCurrentBirth name key world error value nameEq keyEq left right
      (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
      aligned empty unique selected generation current observed found of
      (parent ** birth ** authenticated) =>
        trans authenticated (cong (MkRegistrationGeneration selected)
          (uniqueInsertionPosition unique selected parent otherParent (fiberComponent observed) otherComponent birth otherBirth))

||| A producer-owned exact stamp rules out the later-same-name escape.
||| This scalar step never infers an ordinal from raw-name equality alone.
export
0 exactBirthStampRejectsLater :
  (name : Type) -> (selected : name) ->
  (generation : RegistrationGeneration name) -> (ordinal : Nat) ->
  (generation = MkRegistrationGeneration selected ordinal) ->
  Not (LT (generationBirthOrdinal generation) ordinal)
exactBirthStampRejectsLater name selected generation ordinal exact later =
  LTImpliesNotGTE later
    (replace {p = \position => LTE ordinal position}
      (sym (cong generationBirthOrdinal exact)) reflexive)
