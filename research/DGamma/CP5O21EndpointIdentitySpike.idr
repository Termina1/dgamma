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

||| Original-trace identity capital, not endpoint withdrawal capital.
||| All fields are erased; no runtime state or undo handle is duplicated.
||| The producers below fix the environment to the ACCEPTED side scanner.
public export
record AcceptedEndpointBirthIdentity
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (environment : GenerationEnvironment name) (selected : name) where
  constructor MkAcceptedEndpointBirthIdentity
  0 endpointIdentityGeneration : RegistrationGeneration name
  0 endpointIdentityCurrent :
    (lookupCurrentGeneration @{nameEq} selected environment = Just endpointIdentityGeneration)
  0 endpointIdentityEveryBirth :
    (parent : Parent name) -> (component : Component key value world error) ->
    (birth : LocatedActionOccurrence (OInsert selected parent component) trace) ->
    (endpointIdentityGeneration = MkRegistrationGeneration selected (locatedActionOrdinal birth))
  0 endpointIdentityNoLaterBirth :
    (parent : Parent name) -> (component : Component key value world error) ->
    (birth : LocatedActionOccurrence (OInsert selected parent component) trace) ->
    Not (LT (generationBirthOrdinal endpointIdentityGeneration) (locatedActionOrdinal birth))

||| Derive the precise current LEFT generation from the actual endpoint lookup;
||| no current generation, historical birth or identity witness is a premise.
export
0 acceptedLeftEndpointIdentityCapital :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just observed) ->
  AcceptedEndpointBirthIdentity name key world error value nameEq left
    (leftFinalGenerations (generatedRegistrationTree sameInputs)) selected
acceptedLeftEndpointIdentityCapital name key world error value nameEq keyEq left right sameInputs aligned empty unique
  selected observed found =
    case acceptedLeftEndpointCurrent name key world error value nameEq keyEq left right
      (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
      aligned empty selected observed found of
      (generation ** current) => MkAcceptedEndpointBirthIdentity generation current
        (acceptedLeftEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
          selected generation current observed found)
        (\parent, component, birth => exactBirthStampRejectsLater name selected generation (locatedActionOrdinal birth)
          (acceptedLeftEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
            selected generation current observed found parent component birth))

||| Derive the precise current RIGHT generation from the actual endpoint lookup;
||| no current generation, historical birth or identity witness is a premise.
export
0 acceptedRightEndpointIdentityCapital :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry rightFinal) = Just observed) ->
  AcceptedEndpointBirthIdentity name key world error value nameEq right
    (rightFinalGenerations (generatedRegistrationTree sameInputs)) selected
acceptedRightEndpointIdentityCapital name key world error value nameEq keyEq left right sameInputs aligned empty unique
  selected observed found =
    case acceptedRightEndpointCurrent name key world error value nameEq keyEq left right
      (generatedGenerationBijection sameInputs) (generatedRegistrationTree sameInputs)
      aligned empty selected observed found of
      (generation ** current) => MkAcceptedEndpointBirthIdentity generation current
        (acceptedRightEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
          selected generation current observed found)
        (\parent, component, birth => exactBirthStampRejectsLater name selected generation (locatedActionOrdinal birth)
          (acceptedRightEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
            selected generation current observed found parent component birth))
