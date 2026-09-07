module DGamma.R179O21WrongOriginalBirthNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O21EndpointIdentitySpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Same endpoints and raw actor are NOT authentication of the original trace.
0 wrongOriginalBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (other : Transitions initial leftFinal) ->
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
  (otherBirth : LocatedActionOccurrence (OInsert selected otherParent otherComponent) other) ->
  (generation = MkRegistrationGeneration selected (locatedActionOrdinal otherBirth))
wrongOriginalBirth name key world error value nameEq keyEq left right other sameInputs aligned empty unique
  selected generation current observed found otherParent otherComponent otherBirth =
    acceptedLeftEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs aligned empty unique
      selected generation current observed found otherParent otherComponent otherBirth
