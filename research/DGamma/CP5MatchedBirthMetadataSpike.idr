module DGamma.CP5MatchedBirthMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| The accepted left scanner authenticates the endpoint's EXACT static fields.
export
0 acceptedLeftEndpointMetadataBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (renaming : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming left right) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  (bindings (registry leftFirst) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations registrations) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just observed) ->
  (birth : LocatedActionOccurrence (OInsert selected (fiberParent observed) (fiberComponent observed)) left **
    generation = MkRegistrationGeneration selected (locatedActionOrdinal birth))
acceptedLeftEndpointMetadataBirth name key world error value nameEq keyEq left right renaming registrations aligned empty unique selected generation current observed found =
  currentBirthAtPrefixMetadata name key world error value nameEq keyEq left left NoTransitions
    (currentBirthTraceAppendEmpty name key world error value left) aligned empty unique selected generation
    (acceptedLeftCurrentBirth name key world error value nameEq left right renaming registrations selected generation current) observed found

