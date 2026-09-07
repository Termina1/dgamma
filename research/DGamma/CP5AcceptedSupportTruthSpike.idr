module DGamma.CP5AcceptedSupportTruthSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5AllSupportedMetadataSpike
import DGamma.CP5AcceptedRetirementTransportSpike
import DGamma.CP5SupportClauseTransportSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Construct INTERNAL forward capital solely from the accepted original inputs
||| and the explicit A9 premise. No caller supplies destination support/metadata.
0 acceptedForwardSupportedClauseTransport :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq left -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  SupportedClauseTransport name key world error value nameEq keyEq leftFinal rightFinal (renameForward (currentNameBijection (endpointRenaming sameInputs)))
acceptedForwardSupportedClauseTransport name key world error value nameEq keyEq protocol left right sameInputs matched
  leftAligned rightAligned discipline empty leftUnique rightUnique =
    MkSupportedClauseTransport
      (acceptedAllSupportedMetadataForward name key world error value nameEq keyEq protocol left right sameInputs
        leftAligned rightAligned discipline empty leftUnique rightUnique)
      (acceptedSupportedForwardNotRetired name key world error value nameEq keyEq left right sameInputs matched
        leftAligned rightAligned empty leftUnique rightUnique)

0 acceptedBackwardSupportedClauseTransport :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq right -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  SupportedClauseTransport name key world error value nameEq keyEq rightFinal leftFinal (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
acceptedBackwardSupportedClauseTransport name key world error value nameEq keyEq protocol left right sameInputs matched
  leftAligned rightAligned discipline empty leftUnique rightUnique =
    MkSupportedClauseTransport
      (acceptedAllSupportedMetadataBackward name key world error value nameEq keyEq protocol left right sameInputs
        leftAligned rightAligned discipline empty leftUnique rightUnique)
      (acceptedSupportedBackwardNotRetired name key world error value nameEq keyEq left right sameInputs matched
        leftAligned rightAligned empty leftUnique rightUnique)

||| FIRST closed support-truth implication. All generated/root coverage, actual
||| retirement agreement and smaller-provider/parent recursion are producer-owned.
export
0 acceptedSupportedTruthForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq left -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
    (renameForward (currentNameBijection (endpointRenaming sameInputs)) selected) rightFinal = True)
acceptedSupportedTruthForward name key world error value nameEq keyEq protocol {rightFinal} left right sameInputs matched
  leftAligned rightAligned discipline empty leftUnique rightUnique =
    originalSupportedClauseTransport name key world error value nameEq keyEq protocol left leftAligned discipline empty rightFinal
      (renameForward (currentNameBijection (endpointRenaming sameInputs)))
      (acceptedForwardSupportedClauseTransport name key world error value nameEq keyEq protocol left right sameInputs matched
        leftAligned rightAligned discipline empty leftUnique rightUnique)

||| SECOND closed support-truth implication, using the same accepted bilateral
||| correspondence/A9 and the right ORIGINAL support-edge rank induction.
export
0 acceptedSupportedTruthBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  AlignedTransitions name key world error value nameEq keyEq left -> AlignedTransitions name key world error value nameEq keyEq right ->
  RegistrationDiscipline protocol nameEq right -> (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left -> UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected : name) -> (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected rightFinal = True) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq}
    (renameBackward (currentNameBijection (endpointRenaming sameInputs)) selected) leftFinal = True)
acceptedSupportedTruthBackward name key world error value nameEq keyEq protocol {leftFinal} left right sameInputs matched
  leftAligned rightAligned discipline empty leftUnique rightUnique =
    originalSupportedClauseTransport name key world error value nameEq keyEq protocol right rightAligned discipline empty leftFinal
      (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (acceptedBackwardSupportedClauseTransport name key world error value nameEq keyEq protocol left right sameInputs matched
        leftAligned rightAligned discipline empty leftUnique rightUnique)
