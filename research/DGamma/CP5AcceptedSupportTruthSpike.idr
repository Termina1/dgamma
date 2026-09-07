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
