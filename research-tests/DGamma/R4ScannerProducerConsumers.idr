module DGamma.R4ScannerProducerConsumers

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List.Elem
import Decidable.Equality

%default total

public export
0 leftWithdrawalWithoutScannerPremise :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule leftCapital))) ->
  Elem generation (leftDeletedGenerations (generatedRegistrationTree sameInputs))
leftWithdrawalWithoutScannerPremise nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital generation withdrawn =
    leftWithdrawnInAcceptedScanner
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
      generation withdrawn

public export
0 rightWithdrawalWithoutScannerPremise :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule rightCapital))) ->
  Elem generation (rightDeletedGenerations (generatedRegistrationTree sameInputs))
rightWithdrawalWithoutScannerPremise nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital generation withdrawn =
    rightWithdrawnInAcceptedScanner
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
      generation withdrawn

public export
0 acceptedCorrespondenceWithoutScannerPremise :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  RegistrationTraceCorrespondence nameEq
    (generatedGenerationBijection sameInputs)
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    leftTrace (leftFinalIndex (generatedRegistrationTree sameInputs))
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    rightTrace (rightFinalIndex (generatedRegistrationTree sameInputs)) [] []
acceptedCorrespondenceWithoutScannerPremise nameEq keyEq protocol leftTrace
  rightTrace sameInputs leftCapital rightCapital =
    acceptedRegistrationTrace
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
