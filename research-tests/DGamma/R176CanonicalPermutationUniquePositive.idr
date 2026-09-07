module DGamma.R176CanonicalPermutationUniquePositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameCanonicalCapital
import Decidable.Equality

%default total
%unbound_implicits off

||| Consumer of the exact chosen operational package, NOT a permutation producer.
export
0 canonicalPermutationTargetFresh :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching) ->
  (UniqueRawNameInsertions name key world error value nameEq keyEq (operationalTargetTrace operational))
canonicalPermutationTargetFresh name key world error value nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital leftUnique rightUnique matching operational =
    operationalPermutationUniqueInsertions name key world error value protocol nameEq keyEq
      (selectedPermutationRealized operational)
      (capitalCanonicalUniqueInsertions name key world error value protocol nameEq keyEq leftCapital leftUnique)
