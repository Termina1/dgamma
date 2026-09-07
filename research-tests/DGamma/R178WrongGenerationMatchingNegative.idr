module DGamma.R178WrongGenerationMatchingNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Same traces are insufficient: A9 must use the accepted generation bijection.
0 wrongGenerationMatching :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (otherRenaming : RegistrationGenerationBijection name) ->
  (0 detached : GeneratedOrchestrationMatched name key world error value nameEq leftTrace rightTrace otherRenaming) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
wrongGenerationMatching name key world error value nameEq keyEq protocol leftTrace rightTrace sameInputs
  leftCapital rightCapital leftUnique rightUnique otherRenaming detached =
    canonicalSupportOrdersMatchSpike nameEq keyEq protocol leftTrace rightTrace sameInputs
      leftCapital rightCapital leftUnique rightUnique detached
