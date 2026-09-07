module DGamma.R176WrongOriginalTraceUniqueNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import Decidable.Equality

%default total
%unbound_implicits off

||| Equal endpoints do not identify two whole original traces.
0 wrongOriginalTraceFreshness :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (otherTrace : Transitions initial leftFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 otherUnique : UniqueRawNameInsertions name key world error value nameEq keyEq otherTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
wrongOriginalTraceFreshness name key world error value nameEq keyEq protocol leftTrace rightTrace
  otherTrace sameInputs leftCapital rightCapital otherUnique rightUnique =
    canonicalSupportOrdersMatchSpike nameEq keyEq protocol leftTrace rightTrace
      sameInputs leftCapital rightCapital otherUnique rightUnique
