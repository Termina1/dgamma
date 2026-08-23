module DGamma.R6MixedScheduleNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality

%default total

0 mixedLeftSchedule :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  (leftCapital, otherLeft : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq keyEq
    (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
mixedLeftSchedule {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace} {sameInputs}
  leftCapital otherLeft rightCapital convergence =
    originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
      sameInputs otherLeft rightCapital convergence
