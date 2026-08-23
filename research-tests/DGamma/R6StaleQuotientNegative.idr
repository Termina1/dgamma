module DGamma.R6StaleQuotientNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

0 staleQuotient :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (firstOp, secondOp : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching) ->
  (first : PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital firstOp) ->
  (second : PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital secondOp) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq
    (canonicalFinal (canonicalSchedule leftCapital)) (operationalTargetFinal secondOp)
staleQuotient firstOp secondOp first second = composedPermutationEndpoint first
