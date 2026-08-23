module DGamma.R8WrongTraceBridgeNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

0 wrongTraceBridge :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal, otherFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (convergence : CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (otherTrace : Transitions initial otherFinal) ->
  (otherOccurrences : ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) otherTrace) ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital otherTrace otherOccurrences
    rightCapital
wrongTraceBridge convergence otherTrace otherOccurrences = convergenceBridge convergence
