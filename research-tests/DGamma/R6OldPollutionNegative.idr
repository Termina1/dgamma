module DGamma.R6OldPollutionNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality

%default total

||| The round-5 attack: keep public membership matching, inject any pure
||| certificate, and try to send it to O20.  Revision 6 should reject the pure
||| certificate where a sealed operational package is required.
0 oldPollutionReachesO20 :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (polluted : CertifiedActorPermutation name
    (supportOrder (canonicalSchedule leftCapital))
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital)))) ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching **
   CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational)
oldPollutionReachesO20 {nameEq} {keyEq} {protocol} {leftTrace} {rightTrace}
  {sameInputs} {leftCapital} {rightCapital} matching polluted =
    (polluted ** canonicalSchedulesConvergeSpike nameEq keyEq protocol leftTrace
      rightTrace sameInputs leftCapital rightCapital polluted)
