module DGamma.R6OuterPollutionNegative

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality

%default total

||| One-level-up attack: wrap a legitimate sealed package in a fresh outer
||| existential after prefixing a pure swap/inverse loop, while reusing its old
||| operational realization.  The operational witness index must reject this.
0 wrapPollutedOuter :
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
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {middle : List name} ->
  (forward : AdjacentActorOrderSwap name
    (supportOrder (canonicalSchedule leftCapital)) middle) ->
  (backward : AdjacentActorOrderSwap name middle
    (supportOrder (canonicalSchedule leftCapital))) ->
  CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching ->
  CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching
wrapPollutedOuter forward backward base =
  MkCertifiedOperationalCanonicalPermutation
    (ActorPermutationStep forward
      (ActorPermutationStep backward (selectedActorPermutation base)))
    (operationalTargetFinal base)
    (operationalTargetTrace base)
    (operationalTargetBlocks base)
    (operationalTargetPremises base)
    (selectedPermutationRealized base)
