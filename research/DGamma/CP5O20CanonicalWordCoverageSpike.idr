module DGamma.CP5O20CanonicalWordCoverageSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The WHOLE actual operational-left word has canonical native roles. The
||| classifier uses this execution's OWN decomposition and replay premises;
||| it does not equate either word or manufacture cross-trace stage pairing.
export
0 o20WholePermutedCanonicalRoles :
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
  (operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching) ->
  O20CanonicalTraceRoles (operationalTargetTrace operational)
o20WholePermutedCanonicalRoles {nameEq} {keyEq} {protocol} {sameInputs} {rightCapital} operational =
  o20RolesFromLocations (operationalTargetTrace operational)
    (\action, location => o20DecomposedActionObserved nameEq keyEq protocol
      (operationalTargetTrace operational)
      (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
        (supportOrder (canonicalSchedule rightCapital)))
      (operationalTargetBlocks operational) (operationalTargetPremises operational)
      action location (isLifecycleAction action) Refl)
