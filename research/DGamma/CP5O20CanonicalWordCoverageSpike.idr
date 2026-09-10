module DGamma.CP5O20CanonicalWordCoverageSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20SupportedReferenceSpike
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

||| Every ordered pair of ACTUAL right canonical blocks owns the corresponding
||| physically ordered operational-left blocks at inverse-image actors. Both
||| BlockBefore values come from the two native decompositions. No zero gap,
||| equal block body word, or whole occurrence-history pairing is asserted.
export
0 o20CanonicalMappedBlocksOrdered :
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
  (earlier, later : name) ->
  (earlierIn : Elem earlier (supportOrder (canonicalSchedule rightCapital))) ->
  (laterIn : Elem later (supportOrder (canonicalSchedule rightCapital))) ->
  BeforeIn earlier later (supportOrder (canonicalSchedule rightCapital)) ->
  (BlockBefore name key world error value nameEq keyEq
    (operationalTargetTrace operational)
    ((renameBackward (currentNameBijection (endpointRenaming sameInputs))) earlier) ((renameBackward (currentNameBijection (endpointRenaming sameInputs))) later)
    (decomposedBlock (operationalTargetBlocks operational) ((renameBackward (currentNameBijection (endpointRenaming sameInputs))) earlier) (elemMap (renameBackward (currentNameBijection (endpointRenaming sameInputs))) earlierIn))
    (decomposedBlock (operationalTargetBlocks operational) ((renameBackward (currentNameBijection (endpointRenaming sameInputs))) later) (elemMap (renameBackward (currentNameBijection (endpointRenaming sameInputs))) laterIn)),
   BlockBefore name key world error value nameEq keyEq
    (canonicalTrace (canonicalSchedule rightCapital)) earlier later
    (decomposedBlock (canonicalActorBlockDecomposition rightCapital) earlier earlierIn)
    (decomposedBlock (canonicalActorBlockDecomposition rightCapital) later laterIn))
o20CanonicalMappedBlocksOrdered {sameInputs} {rightCapital} operational earlier later earlierIn laterIn ordered =
  (decomposedBlocksFollowOrder (operationalTargetBlocks operational)
    ((renameBackward (currentNameBijection (endpointRenaming sameInputs))) earlier) ((renameBackward (currentNameBijection (endpointRenaming sameInputs))) later)
    (elemMap (renameBackward (currentNameBijection (endpointRenaming sameInputs))) earlierIn) (elemMap (renameBackward (currentNameBijection (endpointRenaming sameInputs))) laterIn)
    (o20BeforeMap (renameBackward (currentNameBijection (endpointRenaming sameInputs))) ordered),
   decomposedBlocksFollowOrder (canonicalActorBlockDecomposition rightCapital)
    earlier later earlierIn laterIn ordered)
