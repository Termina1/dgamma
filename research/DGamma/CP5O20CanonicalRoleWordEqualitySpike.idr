module DGamma.CP5O20CanonicalRoleWordEqualitySpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20CanonicalPairSelectionSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5O20CanonicalWordCoverageSpike
import DGamma.CP5O20CanonicalBlockComponentSpike
import DGamma.CP5O20SharedBeginAdapterSpike
import DGamma.CP5O20CanonicalBlockWordAgreementSpike
import DGamma.CP5O20BlockEndRemainderSpike
import DGamma.CP5O20ProgramRoleWordSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Accepted selected block pairs have equal PLAIN lifecycle-role words.
||| Both body-end remainders are now PRODUCED empty from the actual aligned
||| blocks. Insert positions and whole occurrence synchronization are separate.
export
0 o20SelectedCanonicalRoleWords :
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
  {operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  (execution : PermutedCanonicalExecution name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital operational) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching operational selected) ->
  (o20ActorLifecycleRoleWord (blockActorOnly (pairLeftBlock pair)) =
   o20ActorLifecycleRoleWord (blockActorOnly (pairRightBlock pair)))
o20SelectedCanonicalRoleWords {name} {key} {value} {world} {error} {nameEq} {keyEq}
  {sameInputs} {rightCapital} {operational} {selected} execution leftUnique rightUnique pair =
    o20EraseEmptyAugmentation
      (o20ActorLifecycleRoleWord (blockActorOnly (pairLeftBlock pair)))
      (o20ActorLifecycleRoleWord (blockActorOnly (pairRightBlock pair)))
      (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        selected (registry (blockEnd (pairLeftBlock pair)))))
      (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (renameForward (expectedBridgeBijection sameInputs) selected) (registry (blockEnd (pairRightBlock pair)))))
      (o20LocatedBlockEndRemainderEmpty (pairLeftBlock pair) (replayAligned (operationalTargetPremises operational)))
      (o20LocatedBlockEndRemainderEmpty (pairRightBlock pair) (replayAligned (canonicalReplayPremises rightCapital)))
      (o20SelectedCanonicalAugmentedRoleWords execution leftUnique rightUnique pair)
