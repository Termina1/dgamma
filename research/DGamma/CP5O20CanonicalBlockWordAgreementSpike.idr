module DGamma.CP5O20CanonicalBlockWordAgreementSpike

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
import DGamma.CP5O20ProgramRoleWordSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Two actual blocks with a shared native Begin packet have equal lifecycle
||| words AUGMENTED by their actual end-of-block remainders. Whole-word roles
||| supply both body invariants. No end remainder is asserted empty, and no
||| generated-Insert ordering or whole occurrence synchronization is claimed.
export
0 o20SharedBlocksAugmentedRoleWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {renaming : NameBijection name} -> {selected : name} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} -> {rightTrace : Transitions initial rightFinal} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected leftTrace) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    (renameForward renaming selected) rightTrace) ->
  O20CanonicalTraceRoles leftTrace -> O20CanonicalTraceRoles rightTrace ->
  O20SharedBeginObservations name key world error value nameEq keyEq renaming selected
    (blockPreStart leftBlock) (blockStart leftBlock) (blockPreStart rightBlock) (blockStart rightBlock) ->
  ((o20ActorLifecycleRoleWord (blockActorOnly leftBlock) ++ o20FiberRoleRemainder
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (blockEnd leftBlock)))) =
   (o20ActorLifecycleRoleWord (blockActorOnly rightBlock) ++ o20FiberRoleRemainder
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (renameForward renaming selected) (registry (blockEnd rightBlock)))))
o20SharedBlocksAugmentedRoleWords {name} {key} {value} {world} {error} {nameEq} {renaming} {selected}
  leftBlock rightBlock leftRoles rightRoles
  (MkO20SharedBeginObservations component leftParent rightParent leftTable rightTable leftView rightView
    leftFound rightFound leftResolved rightResolved leftExact rightExact) =
    trans (sym (o20LocatedBlockRoleWordInvariant leftBlock leftRoles))
      (trans
        (the (o20FiberRoleRemainder
          (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (blockStart leftBlock))) =
          o20FiberRoleRemainder
          (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
            (renameForward renaming selected) (registry (blockStart rightBlock))))
          (rewrite sym leftExact in rewrite sym rightExact in
           rewrite lookupReplacedFiber @{nameEq} selected
             (MkFiber component leftParent False leftTable (Inactive Nothing))
             (MkFiber component leftParent False leftTable (Reloading (componentProgram component) id leftView))
             (registry (blockPreStart leftBlock)) leftFound in
           rewrite lookupReplacedFiber @{nameEq} (renameForward renaming selected)
             (MkFiber component rightParent False rightTable (Inactive Nothing))
             (MkFiber component rightParent False rightTable (Reloading (componentProgram component) id rightView))
             (registry (blockPreStart rightBlock)) rightFound in Refl))
        (o20LocatedBlockRoleWordInvariant rightBlock rightRoles))

||| Accepted-input per-actor AUGMENTED native-word agreement at the prescribed
||| operational permutation. Both whole-word role certificates and the shared
||| initial program are produced. End-of-block remainders remain explicit:
||| eliminating them, pairing Insert positions and constructing ordered,
||| occurrence-labelled whole histories are still separate obligations.
export
0 o20SelectedCanonicalAugmentedRoleWords :
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
  ((o20ActorLifecycleRoleWord (blockActorOnly (pairLeftBlock pair)) ++ o20FiberRoleRemainder
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (blockEnd (pairLeftBlock pair))))) =
   (o20ActorLifecycleRoleWord (blockActorOnly (pairRightBlock pair)) ++ o20FiberRoleRemainder
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (renameForward (expectedBridgeBijection sameInputs) selected) (registry (blockEnd (pairRightBlock pair))))))
o20SelectedCanonicalAugmentedRoleWords {nameEq} {keyEq} {protocol} {rightTrace} {rightCapital} {operational}
  execution leftUnique rightUnique pair =
    o20SharedBlocksAugmentedRoleWords (pairLeftBlock pair) (pairRightBlock pair)
      (o20WholePermutedCanonicalRoles operational)
      (o20WholeCanonicalRoles nameEq keyEq protocol rightTrace rightCapital)
      (o20SelectedCanonicalSharedBegins execution leftUnique rightUnique pair)
