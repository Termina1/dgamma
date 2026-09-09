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
