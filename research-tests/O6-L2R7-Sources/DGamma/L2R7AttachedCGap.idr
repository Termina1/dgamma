module DGamma.L2R7AttachedCGap

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2ConditionalGap
import DGamma.L2R7AttachedC
import DGamma.L2R3AttachedGap
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Authenticated membership in an actual controls bundle, including local
||| root Retire/Remove. Exact source, body decomposition and bounds retained.
public export
record AttachedBundleOccurrenceC
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkAttachedBundleOccurrenceC
  cBundleActor : name
  cContainingBlock : LocatedOpenEpisodeBlockAttachedC name key world error value nameEq keyEq cBundleActor global
  cCoreEnd : SystemState name key value world error
  cMemberCore : Transitions (attachedCStart cContainingBlock) cCoreEnd
  0 cMemberExtended : ActorLifecycleOnlyExtended nameEq cBundleActor cMemberCore
  cMemberBundle : Transitions cCoreEnd (attachedCEnd cContainingBlock)
  0 cMemberForced : OrderedForcedRootBundleC nameEq cBundleActor cMemberCore [] cMemberBundle
  0 cMemberSplit : appendTransitions cMemberCore cMemberBundle = attachedCBody cContainingBlock
  cBundleOccurrence : LocatedActionOccurrence action cMemberBundle
  cBundleOffset : Nat
  0 cOffsetExact : cBundleOffset = transitionCount (attachedCBefore cContainingBlock) + S (transitionCount cMemberCore)
  0 cMemberOrdinal : ordinal = cBundleOffset + locatedActionOrdinal cBundleOccurrence
  0 cMemberLowerBound : LTE cBundleOffset ordinal
  0 cMemberUpperBound : LT ordinal (cBundleOffset + transitionCount cMemberBundle)

||| Coverage for the enlarged grammar; this is a specification, not a general
||| producer. Universal interval separation remains a separate obligation.
public export
record AttachedNormalFormC
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState, gapFirst, gapFinal : SystemState name key value world error}
  (global : Transitions initial finalState)
  (gap : Transitions gapFirst gapFinal) (gapOffset : Nat) where
  constructor MkAttachedNormalFormC
  0 cRootInBundle : (action : Action name key value world error) ->
    (occurrence : LocatedActionOccurrence action gap) ->
    RootOrchestrationStep nameEq (locatedTransition occurrence) ->
    AttachedBundleOccurrenceC name key world error value nameEq keyEq global action
      (gapOffset + locatedActionOrdinal occurrence)

||| Lifted conditional zero-gap theorem for complete attachedC blocks. Its
||| coverage, normal-form and universal separation premises retain the L2R3
||| strength. None is produced or assumed universally by this theorem.
export
0 attachedCZeroGapInNormalForm :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {earlierName, laterName : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (earlier : LocatedOpenEpisodeBlockAttachedC name key world error value nameEq keyEq earlierName global) ->
  (later : LocatedOpenEpisodeBlockAttachedC name key world error value nameEq keyEq laterName global) ->
  (ordered : BlockBeforeAttachedC name key world error value nameEq keyEq global earlierName laterName earlier later) ->
  {gapFirst, gapFinal : SystemState name key value world error} ->
  (gap : Transitions gapFirst gapFinal) -> (offset : Nat) ->
  (0 physical : transitionCount gap = transitionCount (attachedCBetweenBlocks ordered)) ->
  (0 offsetPhysical : offset = transitionCount (attachedCBefore earlier) + S (transitionCount (attachedCBody earlier))) ->
  (0 covered : RemainingGapHeadIsRoot nameEq gap) ->
  (0 normal : AttachedNormalFormC name key world error value nameEq keyEq global gap offset) ->
  (0 separated : (action : Action name key value world error) -> (ordinal : Nat) ->
    (member : AttachedBundleOccurrenceC name key world error value nameEq keyEq global action ordinal) ->
    Either (LTE (cBundleOffset member + transitionCount (cMemberBundle member)) offset)
      (LTE (offset + transitionCount gap) (cBundleOffset member))) ->
  transitionCount (attachedCBetweenBlocks ordered) = 0
attachedCZeroGapInNormalForm earlier later ordered NoTransitions offset physical offsetPhysical covered normal separated = sym physical
attachedCZeroGapInNormalForm {gapFirst} {gapFinal} earlier later ordered (MoreTransitions {middle} step rest) offset physical offsetPhysical covered normal separated =
  void (bundleOutsideHead offset (transitionCount rest) (cBundleOffset (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)) (transitionCount (cMemberBundle (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)))
    (replace {p = \n => LTE (cBundleOffset (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)) n} (plusZeroRightNeutral offset) (cMemberLowerBound (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)))
    (replace {p = \n => LT n (cBundleOffset (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered) + transitionCount (cMemberBundle (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)))} (plusZeroRightNeutral offset) (cMemberUpperBound (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)))
    (separated (transitionAction step) (offset + 0) (cRootInBundle normal (transitionAction step) (MkLocatedActionOccurrence gapFirst middle NoTransitions step rest Refl Refl) covered)))
