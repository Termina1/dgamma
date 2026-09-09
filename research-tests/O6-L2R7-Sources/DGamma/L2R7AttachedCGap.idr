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
