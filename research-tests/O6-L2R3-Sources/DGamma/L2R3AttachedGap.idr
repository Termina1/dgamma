module DGamma.L2R3AttachedGap

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2ConditionalGap
import DGamma.L2R3Attached
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Authenticated membership in an actual attached block's trailing bundle.
||| The core/trail split, native local occurrence and physical ordinal equation
||| are retained. Bounds are explicit redundant specifications, not gap-zero
||| assumptions; a producer must establish them for the actual occurrence.
public export
record AttachedBundleOccurrence
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkAttachedBundleOccurrence
  bundleActor : name
  containingBlock : LocatedOpenEpisodeBlockAttached name key world error value nameEq keyEq bundleActor global
  coreEnd : SystemState name key value world error
  memberCore : Transitions (attachedStart containingBlock) coreEnd
  0 memberExtended : ActorLifecycleOnlyExtended nameEq bundleActor memberCore
  memberBundle : Transitions coreEnd (attachedEnd containingBlock)
  0 memberForced : OrderedForcedRootBundle nameEq bundleActor memberCore [] memberBundle
  0 memberSplit : appendTransitions memberCore memberBundle = attachedBody containingBlock
  bundleOccurrence : LocatedActionOccurrence action memberBundle
  bundleOffset : Nat
  0 offsetExact : bundleOffset = transitionCount (attachedBefore containingBlock) + S (transitionCount memberCore)
  0 memberOrdinal : ordinal = bundleOffset + locatedActionOrdinal bundleOccurrence
  0 memberLowerBound : LTE bundleOffset ordinal
  0 memberUpperBound : LT ordinal (bundleOffset + transitionCount memberBundle)

||| Attached normal-form COVERAGE: every actual root-orchestration occurrence
||| in the gap region belongs to an authenticated bundle at the same physical
||| ordinal. This does not postulate NoRootOrchestration. Nonoverlap of bundles
||| and the residual gap is a SEPARATE schedule/decomposition obligation.
public export
record AttachedNormalForm
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState, gapFirst, gapFinal : SystemState name key value world error}
  (global : Transitions initial finalState)
  (gap : Transitions gapFirst gapFinal) (gapOffset : Nat) where
  constructor MkAttachedNormalForm
  0 rootInBundle : (action : Action name key value world error) ->
    (occurrence : LocatedActionOccurrence action gap) ->
    RootOrchestrationStep nameEq (locatedTransition occurrence) ->
    AttachedBundleOccurrence name key world error value nameEq keyEq global action
      (gapOffset + locatedActionOrdinal occurrence)
