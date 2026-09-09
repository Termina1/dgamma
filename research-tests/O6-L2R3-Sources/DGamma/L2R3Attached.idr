module DGamma.L2R3Attached

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual key-release evidence inside the extended core. The removed entry
||| belongs to selected and declares a key declared by the attached root.
||| LocatedActionOccurrence owns the native ORemove edge and its decomposition.
||| This is local release evidence, not a universal last-release selector.
public export
record AttachedRelease
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  {first, coreEnd : SystemState name key value world error}
  (core : Transitions first coreEnd)
  (component : Component key value world error) where
  constructor MkAttachedRelease
  releasedChild : name
  releasedFiber : Fiber name key value world error
  releaseOccurrence : LocatedActionOccurrence (ORemove releasedChild) core
  0 releaseFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    releasedChild (registry (actionBeforeState releaseOccurrence)) = Just releasedFiber
  0 releaseParent : fiberParent releasedFiber = ChildOf selected
  sharedProvision : key
  0 childDeclares : Elem sharedProvision (dependencies (componentProvisions (fiberComponent releasedFiber)))
  0 rootDeclares : Elem sharedProvision (dependencies (componentProvisions component))

||| Key-forced locally, or barrier-forced by a root already consumed by the
||| same ordered bundle. The initially empty history is supplied only by the
||| attached wrapper; arbitrary prior roots cannot seed an attached body.
public export
data AttachedReason :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, coreEnd : SystemState name key value world error} ->
  (core : Transitions first coreEnd) -> (priorRoots : List name) ->
  (component : Component key value world error) -> Type where
  KeyReleased :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    {component : Component key value world error} ->
    AttachedRelease name key world error value nameEq selected core component ->
    AttachedReason nameEq selected core priorRoots component
  EarlierForcedRoot :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected, earlier : name} ->
    {first, coreEnd : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    {component : Component key value world error} ->
    (0 earlierInBundle : Elem earlier priorRoots) ->
    AttachedReason nameEq selected core priorRoots component

||| A contiguous trail of checked root OInsert transitions in physical (hence
||| external orchestration) order. History grows only after consuming an
||| authenticated root edge; every new root has actual release/barrier evidence.
||| No arbitrary orchestration or lifecycle edge is admitted to this trail.
public export
data OrderedForcedRootBundle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, coreEnd : SystemState name key value world error} ->
  (core : Transitions first coreEnd) -> (priorRoots : List name) ->
  {bundleStart, finalState : SystemState name key value world error} ->
  Transitions bundleStart finalState -> Type where
  ForcedBundleEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, state : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    OrderedForcedRootBundle nameEq selected core priorRoots (NoTransitions {state})
  ForcedBundleStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, before, middle, finalState : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    (root : name) -> (component : Component key value world error) ->
    (step : Transition before middle) -> (rest : Transitions middle finalState) ->
    (0 inserted : transitionAction step = OInsert root Root component) ->
    (0 forced : AttachedReason nameEq selected core priorRoots component) ->
    (0 tail : OrderedForcedRootBundle nameEq selected core (root :: priorRoots) rest) ->
    OrderedForcedRootBundle nameEq selected core priorRoots (MoreTransitions step rest)

||| Research counterpart of CP3 ActorLifecycleOnly:1786. An extended actor
||| core, optionally followed by an ordered forced-root bundle starting with
||| EMPTY history. Release witnesses lie in that same core, hence physically
||| before every bundled root. No reverse coercion or normalization is claimed.
public export
data ActorLifecycleOnlyAttached :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  AttachedWithoutRoots :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, finalState : SystemState name key value world error} ->
    (core : Transitions first finalState) ->
    (0 extended : ActorLifecycleOnlyExtended nameEq selected core) ->
    ActorLifecycleOnlyAttached nameEq selected core
  AttachedWithRoots :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, finalState : SystemState name key value world error} ->
    (core : Transitions first coreEnd) ->
    (0 extended : ActorLifecycleOnlyExtended nameEq selected core) ->
    (bundle : Transitions coreEnd finalState) ->
    (0 orderedForced : OrderedForcedRootBundle nameEq selected core [] bundle) ->
    ActorLifecycleOnlyAttached nameEq selected (appendTransitions core bundle)

||| Sound extended-to-attached inclusion, adding no root and moving no edge.
export
0 extendedIntoAttached :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  ActorLifecycleOnlyExtended nameEq selected trace ->
  ActorLifecycleOnlyAttached nameEq selected trace
extendedIntoAttached {trace} extended = AttachedWithoutRoots trace extended

||| Compose CP5ActorLifecycleOnlyExtended's CP3:1786 inclusion with A5.
||| These are forward inclusions only; frozen blocks cannot absorb root inputs.
export
0 oldIntoAttached :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> {selected : name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  ActorLifecycleOnly selected trace -> ActorLifecycleOnlyAttached nameEq selected trace
oldIntoAttached nameEq old = extendedIntoAttached (actorLifecycleOnlyIntoExtended nameEq old)

||| CP3:1824 via Extended:94, with only body grammar changed to Attached.
||| Physical body and endpoint include the full trailing bundle. All installed,
||| decomposition, no-other-episode and final-active obligations are retained.
public export
record LocatedOpenEpisodeBlockAttached
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedOpenEpisodeBlockAttached
  attachedPreStart : SystemState name key value world error
  attachedStart : SystemState name key value world error
  attachedEnd : SystemState name key value world error
  attachedBefore : Transitions initial attachedPreStart
  attachedOpening : BeginStep nameEq keyEq selected attachedPreStart attachedStart
  attachedBody : Transitions attachedStart attachedEnd
  0 attachedInstalled : InstalledTrace name key world error value nameEq keyEq selected attachedBody
  0 attachedActorOnly : ActorLifecycleOnlyAttached nameEq selected attachedBody
  attachedAfter : Transitions attachedEnd finalState
  0 attachedNoEarlier : NoLifecycleBy selected attachedBefore
  0 attachedNoLater : NoLifecycleBy selected attachedAfter
  0 attachedActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 attachedDecomposition : appendTransitions attachedBefore
    (MoreTransitions (beginTransition attachedOpening)
      (appendTransitions attachedBody attachedAfter)) = global

||| CP3:1873 via CP5L2R1ExtendedZeroGap:19, retaining the same exact
||| physical-order equation. The gap starts AFTER the complete attached body;
||| it is not required to be empty.
public export
record BlockBeforeAttached
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (earlierName, laterName : name)
  (earlier : LocatedOpenEpisodeBlockAttached name key world error value nameEq keyEq earlierName global)
  (later : LocatedOpenEpisodeBlockAttached name key world error value nameEq keyEq laterName global) where
  constructor MkBlockBeforeAttached
  attachedBetweenBlocks : Transitions (attachedEnd earlier) (attachedPreStart later)
  0 attachedBlocksOrdered :
    appendTransitions (attachedBefore later)
      (MoreTransitions (beginTransition (attachedOpening later)) NoTransitions) =
    appendTransitions
      (appendTransitions (attachedBefore earlier)
        (MoreTransitions (beginTransition (attachedOpening earlier)) (attachedBody earlier)))
      (appendTransitions attachedBetweenBlocks
        (MoreTransitions (beginTransition (attachedOpening later)) NoTransitions))
