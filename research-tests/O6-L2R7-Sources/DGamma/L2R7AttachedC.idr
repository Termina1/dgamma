module DGamma.L2R7AttachedC

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R3Attached
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| New SAME-BUNDLE controls grammar. Native edges retain orchestration order.
||| The wrapper starts EMPTY; no arbitrary earlier-bundle history is trusted.
||| Cross-bundle controls require the OPEN authenticated prefix/generation
||| history connector. Local control witnesses also check actual source roots.
public export
data OrderedForcedRootBundleC :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, coreEnd : SystemState name key value world error} ->
  (core : Transitions first coreEnd) -> (priorRoots : List name) ->
  {bundleStart, finalState : SystemState name key value world error} ->
  Transitions bundleStart finalState -> Type where
  ForcedBundleEndC :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, state : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    OrderedForcedRootBundleC nameEq selected core priorRoots (NoTransitions {state})
  ForcedBundleInsertC :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, before, middle, finalState : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    (root : name) -> (component : Component key value world error) ->
    (step : Transition before middle) -> (rest : Transitions middle finalState) ->
    (0 inserted : transitionAction step = OInsert root Root component) ->
    (0 forced : AttachedReason nameEq selected core priorRoots component) ->
    (0 tail : OrderedForcedRootBundleC nameEq selected core (root :: priorRoots) rest) ->
    OrderedForcedRootBundleC nameEq selected core priorRoots (MoreTransitions step rest)

  ForcedBundleRetireC :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, before, middle, finalState : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    (root : name) -> (fiber : Fiber name key value world error) ->
    (step : Transition before middle) -> (rest : Transitions middle finalState) ->
    (0 alreadyBundled : Elem root priorRoots) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root (registry before) = Just fiber) ->
    (0 rootParent : fiberParent fiber = Root) ->
    (0 controlled : transitionAction step = ORetire root) ->
    (0 tail : OrderedForcedRootBundleC nameEq selected core priorRoots rest) ->
    OrderedForcedRootBundleC nameEq selected core priorRoots (MoreTransitions step rest)
  ForcedBundleRemoveC :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, before, middle, finalState : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    (root : name) -> (fiber : Fiber name key value world error) ->
    (step : Transition before middle) -> (rest : Transitions middle finalState) ->
    (0 alreadyBundled : Elem root priorRoots) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root (registry before) = Just fiber) ->
    (0 rootParent : fiberParent fiber = Root) ->
    (0 controlled : transitionAction step = ORemove root) ->
    (0 tail : OrderedForcedRootBundleC nameEq selected core priorRoots rest) ->
    OrderedForcedRootBundleC nameEq selected core priorRoots (MoreTransitions step rest)

||| The enlarged body is core ++ bundle-with-controls. EMPTY local history
||| prevents an arbitrary caller from inventing prior bundled roots.
public export
data ActorLifecycleOnlyAttachedC :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  AttachedWithoutRootsC :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, finalState : SystemState name key value world error} ->
    (core : Transitions first finalState) ->
    (0 extended : ActorLifecycleOnlyExtended nameEq selected core) ->
    ActorLifecycleOnlyAttachedC nameEq selected core
  AttachedWithRootsC :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, finalState : SystemState name key value world error} ->
    (core : Transitions first coreEnd) ->
    (0 extended : ActorLifecycleOnlyExtended nameEq selected core) ->
    (bundle : Transitions coreEnd finalState) ->
    (0 orderedForced : OrderedForcedRootBundleC nameEq selected core [] bundle) ->
    ActorLifecycleOnlyAttachedC nameEq selected (appendTransitions core bundle)

||| Sound forward inclusion: every original insertion-only bundle has the
||| new grammar, with identical edges and local history. No reverse coercion.
export
0 bundleIntoC : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {first, coreEnd, bundleStart, finalState : SystemState name key value world error} ->
  {core : Transitions first coreEnd} -> {priorRoots : List name} ->
  {bundle : Transitions bundleStart finalState} ->
  OrderedForcedRootBundle nameEq selected core priorRoots bundle ->
  OrderedForcedRootBundleC nameEq selected core priorRoots bundle
bundleIntoC ForcedBundleEnd = ForcedBundleEndC
bundleIntoC (ForcedBundleStep root component step rest inserted forced tail) =
  ForcedBundleInsertC root component step rest inserted forced (bundleIntoC tail)

||| Sound inclusion for the whole attached body, preserving the exact native
||| transition index. Old FrontNormal/NeverRetired statements stay unchanged.
export
0 attachedIntoC : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  ActorLifecycleOnlyAttached nameEq selected trace -> ActorLifecycleOnlyAttachedC nameEq selected trace
attachedIntoC (AttachedWithoutRoots core extended) = AttachedWithoutRootsC core extended
attachedIntoC (AttachedWithRoots core extended bundle ordered) =
  AttachedWithRootsC core extended bundle (bundleIntoC ordered)

||| Full located block for the NEW controls grammar. All installedness,
||| episode uniqueness, final activity and physical decomposition fields
||| retain their strength; controls are inside the body, not in the gap.
public export
record LocatedOpenEpisodeBlockAttachedC
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedOpenEpisodeBlockAttachedC
  attachedCPreStart : SystemState name key value world error
  attachedCStart : SystemState name key value world error
  attachedCEnd : SystemState name key value world error
  attachedCBefore : Transitions initial attachedCPreStart
  attachedCOpening : BeginStep nameEq keyEq selected attachedCPreStart attachedCStart
  attachedCBody : Transitions attachedCStart attachedCEnd
  0 attachedCInstalled : InstalledTrace name key world error value nameEq keyEq selected attachedCBody
  0 attachedCActorOnly : ActorLifecycleOnlyAttachedC nameEq selected attachedCBody
  attachedCAfter : Transitions attachedCEnd finalState
  0 attachedCNoEarlier : NoLifecycleBy selected attachedCBefore
  0 attachedCNoLater : NoLifecycleBy selected attachedCAfter
  0 attachedCActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 attachedCDecomposition : appendTransitions attachedCBefore
    (MoreTransitions (beginTransition attachedCOpening)
      (appendTransitions attachedCBody attachedCAfter)) = global

||| Physical order for complete attachedC bodies. The residual gap is an
||| actual native trace and is NOT defined or required to be empty.
public export
record BlockBeforeAttachedC
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (earlierName, laterName : name)
  (earlier : LocatedOpenEpisodeBlockAttachedC name key world error value nameEq keyEq earlierName global)
  (later : LocatedOpenEpisodeBlockAttachedC name key world error value nameEq keyEq laterName global) where
  constructor MkBlockBeforeAttachedC
  attachedCBetweenBlocks : Transitions (attachedCEnd earlier) (attachedCPreStart later)
  0 attachedCBlocksOrdered :
    appendTransitions (attachedCBefore later)
      (MoreTransitions (beginTransition (attachedCOpening later)) NoTransitions) =
    appendTransitions
      (appendTransitions (attachedCBefore earlier)
        (MoreTransitions (beginTransition (attachedCOpening earlier)) (attachedCBody earlier)))
      (appendTransitions attachedCBetweenBlocks
        (MoreTransitions (beginTransition (attachedCOpening later)) NoTransitions))
