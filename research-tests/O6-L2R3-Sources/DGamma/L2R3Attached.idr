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
