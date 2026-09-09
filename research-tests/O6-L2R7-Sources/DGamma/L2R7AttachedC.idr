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
