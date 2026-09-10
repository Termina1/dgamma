module DGamma.CP5O19AttachedPairsSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Seven production forms at the EXACT native source transition. Bundle
||| evidence is indexed by its original core, never relabelled to a replay cut.
||| No guard, diamond, swapped trace, row or desired result is stored here.
public export
data O19AttachedEdge :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  {coreFirst, coreLast : SystemState name key value world error} ->
  (core : Transitions coreFirst coreLast) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  AttachedLifecycle :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (0 lifecycle : isLifecycleAction (transitionAction step) = True) ->
    (0 owned : transitionActor step = actor) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedChildInsert :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction step = OInsert child (ChildOf actor) component) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedChildRetire :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf actor) ->
    (0 controlledAction : transitionAction step = ORetire controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedChildRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf actor) ->
    (0 controlledAction : transitionAction step = ORemove controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedRootInsert :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (root : name) -> (component : Component key value world error) ->
    (0 priorRoots : List name) ->
    (0 inserted : transitionAction step = OInsert root Root component) ->
    (0 forced : AttachedReason nameEq actor core priorRoots component) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedRootRetire :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 priorRoots : List name) -> (0 bundled : Elem controlled priorRoots) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) ->
    (0 controlledAction : transitionAction step = ORetire controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
  AttachedRootRemove :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} ->
    {coreFirst, coreLast, before, afterState : SystemState name key value world error} ->
    {core : Transitions coreFirst coreLast} -> {step : Transition before afterState} ->
    (controlled : name) -> (fiber : Fiber name key value world error) ->
    (0 priorRoots : List name) -> (0 bundled : Elem controlled priorRoots) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} controlled (registry before) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) ->
    (0 controlledAction : transitionAction step = ORemove controlled) ->
    O19AttachedEdge name key world error value nameEq actor core step
