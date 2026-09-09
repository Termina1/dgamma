module DGamma.L2R9ControlClass

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R6Iteration
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Executable source classification for Retire/Remove. Every positive
||| parent result owns the actual lookup and parent equation. Missing/local
||| cases remain explicit for arbitrary input data: neither is admitted.
public export
data ControlClass :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (root, child : name) ->
  (0 source : SystemState name key value world error) -> Type where
  MissingControl :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child : name} ->
    {0 source : SystemState name key value world error} ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Nothing) ->
    ControlClass nameEq root child source
  RootControl :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child : name} ->
    {0 source : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 parent : fiberParent fiber = Root) -> ControlClass nameEq root child source
  LocalChildControl :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child : name} ->
    {0 source : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf root) -> ControlClass nameEq root child source
  ForeignChildControl :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child : name} ->
    {0 source : SystemState name key value world error} ->
    (parent : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 ownChild : fiberParent fiber = ChildOf parent) ->
    (0 foreign : parent = root -> Void) -> ControlClass nameEq root child source
