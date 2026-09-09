module DGamma.L2R6Iteration

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import Data.List
import Data.List.Elem
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Admitted predecessor shapes at the ACTUAL source of a located crossing.
||| Lifecycle has explicit Bool/equation; child controls carry real installed
||| fiber/parent evidence. Every owning actor/parent is foreign to the root.
||| No constructor admits an unplaced root-orchestration predecessor.
public export
data AdmittedCrossing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name -> name -> SystemState name key value world error -> Action name key value world error -> Type where
  CrossLifecycle : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root : name} -> {source : SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (observed : Bool) -> (0 equation : isLifecycleAction action = observed) -> (0 accepted : observed = True) ->
    (0 foreign : actionOwner action = root -> Void) -> AdmittedCrossing nameEq root source action
  CrossChildInsert : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} -> {source : SystemState name key value world error} ->
    {component : Component key value world error} ->
    (0 foreign : parent = root -> Void) -> AdmittedCrossing nameEq root source (OInsert child (ChildOf parent) component)
  CrossChildRetire : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} -> {source : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 ownChild : fiberParent fiber = ChildOf parent) -> (0 foreign : parent = root -> Void) ->
    AdmittedCrossing nameEq root source (ORetire child)
  CrossChildRemove : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} -> {source : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 ownChild : fiberParent fiber = ChildOf parent) -> (0 foreign : parent = root -> Void) ->
    AdmittedCrossing nameEq root source (ORemove child)
