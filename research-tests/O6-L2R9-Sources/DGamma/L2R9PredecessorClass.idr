module DGamma.L2R9PredecessorClass

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R6Iteration
import DGamma.L2R9ControlClass
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Observed source/action sum for the future move producer. Foreign cases
||| carry admissibility evidence; root controls carry source-parent packets.
||| For ARBITRARY source/actions, local-actor and missing-binding outcomes
||| must remain explicit. Excluding those outcomes for a selected native
||| predecessor needs the native-adjacency/installedness linkage, not fiat.
public export
data PredecessorClass :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (root : name) ->
  (0 source : SystemState name key value world error) ->
  Action name key value world error -> Type where
  ForeignPredecessor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root : name} ->
    {0 source : SystemState name key value world error} ->
    {action : Action name key value world error} ->
    AdmittedCrossing nameEq root source action -> PredecessorClass nameEq root source action
  RootInsertPredecessor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, inserted : name} ->
    {0 source : SystemState name key value world error} ->
    {component : Component key value world error} ->
    PredecessorClass nameEq root source (OInsert inserted Root component)
  LocalLifecyclePredecessor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root : name} ->
    {0 source : SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (seen : Bool) -> (0 equation : isLifecycleAction action = seen) ->
    (0 accepted : seen = True) -> (0 owner : actionOwner action = root) ->
    PredecessorClass nameEq root source action
  LocalInsertPredecessor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} ->
    {0 source : SystemState name key value world error} ->
    {component : Component key value world error} ->
    (0 ownParent : parent = root) ->
    PredecessorClass nameEq root source (OInsert child (ChildOf parent) component)
  RetirePredecessor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child : name} ->
    {0 source : SystemState name key value world error} ->
    ControlClass nameEq root child source -> PredecessorClass nameEq root source (ORetire child)
  RemovePredecessor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child : name} ->
    {0 source : SystemState name key value world error} ->
    ControlClass nameEq root child source -> PredecessorClass nameEq root source (ORemove child)

||| Native lifecycle kind plus one observed owner/root Dec. A local actor
||| is returned explicitly, never silently coerced to a foreign crossing.
public export
lifecycleAtDifference : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (root : name) ->
  (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (seen : Bool) -> (0 lifeEquation : isLifecycleAction action = seen) -> (0 lifeAccepted : seen = True) ->
  (decision : Dec (actionOwner action = root)) ->
  (0 equation : decEq @{nameEq} (actionOwner action) root = decision) ->
  PredecessorClass nameEq root source action
lifecycleAtDifference nameEq root source action seen lifeEquation lifeAccepted (Yes same) equation =
  LocalLifecyclePredecessor seen lifeEquation lifeAccepted same
lifecycleAtDifference nameEq root source action seen lifeEquation lifeAccepted (No foreign) equation =
  ForeignPredecessor (CrossLifecycle seen lifeEquation lifeAccepted foreign)

||| Own-child insertion classification observes the ACTUAL parent/root Dec.
public export
insertAtDifference : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (root, child, parent : name) ->
  (source : SystemState name key value world error) ->
  (component : Component key value world error) ->
  (decision : Dec (parent = root)) -> (0 equation : decEq @{nameEq} parent root = decision) ->
  PredecessorClass nameEq root source (OInsert child (ChildOf parent) component)
insertAtDifference nameEq root child parent source component (Yes same) equation = LocalInsertPredecessor same
insertAtDifference nameEq root child parent source component (No foreign) equation =
  ForeignPredecessor (CrossChildInsert foreign)
