module DGamma.L2R10PhaseScan

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R9OrdinalScan
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Own-child actor observation. Root controls never count as actor core.
public export
phaseParentOwner : {name : Type} -> Parent name -> Maybe name
phaseParentOwner Root = Nothing
phaseParentOwner (ChildOf actor) = Just actor

||| Observe the actual installed fiber before classifying a control owner.
public export
phaseControlOwner : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child : name) ->
  (source : SystemState name key value world error) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry source) = found) -> Maybe name
phaseControlOwner nameEq child source Nothing equation = Nothing
phaseControlOwner nameEq child source (Just fiber) equation = phaseParentOwner (fiberParent fiber)

||| Exhaustive executable actor-core classifier, authentic to each source.
||| Lifecycle ownership, yielded child inserts, and installed child controls
||| qualify. A root birth/control or missing control fiber breaks the core.
public export
phaseActionOwner : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (source : SystemState name key value world error) ->
  Action name key value world error -> Maybe name
phaseActionOwner nameEq source (OInsert child parent component) = phaseParentOwner parent
phaseActionOwner {name} {key} {world} {error} {value} nameEq source (ORetire child) =
  phaseControlOwner nameEq child source
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source)) Refl
phaseActionOwner {name} {key} {world} {error} {value} nameEq source (ORemove child) =
  phaseControlOwner nameEq child source
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source)) Refl
phaseActionOwner nameEq source (LBegin actor) = Just actor
phaseActionOwner nameEq source (LAdvance actor) = Just actor
phaseActionOwner nameEq source (LDivert actor) = Just actor
phaseActionOwner nameEq source (LUnload actor) = Just actor
phaseActionOwner nameEq source (LLeave actor) = Just actor

||| Data word from the native source-aware trail. Positions remain physical
||| transition ordinals; the lifecycle flag is the actual action classifier.
public export
phaseEvents : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> AvailabilityTrace name key world error value trace ->
  List (Maybe name, Bool)
phaseEvents nameEq (AvailabilityEnd state) = []
phaseEvents nameEq (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  (phaseActionOwner nameEq source action, isLifecycleAction action) :: phaseEvents nameEq later
