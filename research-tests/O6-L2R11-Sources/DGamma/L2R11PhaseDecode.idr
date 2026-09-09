module DGamma.L2R11PhaseDecode

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R10PhaseScan
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Decode the ACTUAL event-owner classifier into its native child parent.
||| Only the parent is eliminated; Just injectivity preserves owner identity.
export
0 phaseParentDecoded : {name : Type} -> (parent : Parent name) -> (actor : name) ->
  (0 equation : phaseParentOwner parent = Just actor) -> parent = ChildOf actor
phaseParentDecoded Root actor equation = absurd equation
phaseParentDecoded (ChildOf owner) actor equation = cong ChildOf (injective equation)

||| Decode a control event's observed lookup into the SAME installed fiber
||| and own-child parent. The continuation receives data, not a semantic oracle.
export
0 phaseControlDecoded : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child, actor : name) ->
  (source : SystemState name key value world error) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry source) = found) ->
  (0 owner : phaseControlOwner nameEq child source found equation = Just actor) ->
  (0 result : Type) ->
  (0 done : (fiber : Fiber name key value world error) ->
    (0 nativeFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
      child (registry source) = Just fiber) ->
    (0 nativeParent : fiberParent fiber = ChildOf actor) -> result) -> result
phaseControlDecoded nameEq child actor source Nothing equation owner result done = absurd owner
phaseControlDecoded nameEq child actor source (Just fiber) equation owner result done =
  done fiber equation (phaseParentDecoded (fiberParent fiber) actor owner)
