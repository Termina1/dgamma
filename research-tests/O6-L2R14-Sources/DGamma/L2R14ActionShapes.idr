module DGamma.L2R14ActionShapes

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R12PacketContiguity
import DGamma.L2R14LocalOperations
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| A single authentic native edge to a raw per-action snapshot shape.
||| No equality between independent registry representation proofs is needed.
||| Record declaration alone is not a producer of these native shape premises.
public export
record NativeActionShape
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (source : SystemState name key value world error) (tag : RuleTag)
  (0 expected : RuntimeSnapshot name key world error value) where
  constructor MkNativeActionShape
  shapeTarget : SystemState name key value world error
  0 shapeChecked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, shapeTarget)
  0 shapeSnapshot : runtimeSnapshot shapeTarget = expected

||| Native determinism transports a raw operation shape to the ACTUAL
||| packet target. No target/source registry proof-record equality is assumed.
export
0 nativeActionShapeSnapshot : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {action : Action name key value world error} ->
  {source : SystemState name key value world error} -> {tag : RuleTag} ->
  {expected : RuntimeSnapshot name key world error value} ->
  (actual : SystemState name key value world error) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, actual)) ->
  (shape : NativeActionShape name key world error value nameEq keyEq action source tag expected) ->
  runtimeSnapshot actual = expected
nativeActionShapeSnapshot actual original shape =
  trans (cong runtimeSnapshot (cong snd (injective (trans (sym original) (shapeChecked shape)))))
    (shapeSnapshot shape)
