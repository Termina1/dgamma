module DGamma.L2R15NativeInsertShape

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.L2R13InsertExtensional
import DGamma.L2R14ActionShapes
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Arbitrary-state insert shape from the AUTHENTIC raw operation view.
||| Native insertion itself supplies freshness and canonical target; neither
||| target equality nor an extra freshness premise is assumed. Root and Child
||| use this same registry definition. No fixture state is normalized.
export
0 nativeInsertShapeFromView : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (target : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (OInsert actor parent component)
    (MkSystemState ambient source) = Just (tag, target)) ->
  ForeignInsertPlanView name key world error value nameEq keyEq actor parent component ambient source tag target ->
  NativeActionShape name key world error value nameEq keyEq (OInsert actor parent component)
    (MkSystemState ambient source) tag
    (MkRuntimeSnapshot ambient (Bind actor (freshFiber component parent) :: bindings source))
nativeInsertShapeFromView nameEq keyEq actor parent component ambient source _ _ checked
  (MkForeignInsertPlanView absent guards) =
  MkNativeActionShape (MkSystemState ambient (insertBinding @{nameEq} actor (freshFiber component parent) source absent))
    checked (freshInsertSnapshot nameEq actor (freshFiber component parent) ambient source absent)
