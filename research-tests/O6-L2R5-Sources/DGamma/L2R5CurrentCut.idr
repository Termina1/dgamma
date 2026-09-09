module DGamma.L2R5CurrentCut

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2RootSnapshot
import Decidable.Equality

%default total
%unbound_implicits off

||| Eliminate the actual native root-insertion view to obtain declaration
||| freedom at its source. Earliest-at-terminal is deliberately NOT asserted.
export
0 rootCurrentFromView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) -> (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  ForeignInsertPlanView name key world error value nameEq keyEq root Root
    component ambient source tag afterState ->
  rootDeclaredProvisionsFree name key world error value keyEq component
    (MkSystemState ambient source) = True
rootCurrentFromView nameEq keyEq root component ambient source _ _
  (MkForeignInsertPlanView absent guards) = guards
