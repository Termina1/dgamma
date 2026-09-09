module DGamma.L2R5CurrentCut

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5L2R1ChildRelocation
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

||| Current-cut admissibility from the ORIGINAL checked root insertion only.
||| All source and component indices come from that native edge's own view.
export
0 checkedRootCurrentAvailable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) ->
  (first, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) first = Just (tag, afterState)) ->
  rootDeclaredProvisionsFree name key world error value keyEq component first = True
checkedRootCurrentAvailable nameEq keyEq root component (MkSystemState ambient source) afterState tag checked =
  rootCurrentFromView nameEq keyEq root component ambient source tag afterState
    (foreignInsertPlanView nameEq keyEq root Root component ambient source tag afterState
      (checkedActionProjects nameEq keyEq (OInsert root Root component)
        (MkSystemState ambient source) afterState tag checked))

||| For an admitted native swap, both the old and moved root source cuts are
||| declaration-free. The third equation retains the exact no-root-crossing
||| interval certificate. This transports CURRENT legality, not earliestness;
||| the supplied exchange remains responsible for producing the native square.
export
0 admittedSwapCurrentCuts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (0 rootChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) middle = Just (OInsertTag, finalState)) ->
  (exchange : AvailabilityRootSnapshotExchange name key world error value nameEq keyEq root component
    left (Fired {before = middle} {afterState = finalState} nameEq keyEq (OInsert root Root component) OInsertTag rootChecked)) ->
  (rootDeclaredProvisionsFree name key world error value keyEq component middle = True,
   rootDeclaredProvisionsFree name key world error value keyEq component first = True,
   rootCutCompatible name key world error value nameEq keyEq component 0
     (AvailabilityStep first left NoTransitions (AvailabilityEnd middle)) = True)
admittedSwapCurrentCuts nameEq keyEq root component left rootChecked exchange =
  (checkedRootCurrentAvailable nameEq keyEq root component middle finalState OInsertTag rootChecked,
   checkedRootCurrentAvailable nameEq keyEq root component first (snapshotRootMiddle exchange)
     OInsertTag (snapshotRootEarly exchange),
   snapshotRootCompatible exchange)
