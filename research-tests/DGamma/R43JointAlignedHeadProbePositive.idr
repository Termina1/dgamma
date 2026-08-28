module DGamma.R43JointAlignedHeadProbePositive

import DGamma.Calculus
import DGamma.Metatheory
import Decidable.Equality

%default total

||| Probe representation for one source transition and the exact aligned
||| singleton that authenticates its stored dictionaries and checked equation.
||| The real O6 record remains private to the research spike.
data R43JointAlignedHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  MkR43JointAlignedHead :
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    (0 singleton : AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions
        (Fired {before} {afterState} nameEq keyEq action tag checked)
        NoTransitions)) ->
    R43JointAlignedHead name key world error value nameEq keyEq
      (Fired {before} {afterState} nameEq keyEq action tag checked)

r43BuildJoint :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq action tag checked)
r43BuildJoint nameEq keyEq action tag checked =
  MkR43JointAlignedHead action tag checked
    (AlignedStep action tag checked NoTransitions AlignedEnd)

r43BuildInsert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert actor parent component) before = Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq
      (OInsert actor parent component) tag checked)
r43BuildInsert nameEq keyEq actor parent component tag checked =
  r43BuildJoint nameEq keyEq (OInsert actor parent component) tag checked

r43BuildRetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (ORetire actor) tag checked)
r43BuildRetire nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (ORetire actor) tag checked

r43BuildRemove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (ORemove actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (ORemove actor) tag checked)
r43BuildRemove nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (ORemove actor) tag checked

r43BuildBegin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (LBegin actor) tag checked)
r43BuildBegin nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (LBegin actor) tag checked

r43BuildAdvance :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (LAdvance actor) tag checked)
r43BuildAdvance nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (LAdvance actor) tag checked

r43BuildDivert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LDivert actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (LDivert actor) tag checked)
r43BuildDivert nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (LDivert actor) tag checked

r43BuildLeave :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LLeave actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (LLeave actor) tag checked)
r43BuildLeave nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (LLeave actor) tag checked

r43BuildUnload :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} (LUnload actor) before =
    Just (tag, afterState)) ->
  R43JointAlignedHead name key world error value nameEq keyEq
    (Fired {before} {afterState} nameEq keyEq (LUnload actor) tag checked)
r43BuildUnload nameEq keyEq actor tag checked =
  r43BuildJoint nameEq keyEq (LUnload actor) tag checked

||| Coverage target for the second probe direction.
data R43HeadFamily =
    R43Insert
  | R43Retire
  | R43Remove
  | R43Begin
  | R43Advance
  | R43Divert
  | R43Leave
  | R43Unload

||| One dependent elimination over the joint package covers all eight action
||| constructors; there is no second correlated scrutinee.
r43EliminateJoint :
  R43JointAlignedHead name key world error value nameEq keyEq sourceStep ->
  R43HeadFamily
r43EliminateJoint (MkR43JointAlignedHead (OInsert _ _ _) _ _ _) = R43Insert
r43EliminateJoint (MkR43JointAlignedHead (ORetire _) _ _ _) = R43Retire
r43EliminateJoint (MkR43JointAlignedHead (ORemove _) _ _ _) = R43Remove
r43EliminateJoint (MkR43JointAlignedHead (LBegin _) _ _ _) = R43Begin
r43EliminateJoint (MkR43JointAlignedHead (LAdvance _) _ _ _) = R43Advance
r43EliminateJoint (MkR43JointAlignedHead (LDivert _) _ _ _) = R43Divert
r43EliminateJoint (MkR43JointAlignedHead (LLeave _) _ _ _) = R43Leave
r43EliminateJoint (MkR43JointAlignedHead (LUnload _) _ _ _) = R43Unload
