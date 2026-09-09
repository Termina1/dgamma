module DGamma.CP5O20NativeTargetAttachmentSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| A target guard indexed by ONE actual fiber value. This preserves its
||| dependent committed view while ordinary lookup equality changes the fiber
||| index; no equality between two dependent observation records is needed.
public export
data O20NativeReloadingTarget :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fibers : Registry name key value world error) -> Fiber name key value world error -> Type where
  O20TargetReloading :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {fibers : Registry name key value world error} ->
    {component : Component key value world error} -> {parent : Parent name} -> {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    {remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))} ->
    {older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)} ->
    {view : View name (dependencies (componentDependencies component))} ->
    (0 resolved : (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table (Reloading remaining older view)) fibers = Just view)) ->
    O20NativeReloadingTarget name key world error value nameEq keyEq fibers
      (MkFiber component parent retiredFlag table (Reloading remaining older view))

||| Each native paper Advance source owns its target. Transport that property
||| through equality of TWO EXPLICIT fiber values derived from their shared
||| primitive lookup, never through equality of dependent source records.
export
0 o20PaperSourceTargetAtFiber :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor : name} -> {tag : RuleTag} ->
  {before : SystemState name key value world error} ->
  PaperAdvanceSource name key world error value nameEq keyEq actor tag before ->
  (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before) = Just fiber) ->
  O20NativeReloadingTarget name key world error value nameEq keyEq (registry before) fiber
o20PaperSourceTargetAtFiber {name} {key} {world} {error} {value} {nameEq} {keyEq}
  (AdvanceSourceIter {fibers} Refl observedFound target) fiber found =
    replace {p = O20NativeReloadingTarget name key world error value nameEq keyEq fibers}
      (justInjective (trans (sym observedFound) found)) (O20TargetReloading target)
o20PaperSourceTargetAtFiber {name} {key} {world} {error} {value} {nameEq} {keyEq}
  (AdvanceSourceFinishEmpty {fibers} Refl observedFound target) fiber found =
    replace {p = O20NativeReloadingTarget name key world error value nameEq keyEq fibers}
      (justInjective (trans (sym observedFound) found)) (O20TargetReloading target)
o20PaperSourceTargetAtFiber {name} {key} {world} {error} {value} {nameEq} {keyEq}
  (AdvanceSourceFinishOne {fibers} Refl observedFound target) fiber found =
    replace {p = O20NativeReloadingTarget name key world error value nameEq keyEq fibers}
      (justInjective (trans (sym observedFound) found)) (O20TargetReloading target)

||| Eliminate the single native target constructor at known Reloading indices.
export
0 o20NativeReloadingTargetEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {fibers : Registry name key value world error} ->
  {component : Component key value world error} -> {parent : Parent name} -> {retiredFlag : Bool} ->
  {table : OwnedTable key value (componentProvisions component)} ->
  {remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))} ->
  {older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)} ->
  {view : View name (dependencies (componentDependencies component))} ->
  O20NativeReloadingTarget name key world error value nameEq keyEq fibers (MkFiber component parent retiredFlag table (Reloading remaining older view)) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table (Reloading remaining older view)) fibers = Just view)
o20NativeReloadingTargetEquation (O20TargetReloading resolved) = resolved
