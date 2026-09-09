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
