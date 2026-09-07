module DGamma.CP5AvailabilityAwarePlacement

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Declaration occupancy, exactly as in O-Insert: neither retirement nor
||| lifecycle inactivity makes a present provider's declared keys available.
public export
rootDeclaredProvisionsFree :
  (name, key, world, error : Type) -> (value : key -> Type) -> (keyEq : DecEq key) ->
  Component key value world error -> SystemState name key value world error -> Bool
rootDeclaredProvisionsFree name key world error value keyEq component state =
  provisionsDisjointFrom {name = name} {key = key} {value = value} {world = world} {error = error} @{keyEq}
    (componentProvisions component)
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state))

||| Root classification uses the ACTUAL source state for retire/remove.
public export
rootInputAtSource :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  Action name key value world error -> SystemState name key value world error -> Bool
rootInputAtSource name key world error value nameEq (OInsert actor Root component) state = True
rootInputAtSource name key world error value nameEq (OInsert actor (ChildOf parent) component) state = False
rootInputAtSource name key world error value nameEq (ORetire actor) state =
  case lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry state) of
    Nothing => False
    Just fiber => case fiberParent fiber of Root => True; ChildOf parent => False
rootInputAtSource name key world error value nameEq (ORemove actor) state =
  case lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry state) of
    Nothing => False
    Just fiber => case fiberParent fiber of Root => True; ChildOf parent => False
rootInputAtSource name key world error value nameEq (LBegin actor) state = False
rootInputAtSource name key world error value nameEq (LAdvance actor) state = False
rootInputAtSource name key world error value nameEq (LDivert actor) state = False
rootInputAtSource name key world error value nameEq (LLeave actor) state = False
rootInputAtSource name key world error value nameEq (LUnload actor) state = False
