module DGamma.L2R6ForcedScan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R3ForcedClosure
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Declaration overlap is eligible only for a child fiber, never a root.
||| Both sides use declared provisions, independent of lifecycle/table state.
public export
childDeclaredOverlap : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq key -> Component key value world error -> Parent name -> Component key value world error -> Bool
childDeclaredOverlap keyEq root Root child = False
childDeclaredOverlap keyEq root (ChildOf parent) child =
  provisionOverlap @{keyEq} (componentProvisions child) (componentProvisions root)

||| An absent fiber cannot release a declaration. Present fibers delegate to
||| the explicit parent classifier; no activity or retirement test is used.
public export
foundChildOverlap : {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq key -> Component key value world error -> Maybe (Fiber name key value world error) -> Bool
foundChildOverlap keyEq root Nothing = False
foundChildOverlap keyEq root (Just fiber) =
  childDeclaredOverlap keyEq root (fiberParent fiber) (fiberComponent fiber)
