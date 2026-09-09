module DGamma.L2R11WordInventory

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6Iteration
import DGamma.L2R7ObservedAny
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Finite action-kind codes: Begin0, Advance1, Insert2, Retire3, Remove4,
||| Divert5, Leave6, Unload7. Components/names/tags do not affect the kind.
public export
actionKindCode : {name, key, world, error : Type} -> {value : key -> Type} ->
  Action name key value world error -> Nat
actionKindCode (LBegin actor) = 0
actionKindCode (LAdvance actor) = 1
actionKindCode (OInsert child parent component) = 2
actionKindCode (ORetire child) = 3
actionKindCode (ORemove child) = 4
actionKindCode (LDivert actor) = 5
actionKindCode (LLeave actor) = 6
actionKindCode (LUnload actor) = 7
