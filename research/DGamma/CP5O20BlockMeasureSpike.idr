module DGamma.CP5O20BlockMeasureSpike

import DGamma.Core
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceWorkMeasureSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20LinearExtensionSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Finite first-position rank in ONE fixed goal. An absent name receives
||| length goal; later membership lemmas exclude that sentinel where needed.
public export
o20GoalRank : {name : Type} -> (nameEq : DecEq name) -> (goal : List name) -> (selected : name) -> Nat
o20GoalRank nameEq [] selected = Z
o20GoalRank nameEq (head :: rest) selected =
  case decEq @{nameEq} selected head of
    Yes same => Z
    No different => S (o20GoalRank nameEq rest selected)
