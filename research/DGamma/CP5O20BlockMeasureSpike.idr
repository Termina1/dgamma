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

||| Exact head/tail equations, owned by an EXPLICIT equality decision.
||| No inferred local view or computed dependent packet is eliminated.
export
0 o20GoalRankObserved :
  {name : Type} -> (nameEq : DecEq name) -> (selected, head : name) -> (rest : List name) ->
  (decision : Dec (selected = head)) -> (decEq @{nameEq} selected head = decision) ->
  (((selected = head) -> (o20GoalRank nameEq (head :: rest) selected = Z)),
   ((Not (selected = head)) -> (o20GoalRank nameEq (head :: rest) selected = S (o20GoalRank nameEq rest selected))))
o20GoalRankObserved nameEq selected head rest (Yes same) observed =
  (\equal => rewrite observed in Refl, \different => void (different same))
o20GoalRankObserved nameEq selected head rest (No different) observed =
  (\same => void (different same), \unequal => rewrite observed in Refl)
