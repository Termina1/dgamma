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

||| A tail member of a unique goal cannot equal the preceding goal name.
export
0 o20UniqueTailDifferent :
  {name : Type} -> {selected, head : name} -> {rest : List name} ->
  (UniqueKeys (head :: rest)) -> (Elem selected rest) -> (Not (selected = head))
o20UniqueTailDifferent {rest} (UniqueCons absent unique) member same =
  absent (replace {p = \chosen => Elem chosen rest} same member)

||| Genuine BeforeIn in the fixed unique goal DERIVES numeric descent.
||| No rank equation or arbitrary rank function is an input.
export
0 o20BeforeRankCrossing :
  {name : Type} -> {left, right : name} -> (nameEq : DecEq name) -> (goal : List name) ->
  (UniqueKeys goal) -> (BeforeIn left right goal) ->
  (rankCrossing (o20GoalRank nameEq goal right) (o20GoalRank nameEq goal left) = 1)
o20BeforeRankCrossing {left} {right} nameEq (_ :: rest) (UniqueCons absent unique) (BeforeHere member) =
  rewrite Builtin.fst (o20GoalRankObserved nameEq left left rest (decEq @{nameEq} left left) Refl) Refl in
  rewrite Builtin.snd (o20GoalRankObserved nameEq right left rest (decEq @{nameEq} right left) Refl)
    (o20UniqueTailDifferent (UniqueCons absent unique) member) in Refl
o20BeforeRankCrossing {left} {right} nameEq (head :: rest) (UniqueCons absent unique) (BeforeThere ordered) =
  rewrite Builtin.snd (o20GoalRankObserved nameEq left head rest (decEq @{nameEq} left head) Refl)
    (o20UniqueTailDifferent (UniqueCons absent unique) (Builtin.fst (o20BeforeMembers ordered))) in
  rewrite Builtin.snd (o20GoalRankObserved nameEq right head rest (decEq @{nameEq} right head) Refl)
    (o20UniqueTailDifferent (UniqueCons absent unique) (Builtin.snd (o20BeforeMembers ordered))) in
      o20BeforeRankCrossing nameEq rest unique ordered

||| Every unaffected actor sees the same total pair contribution.
export
0 o20CrossingSumSwap :
  (leading : List Nat) -> (left, right : Nat) -> (later : List Nat) -> (pivot : Nat) ->
  (foldr (+) Z (map (rankCrossing pivot) (leading ++ left :: right :: later)) =
   foldr (+) Z (map (rankCrossing pivot) (leading ++ right :: left :: later)))
o20CrossingSumSwap [] left right later pivot =
  rankPlusSwap (rankCrossing pivot left) (rankCrossing pivot right)
    (foldr (+) Z (map (rankCrossing pivot) later))
o20CrossingSumSwap (head :: rest) left right later pivot =
  cong (rankCrossing pivot head +) (o20CrossingSumSwap rest left right later pivot)
