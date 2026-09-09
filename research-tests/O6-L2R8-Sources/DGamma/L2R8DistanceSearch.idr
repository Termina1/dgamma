module DGamma.L2R8DistanceSearch

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Nat

%default total
%unbound_implicits off

||| Computational result of the ordered distance scan. A success owns the
||| exact list decomposition and zero distance of EVERY earlier entry. This
||| does not identify a positive root's key-forcing or prove move existence.
public export
data DistanceSearch : {a : Type} -> (distance : a -> Nat) -> List a -> Type where
  AllDistancesZero : {a : Type} -> {distance : a -> Nat} -> {items : List a} ->
    (0 zeros : All (\item => distance item = 0) items) -> DistanceSearch distance items
  FoundFirstPositive : {a : Type} -> {distance : a -> Nat} -> {items : List a} ->
    (item : a) -> (before, after : List a) -> (predecessor : Nat) ->
    (0 member : Elem item items) -> (0 split : items = before ++ item :: after) ->
    (0 earlierZero : All (\earlier => distance earlier = 0) before) ->
    (0 positiveEquation : distance item = S predecessor) -> DistanceSearch distance items

||| A verified zero head preserves the first positive result in the tail.
||| Only the typed search result is eliminated; no inferred dependent view.
public export
distanceSearchThere : {a : Type} -> {distance : a -> Nat} -> {items : List a} ->
  (head : a) -> (0 zero : distance head = 0) ->
  DistanceSearch distance items -> DistanceSearch distance (head :: items)
distanceSearchThere head zero (AllDistancesZero zeros) = AllDistancesZero (zero :: zeros)
distanceSearchThere head zero (FoundFirstPositive item before after predecessor member split zeros equation) =
  FoundFirstPositive item (head :: before) after predecessor (There member)
    (cong (head ::) split) (zero :: zeros) equation
