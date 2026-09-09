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

||| Eliminate only the explicit observed Nat, with its producer-owned exact
||| equation. No second evaluation or Boolean decision enters the proof.
public export
distanceSearchAtValue : {a : Type} -> (distance : a -> Nat) ->
  (head : a) -> (items : List a) -> (observed : Nat) ->
  (0 equation : distance head = observed) ->
  DistanceSearch distance items -> DistanceSearch distance (head :: items)
distanceSearchAtValue distance head items Z equation tail = distanceSearchThere head equation tail
distanceSearchAtValue distance head items (S predecessor) equation tail =
  FoundFirstPositive head [] items predecessor Here Refl [] equation

||| GENERAL executable first-positive search, in supplied list order.
||| Instantiating distance with rootDistance and items with scanRootCatalog
||| preserves orchestration order. Key-forcing and native swap construction
||| remain separate obligations: this producer does not claim either.
public export
searchDistance : {a : Type} -> (distance : a -> Nat) ->
  (items : List a) -> DistanceSearch distance items
searchDistance distance [] = AllDistancesZero []
searchDistance distance (head :: items) =
  distanceSearchAtValue distance head items (distance head) Refl (searchDistance distance items)

||| General bridge to the ACTUAL sum/map used by totalDistance. A zero scan
||| cannot conceal positive total distance. Proof induction is on All only.
export
0 allZeroTotal : {a : Type} -> (distance : a -> Nat) -> {items : List a} ->
  All (\item => distance item = 0) items -> sum (map distance items) = 0
allZeroTotal distance [] = Refl
allZeroTotal distance (zero :: zeros) = rewrite zero in allZeroTotal distance zeros

||| At positive total, decode the first positive item from the OBSERVED exact
||| search result. Instantiate the call site with searchDistance distance
||| items and Refl. Prefix/suffix are ordinary lists, not dependent state
||| views; the complete zero-prefix and physical list split are retained.
||| This is not ForcedOnTrace decoding or an AdmittedDistanceMove producer.
export
0 selectFirstPositiveObserved : {a : Type} -> (distance : a -> Nat) ->
  (items : List a) -> (observed : DistanceSearch distance items) ->
  (0 equation : searchDistance distance items = observed) ->
  (0 positive : LT 0 (sum (map distance items))) ->
  (item : a ** before : List a ** after : List a **
    (Elem item items, items = before ++ item :: after,
     All (\earlier => distance earlier = 0) before, LT 0 (distance item)))
selectFirstPositiveObserved distance items (AllDistancesZero zeros) equation positive =
  absurd (replace {p = \n => LT 0 n} (allZeroTotal distance zeros) positive)
selectFirstPositiveObserved distance items
  (FoundFirstPositive item before after predecessor member split zeros exact) equation positive =
  (item ** before ** after ** (member, split, zeros,
    replace {p = \n => LT 0 n} (sym exact) (LTESucc LTEZero)))
