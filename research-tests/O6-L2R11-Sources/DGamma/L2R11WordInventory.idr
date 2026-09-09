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

||| Executable SET of kinds as a Boolean characteristic function. Repeated
||| occurrences do not change membership; inputs are the actual action word,
||| not an externally supplied list of allowed roles.
public export
wordActionInventory : {name, key, world, error : Type} -> {value : key -> Type} ->
  List (Action name key value world error) -> Nat -> Bool
wordActionInventory word code = any (\action => actionKindCode action == code) word

||| The native Nat comparison is reflexive on every actual action kind.
||| No unrestricted Nat-to-kind coercion or decider equality is assumed.
export
0 actionKindSelf : {name, key, world, error : Type} -> {value : key -> Type} ->
  (action : Action name key value world error) ->
  (actionKindCode action == actionKindCode action) = True
actionKindSelf (LBegin actor) = Refl
actionKindSelf (LAdvance actor) = Refl
actionKindSelf (OInsert child parent component) = Refl
actionKindSelf (ORetire child) = Refl
actionKindSelf (ORemove child) = Refl
actionKindSelf (LDivert actor) = Refl
actionKindSelf (LLeave actor) = Refl
actionKindSelf (LUnload actor) = Refl

||| A native head is in the inventory of its ACTUAL word. The left-fold
||| library bridge is applied to its actual observed comparison value.
export
0 wordInventoryHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  (action : Action name key value world error) ->
  (word : List (Action name key value world error)) ->
  wordActionInventory (action :: word) (actionKindCode action) = True
wordInventoryHead action word =
  trans (anyFoldObserved (\item => actionKindCode item == actionKindCode action) word
    (actionKindCode action == actionKindCode action))
    (rewrite actionKindSelf action in Refl)

||| Tail-domain inclusion is proved, not given to the replay fold as an
||| inventory oracle. This allows precisely the encountered suffix roles.
export
0 wordInventoryTail : {name, key, world, error : Type} -> {value : key -> Type} ->
  (head : Action name key value world error) ->
  (word : List (Action name key value world error)) -> (code : Nat) ->
  (0 accepted : wordActionInventory word code = True) ->
  wordActionInventory (head :: word) code = True
wordInventoryTail head word code accepted =
  trans (anyFoldObserved (\item => actionKindCode item == code) word (actionKindCode head == code))
    (rewrite accepted in orTrueTrue (actionKindCode head == code))

||| Actual-word inventory and its observed finite-domain subset check.
||| The flag is NOT assumed True: unsupported roles remain observable.
public export
record ObservedWordInventory
  {name, key, world, error : Type} {value : key -> Type}
  (word : List (Action name key value world error)) where
  constructor MkObservedWordInventory
  inventory : Nat -> Bool
  0 inventoryEquation : inventory = wordActionInventory word
  restrictedObserved : Bool
  0 restrictedEquation :
    all (\code => not (inventory code) || elemDec code [0, 1, 2, 3, 4]) [0, 1, 2, 3, 4, 5, 6, 7] = restrictedObserved
