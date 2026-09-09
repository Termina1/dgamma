module DGamma.L2R14LocalOperations

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.L2R10OrdinalData
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| Replacement commutes through a distinct fresh head, at the actual
||| observed library decision. Covers actor updates and child retirement;
||| this is raw registry algebra, never a native split Remove equation.
export
0 localReplaceFreshHead : {a : Type} -> (dictionary : DecEq Nat) ->
  (selected, fresh : Nat) -> (next, inserted : a) -> (entries : List (Binding Nat (\_ => a))) ->
  (0 distinct : selected = fresh -> Void) -> (decision : Dec (selected = fresh)) ->
  (0 equation : decEq @{dictionary} selected fresh = decision) ->
  replaceEntries @{dictionary} selected next (Bind fresh inserted :: entries) =
    Bind fresh inserted :: replaceEntries @{dictionary} selected next entries
localReplaceFreshHead dictionary selected fresh next inserted entries distinct (Yes same) equation = absurd (distinct same)
localReplaceFreshHead dictionary selected fresh next inserted entries distinct (No different) equation =
  rewrite equation in Refl

||| Deletion commutes through a distinct inserted head. The native library
||| decider is observed by its own equation; no checked Remove is evaluated.
export
0 localDeleteFreshHead : {a : Type} -> (dictionary : DecEq Nat) ->
  (removed, fresh : Nat) -> (inserted : a) -> (entries : List (Binding Nat (\_ => a))) ->
  (0 distinct : removed = fresh -> Void) -> (decision : Dec (removed = fresh)) ->
  (0 equation : decEq @{dictionary} removed fresh = decision) ->
  deleteEntries @{dictionary} removed (Bind fresh inserted :: entries) =
    Bind fresh inserted :: deleteEntries @{dictionary} removed entries
localDeleteFreshHead dictionary removed fresh inserted entries distinct (Yes same) equation = absurd (distinct same)
localDeleteFreshHead dictionary removed fresh inserted entries distinct (No different) equation =
  rewrite equation in Refl

||| Fixed-template fresh CHILD insertion is retired and erased after the two
||| foreign actor updates. All payloads and the underlying list are arbitrary.
||| Only concrete Nat key comparisons reduce; this never runs the evaluator.
export
0 localChildInsertRetireDelete : {a : Type} ->
  (child, begun, finished, retired : a) -> (entries : List (Binding Nat (\_ => a))) ->
  deleteEntries @{fst fixtureDictionaries} 5
    (replaceEntries @{fst fixtureDictionaries} 5 retired
      (replaceEntries @{fst fixtureDictionaries} 2 finished
        (replaceEntries @{fst fixtureDictionaries} 2 begun (Bind 5 child :: entries)))) =
  replaceEntries @{fst fixtureDictionaries} 2 finished (replaceEntries @{fst fixtureDictionaries} 2 begun entries)
localChildInsertRetireDelete child begun finished retired entries = Refl
