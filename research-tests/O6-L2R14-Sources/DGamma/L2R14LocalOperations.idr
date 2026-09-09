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
