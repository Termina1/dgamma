module DGamma.L2R14CatalogQuery

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6Iteration
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Shift a genuine catalog action query through exactly one physical head.
||| Both ordinal arithmetic and the native action query are retained.
export
0 catalogQueryThroughHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  (head : Action name key value world error) -> (word : List (Action name key value world error)) ->
  (entry : RootCatalogEntry name key world error value) -> (offset : Nat) ->
  (query : (position : Nat ** (catalogOrdinal entry = S offset + position,
    head' (drop position word) = Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))) ->
  (position : Nat ** (catalogOrdinal entry = offset + position,
    head' (drop position (head :: word)) = Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))
catalogQueryThroughHead head word entry offset (position ** (ordinal, action)) =
  (S position ** (trans ordinal (plusSuccRightSucc offset position), action))
