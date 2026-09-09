module DGamma.L2R12PhaseAccepted

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R9OrdinalScan
import DGamma.L2R10PhaseScan
import DGamma.L2R7ObservedAny
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Library all is an accumulator fold, dual to the inherited any decoder.
export
0 phaseAllFoldFalse : {a : Type} -> (predicate : a -> Bool) -> (items : List a) ->
  foldl (\acc, item => acc && predicate item) False items = False
phaseAllFoldFalse predicate [] = Refl
phaseAllFoldFalse predicate (head :: items) = phaseAllFoldFalse predicate items
