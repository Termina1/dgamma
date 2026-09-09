module DGamma.L2R14AdjacentNative

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R6Iteration
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11LocatedCut
import DGamma.L2R12AlignedCut
import DGamma.L2R14CatalogQuery
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Two genuine dictionary-aligned native edges sharing their intermediate
||| state LITERALLY. Both physical occurrences and consecutive ordinals are
||| retained; no equality between unrelated dictionary values is presumed.
public export
record AlignedAdjacentNative
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (source : SystemState name key value world error)
  (leftAction, rightAction : Action name key value world error) (position : Nat) where
  constructor MkAlignedAdjacentNative
  leftNative : AlignedSourceAction name key world error value nameEq keyEq trace source leftAction position
  rightNative : AlignedSourceAction name key world error value nameEq keyEq trace
    (edgeTarget leftNative) rightAction (S position)
