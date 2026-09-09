module DGamma.L2R11LocatedCut

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R10MoveCutObservation
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A decoded physical source/action query, preserving native occurrence,
||| actual source identity and physical ordinal. No adjacency is asserted yet.
public export
record LocatedSourceAction
  (name, key, world, error : Type) (value : key -> Type)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (source : SystemState name key value world error)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkLocatedSourceAction
  occurrence : LocatedActionOccurrence action trace
  0 exactOrdinal : locatedActionOrdinal occurrence = ordinal
  0 exactSource : actionBeforeState occurrence = source
