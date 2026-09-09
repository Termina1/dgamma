module DGamma.L2R10MoveCutObservation

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R8DistanceSearch
import DGamma.L2R9ControlClass
import DGamma.L2R9PredecessorClass
import DGamma.L2R9NativeSelection
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Actual source/action word, preserving every physical transition position.
||| This is executable data, not a caller-supplied predecessor/catalog oracle.
public export
trailSourceActions : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 initial, finalState : SystemState name key value world error} ->
  {0 trace : Transitions initial finalState} ->
  AvailabilityTrace name key world error value trace ->
  List (SystemState name key value world error, Action name key value world error)
trailSourceActions (AvailabilityEnd state) = []
trailSourceActions (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  (source, action) :: trailSourceActions later
