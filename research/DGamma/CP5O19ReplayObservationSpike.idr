module DGamma.CP5O19ReplayObservationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B21: specialize the EXISTING producer-owned action fold. This observes
||| actual trace data; no execution outcome or replay target is guessed.
public export
0 o19ActionWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> List (Action name key value world error)
o19ActionWord {name} {key} {world} {error} {value} trace =
  traceActionFold name key world error value (List (Action name key value world error)) (::) [] trace
