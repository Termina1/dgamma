module DGamma.L2R10SplitEdges

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R8ContiguityStates
import DGamma.L2R9SplitPacket
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| NEW abstract-state, ONE-equation family. Each native path edge is checked
||| separately; this is not the exhausted three-equation concrete producer.
public export
record SplitNativeEdge
  (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String)
  (from, to : Nat) (action : Action Nat Bool (\key => Unit) Unit String)
  (tag : RuleTag) where
  constructor MkSplitNativeEdge
  0 splitEdgeChecked : checkedApplyAction @{%search} @{%search} action (states from) = Just (tag, states to)
