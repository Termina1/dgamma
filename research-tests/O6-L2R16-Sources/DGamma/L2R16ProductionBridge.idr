module DGamma.L2R16ProductionBridge

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Executable identity-on-native-data bridge from PRODUCTION snapshots to
||| the existing research scanners. No state, action or trace is changed;
||| only the nominal snapshot constructors differ. The trace index stays 0.
public export
researchAvailability : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DGamma.CP3.AvailabilityTrace name key world error value trace ->
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace
researchAvailability (DGamma.CP3.AvailabilityEnd state) =
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd state
researchAvailability (DGamma.CP3.AvailabilityStep first step rest later) =
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep first step rest (researchAvailability later)
