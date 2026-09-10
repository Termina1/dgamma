module DGamma.CP5O19RootInputSeparationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19AttachedPairsSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Native occurrence elimination: no action-word or raw-name relabelling.
export
0 o19NoRootOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, last, before, afterState : SystemState name key value world error} ->
  {trace : Transitions first last} -> {step : Transition before afterState} ->
  NoRootOrchestration nameEq trace -> OccursIn step trace ->
  Not (RootOrchestrationStep nameEq step)
o19NoRootOccurrence (NoRootOrchestrationStep step rest excluded tail) OccursHere = excluded
o19NoRootOccurrence (NoRootOrchestrationStep step rest excluded tail) (OccursLater there) =
  o19NoRootOccurrence tail there
