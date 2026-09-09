module DGamma.L2R15PhaseOccurrence

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R10PhaseScan
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The native event at the head of a physically indexed trail. Eliminating
||| the trail also reveals its forced transition index and genuine source.
export
0 phaseEventAtNativeHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (step : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (trail : AvailabilityTrace name key world error value (MoreTransitions step rest)) ->
  head' (phaseEvents nameEq trail) =
    Just (phaseActionOwner nameEq first (transitionAction step), isLifecycleAction (transitionAction step))
phaseEventAtNativeHead nameEq _ _
  (AvailabilityStep source (Fired ne ke action tag checked) rest later) = Refl
