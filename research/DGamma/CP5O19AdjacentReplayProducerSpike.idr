module DGamma.CP5O19AdjacentReplayProducerSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4TerminalRecovery
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B1: public lower-level internality, without opening any frozen private
||| helper or changing a visibility boundary. Single observed-root elimination.
public export
0 o19LifecycleInternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) ->
  (isLifecycleAction (transitionAction step) = True) ->
  RootOrchestrationStep nameEq step -> Void
o19LifecycleInternal nameEq step lifecycle (RootInsertStep action) =
  uninhabited (trans (sym (cong isLifecycleAction action)) lifecycle)
o19LifecycleInternal nameEq step lifecycle (RootRetireStep fiber found parent action) =
  uninhabited (trans (sym (cong isLifecycleAction action)) lifecycle)
o19LifecycleInternal nameEq step lifecycle (RootRemoveStep fiber found parent action) =
  uninhabited (trans (sym (cong isLifecycleAction action)) lifecycle)

||| B2: consume an actual paper activation constructor, not a Boolean oracle.
public export
0 o19ActivationInternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) -> PaperActivationStep step ->
  RootOrchestrationStep nameEq step -> Void
o19ActivationInternal nameEq step (PaperBeginStep action tag) =
  o19LifecycleInternal nameEq step (trans (cong isLifecycleAction action) Refl)
o19ActivationInternal nameEq step (PaperIterStep action tag) =
  o19LifecycleInternal nameEq step (trans (cong isLifecycleAction action) Refl)
o19ActivationInternal nameEq step (PaperFinishStep action tag) =
  o19LifecycleInternal nameEq step (trans (cong isLifecycleAction action) Refl)
