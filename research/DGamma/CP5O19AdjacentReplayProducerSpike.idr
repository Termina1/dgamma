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

||| B3: exact four-node external evidence for the SAME diamond. Nothing about
||| root placement or independently invented moved transitions is assumed.
public export
0 o19ActivationPairExternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  PaperActivationStep left -> PaperActivationStep right ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
o19ActivationPairExternal nameEq keyEq left right leftActivation rightActivation diamond =
  SkipLeftInternal left (MoreTransitions right NoTransitions)
    (o19ActivationInternal nameEq left leftActivation)
    (SkipLeftInternal right NoTransitions (o19ActivationInternal nameEq right rightActivation)
      (SkipRightInternal (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
        (o19ActivationInternal nameEq (movedRight diamond) (movedRightActivationBranch diamond rightActivation))
        (SkipRightInternal (movedLeft diamond) NoTransitions
          (o19ActivationInternal nameEq (movedLeft diamond) (movedLeftActivationBranch diamond leftActivation))
          SameExternalOrchestrationEnd)))
