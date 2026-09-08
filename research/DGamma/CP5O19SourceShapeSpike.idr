module DGamma.CP5O19SourceShapeSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressProgramBound
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual installation evolution plus paper activation rules forces owner
||| survival. The impossible preserved-uninstalled Advance contradicts its
||| real installed source, not a precomputed target-presence assumption.
export
0 o19ActivationEvolutionInstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (first, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, afterState)) ->
  InstallationEvolution name key world error value nameEq keyEq (actionOwner action) first afterState action tag ->
  PaperActivationStep (Fired {before = first} {afterState} nameEq keyEq action tag checked) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) afterState = True)
o19ActivationEvolutionInstalled nameEq keyEq first afterState action tag checked
  (RemainedInstalled beforeInstalled afterInstalled) activation = afterInstalled
o19ActivationEvolutionInstalled nameEq keyEq first afterState action tag checked
  (RemainedUninstalled beforeUninstalled afterUninstalled) activation =
    case activation of
      PaperBeginStep {actor} sameAction sameTag => case sameAction of
        Refl => snd (snd (lBeginBoundary nameEq keyEq actor first afterState tag checked))
      PaperIterStep {actor} sameAction sameTag => case sameAction of
        Refl => void (uninhabited (trans (sym beforeUninstalled)
          (lAdvanceStartsInstalled nameEq keyEq actor first afterState tag
            (checkedActionProjects nameEq keyEq (LAdvance actor) first afterState tag checked))))
      PaperFinishStep {actor} sameAction sameTag => case sameAction of
        Refl => void (uninhabited (trans (sym beforeUninstalled)
          (lAdvanceStartsInstalled nameEq keyEq actor first afterState tag
            (checkedActionProjects nameEq keyEq (LAdvance actor) first afterState tag checked))))
o19ActivationEvolutionInstalled nameEq keyEq first afterState (LBegin actor) LBeginTag checked
  OpenedInstallation activation = snd (snd (lBeginBoundary nameEq keyEq actor first afterState LBeginTag checked))
o19ActivationEvolutionInstalled nameEq keyEq first afterState (LUnload actor) LUnloadTag checked
  ClosedInstallation activation = case activation of
    PaperBeginStep sameAction sameTag => case sameAction of Refl impossible
    PaperIterStep sameAction sameTag => case sameAction of Refl impossible
    PaperFinishStep sameAction sameTag => case sameAction of Refl impossible

||| Convert installation to presence through the actual owner lookup result.
export
0 o19InstalledOwnerObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) -> (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber @{nameEq} actor (registry state) = observed) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = True) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state)) = True)
o19InstalledOwnerObserved nameEq actor state Nothing exact installed =
  case trans (sym (the (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = False)
    (rewrite exact in Refl))) installed of Refl impossible
o19InstalledOwnerObserved nameEq actor state (Just fiber) exact installed = cong isJust exact

||| Both owner observations are PRODUCED from the aligned actual activation:
||| source presence by rule inversion, target survival by installation evolution.
export
0 o19AlignedActivationOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, afterState : SystemState name key value world error} ->
  (step : Transition first afterState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step NoTransitions) ->
  PaperActivationStep step ->
  ((fiber : Fiber name key value world error ** lookupFiber @{nameEq} (actionOwner (transitionAction step)) (registry first) = Just fiber),
   (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner (transitionAction step)) (registry afterState)) = True))
o19AlignedActivationOwner {first} {afterState} nameEq keyEq _
  (AlignedStep action tag checked _ AlignedEnd) activation =
    (lifecycleActorPresent nameEq keyEq action first afterState tag
      (checkedActionProjects nameEq keyEq action first afterState tag checked)
      (case activation of
        PaperBeginStep sameAction sameTag => trans (cong isLifecycleAction sameAction) Refl
        PaperIterStep sameAction sameTag => trans (cong isLifecycleAction sameAction) Refl
        PaperFinishStep sameAction sameTag => trans (cong isLifecycleAction sameAction) Refl),
     o19InstalledOwnerObserved nameEq (actionOwner action) afterState
       (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry afterState)) Refl
       (o19ActivationEvolutionInstalled nameEq keyEq first afterState action tag checked
         (installationEvolutionStep nameEq keyEq (actionOwner action) action tag first afterState checked) activation))

||| Owner-survival source-shape producer at the ACTUAL O19 pair cut. Bundle
||| alignment is extracted from its authenticated decomposition, never supplied
||| as an extra applicability or owner-observation premise.
export
0 o19SourcePairOwner :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source -> PaperActivationStep left ->
  ((fiber : Fiber name key value world error ** lookupFiber @{nameEq} (actionOwner (transitionAction left)) (registry first) = Just fiber),
   (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner (transitionAction left)) (registry middle)) = True))
o19SourcePairOwner nameEq keyEq protocol source earlier left right later decomposition premises activation =
  o19AlignedActivationOwner nameEq keyEq left
    (fst (alignedAppendSplit (MoreTransitions left NoTransitions) (MoreTransitions right NoTransitions)
      (fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))) activation
