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
