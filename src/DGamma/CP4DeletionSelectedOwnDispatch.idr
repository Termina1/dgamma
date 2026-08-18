module DGamma.CP4DeletionSelectedOwnDispatch

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4RecoverySelectedReplayStep
import DGamma.CP4RecoveryTrace
import Data.List.Elem
import Decidable.Equality

%default total

||| Rule-independent selected lifecycle dispatcher for every installed interior
||| head.  Impossible selected insert/remove/re-begin/unload shapes are excluded
||| by `selectedInstalledAccumulatorStep`; the four accumulator-carrying control
||| branches reuse their checked recovery proofs.
public export
0 deletedSelectedInstalledHeadPreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  actionOwner action = selected ->
  isLifecycleAction action = True ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  installedAt @{nameEq} selected afterState = True ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal) live whole afterState survivor
deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live stamped selectedOutside action tag before afterState
  checked owner lifecycle whole occurs targetInstalled survivor boundary =
    case selectedInstalledStableAccumulatorStep nameEq keyEq selected action tag
      before afterState checked owner lifecycle whole occurs targetInstalled
      (selectedBoundaryModel (selectedBoundaryEffects boundary)) of
      MkSelectedStableAccumulatorStep step retiredSame =>
        skippedSelectedAccumulatorStepPreservesEpisodeBoundary nameEq keyEq
          selected registered ordinal live stamped selectedOutside action tag
          before afterState checked whole survivor boundary owner step retiredSame
