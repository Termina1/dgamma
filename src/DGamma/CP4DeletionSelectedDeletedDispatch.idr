module DGamma.CP4DeletionSelectedDeletedDispatch

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedDeletedOrchestration
import Data.List.Elem
import Decidable.Equality

%default total

||| Exhaustive deleted-R orchestration dispatcher at a selected-episode replay
||| boundary.  O-Insert consumes the registration-discipline evidence needed for
||| fresh childlessness; O-Retire and O-Remove reuse the exact current plan leaf.
public export
0 deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  {restFinal : SystemState name key value world error} ->
  (rest : Transitions afterState restFinal) ->
  RegistrationStepDiscipline protocol nameEq action before rest ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  GenerationOwnedActor nameEq registered ordinal live action ->
  DeletedRegisteredEpisodeBoundaryStep name key world error value nameEq keyEq
    selected registered ordinal live action whole afterState survivor
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (OInsert inserted parent component) orchestration before afterState tag checked
  rest discipline whole survivor boundary oldEmpty deleted =
    deletedRegisteredInsertPreservesEpisodeBoundary protocol nameEq keyEq selected
      registered ordinal live unique selectedOutside inserted parent component
      before afterState tag checked rest discipline whole survivor boundary oldEmpty
      deleted
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (ORetire actor) orchestration before afterState tag checked rest discipline whole
  survivor boundary oldEmpty deleted =
    deletedRegisteredRetirePreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live unique stamped selectedOutside actor before afterState
      tag checked whole survivor boundary oldEmpty deleted
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (ORemove actor) orchestration before afterState tag checked rest discipline whole
  survivor boundary oldEmpty deleted =
    deletedRegisteredRemovePreservesEpisodeBoundary nameEq keyEq selected
      registered ordinal live unique stamped selectedOutside actor before afterState
      tag checked whole survivor boundary oldEmpty deleted
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (LBegin actor) Refl before afterState tag checked rest discipline whole survivor
  boundary oldEmpty deleted impossible
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (LAdvance actor) Refl before afterState tag checked rest discipline whole survivor
  boundary oldEmpty deleted impossible
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (LDivert actor) Refl before afterState tag checked rest discipline whole survivor
  boundary oldEmpty deleted impossible
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (LLeave actor) Refl before afterState tag checked rest discipline whole survivor
  boundary oldEmpty deleted impossible
deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol nameEq keyEq
  selected registered ordinal live unique stamped selectedOutside
  (LUnload actor) Refl before afterState tag checked rest discipline whole survivor
  boundary oldEmpty deleted impossible
