module DGamma.CP5O20PhysicalInsertStageSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The right native insertion-plan observation fixes its actual target and
||| tag. Paired insertion is then constructed using the SAME absence witnesses
||| and checked equations, not independently reconstructed target states.
export
0 o20InsertStageFromRightPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {leftLive, rightLive : GenerationEnvironment name} ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Nothing)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) =
    Just (OInsertTag, MkSystemState leftWorld
      (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent))) ->
  (rightTag : RuleTag) -> (rightAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (renameForward renaming actor) rightParent component) (MkSystemState rightWorld rightRegistry) =
    Just (rightTag, rightAfter)) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) ->
  ForeignInsertPlanView name key world error value nameEq keyEq (renameForward renaming actor)
    rightParent component rightWorld rightRegistry rightTag rightAfter ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
    (MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent)) rightAfter
o20InsertStageFromRightPlan nameEq keyEq renaming actor component leftParent rightParent parents
  leftWorld rightWorld leftRegistry rightRegistry leftAbsent leftChecked _ _ rightChecked matched
  (MkForeignInsertPlanView rightAbsent guards) =
    StampedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked matched

||| Eliminate the left native target observation once, then consume the
||| already observed right plan. The returned stage ends at BOTH actual
||| evaluator targets; no target-state equality or stage is supplied by callers.
export
0 o20InsertStageFromPlans :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {leftLive, rightLive : GenerationEnvironment name} ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftTag : RuleTag) -> (leftAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) = Just (leftTag, leftAfter)) ->
  (rightTag : RuleTag) -> (rightAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (renameForward renaming actor) rightParent component) (MkSystemState rightWorld rightRegistry) =
    Just (rightTag, rightAfter)) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) ->
  ForeignInsertPlanView name key world error value nameEq keyEq (renameForward renaming actor)
    rightParent component rightWorld rightRegistry rightTag rightAfter ->
  ForeignInsertPlanView name key world error value nameEq keyEq actor
    leftParent component leftWorld leftRegistry leftTag leftAfter ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
    leftAfter rightAfter
o20InsertStageFromPlans nameEq keyEq renaming actor component leftParent rightParent parents
  leftWorld rightWorld leftRegistry rightRegistry _ _ leftChecked rightTag rightAfter rightChecked matched rightPlan
  (MkForeignInsertPlanView leftAbsent guards) =
    o20InsertStageFromRightPlan nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftAbsent leftChecked rightTag rightAfter rightChecked matched rightPlan

||| Execute the public insertion-plan observation at each genuine checked
||| edge and immediately build the paired stage. No native target observation
||| is an extra premise; each comes from that SAME checked evaluator equation.
export
0 o20InsertStageFromCheckedRegistries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {leftLive, rightLive : GenerationEnvironment name} ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftTag : RuleTag) -> (leftAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) = Just (leftTag, leftAfter)) ->
  (rightTag : RuleTag) -> (rightAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (renameForward renaming actor) rightParent component) (MkSystemState rightWorld rightRegistry) =
    Just (rightTag, rightAfter)) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
    leftAfter rightAfter
o20InsertStageFromCheckedRegistries nameEq keyEq renaming actor component leftParent rightParent parents
  leftWorld rightWorld leftRegistry rightRegistry leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched =
    o20InsertStageFromPlans nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched
      (foreignInsertPlanView nameEq keyEq (renameForward renaming actor) rightParent component rightWorld rightRegistry
        rightTag rightAfter (checkedActionProjects nameEq keyEq (OInsert (renameForward renaming actor) rightParent component)
          (MkSystemState rightWorld rightRegistry) rightAfter rightTag rightChecked))
      (foreignInsertPlanView nameEq keyEq actor leftParent component leftWorld leftRegistry
        leftTag leftAfter (checkedActionProjects nameEq keyEq (OInsert actor leftParent component)
          (MkSystemState leftWorld leftRegistry) leftAfter leftTag leftChecked))

||| Open only the right source state, retaining its actual checked target.
||| No state is independently rebuilt to establish literal equality.
export
0 o20InsertStageAtRightState :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {leftLive, rightLive : GenerationEnvironment name} ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftWorld : world) -> (leftRegistry : Registry name key value world error) ->
  (rightBefore : SystemState name key value world error) ->
  (leftTag : RuleTag) -> (leftAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) = Just (leftTag, leftAfter)) ->
  (rightTag : RuleTag) -> (rightAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (renameForward renaming actor) rightParent component) rightBefore =
    Just (rightTag, rightAfter)) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    (MkSystemState leftWorld leftRegistry) rightBefore
    leftAfter rightAfter
o20InsertStageAtRightState nameEq keyEq renaming actor component leftParent rightParent parents
  leftWorld leftRegistry (MkSystemState rightWorld rightRegistry) leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched =
    o20InsertStageFromCheckedRegistries nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched

||| Paired Insert at two actual native source/target states. The two checked
||| evaluator equations determine the physical targets; no relation between
||| independently reconstructed states is assumed.
export
0 o20InsertStageAtCheckedStates :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {leftLive, rightLive : GenerationEnvironment name} ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftTag : RuleTag) -> (leftAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor leftParent component) leftBefore = Just (leftTag, leftAfter)) ->
  (rightTag : RuleTag) -> (rightAfter : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (renameForward renaming actor) rightParent component) rightBefore =
    Just (rightTag, rightAfter)) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    leftBefore rightBefore
    leftAfter rightAfter
o20InsertStageAtCheckedStates nameEq keyEq renaming actor component leftParent rightParent parents
  (MkSystemState leftWorld leftRegistry) rightBefore leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched =
    o20InsertStageAtRightState nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld leftRegistry rightBefore leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched

||| Transport a checked evaluator equation along the actual Insert action
||| equation. No native state, tag or checked result is reconstructed.
export
0 o20CheckedInsertFromActionEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (action = OInsert actor parent component) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor parent component) before = Just (tag, afterState))
o20CheckedInsertFromActionEquation {name} {key} {world} {error} {value}
  nameEq keyEq actor parent component action before afterState tag checked exact =
    trans (cong (\operation => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} operation before)
      (sym exact)) checked
