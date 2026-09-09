module DGamma.CP5O20InsertOccurrenceHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20OccurrenceStampedHistorySpike
import DGamma.CP5O20PhysicalInsertStageSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import DGamma.CP5O20PhysicalInsertPositionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A producer-owned Insert stage with exact action/tag label equations.
||| Both equations concern this SAME native stage, not a separately chosen
||| constructor. Later wrappers attach actual supplied-word occurrences.
export
0 o20LabelledInsertFromRightPlan :
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
  (stage : O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
    (MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent)) rightAfter **
    (transitionAction (o20StampedLeftTransition stage) = OInsert actor leftParent component,
     transitionAction (o20StampedRightTransition stage) = OInsert (renameForward renaming actor) rightParent component,
     transitionTag (o20StampedLeftTransition stage) = OInsertTag,
     transitionTag (o20StampedRightTransition stage) = OInsertTag))
o20LabelledInsertFromRightPlan nameEq keyEq renaming actor component leftParent rightParent parents
  leftWorld rightWorld leftRegistry rightRegistry leftAbsent leftChecked _ _ rightChecked matched
  (MkForeignInsertPlanView rightAbsent guards) =
    (StampedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked matched ** (Refl, Refl, Refl, Refl))


||| The observed native insertion plan pins the INPUT tag, not only the tag
||| of a newly built stage. This will authenticate the supplied-word labels.
export
0 o20ForeignInsertPlanTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {actor : name} -> {parent : Parent name} -> {component : Component key value world error} ->
  {ambient : world} -> {fibers : Registry name key value world error} ->
  {tag : RuleTag} -> {afterState : SystemState name key value world error} ->
  ForeignInsertPlanView name key world error value nameEq keyEq actor parent component ambient fibers tag afterState ->
  (tag = OInsertTag)
o20ForeignInsertPlanTag (MkForeignInsertPlanView absent guards) = Refl

||| Both original native tag observations accompany the SAME produced stage.
export
0 o20LabelledInsertFromPlans :
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
  (stage : O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
    leftAfter rightAfter **
    (transitionAction (o20StampedLeftTransition stage) = OInsert actor leftParent component,
     transitionAction (o20StampedRightTransition stage) = OInsert (renameForward renaming actor) rightParent component,
     transitionTag (o20StampedLeftTransition stage) = leftTag,
     transitionTag (o20StampedRightTransition stage) = rightTag))
o20LabelledInsertFromPlans nameEq keyEq renaming actor component leftParent rightParent parents
  leftWorld rightWorld leftRegistry rightRegistry _ _ leftChecked rightTag rightAfter rightChecked matched rightPlan
  (MkForeignInsertPlanView leftAbsent guards) =
    case o20LabelledInsertFromRightPlan nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftAbsent leftChecked rightTag rightAfter rightChecked matched rightPlan of
        (stage ** (leftAction, rightAction, leftTagExact, rightTagExact)) =>
          (stage ** (leftAction, rightAction, leftTagExact,
            trans rightTagExact (sym (o20ForeignInsertPlanTag rightPlan))))
