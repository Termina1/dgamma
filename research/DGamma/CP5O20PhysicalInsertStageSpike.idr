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
