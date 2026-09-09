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
import DGamma.CP5O20NativeInsertEnvironmentSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
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

||| Observe both native insertion plans from the two ACTUAL checked states.
||| No input plan, input tag law or input successor stage is assumed.
export
0 o20LabelledInsertAtCheckedStates :
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
  (stage : O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    leftBefore rightBefore
    leftAfter rightAfter **
    (transitionAction (o20StampedLeftTransition stage) = OInsert actor leftParent component,
     transitionAction (o20StampedRightTransition stage) = OInsert (renameForward renaming actor) rightParent component,
     transitionTag (o20StampedLeftTransition stage) = leftTag,
     transitionTag (o20StampedRightTransition stage) = rightTag))
o20LabelledInsertAtCheckedStates nameEq keyEq renaming actor component leftParent rightParent parents
  (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
  leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched =
    o20LabelledInsertFromPlans nameEq keyEq renaming actor component leftParent rightParent parents
      leftWorld rightWorld leftRegistry rightRegistry leftTag leftAfter leftChecked rightTag rightAfter rightChecked matched
      (foreignInsertPlanView nameEq keyEq (renameForward renaming actor) rightParent component rightWorld rightRegistry
        rightTag rightAfter (checkedActionProjects nameEq keyEq (OInsert (renameForward renaming actor) rightParent component)
          (MkSystemState rightWorld rightRegistry) rightAfter rightTag rightChecked))
      (foreignInsertPlanView nameEq keyEq actor leftParent component leftWorld leftRegistry
        leftTag leftAfter (checkedActionProjects nameEq keyEq (OInsert actor leftParent component)
          (MkSystemState leftWorld leftRegistry) leftAfter leftTag leftChecked))

||| Bind the labelled native stage to TWO actual supplied-word Insert cuts.
||| Both native dictionaries, input tags and source/target states are produced
||| from those very occurrences and their whole-trace alignment.
export
0 o20LocatedLabelledInsertStage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} -> {leftLive, rightLive : GenerationEnvironment name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftBirth : LocatedActionOccurrence (OInsert actor leftParent component) left) ->
  (rightBirth : LocatedActionOccurrence (OInsert (renameForward renaming actor) rightParent component) right) ->
  (generationForward mapping (MkRegistrationGeneration actor (locatedActionOrdinal leftBirth)) =
    MkRegistrationGeneration (renameForward renaming actor) (locatedActionOrdinal rightBirth)) ->
  (stage : O20StampedStage name key world error value nameEq keyEq mapping renaming
    (locatedActionOrdinal leftBirth) (locatedActionOrdinal rightBirth) leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor (locatedActionOrdinal leftBirth)) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) (locatedActionOrdinal rightBirth)) rightLive)
    (actionBeforeState leftBirth) (actionBeforeState rightBirth) (actionAfterState leftBirth) (actionAfterState rightBirth) **
    (transitionAction (o20StampedLeftTransition stage) = OInsert actor leftParent component,
     transitionAction (o20StampedRightTransition stage) = OInsert (renameForward renaming actor) rightParent component,
     transitionTag (o20StampedLeftTransition stage) = transitionTag (locatedTransition leftBirth),
     transitionTag (o20StampedRightTransition stage) = transitionTag (locatedTransition rightBirth)))
o20LocatedLabelledInsertStage {name} {key} {world} {error} {value}
  nameEq keyEq renaming left right leftAligned rightAligned actor component leftParent rightParent parents leftBirth rightBirth matched =
    o20LabelledInsertAtCheckedStates nameEq keyEq renaming actor component leftParent rightParent parents
      (actionBeforeState leftBirth) (actionBeforeState rightBirth)
      (transitionTag (locatedTransition leftBirth)) (actionAfterState leftBirth)
      (o20CheckedInsertFromActionEquation nameEq keyEq actor leftParent component (transitionAction (locatedTransition leftBirth))
        (actionBeforeState leftBirth) (actionAfterState leftBirth) (transitionTag (locatedTransition leftBirth))
        (o20AlignedPhysicalHeadChecked nameEq keyEq (locatedTransition leftBirth) (afterActionOccurrence leftBirth)
          (snd (alignedAppendSplit (beforeActionOccurrence leftBirth)
            (MoreTransitions (locatedTransition leftBirth) (afterActionOccurrence leftBirth))
            (replace {p = AlignedTransitions name key world error value nameEq keyEq}
              (sym (actionOccurrenceDecomposition leftBirth)) leftAligned)))) (locatedAction leftBirth))
      (transitionTag (locatedTransition rightBirth)) (actionAfterState rightBirth)
      (o20CheckedInsertFromActionEquation nameEq keyEq (renameForward renaming actor) rightParent component
        (transitionAction (locatedTransition rightBirth)) (actionBeforeState rightBirth) (actionAfterState rightBirth)
        (transitionTag (locatedTransition rightBirth))
        (o20AlignedPhysicalHeadChecked nameEq keyEq (locatedTransition rightBirth) (afterActionOccurrence rightBirth)
          (snd (alignedAppendSplit (beforeActionOccurrence rightBirth)
            (MoreTransitions (locatedTransition rightBirth) (afterActionOccurrence rightBirth))
            (replace {p = AlignedTransitions name key world error value nameEq keyEq}
              (sym (actionOccurrenceDecomposition rightBirth)) rightAligned)))) (locatedAction rightBirth)) matched

||| A genuine paired RUNTIME occurrence history at two actual native Insert
||| cuts, with the TWO authentic supplied-word action/tag/ordinal labels.
||| The successor environments are computed. This is a one-edge history,
||| not the missing whole-word chronology or an initial-cut producer.
export
0 o20LocatedInsertOccurrenceHistory :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} -> {leftLive, rightLive : GenerationEnvironment name} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  (leftBirth : LocatedActionOccurrence (OInsert actor leftParent component) left) ->
  (rightBirth : LocatedActionOccurrence (OInsert (renameForward renaming actor) rightParent component) right) ->
  (generationForward mapping (MkRegistrationGeneration actor (locatedActionOrdinal leftBirth)) =
    MkRegistrationGeneration (renameForward renaming actor) (locatedActionOrdinal rightBirth)) ->
  O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming left right leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor (locatedActionOrdinal leftBirth)) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) (locatedActionOrdinal rightBirth)) rightLive)
    (actionBeforeState leftBirth) (actionBeforeState rightBirth) (actionAfterState leftBirth) (actionAfterState rightBirth)
o20LocatedInsertOccurrenceHistory nameEq keyEq renaming left right leftAligned rightAligned
  actor component leftParent rightParent parents leftBirth rightBirth matched =
    case o20LocatedLabelledInsertStage nameEq keyEq renaming left right leftAligned rightAligned
      actor component leftParent rightParent parents leftBirth rightBirth matched of
      (stage ** (leftAction, rightAction, leftTag, rightTag)) =>
        OccurrenceHistoryMore stage
          (MkLocatedActionOccurrence (actionBeforeState leftBirth) (actionAfterState leftBirth)
            (beforeActionOccurrence leftBirth) (locatedTransition leftBirth) (afterActionOccurrence leftBirth)
            (trans (locatedAction leftBirth) (sym leftAction)) (actionOccurrenceDecomposition leftBirth))
          (MkLocatedActionOccurrence (actionBeforeState rightBirth) (actionAfterState rightBirth)
            (beforeActionOccurrence rightBirth) (locatedTransition rightBirth) (afterActionOccurrence rightBirth)
            (trans (locatedAction rightBirth) (sym rightAction)) (actionOccurrenceDecomposition rightBirth))
          Refl Refl (sym leftTag) (sym rightTag) OccurrenceHistoryEnd

||| Attach an original-position packet to an actual one-edge runtime history
||| and BOTH computed native prefix scans. No runtime environments, stage,
||| source/target state equations or prefix-cut relation are input. Whole
||| chronological coverage and predecessor ALL-name cuts remain separate.
export
0 o20PrefixInsertOccurrenceHistory :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, nowInitial, leftNowFinal, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions nowInitial leftNowFinal} -> {rightNow : Transitions nowInitial rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  AlignedTransitions name key world error value nameEq keyEq leftNow ->
  AlignedTransitions name key world error value nameEq keyEq rightNow ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  (positions : O20PhysicalInsertOriginPositions name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth) ->
  (GenerationTraceScan nameEq Z [] (beforeRegistration leftBirth) (registrationOrdinal leftBirth)
     (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth)),
   GenerationTraceScan nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths positions)))
     (registrationOrdinal (attachedRightBirth (physicalBirths positions)))
     (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths positions)))),
   O20OccurrenceStampedHistory name key world error value nameEq keyEq
     (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) mapping (replayGenerationRenaming rightReplay)) renaming
     leftNow rightNow
     (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth))
     (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths positions))))
     (putCurrentGeneration @{nameEq} child (registrationGeneration leftBirth)
       (o20ScannedFinalLive nameEq Z [] (beforeRegistration leftBirth)))
     (putCurrentGeneration @{nameEq} (renameForward renaming child) (registrationGeneration (attachedRightBirth (physicalBirths positions)))
       (o20ScannedFinalLive nameEq Z [] (beforeRegistration (attachedRightBirth (physicalBirths positions)))))
     (registrationBefore leftBirth) (registrationBefore (attachedRightBirth (physicalBirths positions)))
     (registrationAfter leftBirth) (registrationAfter (attachedRightBirth (physicalBirths positions))))
o20PrefixInsertOccurrenceHistory {leftNow} {rightNow} nameEq keyEq leftReplay rightReplay mapping renaming
  leftAligned rightAligned child parent component leftBirth positions =
    (o20NativePrefixScan nameEq (beforeRegistration leftBirth),
     o20NativePrefixScan nameEq (beforeRegistration (attachedRightBirth (physicalBirths positions))),
     o20LocatedInsertOccurrenceHistory nameEq keyEq renaming leftNow rightNow leftAligned rightAligned
       child component (ChildOf parent) (ChildOf (renameForward renaming parent)) (ChildrenRelated Refl)
       (generatedRegistrationActionOccurrence leftBirth)
       (generatedRegistrationActionOccurrence (attachedRightBirth (physicalBirths positions)))
       (attachedPhysicalEquation (physicalBirths positions)))
