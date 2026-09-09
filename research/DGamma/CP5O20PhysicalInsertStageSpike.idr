module DGamma.CP5O20PhysicalInsertStageSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import DGamma.CP5O20PhysicalInsertPositionSpike
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

||| Alignment exposes the checked equation of the exact physical head,
||| including its own tag and actual target. Only alignment is eliminated.
export
0 o20AlignedPhysicalHeadChecked :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState, finalState : SystemState name key value world error} ->
  (step : Transition before afterState) -> (rest : Transitions afterState finalState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (transitionAction step) before = Just (transitionTag step, afterState))
o20AlignedPhysicalHeadChecked nameEq keyEq _ _ (AlignedStep action tag checked rest alignedRest) = checked

||| Two authentic aligned physical Insert edges produce a paired stamped
||| stage at their OWN source/target states. Their matched generation equation
||| is consumed without changing either transition or rebuilding its target.
export
0 o20InsertStageFromAlignedHeads :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  {mapping : RegistrationGenerationBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} -> {leftLive, rightLive : GenerationEnvironment name} ->
  (actor : name) -> (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> ParentRelatedBy renaming leftParent rightParent ->
  {leftBefore, leftAfter, leftFinal, rightBefore, rightAfter, rightFinal : SystemState name key value world error} ->
  (leftStep : Transition leftBefore leftAfter) -> (leftRest : Transitions leftAfter leftFinal) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions leftStep leftRest) ->
  (transitionAction leftStep = OInsert actor leftParent component) ->
  (rightStep : Transition rightBefore rightAfter) -> (rightRest : Transitions rightAfter rightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions rightStep rightRest) ->
  (transitionAction rightStep = OInsert (renameForward renaming actor) rightParent component) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive)
    leftBefore rightBefore leftAfter rightAfter
o20InsertStageFromAlignedHeads nameEq keyEq renaming actor component leftParent rightParent parents
  {leftBefore} {leftAfter} {rightBefore} {rightAfter}
  leftStep leftRest leftAligned leftExact rightStep rightRest rightAligned rightExact matched =
    o20InsertStageAtCheckedStates nameEq keyEq renaming actor component leftParent rightParent parents
      leftBefore rightBefore (transitionTag leftStep) leftAfter
      (o20CheckedInsertFromActionEquation nameEq keyEq actor leftParent component (transitionAction leftStep)
        leftBefore leftAfter (transitionTag leftStep)
        (o20AlignedPhysicalHeadChecked nameEq keyEq leftStep leftRest leftAligned) leftExact)
      (transitionTag rightStep) rightAfter
      (o20CheckedInsertFromActionEquation nameEq keyEq (renameForward renaming actor) rightParent component (transitionAction rightStep)
        rightBefore rightAfter (transitionTag rightStep)
        (o20AlignedPhysicalHeadChecked nameEq keyEq rightStep rightRest rightAligned) rightExact) matched

||| Pair two located physical Inserts using alignment at their OWN native
||| cuts. The ordinals are their actual preceding-trace counts, never scanner
||| per-activation positions or an independently chosen counter.
export
0 o20LocatedInsertStage :
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
  O20StampedStage name key world error value nameEq keyEq mapping renaming
    (locatedActionOrdinal leftBirth) (locatedActionOrdinal rightBirth) leftLive rightLive
    (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor (locatedActionOrdinal leftBirth)) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming actor)
      (MkRegistrationGeneration (renameForward renaming actor) (locatedActionOrdinal rightBirth)) rightLive)
    (actionBeforeState leftBirth) (actionBeforeState rightBirth) (actionAfterState leftBirth) (actionAfterState rightBirth)
o20LocatedInsertStage {name} {key} {world} {error} {value}
  nameEq keyEq renaming left right leftAligned rightAligned actor component leftParent rightParent parents leftBirth rightBirth matched =
    o20InsertStageFromAlignedHeads nameEq keyEq renaming actor component leftParent rightParent parents
      (locatedTransition leftBirth) (afterActionOccurrence leftBirth)
      (snd (alignedAppendSplit (beforeActionOccurrence leftBirth)
        (MoreTransitions (locatedTransition leftBirth) (afterActionOccurrence leftBirth))
        (replace {p = AlignedTransitions name key world error value nameEq keyEq}
          (sym (actionOccurrenceDecomposition leftBirth)) leftAligned))) (locatedAction leftBirth)
      (locatedTransition rightBirth) (afterActionOccurrence rightBirth)
      (snd (alignedAppendSplit (beforeActionOccurrence rightBirth)
        (MoreTransitions (locatedTransition rightBirth) (afterActionOccurrence rightBirth))
        (replace {p = AlignedTransitions name key world error value nameEq keyEq}
          (sym (actionOccurrenceDecomposition rightBirth)) rightAligned))) (locatedAction rightBirth) matched

||| The genuine paired generated-birth attachment supplies the conjugated
||| physical map equation. Both Insert checks are produced from the actual
||| trace alignment, yielding a native stage at the attached births' own cuts.
export
0 o20AttachedGeneratedInsertStage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  {leftLive, rightLive : GenerationEnvironment name} ->
  AlignedTransitions name key world error value nameEq keyEq leftNow ->
  AlignedTransitions name key world error value nameEq keyEq rightNow ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  (attached : O20AttachedGeneratedBirth name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth) ->
  O20StampedStage name key world error value nameEq keyEq
    (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) mapping (replayGenerationRenaming rightReplay)) renaming
    (registrationOrdinal leftBirth) (registrationOrdinal (attachedRightBirth attached)) leftLive rightLive
    (putCurrentGeneration @{nameEq} child (registrationGeneration leftBirth) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming child) (registrationGeneration (attachedRightBirth attached)) rightLive)
    (registrationBefore leftBirth) (registrationBefore (attachedRightBirth attached))
    (registrationAfter leftBirth) (registrationAfter (attachedRightBirth attached))
o20AttachedGeneratedInsertStage {leftNow} {rightNow} nameEq keyEq leftReplay rightReplay mapping renaming
  leftAligned rightAligned child parent component leftBirth attached =
    o20LocatedInsertStage nameEq keyEq renaming leftNow rightNow leftAligned rightAligned child component
      (ChildOf parent) (ChildOf (renameForward renaming parent)) (ChildrenRelated Refl)
      (generatedRegistrationActionOccurrence leftBirth) (generatedRegistrationActionOccurrence (attachedRightBirth attached))
      (attachedPhysicalEquation attached)

||| One same-origin package owns original per-activation positions, both
||| physical Insert occurrences, and their native paired stage. No ordering,
||| canonical per-activation preservation, skip or whole history is a field.
public export
record O20PhysicalInsertAttachment
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error}
  {left : Transitions leftFirst leftFinal} {right : Transitions rightFirst rightFinal}
  {leftNow : Transitions leftNowFirst leftNowFinal} {rightNow : Transitions rightNowFirst rightNowFinal}
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow)
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow)
  (mapping : RegistrationGenerationBijection name) (renaming : NameBijection name)
  (leftLive, rightLive : GenerationEnvironment name)
  (child, parent : name) (component : Component key value world error)
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) where
  constructor MkO20PhysicalInsertAttachment
  0 insertOriginPositions : O20PhysicalInsertOriginPositions name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth
  0 insertNativeStage : O20StampedStage name key world error value nameEq keyEq
    (o20ReplayOrdinalBijection (replayGenerationRenaming leftReplay) mapping (replayGenerationRenaming rightReplay)) renaming
    (registrationOrdinal leftBirth) (registrationOrdinal (attachedRightBirth (physicalBirths insertOriginPositions))) leftLive rightLive
    (putCurrentGeneration @{nameEq} child (registrationGeneration leftBirth) leftLive)
    (putCurrentGeneration @{nameEq} (renameForward renaming child)
      (registrationGeneration (attachedRightBirth (physicalBirths insertOriginPositions))) rightLive)
    (registrationBefore leftBirth) (registrationBefore (attachedRightBirth (physicalBirths insertOriginPositions)))
    (registrationAfter leftBirth) (registrationAfter (attachedRightBirth (physicalBirths insertOriginPositions)))

||| Construct positions and native stage together using the SAME physical
||| opposite birth packet. No projected-record equality is required.
export
0 o20PhysicalInsertAttachmentFromOrigins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, leftNowFirst, leftNowFinal, rightNowFirst, rightNowFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} -> {right : Transitions rightFirst rightFinal} ->
  {leftNow : Transitions leftNowFirst leftNowFinal} -> {rightNow : Transitions rightNowFirst rightNowFinal} ->
  (leftReplay : ActionRegistrationReplayCorrespondence name key world error value left leftNow) ->
  (rightReplay : ActionRegistrationReplayCorrespondence name key world error value right rightNow) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (leftLive, rightLive : GenerationEnvironment name) ->
  AlignedTransitions name key world error value nameEq keyEq leftNow ->
  AlignedTransitions name key world error value nameEq keyEq rightNow ->
  (child, parent : name) -> (component : Component key value world error) ->
  (leftBirth : LocatedGeneratedRegistration child parent component leftNow) ->
  (positions : O20PhysicalInsertOriginPositions name key world error value leftReplay rightReplay mapping renaming
    child parent component leftBirth) ->
  O20PhysicalInsertAttachment name key world error value nameEq keyEq leftReplay rightReplay mapping renaming
    leftLive rightLive child parent component leftBirth
o20PhysicalInsertAttachmentFromOrigins nameEq keyEq leftReplay rightReplay mapping renaming leftLive rightLive
  leftAligned rightAligned child parent component leftBirth positions =
    MkO20PhysicalInsertAttachment positions
      (o20AttachedGeneratedInsertStage nameEq keyEq leftReplay rightReplay mapping renaming {leftLive} {rightLive}
        leftAligned rightAligned child parent component leftBirth (physicalBirths positions))
