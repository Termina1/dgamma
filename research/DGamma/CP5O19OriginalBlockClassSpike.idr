module DGamma.CP5O19OriginalBlockClassSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19PairObservationSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Producer-owned ORIGINAL block-word values and child exclusion. Lifecycle
||| ownership is not silently cast to PaperActivationStep: recovery/tag
||| exclusion still needs the actual final-active/no-unload evolution proof.
public export
data O19BlockWordObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (actor, forbidden : name) -> Action name key value world error -> Type where
  BlockOwnLifecycle :
    {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (0 lifecycle : isLifecycleAction action = True) -> (0 owner : actionOwner action = actor) ->
    O19BlockWordObservation name key world error value actor forbidden action
  BlockGenerated :
    {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : action = OInsert child (ChildOf actor) component) ->
    (0 childSafe : Not (child = forbidden)) ->
    O19BlockWordObservation name key world error value actor forbidden action

||| Derive every ORIGINAL body-word observation simultaneously from actual
||| ActorLifecycleOnly and sanctioned NoGeneratedChild spines. Registration
||| child/component values and the opposite-actor exclusion are produced.
export
0 o19OwnedSafeWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (actor, forbidden : name) -> {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> ActorLifecycleOnly actor trace -> NoGeneratedChild forbidden trace ->
  (action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
  O19BlockWordObservation name key world error value actor forbidden action
o19OwnedSafeWord actor forbidden _ ActorLifecycleEnd NoGeneratedChildEnd action absent = void (uninhabited absent)
o19OwnedSafeWord actor forbidden _ (ActorLifecycleStep step rest lifecycle owner tail)
  (NoGeneratedChildStep _ _ excluded safeTail) _ Here =
    BlockOwnLifecycle lifecycle (trans (sym (o19TransitionActorOwner step)) owner)
o19OwnedSafeWord actor forbidden _ (ActorLifecycleStep step rest lifecycle owner tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action (There member) =
    o19OwnedSafeWord actor forbidden rest tail safeTail action member
o19OwnedSafeWord actor forbidden _ (ActorYieldedRegistrationStep {child} {childComponent} step rest inserted tail)
  (NoGeneratedChildStep _ _ excluded safeTail) _ Here =
    BlockGenerated child childComponent inserted
      (\same => excluded actor childComponent (trans inserted (cong (\selected => OInsert selected (ChildOf actor) childComponent) same)))
o19OwnedSafeWord actor forbidden _ (ActorYieldedRegistrationStep step rest inserted tail)
  (NoGeneratedChildStep _ _ excluded safeTail) action (There member) =
    o19OwnedSafeWord actor forbidden rest tail safeTail action member

||| Complete ORIGINAL located block-word values/ownership/licensing exclusion:
||| the actual Begin supplies the head, the actual owned/safe body supplies
||| every tail occurrence. No word classifier is assumed from the caller.
export
0 o19OriginalBlockWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> (actor, forbidden : name) ->
  {initial, finalState : SystemState name key value world error} ->
  {source : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor source) ->
  NoGeneratedChild forbidden (blockBody block) ->
  (action : Action name key value world error) -> Elem action (o19ActionWord (actorBlockTrace block)) ->
  O19BlockWordObservation name key world error value actor forbidden action
o19OriginalBlockWord actor forbidden block safe _ Here = BlockOwnLifecycle Refl Refl
o19OriginalBlockWord actor forbidden block safe action (There member) =
  o19OwnedSafeWord actor forbidden (blockBody block) (blockActorOnly block) safe action member

||| Actual ORIGINAL births with distinct licensing parents have distinct raw
||| child names, by original UniqueRawNameInsertions and immutable birth
||| metadata. No independent row collision/renaming assumption is requested.
export
0 o19OriginalChildrenDistinct :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (leftParent, rightParent, leftChild, rightChild : name) ->
  (leftComponent, rightComponent : Component key value world error) -> Not (leftParent = rightParent) ->
  LocatedActionOccurrence (OInsert leftChild (ChildOf leftParent) leftComponent) source ->
  LocatedActionOccurrence (OInsert rightChild (ChildOf rightParent) rightComponent) source ->
  Not (rightChild = leftChild)
o19OriginalChildrenDistinct {name} {key} {world} {error} {value} nameEq keyEq source unique leftParent rightParent leftChild rightChild
  leftComponent rightComponent parentsDifferent leftBirth rightBirth same = case same of
    Refl => case cong Builtin.fst
      (uniqueRawBirthMetadata name key world error value nameEq keyEq source unique leftChild
        (ChildOf leftParent) (ChildOf rightParent) leftComponent rightComponent leftBirth rightBirth) of
      Refl => parentsDifferent Refl

||| BOTH ORIGINAL selected block observations are now projections of the
||| exact sanctioned decomposition/safety, including BOTH NoGeneratedChild
||| fields. No source-word ownership or licensing callback is requested.
export
0 o19SanctionedOriginalWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (leftAction, rightAction : Action name key value world error) ->
  Elem leftAction (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  Elem rightAction (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  (O19BlockWordObservation name key world error value (actorLeft swap) (actorRight swap) leftAction,
   O19BlockWordObservation name key world error value (actorRight swap) (actorLeft swap) rightAction)
o19SanctionedOriginalWords nameEq keyEq protocol swap source blocks premises safety leftAction rightAction leftMember rightMember =
  (o19OriginalBlockWord (actorLeft swap) (actorRight swap) (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
     (safetyLeftDoesNotGenerateRight safety) leftAction leftMember,
   o19OriginalBlockWord (actorRight swap) (actorLeft swap) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
     (safetyRightDoesNotGenerateLeft safety) rightAction rightMember)

||| The actual explicit insertion-plan constructor owns its exact source tag.
||| This is a constructor elimination, not a Refl observer of an independent
||| nested builder. Used to discharge genuine original O/O and A/O tags.
export
0 o19ObservedOriginalInsertTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) -> (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  ForeignInsertPlanView name key world error value nameEq keyEq child parent component ambient source tag afterState ->
  tag = OInsertTag
o19ObservedOriginalInsertTag nameEq keyEq child parent component ambient source _ _ (MkForeignInsertPlanView absent guards) = Refl

||| Original aligned actual insertion discharges its tag through the actual
||| checked application and explicit F6 plan observation. No tag premise.
export
0 o19AlignedOriginalInsertTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (before, afterState : SystemState name key value world error) ->
  (step : Transition before afterState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step NoTransitions) ->
  transitionAction step = OInsert child parent component -> transitionTag step = OInsertTag
o19AlignedOriginalInsertTag nameEq keyEq child parent component (MkSystemState ambient fibers) afterState _
  (AlignedStep action tag checked _ AlignedEnd) inserted = case inserted of
    Refl => o19ObservedOriginalInsertTag nameEq keyEq child parent component ambient fibers tag afterState
      (foreignInsertPlanView nameEq keyEq child parent component ambient fibers tag afterState
        (checkedActionProjects nameEq keyEq (OInsert child parent component) (MkSystemState ambient fibers) afterState tag checked))

||| CONDITIONAL assembler, NOT the original classifier. The two VISIBLE
||| PaperActivationStep completeness arguments remain hard open: they must
||| be produced from actual block final-active/no-unload evolution excluding
||| absorbing Unloading. Installed-at-cuts is NOT a paper-rule cast. These
||| are NOT new public O19 premises and this conditional result does NOT
||| authorize an input-free column instantiation or any O19 body.
|||
||| All four static constructor/licensing branches are assembled from the
||| explicit producer-owned F5 observations and actual ORIGINAL locations.
||| O/O derives collision exclusion from original unique births and its
||| actual original right tag from original aligned checked application;
||| that branch does not invoke either missing paper-branch argument.
export
0 o19OriginalClassesConditional :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  {leftAction, rightAction : Action name key value world error} ->
  (leftOrigin : LocatedActionOccurrence leftAction source) -> (rightOrigin : LocatedActionOccurrence rightAction source) ->
  (observed : (O19BlockWordObservation name key world error value (actorLeft swap) (actorRight swap) leftAction,
               O19BlockWordObservation name key world error value (actorRight swap) (actorLeft swap) rightAction)) ->
  (0 leftPaperBranch : isLifecycleAction leftAction = True -> PaperActivationStep (locatedTransition leftOrigin)) ->
  (0 rightPaperBranch : isLifecycleAction rightAction = True -> PaperActivationStep (locatedTransition rightOrigin)) ->
  O19SourcePairObservation name key world error value (actorLeft swap) (actorRight swap)
    (locatedTransition leftOrigin) (locatedTransition rightOrigin)
o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockOwnLifecycle leftLife leftOwner, BlockOwnLifecycle rightLife rightOwner) leftPaperBranch rightPaperBranch =
    SourceAA (leftPaperBranch leftLife) (rightPaperBranch rightLife)
      (trans (o19TransitionActorOwner (locatedTransition leftOrigin)) (trans (cong actionOwner (locatedAction leftOrigin)) leftOwner))
      (trans (o19TransitionActorOwner (locatedTransition rightOrigin)) (trans (cong actionOwner (locatedAction rightOrigin)) rightOwner))
o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockGenerated child component inserted childSafe, BlockOwnLifecycle rightLife rightOwner) leftPaperBranch rightPaperBranch =
    SourceOA child component (trans (locatedAction leftOrigin) inserted) (rightPaperBranch rightLife)
      (trans (o19TransitionActorOwner (locatedTransition rightOrigin)) (trans (cong actionOwner (locatedAction rightOrigin)) rightOwner))
      (\same => childSafe (sym same))
o19OriginalClassesConditional nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockOwnLifecycle leftLife leftOwner, BlockGenerated child component inserted childSafe) leftPaperBranch rightPaperBranch =
    SourceAO child component (trans (locatedAction rightOrigin) inserted) (leftPaperBranch leftLife)
      (\same => childSafe (trans same
        (trans (o19TransitionActorOwner (locatedTransition leftOrigin)) (trans (cong actionOwner (locatedAction leftOrigin)) leftOwner))))
      (\licensor, parentSame, ownerSame => case parentSame of
        Refl => actorDistinct swap (trans
          (sym (trans (o19TransitionActorOwner (locatedTransition leftOrigin)) (trans (cong actionOwner (locatedAction leftOrigin)) leftOwner))) ownerSame))
o19OriginalClassesConditional {name} {key} {world} {error} {value} nameEq keyEq protocol swap source premises unique leftOrigin rightOrigin
  (BlockGenerated leftChild leftComponent leftInsert leftSafe, BlockGenerated rightChild rightComponent rightInsert rightSafe)
  leftPaperBranch rightPaperBranch =
    SourceOO leftChild rightChild leftComponent rightComponent (trans (locatedAction leftOrigin) leftInsert) (trans (locatedAction rightOrigin) rightInsert)
      (o19OriginalChildrenDistinct nameEq keyEq source unique (actorLeft swap) (actorRight swap) leftChild rightChild leftComponent rightComponent (actorDistinct swap)
        (MkLocatedActionOccurrence (actionBeforeState leftOrigin) (actionAfterState leftOrigin) (beforeActionOccurrence leftOrigin)
          (locatedTransition leftOrigin) (afterActionOccurrence leftOrigin) (trans (locatedAction leftOrigin) leftInsert) (actionOccurrenceDecomposition leftOrigin))
        (MkLocatedActionOccurrence (actionBeforeState rightOrigin) (actionAfterState rightOrigin) (beforeActionOccurrence rightOrigin)
          (locatedTransition rightOrigin) (afterActionOccurrence rightOrigin) (trans (locatedAction rightOrigin) rightInsert) (actionOccurrenceDecomposition rightOrigin)))
      (\licensor, parentSame, childSame => case parentSame of Refl => rightSafe childSame)
      (\licensor, parentSame, childSame => case parentSame of Refl => leftSafe childSame)
      (o19AlignedOriginalInsertTag nameEq keyEq rightChild (ChildOf (actorRight swap)) rightComponent
        (actionBeforeState rightOrigin) (actionAfterState rightOrigin) (locatedTransition rightOrigin)
        (fst (alignedAppendSplit (MoreTransitions (locatedTransition rightOrigin) NoTransitions) (afterActionOccurrence rightOrigin)
          (snd (alignedAppendSplit (beforeActionOccurrence rightOrigin) (MoreTransitions (locatedTransition rightOrigin) (afterActionOccurrence rightOrigin))
            (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (actionOccurrenceDecomposition rightOrigin)) (replayAligned premises))))))
        (trans (locatedAction rightOrigin) rightInsert))
