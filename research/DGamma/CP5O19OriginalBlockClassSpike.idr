module DGamma.CP5O19OriginalBlockClassSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
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
