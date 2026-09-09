module DGamma.CP5O20StampedOrdinalNecessitySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| A pointwise stamp predicate survives put at the observed name decision.
||| Both library lookup laws concern the SAME updated environment. The observed
||| Dec carries its own library equation; no computed branch is hidden.
export
0 o20LivePredicatePutAtDecision :
  {name : Type} -> (nameEq : DecEq name) ->
  (predicate : RegistrationGeneration name -> Type) ->
  (actor : name) -> (newStamp : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  predicate newStamp ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected live = Just stamp) -> predicate stamp) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (decision : Dec (selected = actor)) -> (decEq @{nameEq} selected actor = decision) ->
  (lookupCurrentGeneration @{nameEq} selected (putCurrentGeneration @{nameEq} actor newStamp live) = Just stamp) ->
  predicate stamp
o20LivePredicatePutAtDecision nameEq predicate actor newStamp live inserted previous
  selected stamp (Yes same) observed found =
    replace {p = predicate}
      (justInjective (trans (sym (lookupPutCurrentSelf nameEq actor newStamp live))
        (trans (sym (cong (\query => lookupCurrentGeneration @{nameEq} query
          (putCurrentGeneration @{nameEq} actor newStamp live)) same)) found))) inserted
o20LivePredicatePutAtDecision nameEq predicate actor newStamp live inserted previous
  selected stamp (No different) observed found =
    previous selected stamp
      (trans (sym (lookupPutCurrentOther nameEq selected actor different newStamp live)) found)

||| Observe the ACTUAL library decider, then preserve a pointwise stamp
||| predicate through the same native generation-environment put.
export
0 o20LivePredicatePut :
  {name : Type} -> (nameEq : DecEq name) ->
  (predicate : RegistrationGeneration name -> Type) ->
  (actor : name) -> (newStamp : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  predicate newStamp ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected live = Just stamp) -> predicate stamp) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (putCurrentGeneration @{nameEq} actor newStamp live) = Just stamp) ->
  predicate stamp
o20LivePredicatePut nameEq predicate actor newStamp live inserted previous selected stamp found =
  o20LivePredicatePutAtDecision nameEq predicate actor newStamp live inserted previous
    selected stamp (decEq @{nameEq} selected actor) Refl found

||| A native stamped stage with EQUAL physical counters can only introduce
||| left live stamps whose forward generation map FIXES their birth ordinal.
||| Existing fixed stamps survive; this is a NECESSITY, not synchronization.
export
0 o20StampedStageForwardOrdinalFixed :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftLive, rightLive, leftNext, rightNext : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming
    leftOrdinal rightOrdinal leftLive rightLive leftNext rightNext
    leftBefore rightBefore leftAfter rightAfter ->
  (leftOrdinal = rightOrdinal) ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected leftLive = Just stamp) ->
    (generationBirthOrdinal (generationForward mapping stamp) = generationBirthOrdinal stamp)) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected leftNext = Just stamp) ->
  (generationBirthOrdinal (generationForward mapping stamp) = generationBirthOrdinal stamp)
o20StampedStageForwardOrdinalFixed {mapping} {leftOrdinal} {rightOrdinal} {leftLive}
  (StampedBeginStage nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening pairwise) equalCounters previous selected stamp found =
    previous selected stamp found
o20StampedStageForwardOrdinalFixed {mapping} {leftOrdinal} {rightOrdinal} {leftLive}
  (StampedAdvanceStage nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked) equalCounters previous selected stamp found =
    previous selected stamp found
o20StampedStageForwardOrdinalFixed {mapping} {leftOrdinal} {rightOrdinal} {leftLive}
  (StampedEmptyFinishStage nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked) equalCounters previous selected stamp found =
    previous selected stamp found
o20StampedStageForwardOrdinalFixed {mapping} {leftOrdinal} {rightOrdinal} {leftLive}
  (StampedRetireStage nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked) equalCounters previous selected stamp found =
    previous selected stamp found
o20StampedStageForwardOrdinalFixed {mapping} {leftOrdinal} {rightOrdinal} {leftLive}
  (StampedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked matched) equalCounters previous selected stamp found =
    o20LivePredicatePut nameEq
      (\candidate => (generationBirthOrdinal (generationForward mapping candidate) = generationBirthOrdinal candidate))
      actor (MkRegistrationGeneration actor leftOrdinal) leftLive
      (trans (cong generationBirthOrdinal matched) (sym equalCounters)) previous selected stamp found
o20StampedStageForwardOrdinalFixed {mapping} {leftOrdinal} {rightOrdinal} {leftLive}
  (StampedRemoveStage nameEq keyEq renaming actor leftUnique rightUnique
    leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked) equalCounters previous selected stamp found =
    previous selected stamp
      (o20HistoryLookupBeforeRemove nameEq actor selected leftLive leftUnique stamp found)

||| Induction over the existing finite paired history: equal starting
||| counters stay equal at each recursive stage, so EVERY surviving left
||| stamp has a forward-map-fixed birth ordinal. Zero/zero epsilon cannot
||| change that invariant. No equality of supplied trace tokens is required.
export
0 o20StampedHistoryForwardOrdinalFixed :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20StampedHistory name key world error value nameEq keyEq mapping renaming
    leftOrdinal rightOrdinal leftLive rightLive leftFinalLive rightFinalLive
    leftBefore rightBefore leftAfter rightAfter ->
  (leftOrdinal = rightOrdinal) ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected leftLive = Just stamp) ->
    (generationBirthOrdinal (generationForward mapping stamp) = generationBirthOrdinal stamp)) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected leftFinalLive = Just stamp) ->
  (generationBirthOrdinal (generationForward mapping stamp) = generationBirthOrdinal stamp)
o20StampedHistoryForwardOrdinalFixed StampedHistoryEnd equalCounters previous selected stamp found =
  previous selected stamp found
o20StampedHistoryForwardOrdinalFixed (StampedHistoryMore stage later) equalCounters previous selected stamp found =
  o20StampedHistoryForwardOrdinalFixed later (cong S equalCounters)
    (o20StampedStageForwardOrdinalFixed stage equalCounters previous) selected stamp found
o20StampedHistoryForwardOrdinalFixed (StampedHistoryEpsilon leftIdle leftZero rightIdle rightZero later)
  equalCounters previous selected stamp found =
    o20StampedHistoryForwardOrdinalFixed later equalCounters previous selected stamp found

||| NECESSARY condition of R197's endpoint/scanner synchronization itself:
||| every final left live stamp must have its birth ordinal FIXED by the map.
||| The empty initial environment discharges the entire initial predicate.
||| This result does not assert that accepted canonical inputs satisfy it.
export
0 o20SynchronizationForwardOrdinalFixed :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {left : Transitions initial leftFinal} -> {right : Transitions initial rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (synchronization : O20HistorySynchronization name key world error value nameEq keyEq mapping left right) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (synchronizationLeftLive synchronization) = Just stamp) ->
  (generationBirthOrdinal (generationForward mapping stamp) = generationBirthOrdinal stamp)
o20SynchronizationForwardOrdinalFixed mapping synchronization selected stamp found =
  o20StampedHistoryForwardOrdinalFixed (synchronizationStages synchronization) Refl
    (\query, candidate, absent => void (nothingIsNotJust absent)) selected stamp found
