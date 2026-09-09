module DGamma.CP5O20StampedHistoryFoldSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20PairedExecutionSpike
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5O20PairedRemovalSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20HistoryExecutionSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP4DeletionGenerationUnique
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Internal history cut at a FIXED live-name bijection, with the same runtime
||| and bidirectional generation fields as O20HistoryCut. The fixed index lets
||| a structural fold retain the map without equating projected observations.
||| This capital is conditional on a supplied stage synchronization; not universal pairing.
public export
record O20StampedCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (mapping : RegistrationGenerationBijection name)
  (renaming : NameBijection name)
  (leftLive, rightLive : GenerationEnvironment name)
  (left, right : SystemState name key value world error) where
  constructor MkO20StampedCut
  0 stampedRuntime : O20AllNameCut name key world error value nameEq renaming left right
  0 stampedForward : (selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected leftLive = Just stamp) ->
    (renameForward renaming selected = o20HistoricalTarget mapping stamp)
  0 stampedBackward : (selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected rightLive = Just stamp) ->
    (renameBackward renaming selected = generationName (generationBackward mapping stamp))

||| Six native paired stages with actual checks and local insertion-stamp
||| equations. The output live environments are fixed by native Insert/Remove;
||| no successor runtime cut or preservation callback is stored.
||| This is conditional on a supplied stage synchronization; not universal pairing.
public export
data O20StampedStage :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  (leftLive, rightLive, leftNext, rightNext : GenerationEnvironment name) ->
  (leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error) -> Type where
  StampedBeginStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    {mapping : RegistrationGenerationBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    (actor : name) ->
    (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
    (0 leftOpening : BeginStep nameEq keyEq actor leftBefore leftAfter) ->
    (0 rightOpening : BeginStep nameEq keyEq (renameForward renaming actor) rightBefore rightAfter) ->
    (0 pairwise : (pairwiseProvisionInvariant {name} {key} {value} {world} {error} @{keyEq} (bindings (registry rightBefore)) = True)) ->
    O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive leftLive rightLive leftBefore rightBefore leftAfter rightAfter
  StampedAdvanceStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    {mapping : RegistrationGenerationBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    (actor : name) ->
    (component : Component key value world error) ->
    (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
    (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
    (leftParent, rightParent : Parent name) ->
    (leftRetired, rightRetired : Bool) ->
    (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
    (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
    (leftView, rightView : View name (dependencies (componentDependencies component))) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (leftAfter, rightAfter : LocalState key value world (componentProvisions component)) ->
    (leftUndo, rightUndo : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
    (leftCapability, rightCapability : DepValues key value (dependencies (componentDependencies component))) ->
    (leftTag, rightTag : RuleTag) ->
    (0 leftFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView)))) ->
    (0 rightFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView)))) ->
    (0 leftResolved : (resolveEffectValues {name} {key} {value} {world} @{keyEq} (dependencies (componentDependencies component)) leftView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) = Just leftCapability)) ->
    (0 rightResolved : (resolveEffectValues {name} {key} {value} {world} @{keyEq} (dependencies (componentDependencies component)) rightView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) = Just rightCapability)) ->
    (0 leftRun : (runStepEffect step leftCapability (MkLocalState {key} {value} {world} {provision = componentProvisions component} leftWorld (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component) (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) actor))) = Right (leftAfter, leftUndo))) ->
    (0 rightRun : (runStepEffect step rightCapability (MkLocalState {key} {value} {world} {provision = componentProvisions component} rightWorld (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component) (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) (renameForward renaming actor)))) = Right (rightAfter, rightUndo))) ->
    (0 leftChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (leftTag, (MkSystemState (localWorld leftAfter) (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) leftRegistry))))) ->
    (0 rightChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (rightTag, (MkSystemState (localWorld rightAfter) (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) rightRegistry))))) ->
    O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive leftLive rightLive (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState (localWorld leftAfter) (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) leftRegistry)) (MkSystemState (localWorld rightAfter) (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) rightRegistry))
  StampedEmptyFinishStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    {mapping : RegistrationGenerationBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    (actor : name) ->
    (component : Component key value world error) ->
    (leftParent, rightParent : Parent name) ->
    (leftRetired, rightRetired : Bool) ->
    (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
    (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
    (leftView, rightView : View name (dependencies (componentDependencies component))) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (0 leftFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView)))) ->
    (0 rightFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView)))) ->
    (0 leftChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LFinishTag, (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry))))) ->
    (0 rightChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (LFinishTag, (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry))))) ->
    O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive leftLive rightLive (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)) (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry))
  StampedRetireStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    {mapping : RegistrationGenerationBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    (actor : name) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (leftOld, rightOld : Fiber name key value world error) ->
    (0 leftFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftOld)) ->
    (0 rightFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightOld)) ->
    (0 leftChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORetire actor) (MkSystemState leftWorld leftRegistry) = Just (ORetireTag, MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry)))) ->
    (0 rightChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORetire (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (ORetireTag, MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (retireFiber rightOld) rightRegistry)))) ->
    O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive leftLive rightLive (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry)) (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (retireFiber rightOld) rightRegistry))
  StampedInsertStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    {mapping : RegistrationGenerationBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    (actor : name) ->
    (component : Component key value world error) ->
    (leftParent, rightParent : Parent name) ->
    (0 parents : ParentRelatedBy renaming leftParent rightParent) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (0 leftAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Nothing)) ->
    (0 rightAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Nothing)) ->
    (0 leftChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) = Just (OInsertTag, MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent)))) ->
    (0 rightChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (OInsert (renameForward renaming actor) rightParent component) (MkSystemState rightWorld rightRegistry) = Just (OInsertTag, MkSystemState rightWorld (insertBinding @{nameEq} (renameForward renaming actor) (freshFiber component rightParent) rightRegistry rightAbsent)))) ->
    (0 matched : (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
      MkRegistrationGeneration (renameForward renaming actor) rightOrdinal)) ->
    O20StampedStage name key world error value nameEq keyEq mapping renaming leftOrdinal rightOrdinal leftLive rightLive
      (putCurrentGeneration @{nameEq} actor (MkRegistrationGeneration actor leftOrdinal) leftLive)
      (putCurrentGeneration @{nameEq} (renameForward renaming actor)
        (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive) (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent)) (MkSystemState rightWorld (insertBinding @{nameEq} (renameForward renaming actor) (freshFiber component rightParent) rightRegistry rightAbsent))
  StampedRemoveStage :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    {mapping : RegistrationGenerationBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    (actor : name) ->
    (0 leftUnique : GenerationEnvironmentNamesUnique leftLive) ->
    (0 rightUnique : GenerationEnvironmentNamesUnique rightLive) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (0 leftChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (ORemove actor) (MkSystemState leftWorld leftRegistry) =
      Just (ORemoveTag, MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry)))) ->
    (0 rightChecked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (ORemove (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) =
      Just (ORemoveTag, MkSystemState rightWorld
        (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry)))) ->
    O20StampedStage name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive
      (deleteCurrentGeneration @{nameEq} actor leftLive)
      (deleteCurrentGeneration @{nameEq} (renameForward renaming actor) rightLive)
      (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
      (MkSystemState leftWorld (deleteBinding @{nameEq} actor leftRegistry))
      (MkSystemState rightWorld (deleteBinding @{nameEq} (renameForward renaming actor) rightRegistry))

||| All six stamped native roles preserve the fixed-index cut. Runtime
||| preservation uses the actual paired-stage/Remove producers; E43 supplies
||| insertion history in both directions and removal uses unique live lookup.
||| This is conditional on a supplied stage synchronization; not universal pairing.
export
0 o20StampedStageCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftLive, rightLive, leftNext, rightNext : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming
    leftOrdinal rightOrdinal leftLive rightLive leftNext rightNext
    leftBefore rightBefore leftAfter rightAfter ->
  O20StampedCut name key world error value nameEq mapping renaming leftLive rightLive leftBefore rightBefore ->
  O20StampedCut name key world error value nameEq mapping renaming leftNext rightNext leftAfter rightAfter
o20StampedStageCut {mapping} {leftOrdinal} {rightOrdinal} {leftLive} {rightLive}
  (StampedBeginStage nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening pairwise) paired =
  MkO20StampedCut
    (o20PairedStageCut nameEq keyEq renaming
      (PairedBeginStage nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening pairwise) (stampedRuntime paired))
    (stampedForward paired) (stampedBackward paired)
o20StampedStageCut {mapping} {leftOrdinal} {rightOrdinal} {leftLive} {rightLive}
  (StampedAdvanceStage nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked) paired =
  MkO20StampedCut
    (o20PairedStageCut nameEq keyEq renaming
      (PairedAdvanceStage nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked) (stampedRuntime paired))
    (stampedForward paired) (stampedBackward paired)
o20StampedStageCut {mapping} {leftOrdinal} {rightOrdinal} {leftLive} {rightLive}
  (StampedEmptyFinishStage nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked) paired =
  MkO20StampedCut
    (o20PairedStageCut nameEq keyEq renaming
      (PairedEmptyFinishStage nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked) (stampedRuntime paired))
    (stampedForward paired) (stampedBackward paired)
o20StampedStageCut {mapping} {leftOrdinal} {rightOrdinal} {leftLive} {rightLive}
  (StampedRetireStage nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked) paired =
  MkO20StampedCut
    (o20PairedStageCut nameEq keyEq renaming
      (PairedRetireStage nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked) (stampedRuntime paired))
    (stampedForward paired) (stampedBackward paired)
o20StampedStageCut {mapping} {leftOrdinal} {rightOrdinal} {leftLive} {rightLive}
  (StampedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked matched) paired =
  MkO20StampedCut
    (o20PairedStageCut nameEq keyEq renaming
      (PairedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked) (stampedRuntime paired))
    (o20HistoryPutCompatibility nameEq (renameForward renaming) (o20HistoricalTarget mapping)
      actor (MkRegistrationGeneration actor leftOrdinal) leftLive
      (sym (cong generationName matched)) (stampedForward paired))
    (o20HistoryPutCompatibility nameEq (renameBackward renaming)
      (\stamp => generationName (generationBackward mapping stamp))
      (renameForward renaming actor) (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal)
      rightLive (trans (renameLeftInverse renaming actor)
        (sym (cong generationName (trans (cong (generationBackward mapping) (sym matched))
          (generationLeftInverse mapping (MkRegistrationGeneration actor leftOrdinal))))))
      (stampedBackward paired))
o20StampedStageCut {leftLive} {rightLive}
  (StampedRemoveStage nameEq keyEq renaming actor leftUnique rightUnique
    leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked) paired =
  MkO20StampedCut
    (o20PairedObservedRemoveCut nameEq keyEq renaming actor leftWorld rightWorld
      leftRegistry rightRegistry leftChecked rightChecked (stampedRuntime paired))
    (\selected, stamp, found => stampedForward paired selected stamp
      (o20HistoryLookupBeforeRemove nameEq actor selected leftLive leftUnique stamp found))
    (\selected, stamp, found => stampedBackward paired selected stamp
      (o20HistoryLookupBeforeRemove nameEq (renameForward renaming actor) selected rightLive rightUnique stamp found))

||| Physical stage synchronization with constructor-indexed scanner offsets
||| and live environments. Only literal same-cut ZERO-edge stuttering is
||| admitted: this does not erase any unmatched native insertion or removal.
||| This is conditional on a supplied stage synchronization; not universal pairing.
public export
data O20StampedHistory :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  (leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name) ->
  (leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error) -> Type where
  StampedHistoryEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    {left, right : SystemState name key value world error} ->
    O20StampedHistory name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive leftLive rightLive left right left right
  StampedHistoryMore :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive, leftNext, rightNext, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
    {leftBefore, rightBefore, leftMiddle, rightMiddle, leftAfter, rightAfter : SystemState name key value world error} ->
    (0 stage : O20StampedStage name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive leftNext rightNext
      leftBefore rightBefore leftMiddle rightMiddle) ->
    (0 later : O20StampedHistory name key world error value nameEq keyEq mapping renaming
      (S leftOrdinal) (S rightOrdinal) leftNext rightNext leftFinalLive rightFinalLive
      leftMiddle rightMiddle leftAfter rightAfter) ->
    O20StampedHistory name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive leftFinalLive rightFinalLive
      leftBefore rightBefore leftAfter rightAfter
  StampedHistoryEpsilon :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
    {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
    (0 leftIdle : Transitions leftBefore leftBefore) -> (0 leftZero : (transitionCount leftIdle = Z)) ->
    (0 rightIdle : Transitions rightBefore rightBefore) -> (0 rightZero : (transitionCount rightIdle = Z)) ->
    (0 later : O20StampedHistory name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive leftFinalLive rightFinalLive
      leftBefore rightBefore leftAfter rightAfter) ->
    O20StampedHistory name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive leftFinalLive rightFinalLive
      leftBefore rightBefore leftAfter rightAfter
