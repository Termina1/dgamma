module DGamma.CP5O20PairedExecutionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20SharedBeginAdapterSpike
import DGamma.CP5O20PairedAdvanceSpike
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Indexed ACTUAL paired stages. Every constructor owns two native checked
||| edges (BeginStep owns its check). Advance payloads are actual callback and
||| capability observations. No post-cut fact, preservation function, endpoint
||| equality or generated-birth triangle is stored here. Insertion/retirement
||| gaps may concern roots OR children. Remove/failure/diversion are NOT covered.
public export
data O20PairedStage :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error) -> Type where
  PairedBeginStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    (actor : name) ->
    (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
    (0 leftOpening : BeginStep nameEq keyEq actor leftBefore leftAfter) ->
    (0 rightOpening : BeginStep nameEq keyEq (renameForward renaming actor) rightBefore rightAfter) ->
    (0 pairwise : pairwiseProvisionInvariant {name} {key} {value} {world} {error} @{keyEq} (bindings (registry rightBefore)) = True) ->
    O20PairedStage name key world error value nameEq keyEq renaming leftBefore rightBefore leftAfter rightAfter
  PairedAdvanceStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
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
    (0 leftFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView))) ->
    (0 rightFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView))) ->
    (0 leftResolved : resolveEffectValues {name} {key} {value} {world} @{keyEq} (dependencies (componentDependencies component)) leftView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) = Just leftCapability) ->
    (0 rightResolved : resolveEffectValues {name} {key} {value} {world} @{keyEq} (dependencies (componentDependencies component)) rightView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) = Just rightCapability) ->
    (0 leftRun : runStepEffect step leftCapability (MkLocalState {key} {value} {world} {provision = componentProvisions component} leftWorld (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component) (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) actor))) = Right (leftAfter, leftUndo)) ->
    (0 rightRun : runStepEffect step rightCapability (MkLocalState {key} {value} {world} {provision = componentProvisions component} rightWorld (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component) (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) (renameForward renaming actor)))) = Right (rightAfter, rightUndo)) ->
    (0 leftChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (leftTag, (MkSystemState (localWorld leftAfter) (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) leftRegistry)))) ->
    (0 rightChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (rightTag, (MkSystemState (localWorld rightAfter) (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) rightRegistry)))) ->
    O20PairedStage name key world error value nameEq keyEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState (localWorld leftAfter) (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) leftRegistry)) (MkSystemState (localWorld rightAfter) (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) rightRegistry))
  PairedEmptyFinishStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    (actor : name) ->
    (component : Component key value world error) ->
    (leftParent, rightParent : Parent name) ->
    (leftRetired, rightRetired : Bool) ->
    (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
    (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
    (leftView, rightView : View name (dependencies (componentDependencies component))) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (0 leftFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView))) ->
    (0 rightFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView))) ->
    (0 leftChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LFinishTag, (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)))) ->
    (0 rightChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (LFinishTag, (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry)))) ->
    O20PairedStage name key world error value nameEq keyEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)) (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry))
  PairedRetireStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    (actor : name) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (leftOld, rightOld : Fiber name key value world error) ->
    (0 leftFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftOld) ->
    (0 rightFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightOld) ->
    (0 leftChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORetire actor) (MkSystemState leftWorld leftRegistry) = Just (ORetireTag, MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry))) ->
    (0 rightChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORetire (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (ORetireTag, MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (retireFiber rightOld) rightRegistry))) ->
    O20PairedStage name key world error value nameEq keyEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry)) (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (retireFiber rightOld) rightRegistry))
  PairedInsertStage :
    {name, key, world, error : Type} ->
    {value : key -> Type} ->
    (nameEq : DecEq name) ->
    (keyEq : DecEq key) ->
    (renaming : NameBijection name) ->
    (actor : name) ->
    (component : Component key value world error) ->
    (leftParent, rightParent : Parent name) ->
    (0 parents : ParentRelatedBy renaming leftParent rightParent) ->
    (leftWorld, rightWorld : world) ->
    (leftRegistry, rightRegistry : Registry name key value world error) ->
    (0 leftAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Nothing) ->
    (0 rightAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Nothing) ->
    (0 leftChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) = Just (OInsertTag, MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent))) ->
    (0 rightChecked : checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (OInsert (renameForward renaming actor) rightParent component) (MkSystemState rightWorld rightRegistry) = Just (OInsertTag, MkSystemState rightWorld (insertBinding @{nameEq} (renameForward renaming actor) (freshFiber component rightParent) rightRegistry rightAbsent))) ->
    O20PairedStage name key world error value nameEq keyEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) (MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent)) (MkSystemState rightWorld (insertBinding @{nameEq} (renameForward renaming actor) (freshFiber component rightParent) rightRegistry rightAbsent))

||| Genuine one-stage all-name preservation by the five operational producers.
||| Every premise was stored as an actual observation in the stage family;
||| no preservation callback or desired post-cut field is unpacked here.
export
0 o20PairedStageCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  O20PairedStage name key world error value nameEq keyEq renaming leftBefore rightBefore leftAfter rightAfter ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  O20AllNameCut name key world error value nameEq renaming leftAfter rightAfter
o20PairedStageCut {name} {key} {world} {error} {value} nameEq keyEq renaming
  (PairedBeginStage nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening pairwise) paired =
    o20PairedActualBeginCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening paired pairwise
o20PairedStageCut {name} {key} {world} {error} {value} nameEq keyEq renaming
  (PairedAdvanceStage nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked) paired =
    o20PairedObservedAdvanceCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked paired
o20PairedStageCut {name} {key} {world} {error} {value} nameEq keyEq renaming
  (PairedEmptyFinishStage nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked) paired =
    o20PairedObservedEmptyFinishCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked paired
o20PairedStageCut {name} {key} {world} {error} {value} nameEq keyEq renaming
  (PairedRetireStage nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked) paired =
    o20PairedObservedRetireCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked paired
o20PairedStageCut {name} {key} {world} {error} {value} nameEq keyEq renaming
  (PairedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked) paired =
    o20PairedObservedInsertCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked paired
