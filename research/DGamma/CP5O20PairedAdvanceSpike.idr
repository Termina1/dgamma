module DGamma.CP5O20PairedAdvanceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20SharedBeginAdapterSpike
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Combine the existing global effect and all-name control frame producers.
||| These are actual registry replacements, not selected-name approximations.
export
0 o20PairedRuntimeReplacementCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld, leftNextWorld, rightNextWorld : world) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftOld) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightOld) ->
  (leftNextWorld = rightNextWorld) ->
  (bindings (ownedValues (fiberTable leftNext)) = bindings (ownedValues (fiberTable rightNext))) ->
  FiberRelatedBy renaming leftNext rightNext ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  O20AllNameCut name key world error value nameEq renaming
    (MkSystemState leftNextWorld (replaceBinding @{nameEq} actor leftNext leftRegistry))
    (MkSystemState rightNextWorld (replaceBinding @{nameEq} (renameForward renaming actor) rightNext rightRegistry))
o20PairedRuntimeReplacementCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor
  leftWorld rightWorld leftNextWorld rightNextWorld leftOld rightOld leftNext rightNext leftRegistry rightRegistry
  leftFound rightFound worlds tables nextRelated paired =
    MkO20AllNameCut
      (pairedRuntimeReplacementEffects name key world error value nameEq keyEq renaming actor
        leftWorld rightWorld leftNextWorld rightNextWorld leftOld rightOld leftNext rightNext leftRegistry rightRegistry
        leftFound rightFound worlds tables (allNameEffects paired))
      (o20PairedReplaceControls nameEq renaming actor leftOld rightOld leftNext rightNext leftRegistry rightRegistry
        leftFound rightFound nextRelated (allNameControls paired))

||| Derive the precise pre-Advance metadata, accumulator and view relation
||| from the already owned fiber control relation. No successor facts assumed.
export
0 o20ReloadingControlParts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : NameBijection name} -> {component : Component key value world error} ->
  {leftParent, rightParent : Parent name} -> {leftRetired, rightRetired : Bool} ->
  {leftTable, rightTable : OwnedTable key value (componentProvisions component)} ->
  {remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))} ->
  {leftAccumulator, rightAccumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)} ->
  {leftView, rightView : View name (dependencies (componentDependencies component))} ->
  FiberRelatedBy renaming
    (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftAccumulator leftView))
    (MkFiber component rightParent rightRetired rightTable (Reloading remaining rightAccumulator rightView)) ->
  (ParentRelatedBy renaming leftParent rightParent, leftRetired = rightRetired,
    AccumulatorRelated leftAccumulator rightAccumulator, ViewRelatedBy renaming leftView rightView)
o20ReloadingControlParts (RenamedFibers leftParent rightParent leftRetired rightRetired leftTable rightTable
  (Reloading remaining leftAccumulator leftView) (Reloading remaining rightAccumulator rightView)
  parents retiredSame (RenamedReloading remainingSame accumulators views)) = (parents, retiredSame, accumulators, views)

||| Exact successful nondiverting Advance control branch of applyAction:
||| consuming the last step finishes immediately; a nonempty tail stays open.
public export
o20SuccessfulAdvanceLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  List (StepEffect key value world error deps provision) ->
  (LocalState key value world provision -> LocalState key value world provision) ->
  View name deps -> Lifecycle key value world error name deps provision
o20SuccessfulAdvanceLifecycle [] accumulator view = Active accumulator view
o20SuccessfulAdvanceLifecycle (step :: rest) accumulator view = Reloading (step :: rest) accumulator view

||| The two actual tail cases preserve full accumulator/view correspondence.
export
0 o20SuccessfulAdvanceControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} -> {renaming : NameBijection name} ->
  (remaining : List (StepEffect key value world error deps provision)) ->
  (leftAccumulator, rightAccumulator : LocalState key value world provision -> LocalState key value world provision) ->
  (leftView, rightView : View name deps) ->
  AccumulatorRelated leftAccumulator rightAccumulator -> ViewRelatedBy renaming leftView rightView ->
  LifecycleRelatedBy renaming (o20SuccessfulAdvanceLifecycle {error} remaining leftAccumulator leftView)
    (o20SuccessfulAdvanceLifecycle {error} remaining rightAccumulator rightView)
o20SuccessfulAdvanceControls {error} [] leftAccumulator rightAccumulator leftView rightView accumulators views = RenamedActive {error} accumulators views
o20SuccessfulAdvanceControls (step :: rest) leftAccumulator rightAccumulator leftView rightView accumulators views =
  RenamedReloading Refl accumulators views

||| ACTUAL observed paired successful Advance/last-step Finish. The exact two
||| checked transitions, captured capabilities and callback equations are
||| authenticated inputs. Outcome equality and EVERY successor field are
||| produced, not assumed. Canonical cut alignment remains a separate debt.
export
0 o20PairedObservedAdvanceCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAfter, rightAfter : LocalState key value world (componentProvisions component)) ->
  (leftUndo, rightUndo : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftCapability, rightCapability : DepValues key value (dependencies (componentDependencies component))) ->
  (leftTag, rightTag : RuleTag) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView))) ->
  (resolveEffectValues {name} {key} {value} {world} @{keyEq} (dependencies (componentDependencies component)) leftView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) = Just leftCapability) ->
  (resolveEffectValues {name} {key} {value} {world} @{keyEq} (dependencies (componentDependencies component)) rightView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) = Just rightCapability) ->
  (runStepEffect step leftCapability (MkLocalState {key} {value} {world} {provision = componentProvisions component} leftWorld (restrictOwnedPreservingOrder {key} {value} @{keyEq}
    (componentProvisions component) (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) actor))) = Right (leftAfter, leftUndo)) ->
  (runStepEffect step rightCapability (MkLocalState {key} {value} {world} {provision = componentProvisions component} rightWorld (restrictOwnedPreservingOrder {key} {value} @{keyEq}
    (componentProvisions component) (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry)) (renameForward renaming actor)))) = Right (rightAfter, rightUndo)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (leftTag, (MkSystemState (localWorld leftAfter) (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) leftRegistry)))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (rightTag, (MkSystemState (localWorld rightAfter) (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) rightRegistry)))) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState (localWorld leftAfter) (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) leftRegistry)) (MkSystemState (localWorld rightAfter) (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) rightRegistry))
o20PairedObservedAdvanceCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor component step rest
  leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
  leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability
  leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked paired =
    case o20ReloadingControlParts (o20PresentControl {left = (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView))} {right = (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView))}
      (rewrite sym leftFound in rewrite sym rightFound in allNameControls paired actor)) of
      (parents, retiredSame, older, views) =>
        case pairedSuccessfulOutcome name key world error value keyEq renaming
          (dependencies (componentDependencies component)) (componentProvisions component) actor step leftView rightView (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState leftWorld leftRegistry)) (projectEffectState {name} {key} {value} {world} {error} @{nameEq} (MkSystemState rightWorld rightRegistry))
          leftCapability rightCapability leftOlder rightOlder leftAfter rightAfter leftUndo rightUndo
          (allNameEffects paired) views older leftResolved rightResolved leftRun rightRun of
          (afterSame, pushed) =>
            o20PairedRuntimeReplacementCut nameEq keyEq renaming actor leftWorld rightWorld (localWorld leftAfter) (localWorld rightAfter)
              (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView)) (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView)) (MkFiber component leftParent leftRetired (localTable leftAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView)) (MkFiber component rightParent rightRetired (localTable rightAfter) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView)) leftRegistry rightRegistry leftFound rightFound (cong localWorld afterSame)
              (cong (\local => bindings (ownedValues (localTable local))) afterSame)
              (RenamedFibers leftParent rightParent leftRetired rightRetired (localTable leftAfter) (localTable rightAfter)
                (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) leftView) (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) rightView) parents retiredSame (o20SuccessfulAdvanceControls rest (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) leftOlder leftUndo) (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) rightOlder rightUndo) leftView rightView pushed views)) paired

||| Full ordered table agreement at two observed actual owner fibers.
||| This bridges the all-name projected invariant back to physical tables.
export
0 o20ObservedOwnerTablesAgree :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightFiber) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  bindings (ownedValues (fiberTable leftFiber)) = bindings (ownedValues (fiberTable rightFiber))
o20ObservedOwnerTablesAgree {name} {key} {world} {error} {value} nameEq renaming actor leftWorld rightWorld
  leftRegistry rightRegistry leftFiber rightFiber leftFound rightFound paired =
    trans (sym (cong bindings (pairedProjectOwnerTableObserved name key world error value nameEq leftWorld
      leftRegistry actor (Just leftFiber) leftFound)))
      (trans (synchronizedTables (allNameEffects paired) actor)
        (cong bindings (pairedProjectOwnerTableObserved name key world error value nameEq rightWorld
          rightRegistry (renameForward renaming actor) (Just rightFiber) rightFound)))

||| ACTUAL zero-program Finish: both checked guards/outputs are authenticated.
||| Complete ordered tables, ambient and all-name control are derived from
||| the pre-cut, including the old pointwise undo relation and captured views.
export
0 o20PairedObservedEmptyFinishCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LFinishTag, (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) = Just (LFinishTag, (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry)))) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)) (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry))
o20PairedObservedEmptyFinishCut {error} nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired
  leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry
  leftFound rightFound leftChecked rightChecked paired =
    case o20ReloadingControlParts (o20PresentControl {left = (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView))} {right = (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView))}
      (rewrite sym leftFound in rewrite sym rightFound in allNameControls paired actor)) of
      (parents, retiredSame, older, views) =>
        o20PairedRuntimeReplacementCut nameEq keyEq renaming actor leftWorld rightWorld leftWorld rightWorld
          (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView)) (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView)) (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) leftRegistry rightRegistry leftFound rightFound (synchronizedAmbient (allNameEffects paired))
          (o20ObservedOwnerTablesAgree nameEq renaming actor leftWorld rightWorld leftRegistry rightRegistry (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView)) (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView)) leftFound rightFound paired)
          (RenamedFibers leftParent rightParent leftRetired rightRetired leftTable rightTable
            (Active leftOlder leftView) (Active rightOlder rightView) parents retiredSame (RenamedActive {error} older views)) paired

||| Retirement changes only its explicit Boolean; undo, views, program and
||| component metadata are preserved for arbitrary related source controls.
export
0 o20RetireRelated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : NameBijection name} -> {left, right : Fiber name key value world error} ->
  FiberRelatedBy renaming left right -> FiberRelatedBy renaming (retireFiber left) (retireFiber right)
o20RetireRelated (RenamedFibers leftParent rightParent leftRetired rightRetired leftTable rightTable leftLifecycle rightLifecycle
  parents retiredSame lifecycle) =
    RenamedFibers leftParent rightParent True True leftTable rightTable leftLifecycle rightLifecycle parents Refl lifecycle

||| An ACTUAL paired retirement gap (root OR generated child) preserves the
||| full cut. Both native checked edges are required; no block ownership or
||| root-first assumption is imposed on this external paired-execution step.
export
0 o20PairedObservedRetireCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftOld, rightOld : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftOld) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightOld) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORetire actor) (MkSystemState leftWorld leftRegistry) =
    Just (ORetireTag, MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (ORetire (renameForward renaming actor)) (MkSystemState rightWorld rightRegistry) =
    Just (ORetireTag, MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (retireFiber rightOld) rightRegistry))) ->
  O20AllNameCut name key world error value nameEq renaming (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  O20AllNameCut name key world error value nameEq renaming
    (MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry))
    (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward renaming actor) (retireFiber rightOld) rightRegistry))
o20PairedObservedRetireCut nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry
  (MkFiber leftComponent leftParent leftRetired leftTable leftLifecycle)
  (MkFiber rightComponent rightParent rightRetired rightTable rightLifecycle) leftFound rightFound leftChecked rightChecked paired =
    o20PairedRuntimeReplacementCut nameEq keyEq renaming actor leftWorld rightWorld leftWorld rightWorld
      (MkFiber leftComponent leftParent leftRetired leftTable leftLifecycle) (MkFiber rightComponent rightParent rightRetired rightTable rightLifecycle)
      (MkFiber leftComponent leftParent True leftTable leftLifecycle) (MkFiber rightComponent rightParent True rightTable rightLifecycle)
      leftRegistry rightRegistry leftFound rightFound (synchronizedAmbient (allNameEffects paired))
      (o20ObservedOwnerTablesAgree nameEq renaming actor leftWorld rightWorld leftRegistry rightRegistry
        (MkFiber leftComponent leftParent leftRetired leftTable leftLifecycle) (MkFiber rightComponent rightParent rightRetired rightTable rightLifecycle)
        leftFound rightFound paired)
      (o20RetireRelated (o20PresentControl
        {left = MkFiber leftComponent leftParent leftRetired leftTable leftLifecycle}
        {right = MkFiber rightComponent rightParent rightRetired rightTable rightLifecycle}
        (rewrite sym leftFound in rewrite sym rightFound in allNameControls paired actor))) paired
