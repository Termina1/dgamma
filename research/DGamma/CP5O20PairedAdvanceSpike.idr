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
