module DGamma.CP5O20CanonicalPairedExtractionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

import DGamma.CP5O20CanonicalPairSelectionSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20PairedExecutionSpike

%default total
%unbound_implicits off

||| Extract BOTH actual Begin edges at the selected physical canonical cuts.
||| No pre-cut agreement or actual-stage witness is a caller premise.
||| This owns the Begin stage, not whole paired execution alignment.
export
0 o20SelectedCanonicalBeginStage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} -> {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq leftTrace rightTrace
    sameInputs leftCapital rightCapital matching operational selected) ->
  O20PairedStage name key world error value nameEq keyEq (expectedBridgeBijection sameInputs)
    (blockPreStart (pairLeftBlock pair)) (blockPreStart (pairRightBlock pair))
    (blockStart (pairLeftBlock pair)) (blockStart (pairRightBlock pair))
o20SelectedCanonicalBeginStage {name} {key} {world} {error} {value} {sameInputs} {selected}
  nameEq keyEq pair =
    PairedBeginStage nameEq keyEq (expectedBridgeBijection sameInputs) selected
      (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
      (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
      (blockOpening (pairLeftBlock pair)) (blockOpening (pairRightBlock pair))
      (registryWellFormedPairwiseOpenAnchor {name} {key} {value} {world} {error}
        nameEq keyEq (blockPreStart (pairRightBlock pair))
        (Builtin.snd (canonicalPairCutsWellFormed nameEq keyEq pair)))

||| One shared program VALUE and both physical Reloading observations. This
||| exposes the component-dependent payloads before equality elimination.
||| No callback, successor or whole-execution alignment is assumed here.
public export
record O20SharedReloadingSources
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (renaming : NameBijection name) (actor : name)
  (left, right : SystemState name key value world error) where
  constructor MkO20SharedReloadingSources
  sharedReloadComponent : Component key value world error
  sharedReloadProgram : List (StepEffect key value world error
    (dependencies (componentDependencies sharedReloadComponent)) (componentProvisions sharedReloadComponent))
  reloadLeftParent : Parent name
  reloadRightParent : Parent name
  reloadLeftRetired : Bool
  reloadRightRetired : Bool
  reloadLeftTable : OwnedTable key value (componentProvisions sharedReloadComponent)
  reloadRightTable : OwnedTable key value (componentProvisions sharedReloadComponent)
  reloadLeftOlder : LocalState key value world (componentProvisions sharedReloadComponent) -> LocalState key value world (componentProvisions sharedReloadComponent)
  reloadRightOlder : LocalState key value world (componentProvisions sharedReloadComponent) -> LocalState key value world (componentProvisions sharedReloadComponent)
  reloadLeftView : View name (dependencies (componentDependencies sharedReloadComponent))
  reloadRightView : View name (dependencies (componentDependencies sharedReloadComponent))
  0 reloadLeftFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) =
    Just (MkFiber sharedReloadComponent reloadLeftParent reloadLeftRetired reloadLeftTable
      (Reloading sharedReloadProgram reloadLeftOlder reloadLeftView)))
  0 reloadRightFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right) =
    Just (MkFiber sharedReloadComponent reloadRightParent reloadRightRetired reloadRightTable
      (Reloading sharedReloadProgram reloadRightOlder reloadRightView)))

||| The native control constructor supplies program equality. Eliminate it at
||| explicit values, never by equating projections of dependent observations.
export
0 o20ReloadingSourcesFromLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : NameBijection name} -> {actor : name} ->
  {left, right : SystemState name key value world error} ->
  (component : Component key value world error) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (rightLifecycle : Lifecycle key value world error name (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (LifecycleRelatedBy renaming (Reloading remaining leftOlder leftView) rightLifecycle) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) = Just (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right) = Just (MkFiber component rightParent rightRetired rightTable rightLifecycle)) ->
  O20SharedReloadingSources name key world error value nameEq renaming actor left right
o20ReloadingSourcesFromLifecycle component remaining leftParent rightParent leftRetired rightRetired
  leftTable rightTable leftOlder leftView (Reloading _ rightOlder rightView)
  (RenamedReloading Refl older views) leftFound rightFound =
    MkO20SharedReloadingSources component remaining leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftOlder rightOlder leftView rightView leftFound rightFound

||| Component identity is constructor-owned by FiberRelatedBy. Open that
||| constructor separately from its dependent lifecycle relation.
export
0 o20ReloadingSourcesFromFibers :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : NameBijection name} -> {actor : name} ->
  {left, right : SystemState name key value world error} ->
  (component : Component key value world error) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent : Parent name) -> (leftRetired : Bool) ->
  (leftTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (rightFiber : Fiber name key value world error) ->
  (FiberRelatedBy renaming (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftOlder leftView)) rightFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) = Just (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right) = Just rightFiber) ->
  O20SharedReloadingSources name key world error value nameEq renaming actor left right
o20ReloadingSourcesFromFibers component remaining leftParent leftRetired leftTable leftOlder leftView _
  (RenamedFibers _ rightParent _ rightRetired _ rightTable _ rightLifecycle parents retiredSame lifecycle) leftFound rightFound =
    o20ReloadingSourcesFromLifecycle component remaining leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftOlder leftView rightLifecycle lifecycle leftFound rightFound

||| Decode an EXPLICIT right lookup. The absent constructor is ruled out by
||| the genuine all-name pre-cut relation, not by an endpoint lookup oracle.
export
0 o20ReloadingSourcesFromObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : NameBijection name} -> {actor : name} ->
  {left, right : SystemState name key value world error} ->
  (component : Component key value world error) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent : Parent name) -> (leftRetired : Bool) ->
  (leftTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (MaybeFiberRelatedBy renaming (Just (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftOlder leftView))) observed) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) = Just (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right) = observed) ->
  O20SharedReloadingSources name key world error value nameEq renaming actor left right
o20ReloadingSourcesFromObservation component remaining leftParent leftRetired leftTable leftOlder leftView (Just rightFiber)
  (RenamedPresent related) leftFound rightFound =
    o20ReloadingSourcesFromFibers component remaining leftParent leftRetired leftTable leftOlder leftView rightFiber related leftFound rightFound

||| Producer of both actual same-program sources from ONE native source
||| observation and the owned pre-cut. No right observation is a premise.
export
0 o20ShareActualReloadingSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : NameBijection name} -> {actor : name} ->
  {left, right : SystemState name key value world error} ->
  (component : Component key value world error) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent : Parent name) -> (leftRetired : Bool) ->
  (leftTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) = Just (MkFiber component leftParent leftRetired leftTable (Reloading remaining leftOlder leftView))) ->
  O20AllNameCut name key world error value nameEq renaming left right ->
  O20SharedReloadingSources name key world error value nameEq renaming actor left right
o20ShareActualReloadingSource {name} {key} {world} {error} {value} {nameEq} {renaming} {actor} {right}
  component remaining leftParent leftRetired leftTable leftOlder leftView leftFound paired =
    o20ReloadingSourcesFromObservation component remaining leftParent leftRetired leftTable leftOlder leftView
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right))
      (rewrite sym leftFound in allNameControls paired actor) leftFound Refl
